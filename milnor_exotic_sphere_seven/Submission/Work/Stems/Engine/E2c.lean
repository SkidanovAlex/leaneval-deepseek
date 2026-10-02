import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2a
import Submission.Work.Serre.serreE2b
import Submission.Work.StemsB.hasHLP_pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# E2(c) for the Serre chapter, proved from the relative cube HLP

`Work.Serre.SerreE2c` (the third of the four statements of the blueprint's `E2`, in the form
prescribed by the lead's ADDENDUM 1) says: for a Serre fibration `p : E → B` and a cube map
`τ : Iⁿ → B` with a point `d₀ ∈ Iⁿ`, the pair `(τ^*E, F_{d₀})` — the pullback of `p` along `τ`
together with the fibre of the pullback projection over `d₀` — has vanishing integral homology.

The proof is the compression argument of the blueprint: `Iⁿ` is convex, so the straight-line
contraction of `τ^*E` onto `F_{d₀}` (in the *base* coordinate, lifted through the Serre fibration
`pullbackSnd p τ`, whose lifting is `Work.StemsB.hasHLP_pullback`) is a homotopy of every cube in
`τ^*E` into `F_{d₀}`, relative to its boundary; `Work.Serre.serreE2b` (the relative cone
construction of ADDENDUM 1 (C)) then gives the vanishing of the relative homology.

The point of isolating this lemma is that it is the `n`-cube case of the cell step `K4` of the
blueprint's ADDENDUM 2 engine (`K4(c) = E2(d)` builds on it), so it is on the critical path of
`Work.Drive.RationalHurewiczStable` -> area THOM and of `Work.Drive.StableStemsTorsion`.
-/

open scoped Topology unitInterval

namespace Work.Stems.Engine

noncomputable section

/-- The straight-line contraction of the cube `Iⁿ` to the point `d₀`, as a continuous map
`Iⁿ × I → Iⁿ` (coordinatewise on `I = [0,1]`, which is convex). -/
def lineCM (n : ℕ) (d₀ : Work.Stems.Cubical.IC n) :
    C(Work.Stems.Cubical.IC n × unitInterval, Work.Stems.Cubical.IC n) where
  toFun p := fun i => ⟨(1 - (p.2 : ℝ)) * (p.1 i : ℝ) + (p.2 : ℝ) * (d₀ i : ℝ), by
    have ha : (0 : ℝ) ≤ ((p.1 i : unitInterval) : ℝ) ∧ (((p.1 i : unitInterval)) : ℝ) ≤ 1 :=
      (p.1 i).2
    have hb : (0 : ℝ) ≤ ((d₀ i : unitInterval) : ℝ) ∧ (((d₀ i : unitInterval)) : ℝ) ≤ 1 :=
      (d₀ i).2
    have hs : (0 : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 := p.2.2
    exact ⟨by nlinarith [ha.1, ha.2, hb.1, hb.2, hs.1, hs.2],
      by nlinarith [ha.1, ha.2, hb.1, hb.2, hs.1, hs.2]⟩⟩
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro i
    apply Continuous.subtype_mk
    show Continuous fun p : Work.Stems.Cubical.IC n × unitInterval =>
      (1 - (p.2 : ℝ)) * (p.1 i : ℝ) + (p.2 : ℝ) * (d₀ i : ℝ)
    fun_prop

@[simp] theorem lineCM_zero (n : ℕ) (d₀ x : Work.Stems.Cubical.IC n) :
    lineCM n d₀ (x, 0) = x := by
  funext i
  apply Subtype.ext
  simp [lineCM]

@[simp] theorem lineCM_one (n : ℕ) (d₀ x : Work.Stems.Cubical.IC n) :
    lineCM n d₀ (x, 1) = d₀ := by
  funext i
  apply Subtype.ext
  simp [lineCM]

theorem lineCM_self (n : ℕ) (d₀ : Work.Stems.Cubical.IC n) (s : unitInterval) :
    lineCM n d₀ (d₀, s) = d₀ := by
  funext i
  show (⟨(1 - (s : ℝ)) * (((d₀ i : unitInterval)) : ℝ) + (s : ℝ) * (((d₀ i : unitInterval)) : ℝ),
      (lineCM n d₀ (d₀, s) i).2⟩ : unitInterval) = d₀ i
  exact Subtype.ext (by ring)

/-- The coordinate swap `(s, x) ↦ (x, s)`, used to match the `(space, time)` convention of the
relative cube HLP with the `(time, space)` convention of `ContinuousMap.Homotopy`. -/
def swapCM (n : ℕ) : C(unitInterval × Work.Stems.Cubical.IC n,
    Work.Stems.Cubical.IC n × unitInterval) where
  toFun p := (p.2, p.1)
  continuous_toFun := by fun_prop

/-- **E2(c)**, proved from the relative cube HLP (E2(a)) and the relative cone construction
(E2(b)). -/
theorem serreE2c : Work.Serre.SerreE2c := by
  intro E B _ _ p n hp τ d₀ k
  -- the pullback projection is a Serre fibration
  have hfib : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p τ) :=
    fun m => Work.StemsB.hasHLP_pullback p τ (hp m)
  -- the fibre of the pullback projection over `d₀`
  set A : Set (Work.StemsB.Pullback p τ) :=
    {x | Work.StemsB.pullbackSnd p τ x = d₀} with hA
  -- it suffices to produce the compression hypothesis of E2(b)
  refine Work.Serre.serreE2b (Work.StemsB.Pullback p τ) A k ?_ k le_rfl
  intro m hm f hf
  -- the base map of `f` and the straight-line homotopy of the base coordinate
  let β : C(Work.Stems.Cubical.IC m, Work.Stems.Cubical.IC n) :=
    (Work.StemsB.pullbackSnd p τ).comp f
  let H : C(Work.Stems.Cubical.IC m × unitInterval, Work.Stems.Cubical.IC n) :=
    (lineCM n d₀).comp ⟨fun w : Work.Stems.Cubical.IC m × unitInterval => (β w.1, w.2),
      by fun_prop⟩
  -- the prescribed lift on the hat `I^m × 0 ∪ ∂I^m × I`: the constant-in-time `f`
  let gHat : C(↥(Work.Serre.hatSet m), Work.StemsB.Pullback p τ) :=
    f.comp ⟨fun w => w.1.1, by fun_prop⟩
  -- the compatibility on the hat
  have hcompat : (Work.StemsB.pullbackSnd p τ).comp gHat = H.comp (Work.Serre.hatIncl m) := by
    apply ContinuousMap.ext
    intro w
    rcases w.2 with h0 | hbdry
    · -- on `I^m × {0}` the base coordinate is unchanged
      show Work.StemsB.pullbackSnd p τ (f w.1.1) = lineCM n d₀ (β w.1.1, w.1.2)
      rw [h0, lineCM_zero]
      rfl
    · -- on `∂I^m × I` the base coordinate is already `d₀`
      show Work.StemsB.pullbackSnd p τ (f w.1.1) = lineCM n d₀ (β w.1.1, w.1.2)
      have hb : β w.1.1 = d₀ := hf w.1.1 hbdry
      rw [hb, lineCM_self]
      exact hb
  -- lift the homotopy
  obtain ⟨G, hG, hGhat⟩ :=
    Work.Serre.serreE2a (Work.StemsB.Pullback p τ) (Work.Stems.Cubical.IC n)
      (Work.StemsB.pullbackSnd p τ) m hfib H gHat hcompat
  -- the end map of the lifted homotopy lies in the fibre
  let gEnd : C(Work.Stems.Cubical.IC m, Work.StemsB.Pullback p τ) :=
    G.comp ⟨fun x => (x, 1), by fun_prop⟩
  refine ⟨gEnd, ?_, ?_⟩
  · -- `gEnd` lands in `A`
    intro x
    show Work.StemsB.pullbackSnd p τ (G (x, 1)) = d₀
    have hx : Work.StemsB.pullbackSnd p τ (G (x, 1)) = H (x, 1) := by
      have := congrArg (fun u : C(Work.Stems.Cubical.IC m × unitInterval,
        Work.Stems.Cubical.IC n) => u (x, 1)) hG
      simpa using this
    rw [hx]
    show lineCM n d₀ (β x, 1) = d₀
    rw [lineCM_one]
  · -- `gEnd` is homotopic to `f` relative to the boundary
    refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
    · refine { toContinuousMap := ?_, map_zero_left := ?_, map_one_left := ?_ }
      · exact ⟨fun q : unitInterval × Work.Stems.Cubical.IC m => G (q.2, q.1), by fun_prop⟩
      · -- at time `0` it is `f`
        intro x
        have hx : G (x, 0) = gHat ⟨(x, 0), Or.inl rfl⟩ := hGhat ⟨(x, 0), Or.inl rfl⟩
        show G (x, 0) = f x
        rw [hx]
        rfl
      · -- at time `1` it is `gEnd`
        intro x
        rfl
    · -- it is constant along the boundary
      intro s x hx
      have hxs : G (x, s) = gHat ⟨(x, s), Or.inr hx⟩ := hGhat ⟨(x, s), Or.inr hx⟩
      show G (x, s) = f x
      rw [hxs]
      rfl

end

end Work.Stems.Engine
