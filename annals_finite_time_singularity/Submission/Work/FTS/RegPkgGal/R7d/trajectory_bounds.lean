/-
# `Work.FTS.RegPkgGal.R7d.trajectory_bounds`

A priori bounds along a trajectory of the (fake-time reversed) characteristic ODE

  `ż = -z·Vz(z,θ,τ₀-t)`,  `θ̇ = -Vθ(z,θ,τ₀-t)`,

for a velocity field whose components are *pointwise* bounded by

  `0 ≤ Vz z θ τ ≤ a`,  `|Vθ z θ τ| ≤ K·θ`,  `|Vθ z θ τ| ≤ K·(π/2-θ)`

on the *open* region `z > 0`, `0 < θ < π/2`, `0 < τ ≤ S`.  Both the hypotheses and the
conclusion only concern points where the trajectory is *strictly* inside the open quadrant, so
a naive Grönwall argument is circular (`Vz ≥ 0` is only available once `z > 0` is known, and
`Vz ≤ a`/the `Vθ`-bounds are only available once `0 < θ < π/2` is known).

The proof therefore bootstraps on the maximal time up to which the trajectory is strictly good:

* `hbounds` — if the trajectory is strictly inside the open quadrant on `(0,b)`, then the four
  a priori bounds hold on `[0,b]`.  This is where the delegated pieces `zBounds` and `thBounds`
  are applied, using `τ₀ - x > 0` for `x < b ≤ T ≤ τ₀` so that the pointwise bounds on the
  velocity field are available;
* `G` is the set of times `b ∈ [0,T]` up to which the trajectory is strictly inside the open
  quadrant; `G` is nonempty, bounded above by `T`, and `sSup G` cannot be `< T` (otherwise
  `quadrant_extend` keeps the trajectory strictly inside on a further right neighbourhood of
  `sSup G`, contradicting maximality);
* hence `sSup G = T`, the trajectory is strictly inside on `(0,T)`, and `hbounds` at `b = T`
  gives the four bounds on all of `[0,T]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.R7d.zBounds
import Submission.Work.FTS.RegPkgGal.R7d.thBounds
import Submission.Work.FTS.RegPkgGal.R7d.quadrant_extend

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open Set Filter
open scoped Topology

/-- The first coordinate of a curve with values in `ℝ × ℝ` is differentiable, with the first
coordinate of the derivative. -/
theorem hasDerivAt_fst {α : ℝ → ℝ × ℝ} {x : ℝ} {v : ℝ × ℝ} (h : HasDerivAt α v x) :
    HasDerivAt (fun y => (α y).1) v.1 x := by
  rw [hasDerivAt_iff_hasFDerivAt] at h
  have h2 : HasFDerivAt (fun y => (α y).1)
      (ContinuousLinearMap.toSpanSingleton ℝ v.1) x := by
    have hh := h.fst
    convert hh using 1
    ext w
    simp [ContinuousLinearMap.comp_apply]
  simpa using h2.hasDerivAt

/-- The second coordinate of a curve with values in `ℝ × ℝ` is differentiable, with the second
coordinate of the derivative. -/
theorem hasDerivAt_snd {α : ℝ → ℝ × ℝ} {x : ℝ} {v : ℝ × ℝ} (h : HasDerivAt α v x) :
    HasDerivAt (fun y => (α y).2) v.2 x := by
  rw [hasDerivAt_iff_hasFDerivAt] at h
  have h2 : HasFDerivAt (fun y => (α y).2)
      (ContinuousLinearMap.toSpanSingleton ℝ v.2) x := by
    have hh := h.snd
    convert hh using 1
    ext w
    simp [ContinuousLinearMap.comp_apply]
  simpa using h2.hasDerivAt

theorem trajectory_bounds {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {a K S τ₀ T z₀ θ₀ : ℝ}
    {α : ℝ → ℝ × ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ τ₀) (hτ₀S : τ₀ ≤ S)
    (hz₀ : 0 < z₀) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < Real.pi / 2)
    (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hα0 : α 0 = (z₀, θ₀))
    (hode : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α
      (-((α t).1 * Vz (α t).1 (α t).2 (τ₀ - t)), -(Vθ (α t).1 (α t).2 (τ₀ - t)))
      (Set.Icc (0:ℝ) T) t)
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθl : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      |Vθ z θ τ| ≤ K * θ)
    (hVθu : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ)) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      z₀ * Real.exp (-(a * t)) ≤ (α t).1 ∧ (α t).1 ≤ z₀ ∧
      θ₀ * Real.exp (-(K * t)) ≤ (α t).2 ∧
      (α t).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * t)) := by
  -- ## Step 1: continuity of the trajectory and its derivative at interior times
  have hαc : ContinuousOn α (Set.Icc (0:ℝ) T) :=
    fun t ht => (hode t ht).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) T, HasDerivAt α
      (-((α x).1 * Vz (α x).1 (α x).2 (τ₀ - x)), -(Vθ (α x).1 (α x).2 (τ₀ - x))) x :=
    fun x hx => (hode x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  -- ## Step 2: the four bounds on `[0,b]`, given that the trajectory is strictly inside the
  -- open quadrant on `(0,b)`
  have hbounds : ∀ b ∈ Set.Icc (0:ℝ) T,
      (∀ x ∈ Set.Ioo (0:ℝ) b, 0 < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2) →
      ∀ x ∈ Set.Icc (0:ℝ) b,
        z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ ∧
        θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
        (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) := by
    intro b hb hQ
    -- the fake time `τ₀ - x` is strictly positive and at most `S` on `(0,b)`
    have hτpos : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 < τ₀ - x := by
      intro x hx
      have hxτ : x < τ₀ := lt_of_lt_of_le (lt_of_lt_of_le hx.2 hb.2) hTS
      linarith
    have hτle : ∀ x ∈ Set.Ioo (0:ℝ) b, τ₀ - x ≤ S := by
      intro x hx
      linarith [hx.1, hτ₀S]
    have hbc : ContinuousOn α (Set.Icc (0:ℝ) b) := hαc.mono (Icc_subset_Icc le_rfl hb.2)
    -- the `z`-bounds
    have hzB : ∀ x ∈ Set.Icc (0:ℝ) b,
        z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ :=
      zBounds (z := fun x => (α x).1) (V := fun x => Vz (α x).1 (α x).2 (τ₀ - x))
        (a := a) (z₀ := z₀) (T := b) hbc.fst (by rw [hα0])
        (fun x hx => hasDerivAt_fst (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hb.2⟩))
        (fun x hx => hVz0 _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => hVza _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => (hQ x hx).1.le)
    -- the `θ`-bounds
    have hθB : ∀ x ∈ Set.Icc (0:ℝ) b,
        θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
        (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) :=
      thBounds (θ := fun x => (α x).2) (V := fun x => Vθ (α x).1 (α x).2 (τ₀ - x))
        (K := K) (θ₀ := θ₀) (T := b) hbc.snd (by rw [hα0])
        (fun x hx => hasDerivAt_snd (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hb.2⟩))
        (fun x hx => hVθl _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => hVθu _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
    intro x hx
    exact ⟨(hzB x hx).1, (hzB x hx).2, (hθB x hx).1, (hθB x hx).2⟩
  -- ## Step 3: the bootstrap on the maximal time of strict interiority
  set G : Set ℝ := {b | b ∈ Set.Icc (0:ℝ) T ∧
    ∀ x ∈ Set.Ioo (0:ℝ) b, 0 < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2}
  have hG0 : (0 : ℝ) ∈ G := by
    refine ⟨⟨le_rfl, hT⟩, ?_⟩
    intro x hx
    exact absurd hx.1 (not_lt.mpr hx.2.le)
  have hGne : G.Nonempty := ⟨0, hG0⟩
  have hGbdd : BddAbove G := ⟨T, fun b hb => hb.1.2⟩
  have hσ0 : 0 ≤ sSup G := le_csSup hGbdd hG0
  have hσT : sSup G ≤ T := (csSup_le_iff hGbdd hGne).mpr (fun b hb => hb.1.2)
  -- the trajectory is strictly inside on `(0, sSup G)`
  have hQsSup : ∀ x ∈ Set.Ioo (0:ℝ) (sSup G),
      0 < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
    intro x hx
    obtain ⟨b, hbG, hxb⟩ := (lt_csSup_iff hGbdd hGne).mp hx.2
    exact hbG.2 x ⟨hx.1, hxb⟩
  -- hence the bounds hold on `[0, sSup G]`
  have hPsSup : ∀ x ∈ Set.Icc (0:ℝ) (sSup G),
      z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ ∧
      θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
      (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) :=
    hbounds (sSup G) ⟨hσ0, hσT⟩ hQsSup
  have hPsSup' := hPsSup (sSup G) ⟨hσ0, le_rfl⟩
  -- strict interiority at `sSup G`
  have hQσ : 0 < (α (sSup G)).1 ∧ 0 < (α (sSup G)).2 ∧ (α (sSup G)).2 < Real.pi / 2 := by
    refine ⟨?_, ?_, ?_⟩
    · have hpos : 0 < z₀ * Real.exp (-(a * sSup G)) := mul_pos hz₀ (Real.exp_pos _)
      linarith [hPsSup'.1]
    · have hpos : 0 < θ₀ * Real.exp (-(K * sSup G)) := mul_pos hθ₀ (Real.exp_pos _)
      linarith [hPsSup'.2.2.1]
    · have hpos : 0 < (Real.pi / 2 - θ₀) * Real.exp (-(K * sSup G)) :=
        mul_pos (by linarith) (Real.exp_pos _)
      linarith [hPsSup'.2.2.2]
  -- `sSup G` is maximal: it cannot be strictly below `T`
  have hσeq : sSup G = T := by
    rcases lt_or_eq_of_le hσT with hlt | heq
    · exfalso
      obtain ⟨δ, hδ0, hσδT, hQδ⟩ :=
        quadrant_extend hσ0 hlt hαc hQσ.1 hQσ.2.1 hQσ.2.2
      have hmem : sSup G + δ ∈ G := by
        refine ⟨⟨by linarith, hσδT⟩, fun x hx => ?_⟩
        rcases lt_trichotomy x (sSup G) with hlt' | heq' | hgt'
        · exact hQsSup x ⟨hx.1, hlt'⟩
        · rw [heq']; exact hQσ
        · exact hQδ x ⟨hgt', hx.2⟩
      have hle : sSup G + δ ≤ sSup G := le_csSup hGbdd hmem
      linarith
    · exact heq
  -- ## Step 4: conclusion
  have hQT : ∀ x ∈ Set.Ioo (0:ℝ) T,
      0 < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
    intro x hx
    rw [← hσeq] at hx
    exact hQsSup x hx
  exact hbounds T ⟨hT, le_rfl⟩ hQT

end Work.FTS.RegPkgGal.R7d
