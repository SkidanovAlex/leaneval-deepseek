import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs

/-!
# Tools for the top-end estimate of the chord sweep

This file fixes the vocabulary of the *wide end* of the doubly smoothed chord sweep
`Work.Drive.sweepFam` (its behaviour at sweep parameters `sig` close to `1`, where the loop is
the knot with a tiny closing chord) and proves the reparametrisation lemma that turns an
explicitly given `C^∞` increasing, period-shifting `Φ` into the `C^∞` period-shifting
reparametrisation `ρ = Φ⁻¹` used by the estimate.

## Contents

* `Work.Drive.topLoopVel` — the (a.e.) loop-parameter velocity of the chamfered loop
  `sweepLoopChamfer`, written out on its four branches (arc, two chamfers, chord).
* `Work.Drive.topCorner` — the (finite, `lam`-dependent) set of loop parameters at which the
  branch formula changes.
* `Work.Drive.topArcPar`, `Work.Drive.topArcParOfLoop` — the knot parameter of an arc point.
* `Work.Drive.exists_contDiff_inverse_of_shift` — **the reparametrisation lemma**: a `C^∞`
  function `Φ` with `Φ' > 0` everywhere and `Φ (t + p) = Φ t + p` has a `C^∞` inverse `ρ` with
  `ρ' > 0`, `ρ (t + p) = ρ t + p`, `ρ (Φ t) = t`, `Φ (ρ s) = s` and
  `deriv ρ s = (deriv Φ (ρ s))⁻¹`.

The estimate itself is `Work.Drive.sweepFamTopEstimate`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology

/-! ## The velocity of the chamfered loop -/

/-- **The loop-parameter velocity of the chamfered loop.**  With `u = sweepParam t`: on the arc
branch (`u ≤ 1/2`) the loop follows the knot, so its velocity is the knot's tangent times the
rate `((1 - 2*lam) * 2 / period) * w` at which the arc parameter advances (`w = sweepW' D sig`);
on the first chamfer the velocity is the constant chord velocity `(2 / (lam * period)) • (B - A)`
towards the chord point; on the chord branch it is the constant
`-((1 - 2*lam) / ((1/2 - lam) * period)) • (r (tbR) - r (taR))`; and on the last chamfer
`(2 / (lam * period)) • (arcPoint - chordPoint)`.  This is the `t`-derivative of the loop away
from the four corners `topCorner lam`. -/
def topLoopVel (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam : ℝ)
    (sig t : ℝ) : Space :=
  let u := sweepParam t
  if u ≤ 1 / 2 then
    (((1 - 2 * lam) * (2 / period)) * sweepW' D sig) •
      velocity r (taR D sig + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D sig)
  else if u ≤ 1 / 2 + lam / 2 then
    ((2 / lam) * (1 / period)) • (sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam))
  else if u ≤ 1 - lam / 2 then
    (-((1 - 2 * lam) / ((1 / 2 - lam) * period))) • (r (tbR D sig) - r (taR D sig))
  else
    ((2 / lam) * (1 / period)) • (sweepArc' r D sig lam - sweepChord' r D sig lam)

/-- The loop parameters at which the branch formula of `sweepLoopChamfer` changes. -/
def topCorner (lam t : ℝ) : Prop :=
  sweepParam t = 0 ∨ sweepParam t = 1 / 2 ∨ sweepParam t = 1 / 2 + lam / 2 ∨
    sweepParam t = 1 - lam / 2

/-- The knot parameter of the point of the retained arc of fraction `ξ` at sweep parameter `sig`. -/
def topArcPar {d : BandArcData} (D : SweepData d) (sig ξ : ℝ) : ℝ :=
  taR D sig + ξ * sweepW' D sig

/-- The knot parameter of the loop at fraction `u = sweepParam t` on the arc branch. -/
def topArcParOfLoop {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) : ℝ :=
  topArcPar D sig (lam + (1 - 2 * lam) * (2 * sweepParam t))

/-! ## The reparametrisation lemma -/

/-- **The inverse of an increasing period-shifting `C^∞` function is again one.**
Let `Φ : ℝ → ℝ` be `C^∞`, with `deriv Φ > 0` everywhere and `Φ (t + p) = Φ t + p` for some
`p > 0`.  Then `Φ` is a strictly increasing bijection, and its inverse `ρ` is `C^∞`, increasing,
period-shifting, with `ρ (Φ t) = t`, `Φ (ρ s) = s` and `deriv ρ s = (deriv Φ (ρ s))⁻¹`. -/
theorem exists_contDiff_inverse_of_shift {Φ : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hderiv : ∀ t : ℝ, 0 < deriv Φ t)
    (hshift : ∀ t : ℝ, Φ (t + p) = Φ t + p) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ (∀ t : ℝ, 0 < deriv ρ t) ∧
      (∀ t : ℝ, ρ (t + p) = ρ t + p) ∧ (∀ t : ℝ, ρ (Φ t) = t) ∧
      (∀ s : ℝ, Φ (ρ s) = s) ∧ (∀ s : ℝ, deriv ρ s = (deriv Φ (ρ s))⁻¹) := by
  have hmono : StrictMono Φ := strictMono_of_deriv_pos hderiv
  have hinj : Function.Injective Φ := hmono.injective
  -- the shift of the "linear part"
  have hgp : Function.Periodic (fun t : ℝ => Φ t - t) p := by
    intro t
    simp only
    rw [hshift t]
    ring
  have hint : ∀ k : ℤ, Φ ((k : ℝ) * p) = Φ 0 + (k : ℝ) * p := by
    intro k
    have h := hgp.int_mul_eq k
    have h' : Φ ((k : ℝ) * p) - (k : ℝ) * p = Φ 0 - 0 := h
    linarith
  -- `Φ` is surjective (the shift drives it to `±∞`)
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨N, hN⟩ := exists_nat_gt (|y - Φ 0| / p + 1)
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have h1 : 0 < |y - Φ 0| / p + 1 := by positivity
      linarith
    have hNp : |y - Φ 0| < (N : ℝ) * p := by
      have h2 := mul_lt_mul_of_pos_right hN hp
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul] at h2
      linarith
    set a : ℝ := -((N : ℝ) * p) with hadef
    set b : ℝ := (N : ℝ) * p with hbdef
    have hab : a ≤ b := by
      simp only [hadef, hbdef]
      nlinarith [mul_pos hN0 hp]
    have hΦb : Φ b = Φ 0 + (N : ℝ) * p := by
      have h := hint (N : ℤ)
      simpa only [hbdef, Int.cast_natCast] using h
    have hΦa : Φ a = Φ 0 - (N : ℝ) * p := by
      have h := hint (-(N : ℤ))
      have hcast : ((-(N : ℤ) : ℤ) : ℝ) = -((N : ℝ)) := by push_cast; ring
      simp only [hadef, hcast, neg_mul] at h ⊢
      exact h
    have hy : y ∈ Set.Icc (Φ a) (Φ b) := by
      rw [hΦa, hΦb]
      constructor <;> linarith [(abs_le.mp (le_of_lt hNp)).1, (abs_le.mp (le_of_lt hNp)).2]
    have hcont : ContinuousOn Φ (Set.Icc a b) := hsm.continuous.continuousOn
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab hcont hy
    exact ⟨t, ht⟩
  -- the inverse and its strict derivative
  have hleft : ∀ t : ℝ, Function.invFun Φ (Φ t) = t :=
    fun t => Function.leftInverse_invFun hinj t
  have hright : ∀ s : ℝ, Φ (Function.invFun Φ s) = s :=
    fun s => Function.rightInverse_invFun hsurj s
  have hstrict : ∀ s : ℝ,
      HasStrictDerivAt (Function.invFun Φ) ((deriv Φ (Function.invFun Φ s))⁻¹) s := by
    intro s
    obtain ⟨u, hu⟩ := hsurj s
    have hρs : Function.invFun Φ s = u := by rw [← hu]; exact hleft u
    have hf : HasStrictDerivAt Φ (deriv Φ u) u :=
      (hsm.contDiffAt.hasStrictDerivAt (by simp))
    have hf' : deriv Φ u ≠ 0 := ne_of_gt (hderiv u)
    have hg : ∀ᶠ x in 𝓝 u, Function.invFun Φ (Φ x) = x :=
      Filter.Eventually.of_forall (fun x => hleft x)
    have hmain : HasStrictDerivAt (Function.invFun Φ) (deriv Φ u)⁻¹ s := by
      have := hf.to_local_left_inverse hf' hg
      rwa [hu] at this
    rwa [hρs]
  have hdiff : Differentiable ℝ (Function.invFun Φ) :=
    fun s => (hstrict s).hasDerivAt.differentiableAt
  have hderivρ : ∀ s : ℝ, deriv (Function.invFun Φ) s = (deriv Φ (Function.invFun Φ s))⁻¹ :=
    fun s => (hstrict s).hasDerivAt.deriv
  -- `C^n` by induction on `n`
  have hCn : ∀ k : ℕ, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (Function.invFun Φ) := by
    intro k
    induction k with
    | zero => exact contDiff_zero.mpr hdiff.continuous
    | succ k ih =>
      have hcast : (((k + 1 : ℕ) : ℕ) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast; ring
      rw [hcast, contDiff_succ_iff_deriv]
      refine ⟨hdiff, ?_, ?_⟩
      · intro h
        exact absurd h (by simp)
      · have hfun : deriv (Function.invFun Φ)
            = fun s : ℝ => (deriv Φ (Function.invFun Φ s))⁻¹ := funext hderivρ
        rw [hfun]
        have hΦ : ContDiff ℝ (((k : ℕ) : WithTop ℕ∞) + 1) Φ := by
          refine hsm.of_le ?_
          rw [show ((k : ℕ) : WithTop ℕ∞) + 1 = (((k + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) from by
            push_cast; ring]
          exact WithTop.coe_le_coe.mpr le_top
        have hdΦ : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (deriv Φ) :=
          (contDiff_succ_iff_deriv.mp hΦ).2.2
        exact (hdΦ.comp ih).inv (fun s => ne_of_gt (hderiv (Function.invFun Φ s)))
  refine ⟨Function.invFun Φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_infty]
    exact hCn
  · intro t
    rw [hderivρ t]
    exact inv_pos.mpr (hderiv (Function.invFun Φ t))
  · intro t
    have h1 : Φ (Function.invFun Φ (t + p)) = t + p := hright (t + p)
    have h2 : Φ (Function.invFun Φ t + p) = Φ (Function.invFun Φ t) + p := hshift _
    rw [hright t] at h2
    exact hinj (by rw [h1, h2])
  · intro t
    exact hleft t
  · intro s
    exact hright s
  · intro s
    exact hderivρ s

end Work.Drive
