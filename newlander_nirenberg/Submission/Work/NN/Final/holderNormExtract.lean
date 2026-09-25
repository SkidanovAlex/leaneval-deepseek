/-
Copyright: none.  Part of the Newlander-Nirenberg formalisation project.

# Unpacking a `holderNorm 0 α` bound: the pointwise sup and Hölder bounds

The hypothesis of `UniformDbarL2` (and of every statement in the project's perturbation chain) is a
bound `holderNorm 0 α g (pd n ρ 4) ≤ ofReal ε` for the components `g` of the perturbation.  Every
analytic estimate in the routes to it consumes instead the two *pointwise* consequences:

* `‖g z‖ ≤ ε` (the sup bound),
* `‖g z − g z'‖ ≤ ε ‖z − z'‖^α` (the Hölder bound).

Both are immediate from the definition of `holderNorm` as
`iterDerivNorm 0 + holderSeminorm 0` (`Work.CR.Flat.le_iterDerivNorm`,
`Work.CR.Flat.le_holderSeminorm`, together with
`Work.CR.Flat.norm_apply_le_holderNorm` and the identification
`dist_iteratedFDerivWithin_zero`), and this module records them as reusable lemmas so that
downstream files do not have to redo the `ENNReal`/`iteratedFDerivWithin 0` bookkeeping.

Note the hypothesis `0 ≤ A`: it cannot be dropped, since `ENNReal.ofReal A = 0` for `A < 0` would
then be a vacuous hypothesis.
-/
import Mathlib
import Submission.Work.NN.Final.dbarStarDefs
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Final

open MeasureTheory Set
open scoped NNReal ENNReal Topology

noncomputable section

variable {n : ℕ}

/-- **The sup bound from a `C^{0,α}` bound.** -/
theorem norm_le_of_holderNorm_zero_le {α A : ℝ} (hA : 0 ≤ A) {Ω : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (h : Work.CR.Flat.holderNorm 0 α g Ω ≤ ENNReal.ofReal A) :
    ∀ z ∈ Ω, ‖g z‖ ≤ A := by
  intro z hz
  exact (ENNReal.ofReal_le_ofReal_iff hA).mp
    (le_trans (Work.CR.Flat.norm_apply_le_holderNorm 0 α g Ω hz) h)

/-- **The Hölder bound from a `C^{0,α}` bound.** -/
theorem norm_sub_le_of_holderNorm_zero_le {α A : ℝ} (hA : 0 ≤ A) {Ω : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (h : Work.CR.Flat.holderNorm 0 α g Ω ≤ ENNReal.ofReal A) :
    ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖g z - g z'‖ ≤ A * ‖z - z'‖ ^ α := by
  intro z hz z' hz'
  by_cases hzz : z = z'
  · subst hzz
    simp only [sub_self, norm_zero]
    exact mul_nonneg hA (Real.rpow_nonneg le_rfl α)
  have h1 : ENNReal.ofReal (‖g z - g z'‖ / ‖z - z'‖ ^ α)
      ≤ Work.CR.Flat.holderSeminorm 0 α g Ω := by
    have hle := Work.CR.Flat.le_holderSeminorm 0 α g Ω hz hz' hzz
    rwa [show ‖iteratedFDerivWithin ℝ 0 g Ω z - iteratedFDerivWithin ℝ 0 g Ω z'‖
        = ‖g z - g z'‖ from by
      simpa [dist_eq_norm] using dist_iteratedFDerivWithin_zero (𝕜 := ℝ) g Ω z g Ω z'] at hle
  have h2 : Work.CR.Flat.holderSeminorm 0 α g Ω ≤ Work.CR.Flat.holderNorm 0 α g Ω :=
    Work.CR.Flat.holderSeminorm_le_holderNorm 0 α g Ω (le_refl 0)
  have hstep : ENNReal.ofReal (‖g z - g z'‖ / ‖z - z'‖ ^ α) ≤ ENNReal.ofReal A :=
    le_trans h1 (le_trans h2 h)
  have hdiv : ‖g z - g z'‖ / ‖z - z'‖ ^ α ≤ A :=
    (ENNReal.ofReal_le_ofReal_iff hA).mp hstep
  have hpos : 0 < ‖z - z'‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
  rw [div_le_iff₀ hpos] at hdiv
  exact hdiv

end

end Work.NN.Final
