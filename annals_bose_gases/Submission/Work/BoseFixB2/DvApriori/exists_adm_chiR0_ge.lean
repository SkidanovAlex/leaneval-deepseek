import ChallengeDeps
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

/-!
# The diluteness threshold at which the box side dominates `R / chiR0`

`sideAt μ a = a · (μa³)^{-163/323}` (FS `eq:def_ell` at the diluteness-correct
parameters), so as `μ → 0⁺` the box side blows up like a negative power of the
diluteness.  Hence the "large box" condition `R ≤ sideAt μ a · chiR0` of the
comparison argument (`Submission.Work.FSKernelCompare`, `Work.BoseFixGlue.ℓB_ge`,
`Work.BoseKinLoc.Pot.potInput_holds`) holds on *all* of the admissible region
`Adm v ε₀ μ` once the diluteness cut-off `ε₀` is small enough:

the admissible region is `0 < μ ∧ μa³ ≤ ε₀ ∧ ParamsOK …`, and the diluteness bound
`μa³ ≤ ε₀` alone already converts into a lower bound for the negative power,
`(μa³)^{-163/323} ≥ ε₀^{-163/323}`, uniformly in `μ`.  Choosing
`ε₀ = min 1 (R/(a·chiR0))^{-323/163}` makes `ε₀^{-163/323} ≥ R/(a·chiR0)`, whence
`sideAt μ a ≥ a·R/(a·chiR0) = R/chiR0`, i.e. `R ≤ sideAt μ a · chiR0`.

This is the pointwise-in-`μ` form of `Work.BoseBox.sideAt_large` (which is an
`∀ᶠ` statement at `μ → 0⁺`); the explicit threshold is what lets the diluteness
bound `μa³ ≤ ε₀` of the `Adm` predicate be used directly, with no `ParamsOK`
input.
-/

/-- **The diluteness threshold making the box side dominate `R / chiR0`.**

For every scale `R > 0` there is `ε₀ > 0` such that every admissible chemical
potential (`Work.BoseBoxFix.Adm v ε₀ μ`, whose diluteness clause is
`μ·(a v)³ ≤ ε₀`) produces a box of side `sideAt μ (a v)` at least `R / chiR0`:

  `R ≤ sideAt μ (a v) · chiR0`.

Explicitly `ε₀ = min 1 ((R / (a v · chiR0))^{-323/163})`, coming from
`sideAt μ a = a (μa³)^{-163/323}` and the monotonicity of the negative power in
the diluteness. -/
theorem exists_adm_chiR0_ge (v : EuclideanSpace ℝ (Fin 3) → ℝ) (hav : 0 < _root_.BoseGases.a v)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
  have ha : 0 < _root_.BoseGases.a v := hav
  have hχ : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have haχ : 0 < _root_.BoseGases.a v * Submission.BoseGases.chiR0 := mul_pos ha hχ
  -- The reference diluteness at which the two factors `a` and `chiR0` are balanced.
  set t₀ : ℝ := R / (_root_.BoseGases.a v * Submission.BoseGases.chiR0) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; exact div_pos hR haχ
  have hKpos : 0 < t₀ ^ (-(323 / 163 : ℝ)) := Real.rpow_pos_of_pos ht₀pos _
  refine ⟨min 1 (t₀ ^ (-(323 / 163 : ℝ))), lt_min one_pos hKpos, ?_⟩
  intro μ hμ
  have hμpos : 0 < μ := hμ.1
  have hμa3le : μ * (_root_.BoseGases.a v) ^ 3 ≤ min 1 (t₀ ^ (-(323 / 163 : ℝ))) := hμ.2.1
  have hε₀pos : 0 < min 1 (t₀ ^ (-(323 / 163 : ℝ))) := lt_min one_pos hKpos
  have hε₀le : min 1 (t₀ ^ (-(323 / 163 : ℝ))) ≤ t₀ ^ (-(323 / 163 : ℝ)) := min_le_right _ _
  have hμa3pos : 0 < μ * (_root_.BoseGases.a v) ^ 3 :=
    mul_pos hμpos (pow_pos ha 3)
  -- Step 1: undoing the outer negative power on the reference value.
  have h₁ : t₀ ≤ (t₀ ^ (-(323 / 163 : ℝ))) ^ (-(163 / 323 : ℝ)) := by
    rw [← Real.rpow_mul ht₀pos.le,
      show (-(323 / 163 : ℝ)) * (-(163 / 323 : ℝ)) = 1 by norm_num, Real.rpow_one]
  -- Step 2: the threshold `ε₀` is below the reference value; exponents negative.
  have h₂ : (t₀ ^ (-(323 / 163 : ℝ))) ^ (-(163 / 323 : ℝ))
      ≤ (min 1 (t₀ ^ (-(323 / 163 : ℝ)))) ^ (-(163 / 323 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hε₀pos hε₀le (by norm_num)
  -- Step 3: the diluteness bound transfers to the negative power, uniformly in `μ`.
  have h₃ : (min 1 (t₀ ^ (-(323 / 163 : ℝ)))) ^ (-(163 / 323 : ℝ))
      ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hμa3pos hμa3le (by norm_num)
  have hkey : t₀ ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) :=
    le_trans h₁ (le_trans h₂ h₃)
  -- `sideAt μ a = a (μa³)^{-163/323}` dominates `a · t₀ = R / chiR0`.
  have hside : _root_.BoseGases.a v * t₀
      ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBox.sideAt_eq_rpow ha hμpos]
    exact mul_le_mul_of_nonneg_left hkey ha.le
  have hR_eq : _root_.BoseGases.a v * t₀ * Submission.BoseGases.chiR0 = R := by
    rw [ht₀]
    field_simp
  calc R = _root_.BoseGases.a v * t₀ * Submission.BoseGases.chiR0 := hR_eq.symm
    _ ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
        mul_le_mul_of_nonneg_right hside hχ.le

end Work.BoseFixB2.DvApriori
