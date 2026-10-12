import ChallengeDeps
import Submission.Work.BoseRowsL.Defs
import Submission.Work.BoseRowsL.Regime.rkh_rpow_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Regime

/-!
# `Work.BoseRowsL.Regime.rkh_threshold` — FS's régime row `(R/ℓ)² ≤ K_H⁻¹` at the honest model

The row `rkh` of `Work.BoseRowsL.HonestInterfaceL` (and of
`Work.BoseRowsFS.HonestInterface`) is the statement

  `(R / ℓ)² ≤ K_H⁻¹`

at the honest data `honE v h fc fu HM μ`, at diluteness `μ(a v)³` below a threshold.  It is a
pure *parameter* row: no state, no mode choice and no geometry enters, so it holds with an
absolute threshold depending only on `R` and `a v`.

## The computation

With `t := μ (a v)³` the honest environment's two scalars unfold (definitionally) to

* `ℓ = K_ℓ (μ a v)^{-1/2}` with `K_ℓ = fsXp t (-3/2) = t^{-3/646}`, hence
  `ℓ² = (a v)² t^{-326/323}`, i.e. `ℓ² = (a v)² / t^{326/323}` (`honE_ell_sq`);
* `K_H = fsXp t (-8/3) · t^{-5/12} = t^{-549/1292}`, hence
  `K_H⁻¹ = t^{549/1292}` (`honE_KH_eq`).

So the row is exactly

  `R² t^{326/323} ≤ (a v)² t^{549/1292}`,

which, since `326/323 - 549/1292 = 755/1292 > 0`, is implied by
`t^{755/1292} ≤ (a v)²/R²`.  The latter follows from the threshold
`t ≤ ((a v)²/(2R²))^{1292/755}`: `1292/755` is the reciprocal of `755/1292`, so raising to the
power `755/1292` gives `t^{755/1292} ≤ (a v)²/(2R²) ≤ (a v)²/R²`.  That real-arithmetic step is
the delegated lemma `Work.BoseRowsL.Regime.rkh_rpow_arith`
(`Submission/Work/BoseRowsL/Regime/rkh_rpow_arith.lean`).
-/

open scoped BigOperators

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option linter.unusedVariables false

/-! ## 1. The two honest scalars, unfolded -/

/-- **The honest `K_H`, in closed form**: `K_H = (t^{549/1292})⁻¹` with `t = μ(a v)³`.

Indeed `(honE …).KH = K̃_H (μa³)^{-5/12}` with `K̃_H = fsXp t (-8/3) = t^{-8/969}`, and
`t^{-8/969}·t^{-5/12} = t^{-549/1292}`. -/
lemma honE_KH_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) (hμ : 0 < μ) (hA : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).KH
      = ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((549 : ℝ) / 1292))⁻¹ := by
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have h0 : (Work.BoseRowsFS.honE v h fc fu HM μ).KH
      = Work.BoseB7.KH (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(8 / 3))) μ
          (_root_.BoseGases.a v) := rfl
  rw [h0, Work.BoseB7.KH]
  rw [Work.BoseBox.fsXp]
  rw [show (-(8 / 3 : ℝ)) / 323 = -(8 / 969) by norm_num]
  rw [← Real.rpow_add ht0]
  rw [show (-(8 / 969 : ℝ)) + (-(5 / 12)) = -(549 / 1292) by norm_num]
  rw [Real.rpow_neg ht0.le]

/-- **The honest box side, squared**: `ℓ² = (a v)² / t^{326/323}` with `t = μ(a v)³`.

Indeed `ℓ = K_ℓ (μ a v)^{-1/2}` with `K_ℓ = fsXp t (-3/2) = t^{-3/646}`, so
`ℓ² = t^{-3/323} (μ a v)^{-1} = t^{-3/323} (a v)²/t = (a v)² t^{-326/323}`. -/
lemma honE_ell_sq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) (hμ : 0 < μ) (hA : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 2
      = (_root_.BoseGases.a v) ^ 2 / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((326 : ℝ) / 323) := by
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hμA : 0 < μ * (_root_.BoseGases.a v) := by positivity
  have hell : (Work.BoseRowsFS.honE v h fc fu HM μ).ell
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2))
          * (μ * (_root_.BoseGases.a v)) ^ (-(1 / 2 : ℝ)) := by
    have h0 : (Work.BoseRowsFS.honE v h fc fu HM μ).ell
        = Work.BoseBox.boxSide (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
            (_root_.BoseGases.a v) := rfl
    rw [h0, Work.BoseBox.boxSide]
    rfl
  rw [hell, mul_pow]
  have hsq1 : (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2))) ^ 2
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 323 : ℝ)) := by
    rw [Work.BoseBox.fsXp_pow (le_of_lt ht0) (-(3 / 2)) 2]
    rw [show (-(3 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = (-(3 : ℝ)) by norm_num]
    rw [Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hsq2 : ((μ * (_root_.BoseGases.a v)) ^ (-(1 / 2 : ℝ))) ^ 2
      = (μ * (_root_.BoseGases.a v)) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hμA)]
    congr 1
    norm_num
  rw [hsq1, hsq2]
  have hinv : (μ * (_root_.BoseGases.a v)) ^ (-(1 : ℝ))
      = (_root_.BoseGases.a v) ^ 2 / (μ * (_root_.BoseGases.a v) ^ 3) := by
    rw [Real.rpow_neg_one, eq_div_iff (by positivity : μ * (_root_.BoseGases.a v) ^ 3 ≠ 0),
      show μ * (_root_.BoseGases.a v) ^ 3
          = (μ * (_root_.BoseGases.a v)) * (_root_.BoseGases.a v) ^ 2 by ring,
      inv_mul_cancel_left₀ (by positivity : μ * (_root_.BoseGases.a v) ≠ 0)]
  rw [hinv]
  have hcomb : (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 323 : ℝ))
      * ((_root_.BoseGases.a v) ^ 2 / (μ * (_root_.BoseGases.a v) ^ 3))
      = (_root_.BoseGases.a v) ^ 2
          / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((326 : ℝ) / 323) := by
    have h1 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 323 : ℝ))
        * ((_root_.BoseGases.a v) ^ 2 / (μ * (_root_.BoseGases.a v) ^ 3))
        = (_root_.BoseGases.a v) ^ 2 * ((μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 323 : ℝ))
            * (μ * (_root_.BoseGases.a v) ^ 3)⁻¹) := by
      rw [div_eq_mul_inv]; ring
    have h2 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 323 : ℝ))
        * (μ * (_root_.BoseGases.a v) ^ 3)⁻¹
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(326 / 323 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
      congr 1
      norm_num
    have h3 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(326 / 323 : ℝ))
        = ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((326 : ℝ) / 323))⁻¹ :=
      Real.rpow_neg ht0.le _
    rw [h1, h2, h3, ← div_eq_mul_inv]
  rw [hcomb]

/-! ## 2. The régime row -/

/-- **FS's régime row `(R/ℓ)² ≤ K_H⁻¹` at the honest model**, with an absolute threshold.

There is `ε₁ > 0` (namely `((a v)²/(2R²))^{1292/755}`, which depends only on `R` and `a v`) such
that for every choice `HM` of honest modes and every `μ > 0` with `μ(a v)³ ≤ ε₁` one has
`(R/ℓ)² ≤ K_H⁻¹` at `honE v h fc fu HM μ`.

By §1 the row is `R² t^{326/323} ≤ (a v)² t^{549/1292}` with `t = μ(a v)³`, and since
`326/323 - 549/1292 = 755/1292`, this is implied by `t^{755/1292} ≤ (a v)²/R²`, which is
`rkh_rpow_arith` at the threshold. -/
theorem rkh_threshold {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
      0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε₁ →
      (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 2
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).KH⁻¹ := by
  refine ⟨((_root_.BoseGases.a v) ^ 2 / (2 * R ^ 2)) ^ ((1292 : ℝ) / 755), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) _
  · intro HM μ hμ ht
    have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    rw [div_pow, honE_ell_sq HM μ hμ hav, honE_KH_eq HM μ hμ hav, inv_inv,
      div_div_eq_mul_div]
    exact rkh_rpow_arith hR hav ht0 ht

end Work.BoseRowsL.Regime
