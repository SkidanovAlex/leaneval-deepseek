import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BandSdefs
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.BandSizeArithB1` — the band-size arithmetic of the low-density bound

FS's `μ ↦ 4μ` band carries the factor `ℓ³·bandK·bandS²` (`ℓ = sideAt μ (a v)`, the
regularity `M = mValue = 48`, `d = (paramsAt μ (a v)).d`).  This file shows that this
factor is bounded uniformly in the admissible `μ` by a constant times `a v`:

    ∃ ε₀ K, 0 < ε₀ ∧ 0 ≤ K ∧ ∀ μ, Adm v ε₀ μ →
      ℓ³·bandK v h M·(bandS M ℓ d μ)² ≤ K·(a v) .

The whole content is the exact monomial identity of the box side and the band
`χ`-scale at FS's parameters (with `t = μ (a v)³`, `X = t^{1/323}`):

    ℓ³·(bandS 48 ℓ d μ)² = chiSupAbs²·(chiSmallDecay 48)²·2^96·(a v)³·t^{4247/323}

(`bandS_sq` plus `chiSmallBandDecay = chiSupAbs²(chiSmallDecay M)²(d⁻¹)^{2M}` plus
`d⁻¹^{96} = t^{-576}`, `(μ^{-1/3}ℓ⁻¹)^{96} = t^{5312}`, `ℓ³ = (a v)³ t^{-489}`, and
`-489 - 576 + 5312 = 4247`), together with the diluteness bound `t ≤ ε₀ = 1`, which
kills the positive power `t^{4247/323}`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The `fsXp` bookkeeping of the two blocks of the band factor -/

/-- `((paramsAt μ A).d)⁻¹ ^ 96 = fsXp (μA³) (-576)`: the `d`-part of
`chiSmallBandDecay 48 (paramsAt μ A).d`. -/
private lemma d_inv_pow96 {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    ((Work.BoseBox.paramsAt μ A).d)⁻¹ ^ 96 = Work.BoseBox.fsXp (μ * A ^ 3) (-576) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_inv ht, Work.BoseBox.fsXp_pow ht.le]
  norm_num

/-- `μ^{-1/3} ℓ⁻¹ = fsXp (μA³) (166/3)`. -/
private lemma mu_inv_third_mul_sideAt_inv {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ ^ (-1 / 3 : ℝ) * (Work.BoseBox.sideAt μ A)⁻¹
      = Work.BoseBox.fsXp (μ * A ^ 3) (166 / 3) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hinv : (Work.BoseBox.fsXp (μ * A ^ 3) (-163))⁻¹
      = Work.BoseBox.fsXp (μ * A ^ 3) 163 := by
    rw [Work.BoseBox.fsXp_inv ht, show (-(-163) : ℝ) = 163 by norm_num]
  rw [show (-1 / 3 : ℝ) = -(1 / 3) by norm_num,
    Work.BoseFixB1.mu_inv_third_eq hA hμ, Work.BoseFixB1.sideAt_eq_fsXp hA hμ,
    mul_inv_rev, hinv]
  have hstep : A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))
        * (Work.BoseBox.fsXp (μ * A ^ 3) 163 * A⁻¹)
      = Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))
        * Work.BoseBox.fsXp (μ * A ^ 3) 163 := by
    calc A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))
          * (Work.BoseBox.fsXp (μ * A ^ 3) 163 * A⁻¹)
        = (A * A⁻¹) * (Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))
            * Work.BoseBox.fsXp (μ * A ^ 3) 163) := by ring
      _ = 1 * (Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))
            * Work.BoseBox.fsXp (μ * A ^ 3) 163) := by
            rw [mul_inv_cancel₀ (ne_of_gt hA)]
      _ = _ := by ring
  rw [hstep, Work.BoseBox.fsXp_mul ht]
  rw [show (-(323 / 3 : ℝ)) + 163 = 166 / 3 by norm_num]

/-- `(μ^{-1/3} ℓ⁻¹)^96 = fsXp (μA³) 5312`. -/
private lemma mu_inv_third_mul_sideAt_inv_pow96 {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (μ ^ (-1 / 3 : ℝ) * (Work.BoseBox.sideAt μ A)⁻¹) ^ 96
      = Work.BoseBox.fsXp (μ * A ^ 3) 5312 := by
  have ht : 0 < μ * A ^ 3 := by positivity
  rw [mu_inv_third_mul_sideAt_inv hA hμ, Work.BoseBox.fsXp_pow ht.le]
  norm_num

/-! ## 2. The band-size identity -/

/-- **The band-size identity at FS's parameters** (regularity `M = 48`):

    ℓ³·(bandS 48 ℓ d μ)² = chiSupAbs²·(chiSmallDecay 48)²·2^96·A³·(μA³)^{4247/323} .

This is the exact monomial form quoted in the literature of
`Submission/Work/BoseFixB1S/BandPerBoxCrudeB1.lean` (there with `fsXp (μA³) 4247`). -/
lemma bandS_cube_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (Work.BoseBox.sideAt μ A) ^ 3
      * (Work.BoseFixB1.bandS 48 (Work.BoseBox.sideAt μ A)
          (Work.BoseBox.paramsAt μ A).d μ) ^ 2
      = Submission.BoseGases.chiSupAbs ^ 2
          * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * 2 ^ 96 * A ^ 3
          * (μ * A ^ 3) ^ (4247 / 323 : ℝ) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hℓ : 0 < Work.BoseBox.sideAt μ A := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp hA hμ]
    exact mul_pos hA (Work.BoseBox.fsXp_pos (c := -163) ht)
  have hd : 0 < (Work.BoseBox.paramsAt μ A).d :=
    Work.BoseBox.fsXp_pos (t := μ * A ^ 3) (c := 6) ht
  have hband : Submission.BoseGases.chiSmallBandDecay 48 (Work.BoseBox.paramsAt μ A).d
      = Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * ((Work.BoseBox.paramsAt μ A).d)⁻¹ ^ 96 := rfl
  have hsplit : (2 * μ ^ (-1 / 3 : ℝ) / Work.BoseBox.sideAt μ A) ^ 96
      = 2 ^ 96 * (μ ^ (-1 / 3 : ℝ) * (Work.BoseBox.sideAt μ A)⁻¹) ^ 96 := by
    rw [div_eq_mul_inv]; ring_nf
  have hkey : (Work.BoseBox.sideAt μ A) ^ 3
        * (Work.BoseFixB1.bandS 48 (Work.BoseBox.sideAt μ A)
            (Work.BoseBox.paramsAt μ A).d μ) ^ 2
      = (Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
            * 2 ^ 96) * A ^ 3
          * (Work.BoseBox.fsXp (μ * A ^ 3) (-489) * Work.BoseBox.fsXp (μ * A ^ 3) (-576)
              * Work.BoseBox.fsXp (μ * A ^ 3) 5312) := by
    rw [Work.BoseFixB1.bandS_sq (M := 48) hℓ hd hμ]
    rw [show (2 * 48 : ℕ) = 96 by norm_num]
    rw [hband, d_inv_pow96 hA hμ, hsplit, mu_inv_third_mul_sideAt_inv_pow96 hA hμ,
      Work.BoseFixB1.sideAt_cube_eq hA hμ]
    ring
  rw [hkey]
  have hmerge3 : Work.BoseBox.fsXp (μ * A ^ 3) (-489) * Work.BoseBox.fsXp (μ * A ^ 3) (-576)
      * Work.BoseBox.fsXp (μ * A ^ 3) 5312 = (μ * A ^ 3) ^ (4247 / 323 : ℝ) := by
    rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]
    rw [show ((-489 : ℝ) + -576 + 5312) = 4247 by norm_num]
    rfl
  rw [hmerge3]

/-! ## 3. The target -/

theorem BandSizeArithB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
            * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
            * (Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) ^ 2
          ≤ K * (_root_.BoseGases.a v) := by
  set A : ℝ := _root_.BoseGases.a v with hAdef
  have hA : 0 < A := by rw [hAdef]; exact hav
  set Kc : ℝ := Submission.BoseGases.chiSupAbs ^ 2
    * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * 2 ^ 96 with hKcdef
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    exact mul_nonneg (mul_nonneg (pow_nonneg Submission.BoseGases.chiSupAbs_nonneg 2)
      (pow_nonneg (Submission.BoseGases.chiSmallDecay_nonneg 48) 2)) (by norm_num)
  refine ⟨1, Work.BoseFixB1.bandK v h 48 * Kc * A ^ 2, one_pos,
    mul_nonneg (mul_nonneg (Work.BoseFixB1.bandK_nonneg 48) hKc0) (sq_nonneg A), ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ht1 : μ * A ^ 3 ≤ 1 := by
    have h1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := Work.BoseFixB1.adm_dilute hAdm
    simpa [hAdef] using h1
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hA 3)
  have hM48 : (Work.BoseBox.paramsAt μ A).M = 48 := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  rw [hM48]
  have hKcnn : 0 ≤ Submission.BoseGases.chiSupAbs ^ 2
      * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * 2 ^ 96 * A ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg Submission.BoseGases.chiSupAbs_nonneg 2)
      (pow_nonneg (Submission.BoseGases.chiSmallDecay_nonneg 48) 2)) (by norm_num))
      (pow_nonneg hA.le 3)
  have hstep : (Work.BoseBox.sideAt μ A) ^ 3
      * (Work.BoseFixB1.bandS 48 (Work.BoseBox.sideAt μ A)
          (Work.BoseBox.paramsAt μ A).d μ) ^ 2
      ≤ Submission.BoseGases.chiSupAbs ^ 2
          * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * 2 ^ 96 * A ^ 3 := by
    rw [bandS_cube_eq (A := A) (μ := μ) hA hμ]
    exact mul_le_of_le_one_right hKcnn
      (Real.rpow_le_one (le_of_lt ht0) ht1 (by norm_num))
  calc (Work.BoseBox.sideAt μ A) ^ 3 * Work.BoseFixB1.bandK v h 48
        * (Work.BoseFixB1.bandS 48 (Work.BoseBox.sideAt μ A)
            (Work.BoseBox.paramsAt μ A).d μ) ^ 2
      = Work.BoseFixB1.bandK v h 48
          * ((Work.BoseBox.sideAt μ A) ^ 3
              * (Work.BoseFixB1.bandS 48 (Work.BoseBox.sideAt μ A)
                  (Work.BoseBox.paramsAt μ A).d μ) ^ 2) := by ring
    _ ≤ Work.BoseFixB1.bandK v h 48
          * (Submission.BoseGases.chiSupAbs ^ 2
              * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * 2 ^ 96 * A ^ 3) :=
        mul_le_mul_of_nonneg_left hstep (Work.BoseFixB1.bandK_nonneg 48)
    _ = (Work.BoseFixB1.bandK v h 48 * Kc * A ^ 2) * A := by
        rw [hKcdef]; ring

end Work.BoseFixB1S
