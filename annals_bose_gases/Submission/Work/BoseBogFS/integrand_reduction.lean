import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBogFS.CleanRowDefs
import Submission.Work.BoseBogFS.ZPCleanDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The scaling layer

`P := ρ·(a v) > 0` is the momentum unit.  Two elementary facts drive everything:

* `𝒵(𝒫A,𝒫B) = 𝒫·𝒵(A,B)` for `𝒫 > 0`, where `𝒵 = bogZeroPoint = A − √(A²−B²)`
  (`Work.BoseB6.bogZeroPoint`).  This is **unconditional**: when `A² − B² < 0` the square
  root is junk `0` on both sides, so the identity survives;
* the mass term `B²/(2T)` scales by the same rule, because `(𝒫B)²/(2·𝒫T) = 𝒫·(B²/(2T))`
  (with the junk convention `x/0 = 0` this also holds for `T = 0`).

Together with `‖√P • t‖² = P‖t‖²` (`norm_smul_sqrt_sq`), these give the pointwise scaling
of the honest clean integrand, and the integral identity is then the Haar change of
variables `∫ f(R⁻¹ • x) = R^{finrank} ∫ f`. -/

/-- **The zero point scales**: `𝒵(𝒫A,𝒫B) = 𝒫·𝒵(A,B)` for `𝒫 > 0`, unconditionally
(the junk branch `A² − B² < 0` scales as well, both square roots being `0`). -/
lemma bogZeroPoint_scale_mul {P A B : ℝ} (hP : 0 < P) :
    Work.BoseB6.bogZeroPoint (P * A) (P * B) = P * Work.BoseB6.bogZeroPoint A B := by
  have h : Real.sqrt ((P * A) ^ 2 - (P * B) ^ 2) = P * Real.sqrt (A ^ 2 - B ^ 2) := by
    have h1 : (P * A) ^ 2 - (P * B) ^ 2 = P ^ 2 * (A ^ 2 - B ^ 2) := by ring
    rw [h1, Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq_eq_abs, abs_of_pos hP]
  unfold Work.BoseB6.bogZeroPoint
  rw [h, mul_sub]

/-- **The mass term scales**: `(𝒫B)²/(2·𝒫T) = 𝒫·(B²/(2T))` for `𝒫 > 0` (junk-compatible
at `T = 0`). -/
lemma div_norm_scale_mul {P B T : ℝ} (hP : 0 < P) :
    (P * B) ^ 2 / (2 * (P * T)) = P * (B ^ 2 / (2 * T)) := by
  by_cases hT : T = 0
  · subst hT; simp
  · field_simp

/-- The `5/2` bookkeeping of the integral identity: `P·((√P)³·X) = P^{5/2}·X` for `P > 0`. -/
lemma mul_sqrt_cube {P X : ℝ} (hP : 0 < P) :
    P * (Real.sqrt P ^ 3 * X) = P ^ (5 / 2 : ℝ) * X := by
  rw [show Real.sqrt P ^ 3 = P * Real.sqrt P by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, Real.sq_sqrt hP.le, pow_one],
      show P ^ (5 / 2 : ℝ) = P ^ 2 * Real.sqrt P by
        rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hP, ← Real.sqrt_eq_rpow]
        rw [Real.rpow_two]]
  ring

/-- **The pointwise scaling of the clean integrand** (the first conjunct of the target),
in the forward direction `t ↦ √P • t`. -/
lemma cleanFun_scaled_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {ρ μ : ℝ}
    (hP : 0 < ρ * a v) (t : EuclideanSpace ℝ (Fin 3)) :
    cleanFun v h ρ μ (Real.sqrt (ρ * a v) • t) = (ρ * a v) * psiSc v h ρ μ t := by
  have hτ : tauAt v μ (Real.sqrt (ρ * a v) • t) + cAt v h ρ μ (Real.sqrt (ρ * a v) • t)
      = (ρ * a v) * (tauSc v ρ μ t + betaSc v h ρ μ t) := by
    simp only [tauSc, betaSc]
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hP), one_mul, one_mul]
  have hc : cAt v h ρ μ (Real.sqrt (ρ * a v) • t) = (ρ * a v) * betaSc v h ρ μ t := by
    simp only [betaSc]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hP), one_mul]
  rw [cleanFun, psiSc, hτ, hc, norm_smul_sqrt_sq hP t, bogZeroPoint_scale_mul hP,
    div_norm_scale_mul hP, mul_sub]

/-- **The pointwise scaling of the clean integrand** (the second conjunct of the target),
in the inverse direction `k ↦ (√P)⁻¹ • k`. -/
lemma cleanFun_eq_scaled {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {ρ μ : ℝ}
    (hP : 0 < ρ * a v) (k : EuclideanSpace ℝ (Fin 3)) :
    cleanFun v h ρ μ k
      = (ρ * a v) * psiSc v h ρ μ ((Real.sqrt (ρ * a v))⁻¹ • k) := by
  have hh := cleanFun_scaled_eq (v := v) (h := h) (ρ := ρ) (μ := μ) hP
    ((Real.sqrt (ρ * a v))⁻¹ • k)
  rwa [smul_inv_smul₀ (ne_of_gt (Real.sqrt_pos.mpr hP))] at hh

/-- **The scaling identity of the clean row.**  With `P = ρ·(a v) > 0`, the honest clean
integrand is `P` times the scaled one at `t = k/√P`:
`cleanFun k = P·psiSc (√P)⁻¹k`, and consequently `∫cleanFun = P^{5/2}∫psiSc`.
Both hold **unconditionally** (`bogZeroPoint` is junk `A` where `A²−B² < 0` on both sides,
and the mass term rescales exactly). -/
theorem integrand_reduction {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ρ μ : ℝ} (hP : 0 < ρ * _root_.BoseGases.a v) :
    (∀ t : EuclideanSpace ℝ (Fin 3),
        Work.BoseBogFS.cleanFun v h ρ μ (Real.sqrt (ρ * _root_.BoseGases.a v) • t)
          = (ρ * _root_.BoseGases.a v) * Work.BoseBogFS.psiSc v h ρ μ t)
      ∧ (∀ k : EuclideanSpace ℝ (Fin 3),
          Work.BoseBogFS.cleanFun v h ρ μ k
            = (ρ * _root_.BoseGases.a v)
              * Work.BoseBogFS.psiSc v h ρ μ ((Real.sqrt (ρ * _root_.BoseGases.a v))⁻¹ • k))
      ∧ (∫ k : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.cleanFun v h ρ μ k)
          = (ρ * _root_.BoseGases.a v) ^ (5 / 2 : ℝ)
            * ∫ t : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.psiSc v h ρ μ t := by
  refine ⟨fun t => ?_, fun k => ?_, ?_⟩
  · exact cleanFun_scaled_eq hP t
  · exact cleanFun_eq_scaled hP k
  · simp_rw [cleanFun_eq_scaled hP]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := MeasureTheory.volume)
        (psiSc v h ρ μ) (Real.sqrt_nonneg (ρ * a v)),
      finrank_euclideanSpace]
    norm_num
    exact mul_sqrt_cube hP

end

end Work.BoseBogFS
