import Mathlib
import Submission.Work.GM.S3.Defs

namespace Work.GM.S3

open MeasureTheory

open Submission.GM (Rfun)

/-- **Support/`sup` bound for the `ψ₂`-weighted fourth power of `R`.**  If `ψ₂` is a bump at `1`
with `IsBumpAtOne ψ₂ 16` (so it is non-negative and supported in `[1/16,16]`) and
`∀ x, |ψ₂ x| ≤ s` with `0 ≤ s`, then for every `W`

`∫_ℝ ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4 dy ≤ s ^ 2 * ∫_{1/16}^{16} ‖Rfun W v‖ ^ 4 dv`.

Proof: `ψ₂ y ^ 2 ≤ s ^ 2 * 1_{[1/16,16]} y` pointwise (outside the support `ψ₂` vanishes), so
`∫_ℝ ψ₂ y ^ 2 ‖Rfun W y‖ ^ 4 dy = ∫_{y ∈ Icc (1/16) 16} ψ₂ y ^ 2 ‖Rfun W y‖ ^ 4 dy
≤ ∫_{y ∈ Icc (1/16) 16} s ^ 2 ‖Rfun W y‖ ^ 4 dy = s ^ 2 ∫_{1/16}^{16} ‖Rfun W v‖ ^ 4 dv`
(set-integral comparison; `y ↦ ‖Rfun W y‖ ^ 4` is continuous on `Icc (1/16) 16`, a compact set
of finite measure, so all integrability needed is automatic; use
`MeasureTheory.integral_Icc_eq_integral_Ioc` together with `intervalIntegral.integral_of_le` to
convert the set integral over `Icc (1/16) 16` into the interval integral). -/
theorem integral_psi2_sq_le (ψ₂ : ℝ → ℝ) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 16) (s : ℝ) (hs : 0 ≤ s)
    (hsb : ∀ x, |ψ₂ x| ≤ s) (W : Finset ℝ) :
    ∫ y, ψ₂ y ^ 2 * ‖Submission.GM.Rfun W y‖ ^ 4
      ≤ s ^ 2 * ∫ v in (1 / 16 : ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 4 := by
  classical
  have hIcc : (1 / 16 : ℝ) ≤ 16 := by norm_num
  -- ψ₂ is continuous, hence so is the integrand on `Icc (1/16) 16`
  have hcontψ : Continuous ψ₂ := hψ₂.1.continuous
  have hRcont : ContinuousOn (fun v : ℝ => ‖Rfun W v‖ ^ 4) (Set.Icc (1 / 16 : ℝ) 16) := by
    intro v hv
    have hv0 : v ≠ 0 := by
      have : (0 : ℝ) < v := lt_of_lt_of_le (by norm_num) hv.1
      exact ne_of_gt this
    exact ((continuousAt_Rfun W hv0).norm.pow 4).continuousWithinAt
  have hf_int : IntegrableOn (fun y : ℝ => ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4)
      (Set.Icc (1 / 16 : ℝ) 16) :=
    ((hcontψ.continuousOn.pow 2).mul hRcont).integrableOn_compact isCompact_Icc
  have hg_int : IntegrableOn (fun y : ℝ => s ^ 2 * ‖Rfun W y‖ ^ 4)
      (Set.Icc (1 / 16 : ℝ) 16) :=
    ((continuousOn_const.mul hRcont)).integrableOn_compact isCompact_Icc
  -- ψ₂ vanishes off its support `[1/16, 16]`
  have hzero : ∀ x ∉ Set.Icc (1 / 16 : ℝ) 16,
      ψ₂ x ^ 2 * ‖Rfun W x‖ ^ 4 = 0 := by
    intro x hx
    have hx0 : ψ₂ x = 0 := by
      by_contra h
      exact hx (hψ₂.2.2.1 x h)
    rw [hx0]
    simp
  -- the integral over ℝ is the integral over the support
  have hint1 : ∫ y, ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4
      = ∫ y in Set.Icc (1 / 16 : ℝ) 16, ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- pointwise comparison on the support
  have hmono : ∫ y in Set.Icc (1 / 16 : ℝ) 16, ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4
      ≤ ∫ y in Set.Icc (1 / 16 : ℝ) 16, s ^ 2 * ‖Rfun W y‖ ^ 4 :=
    setIntegral_mono_on hf_int hg_int measurableSet_Icc fun x _ => by
      have h1 : ψ₂ x ≤ s := (abs_le.mp (hsb x)).2
      have h2 : -s ≤ ψ₂ x := (abs_le.mp (hsb x)).1
      have hx1 : ψ₂ x ^ 2 ≤ s ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hx1 (by positivity)
  have hconst : ∫ y in Set.Icc (1 / 16 : ℝ) 16, s ^ 2 * ‖Rfun W y‖ ^ 4
      = s ^ 2 * ∫ y in Set.Icc (1 / 16 : ℝ) 16, ‖Rfun W y‖ ^ 4 :=
    integral_const_mul (s ^ 2) (fun y : ℝ => ‖Rfun W y‖ ^ 4)
  have hIoc : ∫ y in Set.Icc (1 / 16 : ℝ) 16, ‖Rfun W y‖ ^ 4
      = ∫ y in (1 / 16 : ℝ)..16, ‖Rfun W y‖ ^ 4 := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hIcc]
  calc ∫ y, ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4
      = ∫ y in Set.Icc (1 / 16 : ℝ) 16, ψ₂ y ^ 2 * ‖Rfun W y‖ ^ 4 := hint1
    _ ≤ ∫ y in Set.Icc (1 / 16 : ℝ) 16, s ^ 2 * ‖Rfun W y‖ ^ 4 := hmono
    _ = s ^ 2 * ∫ y in Set.Icc (1 / 16 : ℝ) 16, ‖Rfun W y‖ ^ 4 := hconst
    _ = s ^ 2 * ∫ v in (1 / 16 : ℝ)..16, ‖Rfun W v‖ ^ 4 := by rw [hIoc]

end Work.GM.S3
