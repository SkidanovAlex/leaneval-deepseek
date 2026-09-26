import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.E4cube_cusp_second

/-!
# The second-order cusp expansion of the `j`-invariant

With `E = e^{πiτ}` (`‖E‖ = e^{-π Im τ}`) and `q = E² = e^{2πiτ}` the modular `j`-invariant
`j = E₄³/Δ` has the `q`-expansion `j = q⁻¹ + 744 + O(q)`, i.e.

`j(z) = (E(z)⁻¹)² + 744 + O(‖E(z)‖²)`  as `Im z → ∞`.

We prove this from two second-order cusp estimates:

* `E₄³ = 1 + 720 q + O(‖q‖²)` (`Work.Asymptotics.E4cube_cusp_second`), and
* `Δ⁻¹ = q⁻¹ + 24 + O(‖q‖)` (`Work.Asymptotics.cusp_invDelta`).

Writing `r = E₄³ - 1 - 720 q` and `s = Δ⁻¹ - (q⁻¹ + 24)`, the exact algebraic identity

`j - q⁻¹ - 744 = 17280 q + s (1 + 720 q) + r (q⁻¹ + 24 + s)`

bounds the error by `O(‖q‖) = O(‖E‖²)` because `r = O(‖q‖²)`, `s = O(‖q‖)` and
`‖Δ⁻¹‖ ≤ ‖q‖⁻¹ + 24 + O(‖q‖)`.
-/

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-- **Algebraic core.** The exact rearrangement of `j = E₄³ Δ⁻¹` around its leading terms is a
pure identity in `q, r, s` (with `q ≠ 0`), using only `q · q⁻¹ = 1`. -/
private lemma jInvariantFun_cusp_identity {q r s : ℂ} (hq : q ≠ 0) :
    (1 + 720 * q + r) * (q⁻¹ + 24 + s) - q⁻¹ - 744
      = 17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s) := by
  field_simp
  ring

/-- A one-variable numerical bound: for `0 ≤ t ≤ 1`, `Cr, Cs ≥ 0`,
`17280 t + Cs t (1 + 720 t) + Cr t² (t⁻¹ + 24 + Cs t) ≤ (17280 + 721 Cs + (25 + Cs) Cr) t`.
This is the coefficient estimate obtained by replacing `t², t³ ≤ t`. -/
private lemma cusp_coeff_bound {t Cr Cs : ℝ} (hCr : 0 ≤ Cr) (hCs : 0 ≤ Cs)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    17280 * t + Cs * t * (1 + 720 * t) + Cr * t ^ 2 * (t⁻¹ + 24 + Cs * t)
      ≤ (17280 + 721 * Cs + (25 + Cs) * Cr) * t := by
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_le_mul_of_nonneg_left ht1 ht0]
  have ht3 : t ^ 3 ≤ t := by
    have h := mul_le_mul_of_nonneg_right ht2 ht0
    nlinarith [h, ht2]
  have hid : t ^ 2 * t⁻¹ = t := by
    rcases eq_or_ne t 0 with h | h
    · rw [h]; ring
    · rw [pow_two, mul_assoc, mul_inv_cancel₀ h, mul_one]
  have hexp : Cr * t ^ 2 * (t⁻¹ + 24 + Cs * t)
      = Cr * t + 24 * Cr * t ^ 2 + Cs * Cr * t ^ 3 := by
    have h1 : Cr * t ^ 2 * (t⁻¹ + 24 + Cs * t)
        = Cr * (t ^ 2 * t⁻¹) + 24 * Cr * t ^ 2 + Cs * Cr * t ^ 3 := by ring
    rw [h1, hid]
  have h2e : Cs * t * (1 + 720 * t) = Cs * t + 720 * Cs * t ^ 2 := by ring
  rw [hexp, h2e]
  have e1 : 0 ≤ Cs * (t - t ^ 2) := mul_nonneg hCs (sub_nonneg.mpr ht2)
  have e2 : 0 ≤ Cr * (t - t ^ 2) := mul_nonneg hCr (sub_nonneg.mpr ht2)
  have e3 : 0 ≤ Cs * Cr * (t - t ^ 3) := mul_nonneg (mul_nonneg hCs hCr) (sub_nonneg.mpr ht3)
  nlinarith [e1, e2, e3]

/-- **The second-order cusp expansion of the `j`-invariant.** With `E = e^{πiτ}`
(`‖E‖ = e^{-π Im τ}`) one has `j(z) = (E(z)⁻¹)² + 744 + O(‖E(z)‖²)` as `Im z → ∞`. -/
theorem jInvariantFun_cusp_second :
    ∃ T M : ℝ, 0 < T ∧ 0 < M ∧
      ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.jInvariantFun z - ((Work.Residues.Ept z)⁻¹) ^ 2 - 744‖
          ≤ M * ‖Work.Residues.Ept z‖ ^ 2 := by
  obtain ⟨Cr, hCr, hE4c⟩ := Work.Asymptotics.E4cube_cusp_second
  obtain ⟨Cs, hCs, hinvΔ⟩ := Work.Asymptotics.cusp_invDelta
  refine ⟨1, 17280 + 721 * Cs + (25 + Cs) * Cr, one_pos, by positivity, ?_⟩
  intro z hz
  set q : ℂ := Work.Kernels.qParamFun z with hqdef
  set E : ℂ := Work.Residues.Ept z with hEdef
  have hqE : q = E ^ 2 := by
    rw [hqdef, hEdef, Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
    congr 1; ring
  have hqnorm : ‖q‖ = ‖E‖ ^ 2 := by rw [hqE, norm_pow]
  have hqle1 : ‖q‖ ≤ 1 := by
    rw [hqnorm]
    have h : ‖E‖ < 1 := by rw [hEdef]; exact Work.Residues.norm_Ept_lt_one z
    nlinarith [norm_nonneg E]
  have hEinv : (Work.Residues.Ept z)⁻¹ ^ 2 = q⁻¹ := by
    rw [← hEdef, hqE, inv_pow]
  have hq_ne : q ≠ 0 := by
    rw [hqE]; exact pow_ne_zero 2 (by rw [hEdef]; exact Work.Residues.Ept_ne_zero z)
  -- `r` is the second-order remainder of `E₄³` and `s` that of `Δ⁻¹`.
  set r : ℂ := Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q with hrdef
  set s : ℂ := (Work.Kernels.DeltaFun z)⁻¹ - (q⁻¹ + 24) with hsdef
  have hr_bound : ‖r‖ ≤ Cr * ‖q‖ ^ 2 := by rw [hrdef]; rw [hqdef]; exact hE4c z hz
  have hs_bound : ‖s‖ ≤ Cs * ‖q‖ := by
    have h := hinvΔ z hz
    rw [show (Work.Residues.Ept z)⁻¹ ^ 2 = q⁻¹ from hEinv] at h
    rw [show ‖Work.Residues.Ept z‖ ^ 2 = ‖q‖ from by rw [← hEdef, hqnorm]] at h
    rw [← hsdef] at h
    exact h
  have hjr : Work.Kernels.jInvariantFun z
      = Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.DeltaFun z)⁻¹ := by
    rw [Work.Kernels.jInvariantFun, div_eq_mul_inv]
  have hE4 : Work.Kernels.E4Fun z ^ 3 = 1 + 720 * q + r := by rw [hrdef]; ring
  have hDinv : (Work.Kernels.DeltaFun z)⁻¹ = q⁻¹ + 24 + s := by rw [hsdef]; ring
  have hmain : Work.Kernels.jInvariantFun z - (Work.Residues.Ept z)⁻¹ ^ 2 - 744
      = 17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s) := by
    rw [hjr, hE4, hDinv, hEinv]
    exact jInvariantFun_cusp_identity hq_ne
  rw [hmain]
  have ht0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have h720 : ‖(1 : ℂ) + 720 * q‖ ≤ 1 + 720 * ‖q‖ := by
    calc ‖(1 : ℂ) + 720 * q‖ ≤ ‖(1 : ℂ)‖ + ‖(720 : ℂ) * q‖ := norm_add_le _ _
      _ = 1 + 720 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]; norm_num
  have hs2 : ‖s * (1 + 720 * q)‖ ≤ Cs * ‖q‖ * (1 + 720 * ‖q‖) := by
    rw [norm_mul]
    exact mul_le_mul hs_bound h720 (norm_nonneg _) (by positivity)
  have hqs : ‖q⁻¹ + 24 + s‖ ≤ ‖q‖⁻¹ + 24 + Cs * ‖q‖ := by
    have h1 : ‖q⁻¹ + 24 + s‖ ≤ ‖q⁻¹ + 24‖ + ‖s‖ := norm_add_le _ _
    have h2 : ‖q⁻¹ + 24‖ ≤ ‖q⁻¹‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
    rw [norm_inv, Complex.norm_ofNat] at h2
    linarith [h1, h2, hs_bound]
  have hr3 : ‖r * (q⁻¹ + 24 + s)‖
      ≤ Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖) := by
    rw [norm_mul]
    exact mul_le_mul hr_bound hqs (norm_nonneg _) (by positivity)
  have hsum : ‖17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s)‖
      ≤ 17280 * ‖q‖ + Cs * ‖q‖ * (1 + 720 * ‖q‖)
        + Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖) := by
    have h1 : ‖(17280 : ℂ) * q‖ = 17280 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h2 : ‖17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s)‖
        ≤ ‖17280 * q‖ + ‖s * (1 + 720 * q)‖ + ‖r * (q⁻¹ + 24 + s)‖ := by
      have ha := norm_add_le (17280 * q + s * (1 + 720 * q)) (r * (q⁻¹ + 24 + s))
      have hb := norm_add_le (17280 * q) (s * (1 + 720 * q))
      linarith
    rw [h1] at h2
    linarith [h2, hs2, hr3]
  calc ‖17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s)‖
      ≤ 17280 * ‖q‖ + Cs * ‖q‖ * (1 + 720 * ‖q‖)
          + Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖) := hsum
    _ ≤ (17280 + 721 * Cs + (25 + Cs) * Cr) * ‖q‖ :=
        cusp_coeff_bound hCr.le hCs.le ht0 hqle1
    _ = (17280 + 721 * Cs + (25 + Cs) * Cr) * ‖(Work.Residues.Ept z)‖ ^ 2 := by
        rw [← hEdef, hqnorm]

end

end Work.Asymptotics
