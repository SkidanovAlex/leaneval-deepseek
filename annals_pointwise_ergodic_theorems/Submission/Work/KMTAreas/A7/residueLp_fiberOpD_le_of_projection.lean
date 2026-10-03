/-
# The residue-`ℓᵖ` bound for the exact-height fibre `fiberOpD`

This module proves `Work.KMTAreas.A7.residueLp_fiberOpD_le_of_projection`: **from the
periodised-projection bound for the exact-height arithmetic character `arithCharD ρ l` one gets
the residue-`ℓᵖ` bound for the fibre `fiberOpD ρ l (mStarF u)`.**

* `fiberFold` — the *fold* (periodisation in the convolution index) of a sequence `v` against the
  coefficients `cw m`: `fiberFold ρ l m v x y = ∑'_k cw m (y + k q) · v (x - (y + k q))`,
  `q = arithQ ρ l`;
* `arithCharD_add_mul_arithQ` — `arithCharD ρ l` is `q`-periodic;
* `fiberOpD_eq_sum_range_fiberFold` (the paper's "form-1" in finite-group form) — the fibre at the
  residue `n₀` is the **cyclic convolution** of `arithCharD ρ l (n₀ - ·)` with the fold:
  `fiberOpD ρ l m n₀ v x = ∑_{y<q} arithCharD ρ l (n₀ - y) · fiberFold ρ l m v x y`.  This is the
  regrouping of the `ℤ`-sum defining the fibre into its `q` residue classes, together with the
  `q`-periodicity of the character;
* `tsum_ofReal_cw_mStarF_shift_le` — the `ℓ¹`-mass of the coefficients of the narrow bump
  `mStarF u`, sampled on one residue class `y + qℤ`, is `O(1/q)` (`etaCut_kernel_localMass`), in
  the `ENNReal` form needed below.

The main theorem then follows the paper's §8 argument: the projection bound is applied
*pointwise in `x`* to the fold, and the `q` of the projection bound is cancelled by the `q^{-1}`
mass gain of the kernel on each residue class.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallFibreDefs
import Submission.Work.KMTAreas.A7.eLpNorm_lattice_conv_le
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.tsum_one_div_sq_succ_le_two

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset Polynomial
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## The pointwise power identity for `residueLp` -/

/-- **The pointwise power identity for `residueLp`.**  For `p > 0`,
`residueLp p q W x ^ p = q⁻¹ * ∑_{n₀ < q} W x n₀ ^ p` (in `ℝ≥0∞`).  This is a local copy of
`Work.KMTAreas.A7.residueLp_pow_eq`, kept here so that this file does not depend on the volatile
`fiberVarSamplingG` module. -/
theorem residueLp_pow_eq' {p : ℝ} (hp : 0 < p) (q : ℕ) (W : ℤ → ℕ → ENNReal) (x : ℤ) :
    residueLp p q W x ^ p = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, W x n₀ ^ p := by
  rw [show residueLp p q W x
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (W x n₀) p) (1/p) from rfl]
  simp only [one_div]
  calc ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (W x n₀) p) p⁻¹ ^ p
      = ENNReal.rpow (ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (W x n₀) p) p⁻¹) p := rfl
    _ = ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (W x n₀) p :=
        ENNReal.rpow_inv_rpow hp.ne' _
    _ = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, W x n₀ ^ p := by
        change (q : ENNReal) ^ (-1 : ℝ) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (W x n₀) p
          = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, W x n₀ ^ p
        rw [ENNReal.rpow_neg_one]
        rfl

/-! ## The fold of a sequence against the arithmetic character -/

/-- **The fold** of `v` against the coefficients `cw m`, sampled on the residue class `y + qℤ`
(`q = arithQ ρ l`):

  `fiberFold ρ l m v x y = ∑'_k cw m (y + k q) · v (x - (y + k q))`.

It is the kernel of the arithmetic projection `arithCharD ρ l` decomposed over the residue classes
of `ℤ/q`; the fibre `fiberOpD` is the cyclic convolution with it. -/
def fiberFold (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (v : ℤ → ℂ) (x y : ℤ) : ℂ :=
  ∑' k : ℤ, cw m ((y : ℤ) + (k : ℤ) * (arithQ ρ l : ℤ))
    * v (x - ((y : ℤ) + (k : ℤ) * (arithQ ρ l : ℤ)))

/-! ## Periodicity of the exact-height arithmetic character -/

/-- `(ℚ/ℤ)_l ⊆ (ℚ/ℤ)_{≤l}` for the *exact*-height frequency set `diffFreqs`. -/
theorem diffFreqs_subset_iwArithFreqs (ρ : ℝ) (l : ℕ) :
    diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  intro α hα
  unfold diffFreqs at hα
  split_ifs at hα with h
  · rwa [h]
  · exact (Finset.mem_sdiff.mp hα).1

/-- The modulus `arithQ ρ l = max 1 (lcm P_{≤l})` is the lcm itself. -/
theorem arithQ_eq_iwQl' (ρ : ℝ) (l : ℕ) : arithQ ρ l = iwQl ρ l :=
  max_eq_right (Nat.succ_le_of_lt (iwQl_pos (ρ := ρ) (l := l)))

/-- The modulus `arithQ ρ l` kills every exact-height frequency `α ∈ (ℚ/ℤ)_l`. -/
theorem arithQ_nsmul_eq_zero' {ρ : ℝ} {l : ℕ} {α : Work.Analysis.IonescuWainger.Circle}
    (h : α ∈ diffFreqs ρ l) : (arithQ ρ l : ℤ) • α = 0 := by
  rw [arithQ_eq_iwQl']
  exact iwQl_nsmul_eq_zero (diffFreqs_subset_iwArithFreqs ρ l h)

/-- **`arithCharD ρ l` is periodic of period `arithQ ρ l`.**  Every frequency in `(ℚ/ℤ)_l` is
killed by `arithQ ρ l`, hence every character `y ↦ e(α y)` is `q`-periodic. -/
theorem arithCharD_add_mul_arithQ (ρ : ℝ) (l : ℕ) (y t : ℤ) :
    arithCharD ρ l (y + t * (arithQ ρ l : ℤ)) = arithCharD ρ l y := by
  unfold arithCharD
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [fourier_add]
  have h1 : fourier (T := 1) (t * (arithQ ρ l : ℤ)) α = 1 := by
    rw [fourier_apply, mul_zsmul, arithQ_nsmul_eq_zero' hα, smul_zero]
    exact fourier_zero'
  rw [h1, mul_one]

/-! ## The fibre as a cyclic convolution with the fold -/

/-! ## The `ℓ¹`-mass of the sampled kernel coefficients -/

/-- Summability of the coefficients of the narrow bump `mStarF u`. -/
theorem summable_cw_mStarF_of_decay (u : ℕ) : Summable (fun j : ℤ => ‖cw (mStarF u) j‖) := by
  obtain ⟨C, hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight]
  simpa only [mStarF, div_eq_mul_inv, one_mul] using hC j

/-! ## The main theorem -/

end

end Work.KMTAreas.A7
