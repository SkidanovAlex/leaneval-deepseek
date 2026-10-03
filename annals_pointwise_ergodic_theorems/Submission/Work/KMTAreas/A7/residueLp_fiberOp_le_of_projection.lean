/-
# The residue-`ℓᵖ` bound for the fibre `fiberOp` from the arithmetic projection bound

This module proves `Work.KMTAreas.A7.residueLp_fiberOp_le_of_projection`: **from the
periodised-projection bound for the cumulative-height arithmetic character `arithChar ρ l` one
gets the residue-`ℓᵖ` bound for the fibre `fiberOp ρ l (etaCut kmtEta k)`**, uniformly in `l` and
in the dyadic scale `k` subject to `2^k · arithQ ρ l ≤ 1/8`.

The fibre is the convolution with the *exact*-height character `arithCharNew ρ l`
(`ResidueCharDefs.lean`), and the two characters are related by

  `arithCharNew ρ l = arithChar ρ l - arithChar ρ (l-1)`

(as functions on `ℤ`: the exact-height frequency set is the difference of the two cumulative
ones).  Since `hproj` bounds the `ℓᵖ`-norm of the circulant with kernel `arithChar ρ l` by `C`
*for every* `l`, the circulant with kernel `arithCharNew ρ l` is bounded by `2C`
(`arithCharNew_projection_bound`).  The rest of the argument is the paper's §8 chain:

* `fiberOp_eq_sum_range_fiberFold` — the paper's `form-1` in finite-group form: the fibre at the
  residue `n₀` is the cyclic convolution of `arithCharNew ρ l (n₀ - ·)` with the *fold*
  `fiberFold ρ l (etaCut kmtEta k) v x y = ∑'_t cw (etaCut kmtEta k) (y + t q) · v (x - y - t q)`;
* the projection bound is applied *pointwise in `x`* to the fold, and the `q` of the projection
  bound is cancelled by the `q⁻¹` mass gain of the kernel on each residue class
  (`cw_etaCut_shift_tsum_le`, from `etaCut_kernel_localMass`) via Young's inequality for lattice
  convolutions (`eLpNorm_lattice_conv_le`).

The `⟨l⟩`-free uniform projection bound `hproj` is supplied, in the workspace, by
`Work.KMTAreas.A7.arithProjection_lp_bound` (or by `kmtProj_lp_bound_uniform` plus the
sharp-vs-smoothed comparison); this file is agnostic about its source.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.residueLp_fiberOpD_le_of_projection

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset Polynomial
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract

noncomputable section

/-! ## Summability of the coefficients of the rescaled cutoff -/

/-- Quadratic decay of the coefficients of the rescaled KMT bump `η_{≤k} = etaCut kmtEta k`
(`cw_etaCut_decay`), expressed as summability against the summable weight `kmtKernWeight`. -/
theorem summable_cw_etaCut (k : ℤ) : Summable (fun j : ℤ => ‖cw (etaCut kmtEta k) j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay k
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight]
  simpa only [div_eq_mul_inv, one_mul] using hC j

/-! ## Periodicity of the cumulative arithmetic character -/

/-- **`arithChar ρ l` is periodic of period `arithQ ρ l`.**  Every frequency in
`(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` is killed by `arithQ ρ l`, hence every character `y ↦ e(α y)` is
`q`-periodic. -/
theorem arithChar_add_mul_arithQ (ρ : ℝ) (l : ℕ) (y t : ℤ) :
    arithChar ρ l (y + t * (arithQ ρ l : ℤ)) = arithChar ρ l y := by
  unfold arithChar
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [fourier_add]
  have h1 : fourier (T := 1) (t * (arithQ ρ l : ℤ)) α = 1 := by
    rw [fourier_apply, mul_zsmul]
    have hq : (arithQ ρ l : ℤ) • α = 0 := by
      rw [arithQ_eq_iwQl']
      exact iwQl_nsmul_eq_zero hα
    rw [hq, smul_zero]
    exact fourier_zero'
  rw [h1, mul_one]

/-- Convexity of `t ↦ t ^ p` on `[0, ∞)` for `p ≥ 1`, in the form needed for the difference of two
circulants: `(a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p)`. -/
theorem rpow_add_le_two_pow_pred {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨a, ha⟩ : NNReal) (⟨b, hb⟩ : NNReal) hp
  rw [← NNReal.coe_le_coe] at h
  norm_cast at h

/-! ## The projection bound for the exact-height character -/

/-! ## The main theorem -/

end

end Work.KMTAreas.A7
