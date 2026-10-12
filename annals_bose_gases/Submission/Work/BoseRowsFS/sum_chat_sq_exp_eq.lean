import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.W1low.chat_sub_le
import Submission.Work.BoseRowsFS.KernelDefs
import Submission.Work.BoseRowsFS.integral_integral_tsum_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Gaussian-damped mode sum `Σ_j Ŵ(k_j)² e^{-s‖k_j‖²}` as a double integral

For an integrable `W : ℝ³ → ℝ`, the box modes `k_j = (2π/ℓ)·j` (`j ∈ ℤ³`) and `ℓ, s > 0`,

  `Σ_j (chat W k_j)² e^{-s‖k_j‖²}
      = ½ ∫∫ W x W y (θ(x-y) + θ(x+y))`,

where `chat W k = ∫ W(y)cos⟨k,y⟩ dy` is the (real) Fourier transform and
`θ = thetaK ℓ s` is the Gaussian mode kernel `θ(z) = Σ_j e^{-s‖k_j‖²}cos⟨k_j,z⟩`.

The mathematics is the product-to-sum formula
`cos⟨k,x-y⟩ + cos⟨k,x+y⟩ = 2cos⟨k,x⟩cos⟨k,y⟩`, which turns the two-point kernel into a
product of two one-point kernels; the Gaussian weights make every sum/integral interchange
legal (Fubini for the `tsum`: `integral_integral_tsum_mul`), so both sides collapse onto

  `Σ_j e^{-s‖k_j‖²} (∫ W(y)cos⟨k_j,y⟩ dy)²`.

## Contents

* `fin3IntEquiv` — the bookkeeping bijection `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ`;
* `summable_kvec_gauss` — summability of the Gaussian mode weights `e^{-s‖k_j‖²}`;
* `summable_kvec_gauss_cos` — the same with a cosine factor;
* `thetaK_add_sub_aux` — the product-to-sum identity for `thetaK`;
* `sum_chat_sq_exp_eq` — the target.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. The Gaussian mode sum converges -/

/-- The bookkeeping bijection `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ`, `j ↦ (j 0, j 1, j 2)`. -/
private def fin3IntEquiv : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro k
    funext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨a, b, c⟩
    simp

/-- **The Gaussian mode weights are summable.**  For `ℓ, s > 0` the series
`Σ_{j ∈ ℤ³} e^{-s‖k_j‖²}` (with `k_j = (2π/ℓ)·j`) converges: the weight is the product of
three one-dimensional Gaussians `e^{-c²n²}`, `c = 2π/ℓ`, and each of those is summable over
`ℤ` (`Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int`). -/
private lemma summable_kvec_gauss {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) :
    Summable (fun j : Fin 3 → ℤ => Real.exp (-(s * ‖kvec ℓ j‖ ^ 2))) := by
  set c : ℝ := s * (2 * Real.pi / ℓ) ^ 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have h1 : Summable (fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) :=
    Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int hcpos
  have h2 : Summable (fun p : ℤ × ℤ =>
      Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun n => (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  set F : ℤ × ℤ × ℤ → ℝ := fun p =>
    Real.exp (-c * (p.1 : ℝ) ^ 2)
      * (Real.exp (-c * (p.2.1 : ℝ) ^ 2) * Real.exp (-c * (p.2.2 : ℝ) ^ 2)) with hF
  have h3 : Summable F := by
    rw [hF]
    exact h1.mul_of_nonneg h2 (fun n => (Real.exp_pos _).le)
      (fun p => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hkey : ∀ j : Fin 3 → ℤ,
      Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)) =
        Real.exp (-c * (j 0 : ℝ) ^ 2)
          * (Real.exp (-c * (j 1 : ℝ) ^ 2) * Real.exp (-c * (j 2 : ℝ) ^ 2)) := by
    intro j
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [norm_kvec hℓ.le j, mul_pow, norm_vecZ_sq, Fin.sum_univ_three, hc]
    ring
  have h4 : Summable (fun j : Fin 3 → ℤ =>
      Real.exp (-c * (j 0 : ℝ) ^ 2)
        * (Real.exp (-c * (j 1 : ℝ) ^ 2) * Real.exp (-c * (j 2 : ℝ) ^ 2))) :=
    (Equiv.summable_iff fin3IntEquiv).mpr h3
  refine Summable.of_norm_bounded h4 (fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact le_of_eq (hkey j)

/-- The Gaussian mode weights remain summable after multiplication by a cosine. -/
private lemma summable_kvec_gauss_cos {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun j : Fin 3 → ℤ =>
      Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)) * Real.cos (inner ℝ (kvec ℓ j) z)) := by
  refine (summable_kvec_gauss hℓ hs).of_norm_bounded (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-! ## 2. The product-to-sum identity for the mode kernel -/

/-- **Product-to-sum for the Gaussian mode kernel:**
`Σ_j e^{-s‖k_j‖²}(cos⟨k_j,x-y⟩ + cos⟨k_j,x+y⟩) = Σ_j e^{-s‖k_j‖²}·2cos⟨k_j,x⟩cos⟨k_j,y⟩`.
This is `cos(u-v) + cos(u+v) = 2cos u cos v` applied mode by mode, the sum of the two
absolutely summable series being split by `Summable.tsum_add`. -/
private lemma thetaK_add_sub_aux {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    thetaK ℓ s (x - y) + thetaK ℓ s (x + y)
      = ∑' j : Fin 3 → ℤ, Real.exp (-(s * ‖kvec ℓ j‖ ^ 2))
          * (2 * (Real.cos (inner ℝ (kvec ℓ j) x)
              * Real.cos (inner ℝ (kvec ℓ j) y))) := by
  have h1 := summable_kvec_gauss_cos hℓ hs (x - y)
  have h2 := summable_kvec_gauss_cos hℓ hs (x + y)
  rw [thetaK, thetaK, ← Summable.tsum_add h1 h2]
  apply tsum_congr
  intro j
  rw [inner_sub_right, inner_add_right, Real.cos_sub, Real.cos_add]
  ring

/-! ## 3. The identity -/

theorem sum_chat_sq_exp_eq {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) :
    (∑' j : Fin 3 → ℤ, (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ j)) ^ 2
        * Real.exp (-(s * ‖Work.BoseRowsFS.kvec ℓ j‖ ^ 2)))
      = (1 / 2) * (∫ x, ∫ y, W x * W y
          * (Work.BoseRowsFS.thetaK ℓ s (x - y) + Work.BoseRowsFS.thetaK ℓ s (x + y))) := by
  -- abbreviations
  set e : (Fin 3 → ℤ) → ℝ := fun j => Real.exp (-(s * ‖kvec ℓ j‖ ^ 2)) with he
  set φ : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun j x => W x * Real.cos (inner ℝ (kvec ℓ j) x) with hφ
  have hsumm : Summable e := by rw [he]; exact summable_kvec_gauss hℓ hs
  have hsumm2 : Summable (fun j => 2 * e j) := hsumm.mul_left 2
  -- the one-point cosine transform is integrable, and dominated by `‖W‖`
  have hφint : ∀ j : Fin 3 → ℤ, MeasureTheory.Integrable (φ j) := by
    intro j
    simp only [hφ]
    exact hW.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  have hbφ : ∀ j x, |φ j x| ≤ ‖W x‖ := by
    intro j x
    simp only [hφ]
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  -- Fubini for the `tsum` of products
  have hFub := integral_integral_tsum_mul (ι := Fin 3 → ℤ) (a := fun j => 2 * e j)
    hsumm2 (φ := φ) (ψ := φ) (Φ := fun x => ‖W x‖) (Ψ := fun y => ‖W y‖)
    hφint hφint hW.norm hW.norm (fun x => norm_nonneg _) (fun y => norm_nonneg _) hbφ hbφ
  -- the two-point kernel equals the series of products
  have hpoint : ∀ x y, W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y))
      = ∑' j, (2 * e j) * φ j x * φ j y := by
    intro x y
    rw [thetaK_add_sub_aux hℓ hs x y, ← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [hφ, he]
    ring
  have hstep : (∫ x, ∫ y, W x * W y * (thetaK ℓ s (x - y) + thetaK ℓ s (x + y)))
      = ∫ x, ∫ y, ∑' j, (2 * e j) * φ j x * φ j y := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    exact hpoint x y
  -- the one-point integrals are the Fourier coefficients
  have hA : ∀ j : Fin 3 → ℤ, (∫ x, φ j x) = Work.BoseFixR.chat W (kvec ℓ j) := by
    intro j
    rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hW (kvec ℓ j)]
  -- final algebra
  have hfin : (1 / 2) * (∑' j, (2 * e j) * (∫ x, φ j x) * (∫ y, φ j y))
      = ∑' j, (Work.BoseFixR.chat W (kvec ℓ j)) ^ 2 * e j := by
    have h1 : (∑' j, (2 * e j) * (∫ x, φ j x) * (∫ y, φ j y))
        = ∑' j, 2 * (e j * ((∫ x, φ j x) * (∫ y, φ j y))) := by
      apply tsum_congr
      intro j
      ring
    have h2 : (∑' j, (Work.BoseFixR.chat W (kvec ℓ j)) ^ 2 * e j)
        = ∑' j, e j * ((∫ x, φ j x) * (∫ y, φ j y)) := by
      apply tsum_congr
      intro j
      rw [hA j]
      ring
    rw [h1, tsum_mul_left, h2]
    ring
  rw [hstep, hFub]
  exact hfin.symm

end Work.BoseRowsFS
