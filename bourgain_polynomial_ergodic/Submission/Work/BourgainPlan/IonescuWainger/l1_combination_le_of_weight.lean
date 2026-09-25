import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sum_le_weight
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_sum_of_orthogonal

open scoped BigOperators lp

namespace Work.BourgainPlan.IonescuWainger

/-- For `C ≥ 0`, `(C²)^{1/2} = C`.  (Elementary scaffolding for the weighted Cauchy–Schwarz.) -/
theorem rpow_half_of_sq {C : ℝ} (hC : 0 ≤ C) : (C ^ 2) ^ ((1 : ℝ) / 2) = C := by
  calc (C ^ 2) ^ ((1 : ℝ) / 2) = Real.sqrt (C ^ 2) := (Real.sqrt_eq_rpow (C ^ 2)).symm
    _ = C := Real.sqrt_sq hC

/-- For `C ≥ 0`, if `A ≤ C²` then `A^{1/2} ≤ C`. -/
theorem rpow_half_le_of_le_sq {A C : ℝ} (hC : 0 ≤ C) (h : A ≤ C ^ 2) :
    A ^ ((1 : ℝ) / 2) ≤ C := by
  calc A ^ ((1 : ℝ) / 2) = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
    _ ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt h
    _ = C := Real.sqrt_sq hC

/-- For `C, D ≥ 0`, if `B ≤ C² · D` then `B^{1/2} ≤ C · D^{1/2}`. -/
theorem rpow_half_le_sq_mul {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : B ≤ C ^ 2 * D) : B ^ ((1 : ℝ) / 2) ≤ C * D ^ ((1 : ℝ) / 2) := by
  calc B ^ ((1 : ℝ) / 2) ≤ (C ^ 2 * D) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hB h (by norm_num)
    _ = (C ^ 2) ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) := Real.mul_rpow (sq_nonneg C) hD
    _ = C * D ^ ((1 : ℝ) / 2) := by rw [rpow_half_of_sq hC]

/-- **The weighted `ℓ¹` bound on a combination of kernels** (the weighted Cauchy–Schwarz/Pythagoras
step of Tao's `p = ∞` argument, packaged): if the weighted kernels `w·K i` are square-summable and
pairwise `ℓ²`-orthogonal, `w` is nowhere zero with `∑ ‖w⁻¹‖² ≤ C₁²`, and `∑ ‖w·K i‖² ≤ C₂²` for
every `i`, then every linear combination of the kernels has `ℓ¹`-norm at most
`C₁ C₂ ‖c‖_{ℓ²}`. -/
theorem l1_combination_le_of_weight {ι : Type*} [Fintype ι] {K : ι → ℤ → ℂ} {w : ℤ → ℂ}
    {C₁ C₂ : ℝ} (hw : ∀ n : ℤ, w n ≠ 0) (hK : ∀ i, Memℓp (fun n : ℤ => w n * K i n) 2)
    (horth : ∀ i j, i ≠ j → ∑' n : ℤ, (w n * K i n) * star (w n * K j n) = 0)
    (hwinv : Memℓp (fun n : ℤ => (w n)⁻¹) 2)
    (hC₁ : ∑' n : ℤ, ‖(w n)⁻¹‖ ^ 2 ≤ C₁ ^ 2)
    (hC₂ : ∀ i, ∑' n : ℤ, ‖w n * K i n‖ ^ 2 ≤ C₂ ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) (hKi1 : ∀ i, Summable fun n : ℤ => ‖K i n‖)
    (c : ι → ℂ) :
    ∑' n : ℤ, ‖∑ i, c i * K i n‖ ≤ C₁ * C₂ * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  classical
  -- The combination is absolutely summable: a finite sum of the absolutely summable kernels.
  have hsum : Summable fun n : ℤ => ∑ i, ‖c i * K i n‖ := by
    have heq : (fun n : ℤ => ∑ i, ‖c i * K i n‖)
        = fun n => ∑ i, ‖c i‖ * ‖K i n‖ :=
      funext (fun n => Finset.sum_congr rfl (fun i _ => norm_mul (c i) (K i n)))
    rw [heq]
    exact summable_sum (fun i _ => (hKi1 i).mul_left (‖c i‖))
  -- The abstract weighted Cauchy–Schwarz / Pythagoras estimate.
  have hmain :=
    tsum_norm_sum_le_weight hw hK horth hwinv c hsum
  refine hmain.trans ?_
  -- Nonnegativity of the three quantities appearing in the bound.
  have hA_nn : 0 ≤ ∑' n : ℤ, ‖(w n)⁻¹‖ ^ 2 := tsum_nonneg (fun n => sq_nonneg _)
  have hD_nn : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB_nn : 0 ≤ ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
      (tsum_nonneg (fun n => sq_nonneg _)))
  -- The `ℓ²`-mass of the weighted pieces is bounded by `C₂² ‖c‖²`.
  have hB_le : ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2
      ≤ C₂ ^ 2 * ∑ i, ‖c i‖ ^ 2 := by
    calc ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2
        ≤ ∑ i, ‖c i‖ ^ 2 * C₂ ^ 2 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hC₂ i) (sq_nonneg _))
      _ = (∑ i, ‖c i‖ ^ 2) * C₂ ^ 2 :=
          (Finset.sum_mul Finset.univ (fun i => ‖c i‖ ^ 2) (C₂ ^ 2)).symm
      _ = C₂ ^ 2 * ∑ i, ‖c i‖ ^ 2 := by ring
  -- Both square-root factors are bounded, and the product of the bounds is the claim.
  calc (∑' n : ℤ, ‖(w n)⁻¹‖ ^ 2) ^ ((1 : ℝ) / 2)
        * (∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ C₁ * (C₂ * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul (rpow_half_le_of_le_sq hC₁0 hC₁)
          (rpow_half_le_sq_mul hB_nn hC₂0 hD_nn hB_le)
          (Real.rpow_nonneg hB_nn _) hC₁0
    _ = C₁ * C₂ * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := (mul_assoc C₁ C₂ _).symm

end Work.BourgainPlan.IonescuWainger
