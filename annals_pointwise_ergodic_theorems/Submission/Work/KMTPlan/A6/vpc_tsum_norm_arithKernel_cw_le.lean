import Mathlib
import Submission.Work.KMTAreas.A7.Btwist_bilinear_of_bounded
import Submission.Work.KMTPlan.A6.vpc_summable_arithKernel_cw

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The arithmetic symbol is bounded by one -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one, hence has
modulus at most one. -/
private lemma mZ_norm_le_one' (P : ℤ[X]) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-! ## The uniform bound on the arithmetic kernel -/

/-- **The arithmetic kernel is a bounded kernel.**  Its modulus is bounded, uniformly in the two
integer summation variables, by the product of the cardinalities of the two arithmetic frequency
sets. -/
private lemma arithKernel_norm_le' (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
      ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
  unfold arithKernel
  calc ‖∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
          * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ‖∑ α₂ ∈ iwArithFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ iwArithFreqs ρ l₁, ∑ _α₂ ∈ iwArithFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact mZ_norm_le_one' P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The `ℓ¹(ℤ²)` bound on the kernel of the twisted bilinear multiplier -/

/-- **The kernel of the twisted bilinear multiplier is `ℓ¹(ℤ²)`, with the sharp constant.**
If `j ↦ ‖cw mᵢ j‖` is summable with total mass at most `A` (resp. `B`), then the kernel
`(j₁,j₂) ↦ arithKernel … j₁ j₂ · cw m₁ j₁ · cw m₂ j₂` has `ℓ¹(ℤ²)`-norm at most
`#(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂} · A · B`. -/
theorem vpc_tsum_norm_arithKernel_cw_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    {m₁ m₂ : ℝ → ℂ} {A B : ℝ}
    (h₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (h₁b : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖) ≤ A)
    (h₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (h₂b : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖) ≤ B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.arithKernel ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        l₁ l₂ p.1 p.2 * Work.KMTAreas.A7.cw m₁ p.1 * Work.KMTAreas.A7.cw m₂ p.2‖)
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
        * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * A * B := by
  -- the product family of the two coefficient families is summable over `ℤ × ℤ`
  have hprod : Summable (fun p : ℤ × ℤ => ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) :=
    h₁.mul_of_nonneg h₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  -- the dominating family
  have hmaj : Summable (fun p : ℤ × ℤ =>
      ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
        * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖)) := hprod.mul_left _
  -- the pointwise bound
  have hle : ∀ p : ℤ × ℤ,
      ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖
        ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
            * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) := by
    intro p
    have hk := arithKernel_norm_le' ρ P l₁ l₂ p.1 p.2
    rw [norm_mul, norm_mul]
    calc ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖ * ‖cw m₁ p.1‖
          * ‖cw m₂ p.2‖
        ≤ (((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ))
            * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hk (norm_nonneg _)) (norm_nonneg _)
      _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
            * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) := by ring
  -- summability of the target family
  have hf : Summable (fun p : ℤ × ℤ =>
      ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖) :=
    vpc_summable_arithKernel_cw ρ P l₁ l₂ h₁ h₂
  -- the Fubini computation for the dominating family
  have hprod_eq : (∑' p : ℤ × ℤ, ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖)
      = (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖) :=
    (Summable.tsum_mul_tsum (f := fun j : ℤ => ‖cw m₁ j‖) (g := fun j : ℤ => ‖cw m₂ j‖)
      h₁ h₂ hprod).symm
  -- the `tsum` bound
  have hmain : (∑' p : ℤ × ℤ,
        ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖)
      ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
          * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
    have h := hf.tsum_le_tsum hle hmaj
    rw [tsum_mul_left, hprod_eq] at h
    exact h
  -- final assembly
  calc (∑' p : ℤ × ℤ,
        ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖)
      ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
          * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := hmain
    _ ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) * (A * B) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        exact mul_le_mul h₁b h₂b (tsum_nonneg (fun j => norm_nonneg _)) hA
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) * A * B := by ring

end

end Work.KMTPlan.A6
