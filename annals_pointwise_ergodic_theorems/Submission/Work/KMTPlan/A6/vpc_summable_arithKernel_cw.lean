/-
# Summability of the kernel `arithKernel · cw m₁ · cw m₂` of the twisted bilinear multiplier

`Btwist ρ P l₁ l₂ m₁ m₂` is the twisted bilinear multiplier of §6--§8 of

* B. Krause, M. Mirek, T. Tao, `Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages`, Annals of Math. 195 (3) 2022,

written in the kernel form `∑'_{j₁,j₂} K(j₁,j₂) h(x-j₁)k(x-j₂)` with the *absolutely summable*
kernel

  `K(j₁,j₂) = arithKernel ρ P Q_L l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`,

where `arithKernel = ∑_{α₁ ∈ (ℚ/ℤ)_{≤l₁}} ∑_{α₂ ∈ (ℚ/ℤ)_{≤l₂}} m_Ẑ(α₁,α₂) e(-j₁α₁) e(-j₂α₂)` is a
*finite* double sum over the arithmetic frequency sets and `cw m j = ∫ m(θ) e(-jθ) dθ` are the
Fourier coefficients of the two one-variable symbols.

This file proves that this kernel belongs to `ℓ¹(ℤ²)` whenever the two coefficient families
`j ↦ cw mᵢ j` are `ℓ¹(ℤ)`:

* the arithmetic frequency sets are finite and each summand of `arithKernel` has modulus at most
  one (`m_Ẑ` is the average of `q` numbers of modulus one, `‖e(-jα)‖ = 1`), so
  `‖arithKernel … j₁ j₂‖ ≤ #(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂}` uniformly in `j₁, j₂`;
* a summable family times a bounded family is summable, and the product family
  `(j₁,j₂) ↦ ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖` over `ℤ × ℤ` is summable (Fubini for nonnegative
  real families, `summable_prod_of_nonneg`).

The result is exactly the `ℓ¹(ℤ²)`-hypothesis under which the Fubini/Tonelli and
linearity manipulations on `Btwist` (e.g. `vpc_bilinOp_sub`, `vpc_bilinOp_intervalIntegral`)
are legitimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## 1. The uniform bound on the arithmetic kernel -/

/-- The uniform bound `#(ℚ/ℤ)_{≤l₁} · #(ℚ/ℤ)_{≤l₂}` on the arithmetic kernel. -/
private def arithKB (ρ : ℝ) (l₁ l₂ : ℕ) : ℝ :=
  ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)

private lemma arithKB_nonneg (ρ : ℝ) (l₁ l₂ : ℕ) : 0 ≤ arithKB ρ l₁ l₂ :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The arithmetic symbol `m_Ẑ(α₁,α₂) = E_{n ∈ ℤ/qℤ} e(α₁n + α₂P(n))` is the average of `q`
complex numbers of modulus one, hence has modulus at most one. -/
private lemma mZ_norm_le_one (P : ℤ[X]) (q : ℕ) (hq : 0 < q)
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

/-- **The arithmetic kernel is a bounded kernel.**  Its modulus is bounded, uniformly in the two
integer summation variables, by the product of the cardinalities of the two arithmetic frequency
sets. -/
private lemma arithKernel_norm_le (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖ ≤ arithKB ρ l₁ l₂ := by
  unfold arithKernel arithKB
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
        exact mZ_norm_le_one P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## 2. The product of two `ℓ¹(ℤ)`-families over `ℤ × ℤ` -/

/-- **Fubini for nonnegative real families.**  If `j ↦ ‖cw mᵢ j‖` is summable for `i = 1,2` then
the product family `(j₁,j₂) ↦ ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖` is summable on `ℤ × ℤ`. -/
private lemma summable_cw_prod {m₁ m₂ : ℝ → ℂ} (h₁ : Summable fun j : ℤ => ‖cw m₁ j‖)
    (h₂ : Summable fun j : ℤ => ‖cw m₂ j‖) :
    Summable fun p : ℤ × ℤ => ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
  h₁.mul_of_nonneg h₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-! ## 3. The kernel of `Btwist` is `ℓ¹(ℤ²)` -/

theorem vpc_summable_arithKernel_cw (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    {m₁ m₂ : ℝ → ℂ} (h₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (h₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖) :
    Summable fun p : ℤ × ℤ =>
      ‖Work.KMTAreas.A7.arithKernel ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
        * Work.KMTAreas.A7.cw m₁ p.1 * Work.KMTAreas.A7.cw m₂ p.2‖ := by
  have hprod : Summable fun p : ℤ × ℤ => ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
    summable_cw_prod h₁ h₂
  have hbdd : Summable fun p : ℤ × ℤ => arithKB ρ l₁ l₂ * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) :=
    hprod.mul_left _
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hbdd
  rw [norm_mul, norm_mul]
  have hker : ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖ ≤ arithKB ρ l₁ l₂ :=
    arithKernel_norm_le ρ P l₁ l₂ p.1 p.2
  calc ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖ * ‖cw m₁ p.1‖
        * ‖cw m₂ p.2‖
      ≤ arithKB ρ l₁ l₂ * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hker (norm_nonneg _)) (norm_nonneg _)
    _ = arithKB ρ l₁ l₂ * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) := by ring

end

end Work.KMTPlan.A6
