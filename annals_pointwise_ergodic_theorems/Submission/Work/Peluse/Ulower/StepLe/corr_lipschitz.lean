import Mathlib
import Submission.Work.Peluse.Ulower.supportIn_off_Icc

/-!
# Lipschitz continuity of the normalised correlation in the frequency

For `g : ℤ → ℂ` supported in `[-M, M]` with `‖g x‖ ≤ 1` and `M ≤ B`, the normalised
correlation
`corr g θ = B⁻¹ ∑_x g x e(θ x)`  (`e(t) = e^{2π i t}`)
is Lipschitz in `θ` with constant `2π (2B + 1)`:

`‖B⁻¹ ∑_x g x e(θx) − B⁻¹ ∑_x g x e(θ'x)‖ ≤ 2π (2B+1) |θ − θ'|`.

The proof is the mean-value bound `|e(θx) − e(θ'x)| ≤ 2π |x| |θ − θ'|` summed over the
`2M+1 ≤ 2B+1` integers `x` with `|x| ≤ M ≤ B`:
`(1/B) · (2B+1) · B · 2π |θ−θ'| = 2π (2B+1) |θ−θ'|`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

/-- The phase `2π θ x` of the character `e(θ x)`, written as a purely imaginary complex
number. -/
lemma corr_exp_arg_eq (θ : ℝ) (x : ℤ) :
    (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
      = Complex.I * ((2 * Real.pi * θ * (x : ℝ) : ℝ) : ℂ) := by
  push_cast
  ring

/-- `‖e^{i a} - e^{i b}‖ ≤ |a - b|` for real `a`, `b`. -/
lemma corr_norm_exp_I_mul_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have h1 : Complex.exp (Complex.I * (a : ℂ))
      = Complex.exp (Complex.I * (b : ℂ)) * Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * (b : ℂ))
        * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [h1]; ring
  rw [h2, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

/-- `|2 * π * y| = 2 * π * |y|`. -/
lemma corr_abs_two_pi_mul (y : ℝ) : |2 * Real.pi * y| = 2 * Real.pi * |y| := by
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]

/-- `|e(θ x) - e(θ' x)| ≤ 2π |x| |θ - θ'|`. -/
lemma corr_norm_exp_sub_le (θ θ' : ℝ) (x : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
      - Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ))‖
      ≤ 2 * Real.pi * |(x : ℝ)| * |θ - θ'| := by
  rw [corr_exp_arg_eq θ x, corr_exp_arg_eq θ' x]
  refine (corr_norm_exp_I_mul_sub_le (2 * Real.pi * θ * (x : ℝ))
    (2 * Real.pi * θ' * (x : ℝ))).trans ?_
  have h : 2 * Real.pi * θ * (x : ℝ) - 2 * Real.pi * θ' * (x : ℝ)
      = 2 * Real.pi * ((x : ℝ) * (θ - θ')) := by ring
  rw [h, corr_abs_two_pi_mul, abs_mul]
  exact le_of_eq (by ring)

/-- The `‖x‖ ≤ B` bound for `x` in the support interval. -/
lemma corr_abs_coe_le {B M : ℕ} (hMB : M ≤ B) {x : ℤ}
    (hx : x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) : |(x : ℝ)| ≤ (B : ℝ) := by
  have hx2 : -(M : ℤ) ≤ x ∧ x ≤ (M : ℤ) := Finset.mem_Icc.mp hx
  have h1 : |(x : ℝ)| ≤ (M : ℝ) :=
    abs_le.mpr ⟨by exact_mod_cast hx2.1, by exact_mod_cast hx2.2⟩
  have h2 : (M : ℝ) ≤ (B : ℝ) := by exact_mod_cast hMB
  linarith

/-- The termwise Lipschitz bound. -/
lemma corr_term_le {B M : ℕ} {g : ℤ → ℂ} (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1) (hMB : M ≤ B)
    {x : ℤ} (hx : x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) (θ θ' : ℝ) :
    ‖g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
      - g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ))‖
      ≤ 2 * Real.pi * (B : ℝ) * |θ - θ'| := by
  have he : g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
      - g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ))
      = g x * (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ))) := by ring
  rw [he, norm_mul]
  refine (mul_le_mul (hg1 x) (corr_norm_exp_sub_le θ θ' x) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
  rw [one_mul]
  have hle : 2 * Real.pi * |(x : ℝ)| ≤ 2 * Real.pi * (B : ℝ) :=
    mul_le_mul_of_nonneg_left (corr_abs_coe_le hMB hx) (by positivity)
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

/-- The cardinality bound for the support interval. -/
lemma corr_card_Icc_le (B M : ℕ) (hMB : M ≤ B) :
    (Finset.Icc (-(M : ℤ)) (M : ℤ)).card ≤ 2 * B + 1 := by
  have hsub : Finset.Icc (-(M : ℤ)) (M : ℤ) ⊆ Finset.Icc (-(B : ℤ)) (B : ℤ) := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have hMBi : (M : ℤ) ≤ (B : ℤ) := by exact_mod_cast hMB
    constructor <;> omega
  calc (Finset.Icc (-(M : ℤ)) (M : ℤ)).card
      ≤ (Finset.Icc (-(B : ℤ)) (B : ℤ)).card := Finset.card_le_card hsub
    _ = 2 * B + 1 := by
        rw [Int.card_Icc]
        have hbit : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
        rw [hbit]

/-- The difference of the two correlation sums, bounded before dividing by `B`. -/
lemma corr_tsum_diff_le {B M : ℕ} {g : ℤ → ℂ} (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1)
    (hgs : Work.Peluse.SupportIn g M) (hMB : M ≤ B) (θ θ' : ℝ) :
    ‖(∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)))
      - (∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ)))‖
    ≤ 2 * Real.pi * (B : ℝ) * ((2 * B + 1 : ℕ) : ℝ) * |θ - θ'| := by
  classical
  have hoff : ∀ x : ℤ, x ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) → g x = 0 :=
    supportIn_off_Icc hgs
  have hzero : ∀ (ψ : ℝ) (x : ℤ), x ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) →
      g x * Complex.exp (2 * Real.pi * Complex.I * (ψ : ℂ) * (x : ℂ)) = 0 :=
    fun ψ x hx => by rw [hoff x hx, zero_mul]
  rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun x hx => hzero θ x hx),
    tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun x hx => hzero θ' x hx),
    ← Finset.sum_sub_distrib]
  calc ‖∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
          - g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ)))‖
      ≤ ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ‖g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
            - g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (2 * Real.pi * (B : ℝ) * |θ - θ'|) :=
        Finset.sum_le_sum fun x hx => corr_term_le hg1 hMB hx θ θ'
    _ = ((Finset.Icc (-(M : ℤ)) (M : ℤ)).card : ℝ) * (2 * Real.pi * (B : ℝ) * |θ - θ'|) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * B + 1 : ℕ) : ℝ) * (2 * Real.pi * (B : ℝ) * |θ - θ'|) := by
        have hcardR : (((Finset.Icc (-(M : ℤ)) (M : ℤ)).card : ℕ) : ℝ)
            ≤ ((2 * B + 1 : ℕ) : ℝ) := by exact_mod_cast corr_card_Icc_le B M hMB
        have hnn : (0 : ℝ) ≤ 2 * Real.pi * (B : ℝ) * |θ - θ'| :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
            (by positivity)) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right hcardR hnn
    _ = 2 * Real.pi * (B : ℝ) * ((2 * B + 1 : ℕ) : ℝ) * |θ - θ'| := by ring

theorem corr_lipschitz {B M : ℕ} {g : ℤ → ℂ} (hB : 1 ≤ B) (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1)
    (hgs : Work.Peluse.SupportIn g M) (hMB : M ≤ B) (θ θ' : ℝ) :
    ‖((B : ℂ))⁻¹ * ∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))
      - ((B : ℂ))⁻¹ * ∑' x : ℤ, g x *
          Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ))‖
      ≤ 2 * Real.pi * (((2 * B + 1 : ℕ) : ℝ)) * |θ - θ'| := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : (0 : ℕ) < B := by omega
    exact_mod_cast this
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
  have hfac : ((B : ℂ))⁻¹ *
        (∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)))
      - ((B : ℂ))⁻¹ *
        (∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ)))
      = ((B : ℂ))⁻¹ *
        ((∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)))
          - (∑' x : ℤ, g x * Complex.exp (2 * Real.pi * Complex.I * (θ' : ℂ) * (x : ℂ)))) := by
    ring
  rw [hfac, norm_mul, norm_inv, Complex.norm_natCast]
  have key := corr_tsum_diff_le hg1 hgs hMB θ θ'
  refine (mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hBpos.le)).trans ?_
  have hrew : (B : ℝ)⁻¹ * (2 * Real.pi * (B : ℝ) * ((2 * B + 1 : ℕ) : ℝ) * |θ - θ'|)
      = ((B : ℝ)⁻¹ * (B : ℝ)) * (2 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) * |θ - θ'|) := by ring
  rw [hrew, inv_mul_cancel₀ hBne, one_mul]

end Work.Peluse.Ulower.StepLe
