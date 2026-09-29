import Mathlib
import Submission.Work.C17.sigma_defs

/-!
# The second-order expansion of `ρ^e` at `x = 0`

`ρ = (x-1)⁻¹` is the ratio `σ(x)/x` of the deck involution `σ : x ↦ x/(x-1)` at its fixed point
`x = 0` (`Work.C17.rhoS`).  Since `ρ = -1/(1-x)` is a unit of the local ring at `0` with value
`-1`, every integer power of `ρ` is regular at `0` and has the second order expansion

  `ρ^e = (-1)^e + (-1)^e·e·x + O(x²)`     at `x = 0`.

This module proves that expansion in the *equation* form used by the `Lead2At` API of
`Work.C17.lead_api`: for every `e : ℤ` there is a rational function `h`, regular at `0`, with

  `ρ^e = (-1)^e + (-1)^e·e·x + x²·h`.

The proof is a two-sided induction on `e` (`Int.induction_on`): the identity
`ρ = -1 - x + x²·ρ` (resp. `ρ⁻¹ = -1 + x`) upgrades an expansion of `ρ^e` to one of `ρ^{e+1}`
(resp. `ρ^{e-1}`), multiplying the coefficients by the rational arithmetic
`(-1)^{e+1} = -(-1)^e`, `(-1)^{e+1}(e+1) = -(-1)^e - (-1)^e·e`
(resp. `(-1)^{e-1} = -(-1)^e`, `(-1)^{e-1}(e-1) = (-1)^e - (-1)^e·e`).
Regularity of `h` is preserved because `Reg` is closed under sums, products and negatives.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

/-! ## The two first-order expansions of `ρ` and `ρ⁻¹` -/

/-- `ρ = -1 - x + x²·ρ`: the expansion of `ρ` at `0` with remainder `ρ` itself. -/
private lemma rhoS_selfExpand : rhoS = -1 - xQ + xQ ^ 2 * rhoS := by
  have h1 : rhoS * (xQ - 1) = 1 := by
    rw [rhoS]; exact inv_mul_cancel₀ xQ_sub_one_ne_zero_sigma_defs
  have key : (-1 - xQ + xQ ^ 2 * rhoS) * (xQ - 1) = 1 := by
    linear_combination (xQ ^ 2) * h1
  exact mul_right_cancel₀ xQ_sub_one_ne_zero_sigma_defs (by rw [h1, key])

/-- `ρ⁻¹ = -1 + x`: the expansion of `ρ⁻¹ = x - 1` at `0` (the remainder vanishes). -/
private lemma rhoS_invExpand : rhoS⁻¹ = -1 + xQ := by
  rw [rhoS, inv_inv]; ring

/-! ## The coefficient families `e ↦ (-1)^e` and `e ↦ (-1)^e·e` -/

/-- The constant coefficient `(-1)^e` of the expansion of `ρ^e`. -/
private def A (e : ℤ) : RatFunc ℚ := algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e)

/-- The linear coefficient `(-1)^e·e` of the expansion of `ρ^e`. -/
private def B (e : ℤ) : RatFunc ℚ := algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e * (e : ℚ))

private lemma A_zero : A 0 = 1 := by simp [A]

private lemma B_zero : B 0 = 0 := by simp [B]

private lemma A_succ (e : ℤ) : A (e + 1) = -A e := by
  unfold A
  rw [zpow_add_one₀ (by norm_num : (-1 : ℚ) ≠ 0), map_mul, map_neg, map_one, mul_neg, mul_one]

private lemma B_succ (e : ℤ) : B (e + 1) = -A e - B e := by
  unfold A B
  have h1 : (-1 : ℚ) ^ (e + 1) = (-1) ^ e * (-1) := zpow_add_one₀ (by norm_num) e
  have h2 : ((e + 1 : ℤ) : ℚ) = (e : ℚ) + 1 := by push_cast; ring
  rw [h1, h2,
    show ((-1:ℚ)^e * (-1)) * ((e:ℚ) + 1) = -((-1:ℚ)^e) - (-1:ℚ)^e * (e:ℚ) by ring]
  rw [map_sub, map_neg]

private lemma A_pred (e : ℤ) : A (e - 1) = -A e := by
  unfold A
  have hinv : ((-1 : ℚ))⁻¹ = -1 := by norm_num
  rw [zpow_sub_one₀ (by norm_num : (-1 : ℚ) ≠ 0), hinv, map_mul, map_neg, map_one, mul_neg,
    mul_one]

private lemma B_pred (e : ℤ) : B (e - 1) = A e - B e := by
  unfold A B
  have hinv : ((-1 : ℚ))⁻¹ = -1 := by norm_num
  have h1 : (-1 : ℚ) ^ (e - 1) = (-1) ^ e * (-1) := by
    rw [zpow_sub_one₀ (by norm_num : (-1 : ℚ) ≠ 0), hinv]
  have h2 : ((e - 1 : ℤ) : ℚ) = (e : ℚ) - 1 := by push_cast; ring
  rw [h1, h2,
    show ((-1:ℚ)^e * (-1)) * ((e:ℚ) - 1) = (-1:ℚ)^e - (-1:ℚ)^e * (e:ℚ) by ring]
  rw [map_sub]

/-! ## The two induction steps -/

/-- Multiplication by `ρ = -1 - x + x²·ρ` upgrades an expansion of `ρ^e` to one of `ρ^{e+1}`. -/
private lemma step_up {e : ℤ} {a b h : RatFunc ℚ}
    (_ha : Reg a) (hb : Reg b) (hh : Reg h)
    (he : rhoS ^ e = a + b * xQ + xQ ^ 2 * h) :
    ∃ h' : RatFunc ℚ, Reg h' ∧ rhoS ^ (e + 1) = -a + (-a - b) * xQ + xQ ^ 2 * h' := by
  refine ⟨a * rhoS - b + b * xQ * rhoS - h - xQ * h + xQ ^ 2 * h * rhoS, ?_, ?_⟩
  · have h1 : Reg (a * rhoS) := reg_mul _ha reg_rhoS
    have h2 : Reg (b * xQ * rhoS) := reg_mul (reg_mul hb reg_X) reg_rhoS
    have h3 : Reg (xQ * h) := reg_mul reg_X hh
    have h4 : Reg (xQ ^ 2 * h * rhoS) := reg_mul (reg_mul (reg_pow reg_X 2) hh) reg_rhoS
    exact reg_add (reg_sub (reg_sub (reg_add (reg_sub h1 hb) h2) hh) h3) h4
  · rw [zpow_add_one₀ rhoS_ne_zero, he]
    conv_lhs => rw [rhoS_selfExpand]
    ring

/-- Multiplication by `ρ⁻¹ = -1 + x` upgrades an expansion of `ρ^e` to one of `ρ^{e-1}`. -/
private lemma step_down {e : ℤ} {a b h : RatFunc ℚ}
    (_ha : Reg a) (hb : Reg b) (hh : Reg h)
    (he : rhoS ^ e = a + b * xQ + xQ ^ 2 * h) :
    ∃ h' : RatFunc ℚ, Reg h' ∧ rhoS ^ (e - 1) = -a + (a - b) * xQ + xQ ^ 2 * h' := by
  refine ⟨b - h + xQ * h, ?_, ?_⟩
  · exact reg_add (reg_sub hb hh) (reg_mul reg_X hh)
  · rw [zpow_sub_one₀ rhoS_ne_zero, he, rhoS_invExpand]
    ring

/-! ## The two-sided induction -/

/-- `ρ^e = A e + B e·x + x²·h` for a regular `h`. -/
private def Good (e : ℤ) : Prop :=
  ∃ h : RatFunc ℚ, Reg h ∧ rhoS ^ e = A e + B e * xQ + xQ ^ 2 * h

private lemma good_base : Good 0 := by
  refine ⟨0, reg_zero, ?_⟩
  simp [A_zero, B_zero]

private lemma good_succ (e : ℤ) (he : Good e) : Good (e + 1) := by
  obtain ⟨h, hhr, hhe⟩ := he
  obtain ⟨h', hhr', hhe'⟩ := step_up (reg_rat ((-1:ℚ)^e)) (reg_rat ((-1:ℚ)^e * (e:ℚ))) hhr hhe
  exact ⟨h', hhr', by rw [A_succ e, B_succ e]; exact hhe'⟩

private lemma good_pred (e : ℤ) (he : Good e) : Good (e - 1) := by
  obtain ⟨h, hhr, hhe⟩ := he
  obtain ⟨h', hhr', hhe'⟩ := step_down (reg_rat ((-1:ℚ)^e)) (reg_rat ((-1:ℚ)^e * (e:ℚ))) hhr hhe
  exact ⟨h', hhr', by rw [A_pred e, B_pred e]; exact hhe'⟩

/-- **Second-order expansion of `ρ^e` at `x = 0`.**  For every integer `e` the rational function
`ρ^e` agrees with `(-1)^e + (-1)^e·e·x` up to a multiple of `x²` whose quotient is regular at `0`. -/
theorem rhoS_zpow_expand (e : ℤ) :
    ∃ h : RatFunc ℚ, Reg h ∧
      rhoS ^ e = algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e)
        + algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e * (e : ℚ)) * xQ
        + xQ ^ 2 * h := by
  have h := Int.induction_on (motive := Good) e good_base
    (fun n ih => good_succ (n : ℤ) ih) (fun n ih => good_pred (-(n : ℤ)) ih)
  simpa [Good, A, B] using h

end

end Work.C17
