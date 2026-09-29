import Mathlib
import Submission.Work.CPull.sympSym_radius
import Submission.Work.C17I.sympQ_coeff_degree
import Submission.Work.C17I.sympQ_coeff_choose_bound
import Submission.Work.C17I.sympSym_coeff_bound_of
import Submission.Work.C17I.poly_rate_bound

namespace Work.C17I

open PowerSeries

/- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# A better coefficient bound for `G = Sym⁺P` and its `y`-derivatives

`Work.CPull.sympSym_radius` (proved) gives, from `‖coeff_m P‖ ≤ C ρ₀^m` with `ρ₀ > 0`, that
`‖coeff_n (Sym⁺P)‖ ≤ C' (8 (1+ρ₀)²)^n`; the factor `8(1+ρ₀)²` is far from optimal and too large
for the downstream substitution estimate (which needs a rate `≤ 4`).

The refinement wanted here: use `Sym⁺P = Σ_m coeff_m(P) · P_m` with `P_m = x^m + φ^m`
(`Work.CPull.sympSym_eq_sympRep`, `Submission.CDT.sympQ`), for which `[y^n]P_{n+j}` is a rational
combination of `C(n,j)` and `C(n-1,j-1)` (or `C(n,j-1)`), in particular bounded by
`2 C(n,j) + C(n,j-1)` (with `C(u,v) = 0` for `v < 0`).  Hence
`|coeff_n (Sym⁺P)| ≤ Σ_j |coeff_{n+j} P| (2 C(n,j) + C(n,j-1)) ≤ C (2+ρ₀) (ρ₀(1+ρ₀))^n`,
a rate `ρ₀(1+ρ₀) ≤ 45/16 < 4` under `ρ₀ ≤ 5/4`.

The order-`k` derivative of `G` is not needed separately: `coeff_n (G^{(k)})` is a polynomial
multiple (`(n+1)⋯(n+k)`) of `coeff_{n+k} G`, and `n^k (ρ₀(1+ρ₀))^n ≤ C_ε (4-ε)^n` for every
`ε > 0`, so the same bound `C · 4^n` holds for `k ≤ 3` (including the shifted starting index).

Helper auxiliary results may be added above the claim; do not change the claim. -/

/-- The rising factorial `(n+1)(n+2)⋯(n+k) = (n+1).ascFactorial k`, for `k ≤ 3`, is at most
`(n+3)^3`: every one of the at most three factors is `≤ n+3`. -/
lemma ascFactorial_le_cube (n k : ℕ) (hk : k ≤ 3) :
    ((n + 1).ascFactorial k : ℝ) ≤ ((n : ℝ) + 3) ^ 3 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : (1 : ℝ) ≤ (n : ℝ) + 3 := by linarith
  have hprod : ((n + 1).ascFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((n : ℝ) + 1 + i) := by
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast
    rfl
  rw [hprod]
  have hbound : ∀ i ∈ Finset.range k, ((n : ℝ) + 1 + i) ≤ ((n : ℝ) + 3) := by
    intro i hi
    have hi3 : ((i : ℕ) : ℝ) ≤ 2 := by
      have hik : i < k := Finset.mem_range.mp hi
      have : i ≤ 2 := by omega
      exact_mod_cast this
    push_cast
    linarith
  calc ∏ i ∈ Finset.range k, ((n : ℝ) + 1 + i)
      ≤ ∏ _i ∈ Finset.range k, ((n : ℝ) + 3) :=
        Finset.prod_le_prod₀ (fun i _ => by positivity) hbound
    _ = ((n : ℝ) + 3) ^ k := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ((n : ℝ) + 3) ^ 3 := pow_le_pow_right₀ h3 hk

theorem sympSym_deriv_coeff_bound {P : PowerSeries ℚ} {C₀ ρ₀ : ℝ} (hC₀ : 0 < C₀) (hρ₀ : 0 < ρ₀)
    (hρ₀1 : ρ₀ ≤ 5 / 4)
    (hP : ∀ m : ℕ, ‖((PowerSeries.coeff m P : ℚ) : ℂ)‖ ≤ C₀ * ρ₀ ^ m) (k : ℕ) (hk : k ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖((PowerSeries.coeff n (((PowerSeries.derivative (R := ℚ))^[k]) (Submission.CDT.sympSym P)) : ℚ) : ℂ)‖
        ≤ C * 4 ^ n := by
  have hPreal : ∀ m : ℕ, |((PowerSeries.coeff m P : ℚ) : ℝ)| ≤ C₀ * ρ₀ ^ m := by
    intro m
    have h := hP m
    rwa [Work.CPull.norm_rat_cast_complex] at h
  have hG : ∀ n : ℕ, |((PowerSeries.coeff n (Submission.CDT.sympSym P) : ℚ) : ℝ)|
      ≤ 2 * C₀ * (ρ₀ * (1 + ρ₀)) ^ n := fun n =>
    sympSym_coeff_bound_of (fun m n h => sympQ_coeff_degree m n h)
      (fun n j => sympQ_coeff_choose_bound n j) hC₀ hρ₀ hPreal n
  have hRpos : 0 < ρ₀ * (1 + ρ₀) := by positivity
  have hRle : ρ₀ * (1 + ρ₀) ≤ 45 / 16 := by nlinarith
  obtain ⟨Cp, hCp, hCpbound⟩ := poly_rate_bound (ρ₀ * (1 + ρ₀)) hRpos hRle
  have hrk : (ρ₀ * (1 + ρ₀)) ^ k ≤ (45 / 16 : ℝ) ^ 3 := by
    rcases le_total 1 (ρ₀ * (1 + ρ₀)) with h1 | h1
    · calc (ρ₀ * (1 + ρ₀)) ^ k ≤ (ρ₀ * (1 + ρ₀)) ^ 3 := pow_le_pow_right₀ h1 hk
        _ ≤ (45 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ (le_of_lt hRpos) hRle 3
    · have h2 : (ρ₀ * (1 + ρ₀)) ^ k ≤ 1 := pow_le_one₀ (le_of_lt hRpos) h1
      have h3 : (1 : ℝ) ≤ (45 / 16) ^ 3 := by norm_num
      linarith
  refine ⟨2 * C₀ * (45 / 16) ^ 3 * Cp, by positivity, fun n => ?_⟩
  have hcoeff : PowerSeries.coeff n (((PowerSeries.derivative (R := ℚ))^[k]) (Submission.CDT.sympSym P))
      = ((n + 1).ascFactorial k : ℚ) * PowerSeries.coeff (n + k) (Submission.CDT.sympSym P) :=
    PowerSeries.coeff_iterate_derivative (Submission.CDT.sympSym P) k n
  rw [Work.CPull.norm_rat_cast_complex, hcoeff]
  have hcast : ((((n + 1).ascFactorial k : ℚ) * PowerSeries.coeff (n + k) (Submission.CDT.sympSym P) : ℚ) : ℝ)
      = ((n + 1).ascFactorial k : ℝ)
        * ((PowerSeries.coeff (n + k) (Submission.CDT.sympSym P) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ((n + 1).ascFactorial k))]
  calc ((n + 1).ascFactorial k : ℝ)
        * |((PowerSeries.coeff (n + k) (Submission.CDT.sympSym P) : ℚ) : ℝ)|
      ≤ ((n : ℝ) + 3) ^ 3 * (2 * C₀ * (ρ₀ * (1 + ρ₀)) ^ (n + k)) :=
        mul_le_mul (ascFactorial_le_cube n k hk) (hG (n + k)) (abs_nonneg _) (by positivity)
    _ = 2 * C₀ * (ρ₀ * (1 + ρ₀)) ^ k * (((n : ℝ) + 3) ^ 3 * (ρ₀ * (1 + ρ₀)) ^ n) := by
        rw [pow_add]
        ring
    _ ≤ 2 * C₀ * (45 / 16) ^ 3 * (Cp * 4 ^ n) := by
        have hK : (0 : ℝ) ≤ ((n : ℝ) + 3) ^ 3 * (ρ₀ * (1 + ρ₀)) ^ n := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hrk (by positivity)) (hCpbound n) hK
          (by positivity)
    _ = 2 * C₀ * (45 / 16) ^ 3 * Cp * 4 ^ n := by ring

end Work.C17I
