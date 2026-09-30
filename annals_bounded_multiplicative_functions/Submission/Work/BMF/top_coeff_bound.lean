import Mathlib
import Submission.Work.BMF.adi_lagrange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bound on the top coefficient of a polynomial bounded on an interval

If `e : ℝ[X]` has `natDegree ≤ j` and `|e| ≤ A` on an interval `[t0, t0 + lam]` of length
`lam > 0`, then the `j`-th coefficient (the top coefficient when `deg e = j`) satisfies

`|e.coeff j| ≤ A * (j + 1) * j^j / lam^j`.

The proof uses Lagrange interpolation at the equally spaced nodes `t0 + r·(lam/j)`
(`r = 0, …, j`), which all lie in the interval, and the crude lower bound
`|v_r - v_m| ≥ lam/j` for `m ≠ r`: hence every coefficient of the Lagrange basis is
`≥ (lam/j)^j` in modulus and the `j + 1` terms sum to the required bound.

This is the "leading coefficient of a degree-`≤ j` polynomial bounded on an interval"
estimate needed in the polynomial-phase short-interval argument.
-/

namespace Work.BMF

open Polynomial Finset

/-- Two distinct natural numbers, cast to `ℝ`, are at distance at least `1`. -/
theorem one_le_abs_cast_sub_nat {a b : ℕ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  have hz : ((a : ℤ) - (b : ℤ)) ≠ 0 := by
    intro hh
    exact h (by exact_mod_cast (sub_eq_zero.mp hh : (a : ℤ) = (b : ℤ)))
  have h1 : (1 : ℤ) ≤ |(a : ℤ) - (b : ℤ)| := Int.one_le_abs hz
  calc (1 : ℝ) ≤ ((|(a : ℤ) - (b : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h1
    _ = |(((a : ℤ) - (b : ℤ) : ℤ) : ℝ)| := by rw [Int.cast_abs]
    _ = |(a : ℝ) - (b : ℝ)| := by push_cast; ring_nf

theorem top_coeff_bound {j : ℕ} {e : ℝ[X]} (hdeg : e.natDegree ≤ j) {A t0 lam : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hbd : ∀ t ∈ Set.Icc t0 (t0 + lam), |e.eval t| ≤ A) :
    |e.coeff j| ≤ A * ((j : ℝ) + 1) * (j : ℝ) ^ j / lam ^ j := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hconst : e = Polynomial.C (e.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
    have hmem : t0 ∈ Set.Icc t0 (t0 + lam) := ⟨le_rfl, by linarith⟩
    have hb := hbd t0 hmem
    rw [hconst] at hb
    simp only [Polynomial.eval_C] at hb
    simpa using hb
  · set h : ℝ := lam / (j : ℝ) with hhdef
    have hjR : (0:ℝ) < (j : ℝ) := by exact_mod_cast hjpos
    have hhpos : 0 < h := by rw [hhdef]; exact div_pos hlam hjR
    set v : Fin (j + 1) → ℝ := fun r => t0 + (r : ℝ) * h with hvdef
    have hvr : ∀ r : Fin (j + 1), v r = t0 + (r : ℝ) * h := fun r => by rw [hvdef]
    have hvinj : Function.Injective v := by
      intro r s hrs
      rw [hvr r, hvr s] at hrs
      have hmul : (r : ℝ) * h = (s : ℝ) * h := by linarith
      have hcast : (r : ℝ) = (s : ℝ) := mul_right_cancel₀ (ne_of_gt hhpos) hmul
      exact Fin.ext (by exact_mod_cast hcast)
    have hmemv : ∀ r : Fin (j + 1), v r ∈ Set.Icc t0 (t0 + lam) := by
      intro r
      rw [hvr r]
      have hrle : (r : ℝ) ≤ (j : ℝ) := by
        have hrlt := r.isLt
        exact_mod_cast (Nat.lt_succ_iff.mp hrlt)
      have hjh : (j:ℝ) * h = lam := by rw [hhdef]; exact mul_div_cancel₀ lam (ne_of_gt hjR)
      have hrh : (r : ℝ) * h ≤ lam := by
        calc (r:ℝ) * h ≤ (j:ℝ) * h := mul_le_mul_of_nonneg_right hrle hhpos.le
          _ = lam := hjh
      constructor
      · have : 0 ≤ (r : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hhpos.le
        linarith
      · linarith
    have hlag := lagrange_coeff_top (n := j) (v := v) hvinj (Q := e) hdeg
    rw [hlag]
    have hsum : |∑ r : Fin (j + 1), e.eval (v r) * (∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹|
        ≤ ∑ r : Fin (j + 1), A * (h ^ j)⁻¹ := by
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun r : Fin (j + 1) => e.eval (v r) * (∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹)
        Finset.univ) ?_
      apply Finset.sum_le_sum
      intro r _
      have h1 : |e.eval (v r)| ≤ A := hbd (v r) (hmemv r)
      have h2 : |(∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹| ≤ (h ^ j)⁻¹ := by
        rw [abs_inv, Finset.abs_prod]
        have hcard : (Finset.univ.erase r : Finset (Fin (j+1))).card = j := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
          omega
        have hstep : (∏ m ∈ Finset.univ.erase r, (h:ℝ))
            ≤ ∏ m ∈ Finset.univ.erase r, |v r - v m| := by
          apply Finset.prod_le_prod₀
          · intro m _
            exact hhpos.le
          · intro m hm
            have hmne : m ≠ r := (Finset.mem_erase.mp hm).1
            have hneed : (1:ℝ) ≤ |((r:ℝ) - (m:ℝ))| := by
              rw [abs_sub_comm]
              exact one_le_abs_cast_sub_nat (fun hh => hmne (Fin.ext hh))
            have hveq : v r - v m = ((r:ℝ) - (m:ℝ)) * h := by
              rw [hvr r, hvr m]; ring
            rw [hveq, abs_mul, abs_of_pos hhpos]
            exact le_trans (le_of_eq (one_mul h).symm) (mul_le_mul_of_nonneg_right hneed hhpos.le)
        rw [Finset.prod_const, hcard] at hstep
        simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hhpos j) hstep
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hA
    have hcast_sum : (∑ r : Fin (j + 1), A * (h ^ j)⁻¹)
        = ((j:ℝ) + 1) * (A * (h ^ j)⁻¹) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [hcast_sum] at hsum
    refine le_trans hsum (le_of_eq ?_)
    rw [hhdef, div_pow, inv_div]
    ring

end Work.BMF
