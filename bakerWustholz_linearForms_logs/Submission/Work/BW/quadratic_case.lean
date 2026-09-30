import Mathlib
import Submission.Work.BW.roots_facts
import Submission.Work.BW.rootOfUnity_of_quadratic_small
import Submission.Work.BW.false_of_quadratic_factor_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- A monic integer polynomial of degree `2` is determined by its two lowest coefficients. -/
private lemma eq_quadratic_of_monic_natDegree_two (P : Polynomial ℤ) (hP : P.Monic)
    (hdeg : P.natDegree = 2) : P = X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) := by
  ext n
  match n with
  | 0 => rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  | 1 => rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_C]; norm_num
  | 2 =>
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
      rw [← hdeg, Polynomial.coeff_natDegree, hP.leadingCoeff]
  | k+3 =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_add, Polynomial.coeff_add,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      rw [if_neg (show ¬ (k + 3 = 2) by omega), if_neg (show ¬ (1 = k + 3) by omega),
        if_neg (show ¬ (k + 3 = 0) by omega)]
      ring

/-- **The degree-`2` case.** A monic irreducible quadratic `P ∈ ℤ[X]` with
`M(P) ≤ 1 + 1/(104 log 12)` has only roots of unity.

Proof: `M(P) < 2` forces `|P.coeff 0| = 1`, so `P = X² - tX + s` with `s = ±1` and `t ∈ ℤ`.  If the
roots are non-real then `|t| ≤ 1`, whence `P ∈ {X²±1, X²±X+1}` is cyclotomic; if they are real
then `P = X² - tX + s` with `|t| ≥ 3` (as `t = ±2` gives the double root `±1`, i.e. degree `< 2`),
and the largest root has modulus `≥ (3+√5)/2 > 1.618 > 1 + 1/(104 log 12)`. -/
theorem quadratic_case (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : P.natDegree = 2)
    (hM : (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1 + 1/(52 * (2:ℝ) * Real.log 12)) :
    ∀ {α : ℂ}, (P.map (Int.castRingHom ℂ)).IsRoot α → ∃ k : ℕ, 0 < k ∧ α ^ k = 1 := by
  intro α hα
  -- The constant coefficient does not vanish (a root of an irreducible polynomial of degree `> 1`).
  have hs_ne : P.coeff 0 ≠ 0 := (roots_facts P hP hirr (by omega)).2.2.2
  -- ## numeric preparation
  have hlog12 : 1 < Real.log 12 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 12)]
    linarith [Real.exp_one_lt_three]
  have hc : 1/(52 * (2:ℝ) * Real.log 12) < 1/5 := by
    have h2 : (52:ℝ) * 2 * Real.log 12 = 104 * Real.log 12 := by norm_num
    rw [h2]
    refine one_div_lt_one_div_of_lt (by norm_num) ?_
    linarith
  -- ## the quadratic presentation of `P` and of its image `Q`
  have hPq : P = X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) :=
    eq_quadratic_of_monic_natDegree_two P hP hdeg
  have hQq : (P.map (Int.castRingHom ℂ))
      = X^2 + C ((P.coeff 1 : ℤ) : ℂ) * X + C ((P.coeff 0 : ℤ) : ℂ) := by
    conv_lhs => rw [hPq]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Int.coe_castRingHom]
  -- ## the equation satisfied by a root
  have heval : α^2 + ((P.coeff 1 : ℤ) : ℂ) * α + ((P.coeff 0 : ℤ) : ℂ) = 0 := by
    have h : (P.map (Int.castRingHom ℂ)).eval α = 0 := Polynomial.IsRoot.def.mp hα
    rw [hQq] at h
    simpa using h
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h : ((P.coeff 0 : ℤ) : ℂ) = 0 := by simpa using heval
    exact hs_ne (by exact_mod_cast h)
  -- ## the second root
  set β : ℂ := ((P.coeff 0 : ℤ) : ℂ) / α with hβdef
  have hαβ : α * β = ((P.coeff 0 : ℤ) : ℂ) := by
    rw [hβdef, div_eq_mul_inv, mul_comm α, mul_assoc, inv_mul_cancel₀ hα0, mul_one]
  have hsum : α + β = -((P.coeff 1 : ℤ) : ℂ) := by
    have h3 : α * (α + ((P.coeff 1 : ℤ) : ℂ) + β) = 0 := by
      have h4 : α * (α + ((P.coeff 1 : ℤ) : ℂ) + β)
          = α^2 + ((P.coeff 1 : ℤ) : ℂ) * α + α * β := by ring
      rw [h4, hαβ]; exact heval
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hα0
    · linear_combination h
  have hfac : (P.map (Int.castRingHom ℂ)) = (X - C α) * (X - C β) := by
    have ht : ((P.coeff 1 : ℤ) : ℂ) = -(α + β) := by rw [hsum, neg_neg]
    have hs : ((P.coeff 0 : ℤ) : ℂ) = α * β := by rw [hαβ]
    rw [hQq, ht, hs]
    simp only [Polynomial.C_add, Polynomial.C_neg, Polynomial.C_mul]
    ring
  -- ## Mahler measure as a product over the two roots
  have hMfac : (P.map (Int.castRingHom ℂ)).mahlerMeasure = max 1 ‖α‖ * max 1 ‖β‖ := by
    rw [hfac, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_X_sub_C,
      Polynomial.mahlerMeasure_X_sub_C]
  have hM' : max 1 ‖α‖ * max 1 ‖β‖ ≤ 1 + 1/(52 * (2:ℝ) * Real.log 12) := hMfac ▸ hM
  -- ## the constant coefficient is `±1`
  have hs_le : ‖((P.coeff 0 : ℤ) : ℂ)‖ ≤ 1 + 1/(52 * (2:ℝ) * Real.log 12) := by
    calc ‖((P.coeff 0 : ℤ) : ℂ)‖ = ‖α * β‖ := by rw [hαβ]
      _ = ‖α‖ * ‖β‖ := norm_mul α β
      _ ≤ max 1 ‖α‖ * max 1 ‖β‖ :=
          mul_le_mul (le_max_right 1 ‖α‖) (le_max_right 1 ‖β‖) (norm_nonneg β) (by positivity)
      _ ≤ 1 + 1/(52 * (2:ℝ) * Real.log 12) := hM'
  have hs_cases : P.coeff 0 = 1 ∨ P.coeff 0 = -1 := by
    have h1 : |(((P.coeff 0 : ℤ)) : ℝ)| < 2 := by
      rw [Complex.norm_intCast] at hs_le
      linarith
    have h2 : (-2 : ℝ) < (((P.coeff 0 : ℤ)) : ℝ) := (abs_lt.mp h1).1
    have h3 : (((P.coeff 0 : ℤ)) : ℝ) < 2 := (abs_lt.mp h1).2
    have h2' : (-2 : ℤ) < P.coeff 0 := by exact_mod_cast h2
    have h3' : P.coeff 0 < 2 := by exact_mod_cast h3
    omega
  -- ## the discriminant of the two roots is bounded by the Mahler measure bound
  have hdiff : (α - β)^2 = ((P.coeff 1 : ℤ) : ℂ)^2 - 4 * ((P.coeff 0 : ℤ) : ℂ) := by
    have h4 : (α - β)^2 = (α + β)^2 - 4 * (α * β) := by ring
    rw [h4, hsum, hαβ]; ring
  have hkey : ¬ (5 ≤ (P.coeff 1)^2 - 4 * (P.coeff 0)) := by
    intro h5
    have hnorm : ‖α - β‖^2 = |(((P.coeff 1)^2 - 4 * (P.coeff 0) : ℤ) : ℝ)| := by
      rw [← Complex.norm_pow, hdiff]
      have hcast : ((P.coeff 1 : ℤ) : ℂ)^2 - 4 * ((P.coeff 0 : ℤ) : ℂ)
          = (((P.coeff 1)^2 - 4 * (P.coeff 0) : ℤ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_intCast]
    have hd : 5 ≤ ‖α - β‖^2 := by
      rw [hnorm]
      have h6 : (5:ℝ) ≤ (((P.coeff 1)^2 - 4 * (P.coeff 0) : ℤ) : ℝ) := by exact_mod_cast h5
      rw [abs_of_nonneg (by linarith)]; exact h6
    have hprod : α * β = 1 ∨ α * β = -1 := by
      rcases hs_cases with h | h
      · left; rw [hαβ, h]; norm_num
      · right; rw [hαβ, h]; norm_num
    exact false_of_quadratic_factor_bound α β _ hc hprod hM' hd
  -- ## conclusion
  rcases hs_cases with hs1 | hs1
  · have ht : -2 ≤ P.coeff 1 ∧ P.coeff 1 ≤ 2 := by
      have h9 : (P.coeff 1)^2 < (9:ℤ) := by
        have h4 : ¬ (5 ≤ (P.coeff 1)^2 - 4) := by rw [hs1] at hkey; simpa using hkey
        omega
      have habs : |P.coeff 1| < (3:ℤ) := by
        have h3 : |P.coeff 1|^2 < (3:ℤ)^2 := by rw [sq_abs]; norm_num; exact h9
        simpa using (sq_lt_sq.mp h3)
      have hlt := abs_lt.mp habs
      constructor <;> omega
    exact rootOfUnity_of_quadratic_small α (P.coeff 1) (P.coeff 0) (Or.inl ⟨hs1, ht.1, ht.2⟩) heval
  · have ht0 : P.coeff 1 = 0 := by
      have h4 : ¬ (5 ≤ (P.coeff 1)^2 + 4) := by rw [hs1] at hkey; simpa using hkey
      have h9 : (P.coeff 1)^2 = 0 := by
        have h11 : (P.coeff 1)^2 ≤ 0 := by omega
        exact le_antisymm h11 (sq_nonneg _)
      exact sq_eq_zero_iff.mp h9
    exact rootOfUnity_of_quadratic_small α (P.coeff 1) (P.coeff 0) (Or.inr ⟨hs1, ht0⟩) heval

end Work.BW
