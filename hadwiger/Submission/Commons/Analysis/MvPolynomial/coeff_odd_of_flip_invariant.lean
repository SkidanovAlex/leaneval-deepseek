import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.MvPolynomial

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- `(-X i)^k = C ((-1)^k) * X i^k` over ℝ. -/
private lemma neg_X_pow (i : Fin n) (k : ℕ) :
    (-(MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) ^ k
      = MvPolynomial.C ((-1 : ℝ) ^ k) * MvPolynomial.X i ^ k := by
  rw [show -(MvPolynomial.X i : MvPolynomial (Fin n) ℝ)
        = MvPolynomial.C (-1 : ℝ) * MvPolynomial.X i by
        ext d; simp]
  rw [mul_pow, ← map_pow]

/-- Each power of a flipped variable splits into a sign and the power of the variable. -/
private lemma flip_X_pow (i j : Fin n) (k : ℕ) :
    (if j = i then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) ^ k
      = MvPolynomial.C ((-1 : ℝ) ^ (if j = i then k else 0)) * MvPolynomial.X j ^ k := by
  by_cases h : j = i
  · have hk : (if j = i then k else 0) = (k : ℕ) := by simp [h]
    rw [if_pos h, hk]
    exact neg_X_pow j k
  · have hk : (if j = i then k else 0) = (0 : ℕ) := by simp [h]
    rw [if_neg h, hk]
    simp

/-- The product of the signs appearing when flipping the `i`-th variable is `(-1)^(m i)`. -/
private lemma prod_sgn_pow (i : Fin n) (m : Fin n →₀ ℕ) (s : Finset (Fin n))
    (hi : i ∈ s ∨ m i = 0) :
    ∏ j ∈ s, (-1 : ℝ) ^ (if j = i then m j else 0) = (-1 : ℝ) ^ (m i) := by
  classical
  have hrewrite :
      (∏ j ∈ s, (-1 : ℝ) ^ (if j = i then m j else 0))
        = ∏ j ∈ s, (if j = i then (-1 : ℝ) ^ (m j) else 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j = i <;> simp [hji]
  rw [hrewrite]
  rw [Finset.prod_ite_eq' s i (fun j => (-1 : ℝ) ^ (m j))]
  by_cases hmem : i ∈ s
  · simp [hmem]
  · rcases hi with hmem' | hm0
    · exact False.elim (hmem hmem')
    · simp [hmem, hm0]

/-- Flipping the `i`-th variable throughout a monomial product only introduces
the sign `C ((-1)^(m i))`. -/
private lemma prod_flip_X_pow (i : Fin n) (m : Fin n →₀ ℕ) :
    (∏ j ∈ m.support,
        (if j = i then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) ^ (m j))
      = MvPolynomial.C ((-1 : ℝ) ^ (m i)) * ∏ j ∈ m.support, MvPolynomial.X j ^ (m j) := by
  classical
  calc
    (∏ j ∈ m.support,
        (if j = i then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) ^ (m j))
        = ∏ j ∈ m.support,
            (MvPolynomial.C ((-1 : ℝ) ^ (if j = i then m j else 0)) * MvPolynomial.X j ^ (m j)) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact flip_X_pow i j (m j)
    _ = (∏ j ∈ m.support, MvPolynomial.C ((-1 : ℝ) ^ (if j = i then m j else 0))) *
        (∏ j ∈ m.support, MvPolynomial.X j ^ (m j)) := by
            rw [Finset.prod_mul_distrib]
    _ = MvPolynomial.C (∏ j ∈ m.support, (-1 : ℝ) ^ (if j = i then m j else 0)) *
        (∏ j ∈ m.support, MvPolynomial.X j ^ (m j)) := by
            congr 1
            rw [← map_prod]
    _ = MvPolynomial.C ((-1 : ℝ) ^ (m i)) * (∏ j ∈ m.support, MvPolynomial.X j ^ (m j)) := by
            rw [prod_sgn_pow i m m.support (by
              by_cases h : i ∈ m.support
              · exact Or.inl h
              · exact Or.inr (by simpa [Finsupp.mem_support_iff] using h))]

/-- Flipping the `i`-th variable sends the monomial `m` to itself up to the sign
`(-1)^(m i)`. -/
private lemma bind₁_monomial_flip (i : Fin n) (m : Fin n →₀ ℕ) (c : ℝ) :
    MvPolynomial.bind₁ (fun j : Fin n => if j = i then -MvPolynomial.X j else MvPolynomial.X j)
        (MvPolynomial.monomial m c)
      = MvPolynomial.monomial m (c * (-1 : ℝ) ^ (m i)) := by
  classical
  rw [MvPolynomial.bind₁_monomial]
  rw [prod_flip_X_pow]
  rw [MvPolynomial.monomial_eq]
  rw [← mul_assoc, ← map_mul]
  rfl

/-- The coefficient functional commutes with the sign flip in the sense that
`coeff d (flip_i P) = (-1)^(d i) * coeff d P`. -/
private lemma coeff_bind₁_monomial_flip (i : Fin n) (m d : Fin n →₀ ℕ) (c : ℝ) :
    MvPolynomial.coeff d (MvPolynomial.bind₁
        (fun j : Fin n => if j = i then -MvPolynomial.X j else MvPolynomial.X j)
        (MvPolynomial.monomial m c))
      = (-1 : ℝ) ^ (d i) * MvPolynomial.coeff d (MvPolynomial.monomial m c) := by
  classical
  rw [bind₁_monomial_flip]
  rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases h : m = d
  · subst h
    simp [mul_comm]
  · simp [h]

/-- Flipping the sign of the `i`-th variable multiplies the `d`-th coefficient by
`(-1)^(d i)`. -/
private lemma coeff_bind₁_flip (i : Fin n) (P : MvPolynomial (Fin n) ℝ) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.bind₁
        (fun j : Fin n => if j = i then -MvPolynomial.X j else MvPolynomial.X j) P)
      = (-1 : ℝ) ^ (d i) * MvPolynomial.coeff d P := by
  classical
  calc
    MvPolynomial.coeff d (MvPolynomial.bind₁
        (fun j : Fin n => if j = i then -MvPolynomial.X j else MvPolynomial.X j) P)
        = MvPolynomial.coeff d (∑ m ∈ P.support, MvPolynomial.bind₁
            (fun j : Fin n => if j = i then -MvPolynomial.X j else MvPolynomial.X j)
            (MvPolynomial.monomial m (P.coeff m))) := by
            conv_lhs => rw [P.as_sum]
            rw [map_sum]
    _ = ∑ m ∈ P.support, MvPolynomial.coeff d (MvPolynomial.bind₁
            (fun j : Fin n => if j = i then -MvPolynomial.X j else MvPolynomial.X j)
            (MvPolynomial.monomial m (P.coeff m))) := by
            rw [MvPolynomial.coeff_sum]
    _ = ∑ m ∈ P.support, (-1 : ℝ) ^ (d i) * MvPolynomial.coeff d (MvPolynomial.monomial m (P.coeff m)) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [coeff_bind₁_monomial_flip]
    _ = (-1 : ℝ) ^ (d i) * ∑ m ∈ P.support, MvPolynomial.coeff d (MvPolynomial.monomial m (P.coeff m)) := by
            rw [Finset.mul_sum]
    _ = (-1 : ℝ) ^ (d i) * MvPolynomial.coeff d (∑ m ∈ P.support, MvPolynomial.monomial m (P.coeff m)) := by
            rw [← MvPolynomial.coeff_sum]
    _ = (-1 : ℝ) ^ (d i) * MvPolynomial.coeff d P := by
            rw [← P.as_sum]

/-- A polynomial fixed under flipping the sign of the `i`-th variable has vanishing
coefficients at every monomial with odd exponent in the `i`-th variable. -/
theorem coeff_odd_of_flip_invariant {n : ℕ} (i : Fin n)
    (P : MvPolynomial (Fin n) ℝ) (d : Fin n →₀ ℕ) (hodd : Odd (d i))
    (hflip : MvPolynomial.bind₁
        (fun j : Fin n => if j = i then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
          else MvPolynomial.X j) P = P) :
    P.coeff d = 0 := by
  classical
  have hc : P.coeff d = (-1 : ℝ) ^ (d i) * P.coeff d := by
    calc
      P.coeff d = MvPolynomial.coeff d (MvPolynomial.bind₁
          (fun j : Fin n => if j = i then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
            else MvPolynomial.X j) P) := by rw [hflip]
      _ = (-1 : ℝ) ^ (d i) * P.coeff d := coeff_bind₁_flip i P d
  have hpow : (-1 : ℝ) ^ (d i) = -1 := Odd.neg_one_pow hodd
  rw [hpow, neg_one_mul] at hc
  nlinarith

end

end Commons.Analysis.MvPolynomial