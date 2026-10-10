import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZS2

open MvPolynomial

/-- The monomial `X_0 ^ i * X_1 ^ j` of `L[X_0, X_1]`, as an exponent vector. -/
noncomputable def mon (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j

@[simp] theorem mon_apply_zero (i j : ℕ) : mon i j 0 = i := by simp [mon]
@[simp] theorem mon_apply_one (i j : ℕ) : mon i j 1 = j := by simp [mon]

@[simp] theorem mon_inj {i j i' j' : ℕ} : mon i j = mon i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h,
           by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem mon_zero_right (i : ℕ) : mon i 0 = Finsupp.single (0 : Fin 2) i := by
  ext k; fin_cases k <;> simp [mon]

theorem mon_zero_left (j : ℕ) : mon 0 j = Finsupp.single (1 : Fin 2) j := by
  ext k; fin_cases k <;> simp [mon]

theorem mon_zero_zero : mon (0 : ℕ) 0 = 0 := by
  ext k; fin_cases k <;> simp [mon]

/-- The six monomials of total degree at most two in two variables. -/
noncomputable def six : Finset (Fin 2 →₀ ℕ) :=
  {mon 2 0, mon 1 1, mon 1 0, mon 0 2, mon 0 1, mon 0 0}

theorem mem_six_iff {v : Fin 2 →₀ ℕ} :
    v ∈ six ↔
      v = mon 2 0 ∨ v = mon 1 1 ∨ v = mon 1 0 ∨ v = mon 0 2 ∨ v = mon 0 1 ∨ v = mon 0 0 := by
  simp only [six, Finset.mem_insert, Finset.mem_singleton]

theorem mem_six_of_sum_le_two {m : Fin 2 →₀ ℕ} (h : m.sum (fun _ e => e) ≤ 2) : m ∈ six := by
  have hm : m = mon (m 0) (m 1) := by
    ext i; fin_cases i <;> simp [mon]
  have hsum : m.sum (fun _ e => e) = m 0 + m 1 := by
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_two]
    · intro i; rfl
  have hab : m 0 + m 1 ≤ 2 := by rw [← hsum]; exact h
  rw [hm, mem_six_iff]
  simp only [mon_inj]
  omega

/-- A polynomial of total degree at most two is the sum of its coefficients times the six
monomials of degree at most two. -/
theorem as_sum_six {L : Type} [CommSemiring L] (p : MvPolynomial (Fin 2) L)
    (h : p.totalDegree ≤ 2) : p = ∑ v ∈ six, monomial v (p.coeff v) := by
  calc p = ∑ v ∈ p.support, monomial v (p.coeff v) := MvPolynomial.as_sum p
    _ = ∑ v ∈ six, monomial v (p.coeff v) := by
      apply Finset.sum_subset
      · intro v hv
        exact mem_six_of_sum_le_two (le_trans (le_totalDegree hv) h)
      · intro x _ hxs
        have hc : p.coeff x = 0 := by
          by_contra hne
          exact hxs (MvPolynomial.mem_support_iff.mpr hne)
        rw [hc]
        exact map_zero _

theorem sum_six_eq {L : Type} [CommSemiring L] (p : MvPolynomial (Fin 2) L) :
    (∑ v ∈ six, monomial v (p.coeff v))
    = monomial (mon 2 0) (p.coeff (mon 2 0))
      + monomial (mon 1 1) (p.coeff (mon 1 1))
      + monomial (mon 1 0) (p.coeff (mon 1 0))
      + monomial (mon 0 2) (p.coeff (mon 0 2))
      + monomial (mon 0 1) (p.coeff (mon 0 1))
      + monomial (mon 0 0) (p.coeff (mon 0 0)) := by
  rw [show six = ({(mon 2 0), (mon 1 1), (mon 1 0), (mon 0 2), (mon 0 1),
      (mon 0 0)} : Finset (Fin 2 →₀ ℕ)) from rfl]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_singleton]
  all_goals first | ac_rfl | simp

theorem monomial_mon_20 {L : Type} [CommSemiring L] (c : L) :
    (monomial (mon 2 0) c : MvPolynomial (Fin 2) L) = C c * X 0 ^ 2 := by
  rw [mon_zero_right, X_pow_eq_monomial, C_mul_monomial, mul_one]

theorem monomial_mon_11 {L : Type} [CommSemiring L] (c : L) :
    (monomial (mon 1 1) c : MvPolynomial (Fin 2) L) = C c * X 1 * X 0 := by
  rw [← pow_one (X 1), ← pow_one (X 0), X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial,
    monomial_mul_monomial, add_comm, mul_one, mul_one]
  rfl

theorem monomial_mon_10 {L : Type} [CommSemiring L] (c : L) :
    (monomial (mon 1 0) c : MvPolynomial (Fin 2) L) = C c * X 0 := by
  rw [mon_zero_right, ← pow_one (X 0), X_pow_eq_monomial, C_mul_monomial, mul_one]

theorem monomial_mon_02 {L : Type} [CommSemiring L] (c : L) :
    (monomial (mon 0 2) c : MvPolynomial (Fin 2) L) = C c * X 1 ^ 2 := by
  rw [mon_zero_left, X_pow_eq_monomial, C_mul_monomial, mul_one]

theorem monomial_mon_01 {L : Type} [CommSemiring L] (c : L) :
    (monomial (mon 0 1) c : MvPolynomial (Fin 2) L) = C c * X 1 := by
  rw [mon_zero_left, ← pow_one (X 1), X_pow_eq_monomial, C_mul_monomial, mul_one]

theorem monomial_mon_00 {L : Type} [CommSemiring L] (c : L) :
    (monomial (mon 0 0) c : MvPolynomial (Fin 2) L) = C c := by
  rw [mon_zero_zero, monomial_eq, Finsupp.prod_zero_index, mul_one]

theorem shape_le_two {L : Type} [Field L] (p : MvPolynomial (Fin 2) L)
    (h : p.totalDegree ≤ 2) (hd : p.degreeOf 0 ≤ 2) :
    ∃ a b1 b0 c2 c1 c0 : L,
      p = MvPolynomial.C a * (MvPolynomial.X 0) ^ 2
          + (MvPolynomial.C b1 * MvPolynomial.X 1 + MvPolynomial.C b0) * MvPolynomial.X 0
          + (MvPolynomial.C c2 * (MvPolynomial.X 1) ^ 2 + MvPolynomial.C c1 * MvPolynomial.X 1
              + MvPolynomial.C c0) := by
  refine ⟨p.coeff (mon 2 0), p.coeff (mon 1 1), p.coeff (mon 1 0), p.coeff (mon 0 2),
    p.coeff (mon 0 1), p.coeff (mon 0 0), ?_⟩
  conv_lhs => rw [as_sum_six p h, sum_six_eq p]
  rw [add_mul, monomial_mon_20, monomial_mon_11, monomial_mon_10, monomial_mon_02,
    monomial_mon_01, monomial_mon_00]
  ac_rfl

end Work.MotK.TGen.ZS2
