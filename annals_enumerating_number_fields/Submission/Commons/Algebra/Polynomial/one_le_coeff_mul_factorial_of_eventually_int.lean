import Mathlib.Algebra.Polynomial.Taylor
import Submission.Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg

namespace Commons.Algebra.Polynomial

noncomputable section

/-- The forward difference operator `P ↦ P(X+1) - P(X)`. -/
def fdiff (P : Polynomial ℚ) : Polynomial ℚ := Polynomial.taylor 1 P - P

lemma fdiff_eval (P : Polynomial ℚ) (x : ℚ) :
    (fdiff P).eval x = P.eval (x + 1) - P.eval x := by
  simp [fdiff, Polynomial.taylor_eval]

/-- For a polynomial of degree `≤ 1`, the value at `1` is the sum of the first two coefficients. -/
lemma eval_one_of_natDegree_le_one {q : Polynomial ℚ} (h : q.natDegree ≤ 1) :
    q.eval 1 = q.coeff 0 + q.coeff 1 := by
  have h2 : q.natDegree < 2 := by omega
  rw [Polynomial.eval_eq_sum_range' (p := q) (n := 2) h2 (1 : ℚ)]
  simp [Finset.sum_range_succ]

/-- The coefficient of `X^(m-1)` in the Taylor shift of `Q` at `1`. -/
lemma coeff_taylor_one_pred {Q : Polynomial ℚ} {m : ℕ} (hm : 1 ≤ m)
    (hQ : Q.natDegree ≤ m) :
    (Polynomial.taylor 1 Q).coeff (m - 1) = Q.coeff (m - 1) + (m : ℚ) * Q.coeff m := by
  rw [Polynomial.taylor_coeff]
  have hdeg : (Polynomial.hasseDeriv (m - 1) Q).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_hasseDeriv_le Q (m - 1)
    omega
  rw [eval_one_of_natDegree_le_one hdeg,
    Polynomial.hasseDeriv_coeff (k := m - 1) (f := Q) (n := 0),
    Polynomial.hasseDeriv_coeff (k := m - 1) (f := Q) (n := 1)]
  have hch : (m.choose (m - 1) : ℚ) = (m : ℚ) := by
    have h := Nat.choose_symm (show m - 1 ≤ m by omega)
    rw [show m - (m - 1) = 1 by omega, Nat.choose_one_right] at h
    exact_mod_cast h.symm
  rw [show 0 + (m - 1) = m - 1 by omega, show 1 + (m - 1) = m by omega,
    Nat.choose_self, Nat.cast_one, one_mul, hch]

/-- The coefficient of `X^m` in the Taylor shift of `Q` at `1`. -/
lemma coeff_taylor_one_self {Q : Polynomial ℚ} {m : ℕ} (hQ : Q.natDegree ≤ m) :
    (Polynomial.taylor 1 Q).coeff m = Q.coeff m := by
  rw [Polynomial.taylor_coeff]
  have hdeg : (Polynomial.hasseDeriv m Q).natDegree ≤ 0 := by
    have h := Polynomial.natDegree_hasseDeriv_le Q m
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero (le_antisymm hdeg (Nat.zero_le _)),
    Polynomial.eval_C, Polynomial.hasseDeriv_coeff (k := m) (f := Q) (n := 0)]
  simp

/-- The forward difference of a polynomial of degree `m ≠ 0` has degree `m - 1` and leading
coefficient `m` times the original leading coefficient. -/
lemma fdiff_natDegree_leadingCoeff {Q : Polynomial ℚ} (hm : Q.natDegree ≠ 0) :
    (fdiff Q).natDegree = Q.natDegree - 1 ∧
    (fdiff Q).leadingCoeff = (Q.natDegree : ℚ) * Q.leadingCoeff := by
  set m := Q.natDegree with hmdef
  have hm1 : 1 ≤ m := by omega
  have hcoeff : (fdiff Q).coeff (m - 1) = (m : ℚ) * Q.coeff m := by
    rw [fdiff, Polynomial.coeff_sub, coeff_taylor_one_pred hm1 (le_of_eq hmdef.symm)]
    ring
  have hcoeffm : (fdiff Q).coeff m = 0 := by
    rw [fdiff, Polynomial.coeff_sub, coeff_taylor_one_self (le_of_eq hmdef.symm)]
    ring
  have hQne : Q ≠ 0 := by
    intro h0
    exact hm (by rw [hmdef, h0, Polynomial.natDegree_zero])
  have hlc : Q.coeff m ≠ 0 := by
    rw [hmdef, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  have hne : (fdiff Q).coeff (m - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega)) hlc
  have hsub : (fdiff Q).natDegree ≤ m := by
    rw [fdiff]
    calc (Polynomial.taylor 1 Q - Q).natDegree
        ≤ max (Polynomial.taylor 1 Q).natDegree Q.natDegree := Polynomial.natDegree_sub_le _ _
      _ = max m m := by rw [Polynomial.natDegree_taylor, hmdef]
      _ = m := max_self m
  have hge : m - 1 ≤ (fdiff Q).natDegree := Polynomial.le_natDegree_of_ne_zero hne
  have hlt : (fdiff Q).natDegree < m := by
    rcases lt_or_eq_of_le hsub with h | h
    · exact h
    · exfalso
      have hfdne : fdiff Q ≠ 0 := fun h0 => hne (by rw [h0, Polynomial.coeff_zero])
      have : (fdiff Q).coeff m ≠ 0 := by
        rw [← h, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hfdne
      exact this hcoeffm
  have hnd : (fdiff Q).natDegree = m - 1 := by omega
  refine ⟨by rw [hnd, hmdef], ?_⟩
  rw [← Polynomial.coeff_natDegree, hnd, hcoeff, hmdef, Polynomial.coeff_natDegree]

/-- The forward difference of an eventually-integer-valued rational polynomial is again
eventually integer valued. -/
lemma fdiff_eventually_int {Q : Polynomial ℚ}
    (h : ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, Q.eval t = z) :
    ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, (fdiff Q).eval t = z := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨z1, h1⟩ := hN (t + 1) (by linarith)
  obtain ⟨z2, h2⟩ := hN t ht
  refine ⟨z1 - z2, ?_⟩
  rw [fdiff_eval, h1, h2]
  push_cast
  ring

/-- Any iterate of the forward difference of an eventually-integer-valued rational polynomial
is again eventually integer valued. -/
lemma fdiff_iterate_eventually_int (k : ℕ) {P : Polynomial ℚ}
    (h : ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, P.eval t = z) :
    ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, ((fdiff^[k]) P).eval t = z := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fdiff_eventually_int ih

/-- Iterating the forward difference: after `k` steps the degree has dropped by `k` and the
leading coefficient has been multiplied by the descending factorial `n.descFactorial k`. -/
lemma fdiff_iterate_natDegree_coeff (P : Polynomial ℚ) (k : ℕ) (hk : k ≤ P.natDegree) :
    ((fdiff^[k]) P).natDegree = P.natDegree - k ∧
    ((fdiff^[k]) P).coeff (P.natDegree - k) =
      ((P.natDegree.descFactorial k : ℕ) : ℚ) * P.coeff P.natDegree := by
  induction k with
  | zero => simp [Nat.descFactorial_zero]
  | succ k ih =>
    have hk' : k ≤ P.natDegree := by omega
    obtain ⟨hnd, hcoeff⟩ := ih hk'
    have hmne : ((fdiff^[k]) P).natDegree ≠ 0 := by rw [hnd]; omega
    obtain ⟨hdnd, hdlc⟩ := fdiff_natDegree_leadingCoeff (Q := (fdiff^[k]) P) hmne
    have hidx : P.natDegree - (k + 1) = P.natDegree - k - 1 := by omega
    constructor
    · rw [Function.iterate_succ_apply', hdnd, hnd]
      omega
    · have hlc2 : ((fdiff^[k]) P).leadingCoeff =
          ((P.natDegree.descFactorial k : ℕ) : ℚ) * P.coeff P.natDegree := by
        rw [← Polynomial.coeff_natDegree, hnd, hcoeff]
      rw [Function.iterate_succ_apply', hidx,
        show P.natDegree - k - 1 = (fdiff ((fdiff^[k]) P)).natDegree by rw [hdnd, hnd],
        Polynomial.coeff_natDegree, hdlc, hlc2, Nat.descFactorial_succ]
      rw [hnd]
      push_cast
      ring

theorem one_le_coeff_mul_factorial_of_eventually_int {P : Polynomial ℚ}
    (hpos : ∃ N, ∀ t ≥ N, 0 < P.eval (t : ℚ))
    (hint : ∃ N, ∀ t ≥ N, ∃ z : ℤ, P.eval (t : ℚ) = z) :
    1 ≤ P.coeff P.natDegree * P.natDegree.factorial := by
  have hPne : P ≠ 0 := by
    intro h0
    obtain ⟨N, hN⟩ := hpos
    have := hN N le_rfl
    rw [h0, Polynomial.eval_zero] at this
    exact lt_irrefl 0 this
  obtain ⟨hnd, hcoeff⟩ := fdiff_iterate_natDegree_coeff P P.natDegree le_rfl
  have hnd0 : ((fdiff^[P.natDegree]) P).natDegree = 0 := by
    rw [hnd, Nat.sub_self]
  have hconst : ((fdiff^[P.natDegree]) P) =
      Polynomial.C ((P.natDegree.factorial : ℚ) * P.coeff P.natDegree) := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnd0]
    congr 1
    have h := hcoeff
    rw [Nat.sub_self, Nat.descFactorial_self] at h
    exact h
  -- integrality of the top finite difference
  obtain ⟨N', hN'⟩ := fdiff_iterate_eventually_int P.natDegree hint
  obtain ⟨z, hz⟩ := hN' N' le_rfl
  rw [hconst, Polynomial.eval_C] at hz
  -- positivity of the leading coefficient
  have hnonneg : 0 ≤ P.coeff P.natDegree := by
    apply coeff_nonneg_of_eventually_eval_nonneg (f := P) (d := P.natDegree) le_rfl
    obtain ⟨N, hN⟩ := hpos
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge N
    refine ⟨N₀, fun n hn => ?_⟩
    have hcast : N ≤ (n : ℚ) := le_trans hN₀ (by exact_mod_cast hn)
    exact le_of_lt (hN (n : ℚ) hcast)
  have hane : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hapos : 0 < P.coeff P.natDegree := lt_of_le_of_ne hnonneg (Ne.symm hane)
  have hfacpos : (0 : ℚ) < (P.natDegree.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos P.natDegree
  have hqpos : 0 < (P.natDegree.factorial : ℚ) * P.coeff P.natDegree := mul_pos hfacpos hapos
  have hzpos : 0 < z := by
    have h := hqpos
    rw [hz] at h
    exact_mod_cast h
  have hgoal : (1 : ℚ) ≤ (P.natDegree.factorial : ℚ) * P.coeff P.natDegree := by
    rw [hz]
    exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  simpa [mul_comm] using hgoal

end

end Commons.Algebra.Polynomial