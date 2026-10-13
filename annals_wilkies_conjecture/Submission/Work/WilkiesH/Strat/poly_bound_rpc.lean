import Mathlib
import Submission.Work.WilG5.Basic

namespace Work.WilkiesH.Strat

/-- **Two-variable evaluation bound.**  For a natural two-variable polynomial, the value at
`![t, s]` is bounded by the value at `![1, 1]` times the powers of `t + 1` and `s + 1` whose
exponents are the sums of the respective exponents over the support. -/
theorem mv_eval_le_one_one (p : MvPolynomial (Fin 2) ℕ) (t s : ℕ) :
    MvPolynomial.eval ![t, s] p ≤ MvPolynomial.eval ![1, 1] p *
      (t + 1) ^ (∑ m ∈ p.support, m 0) * (s + 1) ^ (∑ m ∈ p.support, m 1) := by
  have h1 : MvPolynomial.eval ![t, s] p
      = ∑ m ∈ p.support, p.coeff m * (t ^ m 0 * s ^ m 1) := by
    rw [MvPolynomial.eval_eq']
    exact Finset.sum_congr rfl fun m _ => by
      simp [Fin.prod_univ_two]
  have h2 : MvPolynomial.eval ![1, 1] p = ∑ m ∈ p.support, p.coeff m := by
    rw [MvPolynomial.eval_eq']
    exact Finset.sum_congr rfl fun m _ => by
      simp [Fin.prod_univ_two]
  rw [h1, h2, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  have h3 : m 0 ≤ ∑ m' ∈ p.support, m' 0 :=
    Finset.single_le_sum (f := fun m' : Fin 2 →₀ ℕ => m' 0) (fun _ _ => Nat.zero_le _) hm
  have h4 : m 1 ≤ ∑ m' ∈ p.support, m' 1 :=
    Finset.single_le_sum (f := fun m' : Fin 2 →₀ ℕ => m' 1) (fun _ _ => Nat.zero_le _) hm
  have h5 : t ^ m 0 ≤ (t + 1) ^ (∑ m' ∈ p.support, m' 0) :=
    le_trans (Nat.pow_le_pow_left (Nat.le_succ t) (m 0)) (Nat.pow_le_pow_right (by omega) h3)
  have h6 : s ^ m 1 ≤ (s + 1) ^ (∑ m' ∈ p.support, m' 1) :=
    le_trans (Nat.pow_le_pow_left (Nat.le_succ s) (m 1)) (Nat.pow_le_pow_right (by omega) h4)
  calc p.coeff m * (t ^ m 0 * s ^ m 1)
      ≤ p.coeff m * ((t + 1) ^ (∑ m' ∈ p.support, m' 0) * (s + 1) ^ (∑ m' ∈ p.support, m' 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h5 h6)
    _ = p.coeff m * (t + 1) ^ (∑ m' ∈ p.support, m' 0) *
          (s + 1) ^ (∑ m' ∈ p.support, m' 1) := by ring

/-- **Univariate evaluation bound.**  `c.eval t ≤ c.eval 1 · (t + 1) ^ c.natDegree`. -/
theorem poly_eval_le_eval_one_rpc (c : Polynomial ℕ) (t : ℕ) :
    c.eval t ≤ c.eval 1 * (t + 1) ^ c.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  conv_rhs => rw [Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) (le_of_eq (Finset.sum_mul ..).symm)
  refine Nat.mul_le_mul_left _ ?_
  have hi' : i ≤ c.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  exact le_trans (Nat.pow_le_pow_left (Nat.le_succ t) i)
    (Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) hi')

/-- **The bookkeeping lemma of the regular-part cover.**  There is a fixed two-variable
polynomial `pm` which dominates, at `![D, n + 1]`, both `D` and the degree index
`b(D,1) · (4 + c(D) + q(c(D) + D, n + 1))` of the union of the pieces used in
`Work.WilkiesH.Strat.regular_part_cover`. -/
theorem poly_bound_rpc (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) (q : MvPolynomial (Fin 2) ℕ)
    (n : ℕ) :
    ∃ pm : MvPolynomial (Fin 2) ℕ, ∀ D : ℕ,
      D ≤ MvPolynomial.eval ![D, n + 1] pm ∧
      MvPolynomial.eval ![D, 1] b * (4 + Polynomial.eval D c +
        MvPolynomial.eval ![Polynomial.eval D c + D, n + 1] q) ≤
        MvPolynomial.eval ![D, n + 1] pm := by
  classical
  set B : ℕ := MvPolynomial.eval ![1, 1] b with hB
  set eb : ℕ := ∑ m ∈ b.support, m 0 with heb
  set Cc : ℕ := c.eval 1 with hC
  set dc : ℕ := c.natDegree with hdc
  set Q : ℕ := MvPolynomial.eval ![1, 1] q with hQ
  set e0 : ℕ := ∑ m ∈ q.support, m 0 with he0
  set e1 : ℕ := ∑ m ∈ q.support, m 1 with he1
  set M : ℕ := max dc 1 with hM
  set Mp : ℕ := max (max dc (M * e0)) 1 with hMp
  set eb1 : ℕ := ∑ m ∈ b.support, m 1 with heb1
  set E : ℕ := eb + Mp with hE
  set K : ℕ := B * 2 ^ eb1 * (4 + Cc + Q * (Cc + 1) ^ e0) with hK
  refine ⟨MvPolynomial.X 0 + MvPolynomial.C K * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ E *
      (MvPolynomial.X 1 + MvPolynomial.C 1) ^ e1, fun D => ?_⟩
  have hX0 : MvPolynomial.eval ![D, n + 1] (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) = D := by
    simp
  have hX1 : MvPolynomial.eval ![D, n + 1] (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℕ) = n + 1 := by
    simp
  have hpow0 : MvPolynomial.eval ![D, n + 1]
      ((MvPolynomial.X 0 + MvPolynomial.C 1 : MvPolynomial (Fin 2) ℕ) ^ E) = (D + 1) ^ E := by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_add, hX0, MvPolynomial.eval_C]
  have hpow1 : MvPolynomial.eval ![D, n + 1]
      ((MvPolynomial.X 1 + MvPolynomial.C 1 : MvPolynomial (Fin 2) ℕ) ^ e1) = (n + 2) ^ e1 := by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_add, hX1, MvPolynomial.eval_C]
  have hCst : MvPolynomial.eval ![D, n + 1] (MvPolynomial.C K : MvPolynomial (Fin 2) ℕ) = K :=
    MvPolynomial.eval_C K
  have hval : MvPolynomial.eval ![D, n + 1]
      (MvPolynomial.X 0 + MvPolynomial.C K * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ E *
        (MvPolynomial.X 1 + MvPolynomial.C 1) ^ e1) = D + K * (D + 1) ^ E * (n + 2) ^ e1 := by
    rw [MvPolynomial.eval_add, hX0, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hCst,
      hpow0, hpow1]
  rw [hval]
  constructor
  · omega
  · have hb : MvPolynomial.eval ![D, 1] b ≤ B * (D + 1) ^ eb * 2 ^ eb1 := by
      have h := mv_eval_le_one_one b D 1
      rw [← hB, ← heb, ← heb1] at h
      simpa using h
    have hc : c.eval D ≤ Cc * (D + 1) ^ dc := by
      have h := poly_eval_le_eval_one_rpc c D
      rw [← hC, ← hdc] at h
      exact h
    have hD1 : D + 1 ≤ (D + 1) ^ M := by
      calc D + 1 = (D + 1) ^ 1 := (pow_one _).symm
        _ ≤ (D + 1) ^ M := Nat.pow_le_pow_right (by omega) (by rw [hM]; exact le_max_right _ _)
    have hdcM : (D + 1) ^ dc ≤ (D + 1) ^ M :=
      Nat.pow_le_pow_right (by omega) (by rw [hM]; exact le_max_left _ _)
    have hsum : c.eval D + (D + 1) ≤ (Cc + 1) * (D + 1) ^ M := by
      have h1 : c.eval D ≤ Cc * (D + 1) ^ M := le_trans hc (Nat.mul_le_mul_left _ hdcM)
      have h2 : Cc * (D + 1) ^ M + (D + 1) ^ M = (Cc + 1) * (D + 1) ^ M := by ring
      calc c.eval D + (D + 1) ≤ Cc * (D + 1) ^ M + (D + 1) ^ M := add_le_add h1 hD1
        _ = (Cc + 1) * (D + 1) ^ M := h2
    have hM0 : M * e0 ≤ Mp := by rw [hMp]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hdcp : dc ≤ Mp := by rw [hMp]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hq : MvPolynomial.eval ![c.eval D + D, n + 1] q ≤
        Q * (Cc + 1) ^ e0 * (D + 1) ^ Mp * (n + 2) ^ e1 := by
      have h := mv_eval_le_one_one q (c.eval D + D) (n + 1)
      rw [← hQ, ← he0, ← he1] at h
      have h2 : (c.eval D + D + 1) ^ e0 ≤ ((Cc + 1) * (D + 1) ^ M) ^ e0 := by
        refine Nat.pow_le_pow_left ?_ e0
        calc c.eval D + D + 1 = c.eval D + (D + 1) := by omega
          _ ≤ (Cc + 1) * (D + 1) ^ M := hsum
      have h3 : ((Cc + 1) * (D + 1) ^ M) ^ e0 = (Cc + 1) ^ e0 * (D + 1) ^ (M * e0) := by
        rw [mul_pow, ← pow_mul]
      have h4 : (D + 1) ^ (M * e0) ≤ (D + 1) ^ Mp :=
        Nat.pow_le_pow_right (by omega) hM0
      calc MvPolynomial.eval ![c.eval D + D, n + 1] q
          ≤ Q * (c.eval D + D + 1) ^ e0 * (n + 1 + 1) ^ e1 := h
        _ ≤ Q * ((Cc + 1) ^ e0 * (D + 1) ^ (M * e0)) * (n + 1 + 1) ^ e1 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_trans h2 (le_of_eq h3)))
        _ ≤ Q * ((Cc + 1) ^ e0 * (D + 1) ^ Mp) * (n + 2) ^ e1 := by
              rw [show n + 1 + 1 = n + 2 from rfl]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4))
        _ = Q * (Cc + 1) ^ e0 * (D + 1) ^ Mp * (n + 2) ^ e1 := by ring
    have hn1 : 1 ≤ (n + 2) ^ e1 := Nat.one_le_pow _ _ (by omega)
    have hbr : 4 + Polynomial.eval D c + MvPolynomial.eval ![Polynomial.eval D c + D, n + 1] q
        ≤ (4 + Cc + Q * (Cc + 1) ^ e0) * (D + 1) ^ Mp * (n + 2) ^ e1 := by
      have h4 : 4 ≤ 4 * (D + 1) ^ Mp * (n + 2) ^ e1 := by
        calc (4 : ℕ) = 4 * 1 * 1 := by ring
          _ ≤ 4 * (D + 1) ^ Mp * (n + 2) ^ e1 :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))) hn1
      have h5 : c.eval D ≤ Cc * (D + 1) ^ Mp * (n + 2) ^ e1 := by
        refine le_trans hc ?_
        calc Cc * (D + 1) ^ dc ≤ Cc * (D + 1) ^ Mp :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdcp)
          _ = Cc * (D + 1) ^ Mp * 1 := (mul_one _).symm
          _ ≤ Cc * (D + 1) ^ Mp * (n + 2) ^ e1 := Nat.mul_le_mul_left _ hn1
      calc 4 + Polynomial.eval D c + MvPolynomial.eval ![Polynomial.eval D c + D, n + 1] q
          ≤ 4 * (D + 1) ^ Mp * (n + 2) ^ e1 + Cc * (D + 1) ^ Mp * (n + 2) ^ e1
            + Q * (Cc + 1) ^ e0 * (D + 1) ^ Mp * (n + 2) ^ e1 :=
            add_le_add (add_le_add h4 h5) hq
        _ = (4 + Cc + Q * (Cc + 1) ^ e0) * (D + 1) ^ Mp * (n + 2) ^ e1 := by ring
    have hfin : MvPolynomial.eval ![D, 1] b * (4 + Polynomial.eval D c +
        MvPolynomial.eval ![Polynomial.eval D c + D, n + 1] q)
        ≤ K * (D + 1) ^ E * (n + 2) ^ e1 := by
      have hpow : (D + 1) ^ eb * (D + 1) ^ Mp = (D + 1) ^ E := by
        rw [← pow_add, hE]
      calc MvPolynomial.eval ![D, 1] b * (4 + Polynomial.eval D c +
            MvPolynomial.eval ![Polynomial.eval D c + D, n + 1] q)
          ≤ (B * (D + 1) ^ eb * 2 ^ eb1) * ((4 + Cc + Q * (Cc + 1) ^ e0) * (D + 1) ^ Mp *
              (n + 2) ^ e1) := Nat.mul_le_mul hb hbr
        _ = B * 2 ^ eb1 * (4 + Cc + Q * (Cc + 1) ^ e0) *
              ((D + 1) ^ eb * (D + 1) ^ Mp) * (n + 2) ^ e1 := by ring
        _ = K * (D + 1) ^ E * (n + 2) ^ e1 := by rw [← hK, hpow]
    calc MvPolynomial.eval ![D, 1] b * (4 + Polynomial.eval D c +
          MvPolynomial.eval ![Polynomial.eval D c + D, n + 1] q)
        ≤ K * (D + 1) ^ E * (n + 2) ^ e1 := hfin
      _ ≤ D + K * (D + 1) ^ E * (n + 2) ^ e1 := Nat.le_add_left _ _

end Work.WilkiesH.Strat
