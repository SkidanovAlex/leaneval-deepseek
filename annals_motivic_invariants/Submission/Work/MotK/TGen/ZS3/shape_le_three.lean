import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZS3

/-! ### Elementary shape lemmas for polynomials of small total degree -/

/-- `finSuccEquiv` sends a constant to the corresponding constant. -/
private theorem finSuccEquiv_C' {L : Type*} [CommSemiring L] (n : ℕ) (r : L) :
    MvPolynomial.finSuccEquiv L n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rfl

/-- A univariate polynomial of total degree at most `d` is the sum of its `d+1` lowest
homogeneous components, written in terms of its coefficients. -/
private theorem univ_shape {L : Type*} [CommSemiring L] (c : MvPolynomial (Fin 1) L) (d : ℕ)
    (h : c.totalDegree ≤ d) :
    c = ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (c.coeff (Finsupp.single 0 k)) * (MvPolynomial.X 0) ^ k := by
  have hm : ∀ m : Fin 1 →₀ ℕ, m = Finsupp.single (0 : Fin 1) (m 0) := by
    intro m
    exact Finsupp.ext (fun j => by fin_cases j; simp)
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  rw [hm m]
  simp only [(Finsupp.single_injective (0 : Fin 1)).eq_iff]
  rw [Finset.sum_ite_eq']
  by_cases hk : m 0 ∈ Finset.range (d + 1)
  · simp only [if_pos hk]
  · simp only [if_neg hk]
    by_contra hne
    have hmem : Finsupp.single (0 : Fin 1) (m 0) ∈ c.support := by
      rwa [MvPolynomial.mem_support_iff]
    have h1 : (Finsupp.single (0 : Fin 1) (m 0)) (0 : Fin 1) ≤ c.degreeOf 0 :=
      (MvPolynomial.degreeOf_le_iff (n := (0 : Fin 1)) (f := c) (d := c.degreeOf 0)).mp
        (le_refl _) _ hmem
    rw [Finsupp.single_eq_same] at h1
    have h2 : c.degreeOf 0 ≤ c.totalDegree := MvPolynomial.degreeOf_le_totalDegree c 0
    have hk' : ¬ (m 0 < d + 1) := by simpa [Finset.mem_range] using hk
    omega

/-- Univariate `MvPolynomial`s of total degree at most `3`. -/
private theorem fin1_shape_le_three {L : Type*} [CommSemiring L] (c : MvPolynomial (Fin 1) L)
    (h : c.totalDegree ≤ 3) :
    c = MvPolynomial.C (c.coeff (Finsupp.single 0 3)) * (MvPolynomial.X 0) ^ 3
      + MvPolynomial.C (c.coeff (Finsupp.single 0 2)) * (MvPolynomial.X 0) ^ 2
      + MvPolynomial.C (c.coeff (Finsupp.single 0 1)) * MvPolynomial.X 0
      + MvPolynomial.C (c.coeff 0) := by
  have hgen := univ_shape c 3 h
  conv_lhs => rw [hgen]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_one, pow_zero, mul_one, Finsupp.single_zero]
  first | refl_ring1 | ring

/-- Univariate `MvPolynomial`s of total degree at most `2`. -/
private theorem fin1_shape_le_two {L : Type*} [CommSemiring L] (c : MvPolynomial (Fin 1) L)
    (h : c.totalDegree ≤ 2) :
    c = MvPolynomial.C (c.coeff (Finsupp.single 0 2)) * (MvPolynomial.X 0) ^ 2
      + MvPolynomial.C (c.coeff (Finsupp.single 0 1)) * MvPolynomial.X 0
      + MvPolynomial.C (c.coeff 0) := by
  have hgen := univ_shape c 2 h
  conv_lhs => rw [hgen]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_one, pow_zero, mul_one, Finsupp.single_zero]
  first | refl_ring1 | ring

/-- Univariate `MvPolynomial`s of total degree at most `1`. -/
private theorem fin1_shape_le_one {L : Type*} [CommSemiring L] (c : MvPolynomial (Fin 1) L)
    (h : c.totalDegree ≤ 1) :
    c = MvPolynomial.C (c.coeff (Finsupp.single 0 1)) * MvPolynomial.X 0
      + MvPolynomial.C (c.coeff 0) := by
  have hgen := univ_shape c 1 h
  conv_lhs => rw [hgen]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_one, pow_zero, mul_one, Finsupp.single_zero]
  first | refl_ring1 | ring

/-- A polynomial of `natDegree ≤ 3` written in terms of its four lowest coefficients. -/
private theorem poly_coeff_shape_three {M : Type*} [Semiring M] (Q : Polynomial M)
    (h : Q.natDegree ≤ 3) :
    Q = Polynomial.C (Q.coeff 3) * Polynomial.X ^ 3
      + Polynomial.C (Q.coeff 2) * Polynomial.X ^ 2
      + Polynomial.C (Q.coeff 1) * Polynomial.X ^ 1
      + Polynomial.C (Q.coeff 0) := by
  rw [Polynomial.ext_iff]
  intro n
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C]
  rcases lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp
  · have h0 : Q.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have e1 : ¬ (n = 3) := by omega
    have e2 : ¬ (n = 2) := by omega
    have e3 : ¬ (n = 1) := by omega
    have e4 : ¬ (n = 0) := by omega
    simp [h0, e1, e2, e3, e4]

/-- The image of the explicit cubic shape under `finSuccEquiv`. -/
private theorem finSucc_cubic {L : Type*} [CommSemiring L]
    (a b1 b0 c2 c1 c0 d3 d2 d1 d0 : L) :
    MvPolynomial.finSuccEquiv L 1
        (MvPolynomial.C a * (MvPolynomial.X 0) ^ 3
          + (MvPolynomial.C b1 * MvPolynomial.X 1 + MvPolynomial.C b0) * (MvPolynomial.X 0) ^ 2
          + (MvPolynomial.C c2 * (MvPolynomial.X 1) ^ 2 + MvPolynomial.C c1 * MvPolynomial.X 1
              + MvPolynomial.C c0) * MvPolynomial.X 0
          + (MvPolynomial.C d3 * (MvPolynomial.X 1) ^ 3 + MvPolynomial.C d2 * (MvPolynomial.X 1) ^ 2
              + MvPolynomial.C d1 * MvPolynomial.X 1 + MvPolynomial.C d0))
      = Polynomial.C (MvPolynomial.C a) * Polynomial.X ^ 3
          + Polynomial.C (MvPolynomial.C b1 * MvPolynomial.X 0 + MvPolynomial.C b0) * Polynomial.X ^ 2
          + Polynomial.C (MvPolynomial.C c2 * (MvPolynomial.X 0) ^ 2
              + MvPolynomial.C c1 * MvPolynomial.X 0 + MvPolynomial.C c0) * Polynomial.X
          + Polynomial.C (MvPolynomial.C d3 * (MvPolynomial.X 0) ^ 3
              + MvPolynomial.C d2 * (MvPolynomial.X 0) ^ 2
              + MvPolynomial.C d1 * MvPolynomial.X 0 + MvPolynomial.C d0) := by
  simp only [map_add, map_mul, map_pow, finSuccEquiv_C', MvPolynomial.finSuccEquiv_X_zero]
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem shape_le_three {L : Type} [Field L] (p : MvPolynomial (Fin 2) L)
    (h : p.totalDegree ≤ 3) (hd : p.degreeOf 0 ≤ 3) :
    ∃ a b1 b0 c2 c1 c0 d3 d2 d1 d0 : L,
      p = MvPolynomial.C a * (MvPolynomial.X 0) ^ 3
          + (MvPolynomial.C b1 * MvPolynomial.X 1 + MvPolynomial.C b0) * (MvPolynomial.X 0) ^ 2
          + (MvPolynomial.C c2 * (MvPolynomial.X 1) ^ 2 + MvPolynomial.C c1 * MvPolynomial.X 1
              + MvPolynomial.C c0) * MvPolynomial.X 0
          + (MvPolynomial.C d3 * (MvPolynomial.X 1) ^ 3 + MvPolynomial.C d2 * (MvPolynomial.X 1) ^ 2
              + MvPolynomial.C d1 * MvPolynomial.X 1 + MvPolynomial.C d0) := by
  set P := MvPolynomial.finSuccEquiv L 1 p with hP
  have hPnat : P.natDegree ≤ 3 := by
    rw [hP, MvPolynomial.natDegree_finSuccEquiv]
    exact hd
  have hPshape : P = Polynomial.C (P.coeff 3) * Polynomial.X ^ 3
      + Polynomial.C (P.coeff 2) * Polynomial.X ^ 2
      + Polynomial.C (P.coeff 1) * Polynomial.X ^ 1
      + Polynomial.C (P.coeff 0) := poly_coeff_shape_three P hPnat
  have hc3 : (P.coeff 3).totalDegree ≤ 0 := by
    by_cases hz : P.coeff 3 = 0
    · simp [hz, MvPolynomial.totalDegree_zero]
    · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := L) (n := 1) p 3
        (by rwa [hP] at hz)
      rw [← hP] at hle
      omega
  have hc2 : (P.coeff 2).totalDegree ≤ 1 := by
    by_cases hz : P.coeff 2 = 0
    · simp [hz, MvPolynomial.totalDegree_zero]
    · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := L) (n := 1) p 2
        (by rwa [hP] at hz)
      rw [← hP] at hle
      omega
  have hc1 : (P.coeff 1).totalDegree ≤ 2 := by
    by_cases hz : P.coeff 1 = 0
    · simp [hz, MvPolynomial.totalDegree_zero]
    · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := L) (n := 1) p 1
        (by rwa [hP] at hz)
      rw [← hP] at hle
      omega
  have hc0 : (P.coeff 0).totalDegree ≤ 3 := by
    by_cases hz : P.coeff 0 = 0
    · simp [hz, MvPolynomial.totalDegree_zero]
    · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := L) (n := 1) p 0
        (by rwa [hP] at hz)
      rw [← hP] at hle
      omega
  obtain ⟨a, ha⟩ : ∃ a : L, P.coeff 3 = MvPolynomial.C a :=
    ⟨(P.coeff 3).coeff 0,
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := P.coeff 3)).mp (by omega)⟩
  obtain ⟨b1, b0, hb⟩ : ∃ b1 b0 : L,
      P.coeff 2 = MvPolynomial.C b1 * MvPolynomial.X 0 + MvPolynomial.C b0 :=
    ⟨(P.coeff 2).coeff (Finsupp.single 0 1), (P.coeff 2).coeff 0,
      fin1_shape_le_one (P.coeff 2) hc2⟩
  obtain ⟨c2, c1, c0, hc⟩ : ∃ c2 c1 c0 : L,
      P.coeff 1 = MvPolynomial.C c2 * (MvPolynomial.X 0) ^ 2 + MvPolynomial.C c1 * MvPolynomial.X 0
        + MvPolynomial.C c0 :=
    ⟨(P.coeff 1).coeff (Finsupp.single 0 2), (P.coeff 1).coeff (Finsupp.single 0 1),
      (P.coeff 1).coeff 0, fin1_shape_le_two (P.coeff 1) hc1⟩
  obtain ⟨d3, d2, d1, d0, hdsh⟩ : ∃ d3 d2 d1 d0 : L,
      P.coeff 0 = MvPolynomial.C d3 * (MvPolynomial.X 0) ^ 3
        + MvPolynomial.C d2 * (MvPolynomial.X 0) ^ 2
        + MvPolynomial.C d1 * MvPolynomial.X 0 + MvPolynomial.C d0 :=
    ⟨(P.coeff 0).coeff (Finsupp.single 0 3), (P.coeff 0).coeff (Finsupp.single 0 2),
      (P.coeff 0).coeff (Finsupp.single 0 1), (P.coeff 0).coeff 0,
      fin1_shape_le_three (P.coeff 0) hc0⟩
  refine ⟨a, b1, b0, c2, c1, c0, d3, d2, d1, d0, ?_⟩
  apply (MvPolynomial.finSuccEquiv L 1).injective
  rw [← hP, hPshape, finSucc_cubic, ha, hb, hc, hdsh]
  first | refl_ring1 | ring

end Work.MotK.TGen.ZS3
