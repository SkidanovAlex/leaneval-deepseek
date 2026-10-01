import Mathlib

namespace Work.LinnikBurgess

/-- The coefficient of the polynomial obtained by dividing every coefficient of `Q` by `c`. -/
lemma coeff_sum_div (Q : Polynomial ℤ) (c : ℤ) (m : ℕ) :
    (Q.sum (fun n a => Polynomial.C (a / c) * Polynomial.X ^ n)).coeff m = Q.coeff m / c := by
  rw [Polynomial.coeff_sum, Polynomial.sum_def]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · rw [Polynomial.notMem_support_iff.mp hm, Int.zero_ediv]

/-- `p ^ (J+1)` cast to `ℤ` equals `(p^J) * p`. -/
lemma pow_succ_cast_int (p J : ℕ) :
    ((p ^ (J + 1) : ℕ) : ℤ) = ((p ^ J : ℕ) : ℤ) * (p : ℤ) := by
  rw [pow_succ]
  push_cast
  ring

theorem capContent_divPoly (p J : ℕ) (Q : Polynomial ℤ)
    (h : ∀ n, ((p ^ J : ℕ) : ℤ) ∣ Q.coeff n) :
    ∃ Q' : Polynomial ℤ,
      Polynomial.C (((p ^ J : ℕ) : ℤ)) * Q' = Q ∧
      (∀ n, Q'.coeff n = Q.coeff n / (((p ^ J : ℕ) : ℤ))) ∧
      (Q' = 0 ↔ Q = 0) ∧
      Q'.natDegree = Q.natDegree ∧
      (Q'.map (Int.castRingHom (ZMod p)) = 0 ↔ ∀ n, ((p ^ (J + 1) : ℕ) : ℤ) ∣ Q.coeff n) := by
  set c : ℤ := ((p ^ J : ℕ) : ℤ) with hc
  let Q' : Polynomial ℤ := Q.sum (fun n a => Polynomial.C (a / c) * Polynomial.X ^ n)
  have hcoeff : ∀ n, Q'.coeff n = Q.coeff n / c := fun n => coeff_sum_div Q c n
  have h1 : Polynomial.C c * Q' = Q := by
    apply Polynomial.ext
    intro m
    rw [Polynomial.coeff_C_mul, hcoeff m]
    exact Int.mul_ediv_cancel' (h m)
  have hcast : ((p ^ (J + 1) : ℕ) : ℤ) = c * (p : ℤ) := by
    rw [hc]; exact pow_succ_cast_int p J
  refine ⟨Q', h1, hcoeff, ?_, ?_, ?_⟩
  · constructor
    · intro hQ'; rw [← h1, hQ', mul_zero]
    · intro hQ
      apply Polynomial.ext
      intro n
      rw [hcoeff n, hQ, Polynomial.coeff_zero]
      exact Int.zero_ediv c
  · apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hcoeff N, (Polynomial.natDegree_le_iff_coeff_eq_zero.mp le_rfl N hN), Int.zero_ediv]
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [← h1, Polynomial.coeff_C_mul,
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mp le_rfl N hN), mul_zero]
  · rw [hcast]
    have hmap : Q'.map (Int.castRingHom (ZMod p)) = 0 ↔ ∀ n, (p : ℤ) ∣ Q'.coeff n := by
      constructor
      · intro hz n
        have hcn := congrArg (fun P : Polynomial (ZMod p) => P.coeff n) hz
        rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hcn
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Q'.coeff n) p).mp hcn
      · intro hn
        apply Polynomial.ext
        intro n
        rw [Polynomial.coeff_map, Polynomial.coeff_zero]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Q'.coeff n) p).mpr (hn n)
    rw [hmap]
    constructor
    · intro hp n
      have heq : Q.coeff n = c * Q'.coeff n := by rw [← h1, Polynomial.coeff_C_mul]
      rw [heq]
      exact mul_dvd_mul_left c (hp n)
    · intro hc' n
      by_cases hc0 : c = 0
      · have h0 : Q.coeff n = 0 := by
          have hz := hc' n
          rw [hc0, zero_mul] at hz
          exact zero_dvd_iff.mp hz
        rw [hcoeff n, h0, Int.zero_ediv]
        exact dvd_zero _
      · have hspec := hc' n
        have heq : Q.coeff n = c * Q'.coeff n := by rw [← h1, Polynomial.coeff_C_mul]
        rw [heq] at hspec
        exact (mul_dvd_mul_iff_left hc0).mp hspec

end Work.LinnikBurgess
