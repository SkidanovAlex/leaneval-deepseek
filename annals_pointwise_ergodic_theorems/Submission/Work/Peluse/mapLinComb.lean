import Mathlib

namespace Work.Peluse

/-- For `P : ℤ[X]` of degree `≥ 2`, `β ≠ 0` and any `ξ : ℝ`, the polynomial
`β · P − ξ · X ∈ ℝ[X]` (where `P` is mapped along `ℤ → ℝ`) has the same degree as `P`,
leading coefficient `β · lc P`, and value `β P(y) − ξ y` at every integer `y`. -/
theorem mapLinComb (P : Polynomial ℤ) (β ξ : ℝ) (hβ : β ≠ 0) (hd : 2 ≤ P.natDegree) :
    (Polynomial.C β * P.map (Int.castRingHom ℝ) - Polynomial.C ξ * Polynomial.X).natDegree
        = P.natDegree ∧
      (Polynomial.C β * P.map (Int.castRingHom ℝ) - Polynomial.C ξ * Polynomial.X).leadingCoeff
        = β * ((P.leadingCoeff : ℤ) : ℝ) ∧
      (∀ y : ℤ, (Polynomial.C β * P.map (Int.castRingHom ℝ)
          - Polynomial.C ξ * Polynomial.X).eval (y : ℝ)
        = β * ((P.eval y : ℤ) : ℝ) - ξ * (y : ℝ)) := by
  set A : Polynomial ℝ := Polynomial.C β * P.map (Int.castRingHom ℝ) with hA
  set B : Polynomial ℝ := Polynomial.C ξ * Polynomial.X with hB
  have hf_inj : Function.Injective (Int.castRingHom ℝ) := by
    intro a b hab
    have h : (a : ℝ) = (b : ℝ) := hab
    exact_mod_cast h
  have hA_deg : A.natDegree = P.natDegree := by
    rw [hA, Polynomial.natDegree_C_mul hβ,
      Polynomial.natDegree_map_eq_of_injective hf_inj]
  have hA_lc : A.leadingCoeff = β * ((P.leadingCoeff : ℤ) : ℝ) := by
    rw [hA, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_map_of_injective hf_inj]
    rfl
  have hB_deg : B.natDegree ≤ 1 := by
    rw [hB]
    exact (Polynomial.natDegree_C_mul_le ξ Polynomial.X).trans Polynomial.natDegree_X_le
  have hlt : B.natDegree < A.natDegree := by
    rw [hA_deg]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hA_deg]
  · rw [Polynomial.leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree hlt), hA_lc]
  · intro y
    have h1 : P.eval₂ (Int.castRingHom ℝ) ((y : ℤ) : ℝ) = ((P.eval y : ℤ) : ℝ) := by
      simp
    have hA_eval : A.eval (y : ℝ) = β * ((P.eval y : ℤ) : ℝ) := by
      rw [hA, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, h1]
    have hB_eval : B.eval (y : ℝ) = ξ * (y : ℝ) := by
      rw [hB, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [Polynomial.eval_sub, hA_eval, hB_eval]

end Work.Peluse
