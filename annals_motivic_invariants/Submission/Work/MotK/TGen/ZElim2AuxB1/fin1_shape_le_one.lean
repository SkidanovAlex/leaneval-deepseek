import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZElim2AuxB1

/-- The monomial `single 0 1` in `Fin 1 →₀ ℕ` is not the zero monomial. -/
private lemma fin1_single_ne_zero : ¬ (Finsupp.single (0 : Fin 1) 1 = (0 : Fin 1 →₀ ℕ)) := by
  intro hh
  have h' := congrArg (fun f : Fin 1 →₀ ℕ => f 0) hh
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
  omega

/-- The zero monomial in `Fin 1 →₀ ℕ` is not `single 0 1`. -/
private lemma fin1_zero_ne_single : ¬ ((0 : Fin 1 →₀ ℕ) = Finsupp.single (0 : Fin 1) 1) := by
  intro hh
  have h' := congrArg (fun f : Fin 1 →₀ ℕ => f 0) hh
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
  omega

/-- Every element of `MvPolynomial (Fin 1) L` of total degree ≤ 1 has the shape
`a * X 0 + b`. -/
theorem fin1_shape_le_one {L : Type*} [Field L] (p : MvPolynomial (Fin 1) L) (h : p.totalDegree ≤ 1) :
    ∃ a b : L, p = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b := by
  refine ⟨p.coeff (Finsupp.single 0 1), p.coeff 0, ?_⟩
  ext s
  rw [MvPolynomial.coeff_add, MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_C]
  have hs_cases : s 0 = 0 ∨ s 0 = 1 ∨ 2 ≤ s 0 := by omega
  rcases hs_cases with h0 | h1 | h2
  · have hs : s = 0 := by
      apply Finsupp.ext; intro i; fin_cases i; simpa using h0
    rw [hs, if_neg fin1_single_ne_zero, if_pos rfl, zero_add]
  · have hs : s = Finsupp.single 0 1 := by
      apply Finsupp.ext; intro i; fin_cases i; simpa using h1
    rw [hs, if_pos rfl, if_neg fin1_zero_ne_single, add_zero]
  · have hcoeff : p.coeff s = 0 := by
      rw [← MvPolynomial.notMem_support_iff]
      intro hmem
      have hle : s 0 ≤ 1 :=
        (MvPolynomial.degreeOf_le_iff.mp
          ((MvPolynomial.degreeOf_le_totalDegree p 0).trans h)) s hmem
      omega
    rw [hcoeff]
    have hne1 : Finsupp.single (0 : Fin 1) 1 ≠ s := by
      intro hh
      have h' := congrArg (fun f : Fin 1 →₀ ℕ => f 0) hh
      simp only [Finsupp.single_eq_same] at h'
      omega
    have hne0 : (0 : Fin 1 →₀ ℕ) ≠ s := by
      intro hh
      have h' := congrArg (fun f : Fin 1 →₀ ℕ => f 0) hh
      simp only [Finsupp.zero_apply] at h'
      omega
    rw [if_neg hne1, if_neg hne0, zero_add]

end Work.MotK.TGen.ZElim2AuxB1
