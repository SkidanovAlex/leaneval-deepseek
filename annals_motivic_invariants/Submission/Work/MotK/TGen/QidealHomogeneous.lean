import Mathlib
import Submission.Work.MotK.TGen.ZTwistQidealAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-
Route: by `Work.MotK.TGen.Qideal_eq_radical_span_Ptw`,
`Work.MotK.TwCensus.Qideal a b (h ^ 2) = (Ideal.span (Set.range (Ptw a b h))).radical`.
Each `Ptw a b h k` is homogeneous of degree `2` (`fin_cases k` and the
`MvPolynomial.IsHomogeneous` API: `isHomogeneous_X`, `isHomogeneous_C`, `IsHomogeneous.C_mul`,
`IsHomogeneous.mul`, `IsHomogeneous.pow`, `IsHomogeneous.add`, `IsHomogeneous.sub`, `IsHomogeneous.neg`).
Hence `Ideal.span (Set.range (Ptw a b h))` is homogeneous with respect to the grading
`MvPolynomial.homogeneousSubmodule (Fin 5) K` (`Ideal.homogeneous_span` with
`SetLike.IsHomogeneousElem := ∃ n, p ∈ homogeneousSubmodule _ _ n`; the file needs
`attribute [local instance] MvPolynomial.gradedAlgebra` for the `GradedRing` instance), so its
radical is homogeneous too (`Ideal.IsHomogeneous.radical`, the indexing monoid being `ℕ`).  Then
`MvPolynomial.homogeneousComponent_mem_of_mem` gives the claim.
-/

variable {K : Type} [Field K]

/-- A product `φ * X i * X j` of a homogeneous element `φ` of degree `0` with two variables is
homogeneous of degree `2`. -/
lemma isHomogeneous_mul_X_mul_X {σ : Type*} {R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} (hφ : φ.IsHomogeneous 0) (i j : σ) :
    (φ * X i * X j).IsHomogeneous 2 := by
  have h := hφ.mul ((isHomogeneous_X (R := R) i).mul (isHomogeneous_X (R := R) j))
  simpa only [mul_assoc] using h

/-- A product `φ * X i ^ 2` of a homogeneous element `φ` of degree `0` with the square of a
variable is homogeneous of degree `2`. -/
lemma isHomogeneous_mul_X_sq {σ : Type*} {R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} (hφ : φ.IsHomogeneous 0) (i : σ) :
    (φ * X i ^ 2).IsHomogeneous 2 := by
  have h := hφ.mul ((isHomogeneous_X (R := R) i).pow 2)
  simpa only [mul_assoc] using h

/-- Each twisted Pfaffian `Ptw a b h k` is a quadratic form in the variables `X 0, …, X 4`,
hence homogeneous of degree `2`. -/
lemma isHomogeneous_Ptw (a b h : K) (k : Fin 5) : (Ptw a b h k).IsHomogeneous 2 := by
  fin_cases k
  · simp only [Ptw, Work.MotK.kleinTwP, Work.MotK.kleinTwP0]
    refine IsHomogeneous.sub (IsHomogeneous.add ?_ ?_) ?_
    · exact isHomogeneous_mul_X_sq (((isHomogeneous_C (Fin 5) a).neg).mul (isHomogeneous_C (Fin 5) b)) 0
    · exact isHomogeneous_mul_X_mul_X (((isHomogeneous_C (Fin 5) a).pow 2).mul (isHomogeneous_C (Fin 5) (h ^ 2))) 2 3
    · exact isHomogeneous_mul_X_mul_X (((isHomogeneous_C (Fin 5) b).pow 2).mul (isHomogeneous_C (Fin 5) (h ^ 2))) 1 4
  · simp only [Ptw, Work.MotK.kleinTwP, Work.MotK.kleinTwP1]
    refine IsHomogeneous.sub (IsHomogeneous.add ?_ ?_) ?_
    · exact isHomogeneous_mul_X_sq (((isHomogeneous_C (Fin 5) a).neg).mul (isHomogeneous_C (Fin 5) b)) 2
    · exact isHomogeneous_mul_X_mul_X ((isHomogeneous_C (Fin 5) a).pow 2) 0 4
    · exact isHomogeneous_mul_X_mul_X ((isHomogeneous_C (Fin 5) b).pow 2) 1 3
  · simp only [Ptw, Work.MotK.kleinTwP, Work.MotK.kleinTwP2]
    refine IsHomogeneous.sub (IsHomogeneous.add ?_ ?_) ?_
    · exact isHomogeneous_mul_X_sq ((((isHomogeneous_C (Fin 5) a).neg).mul (isHomogeneous_C (Fin 5) b)).mul (isHomogeneous_C (Fin 5) (h ^ 2))) 4
    · exact isHomogeneous_mul_X_mul_X ((isHomogeneous_C (Fin 5) a).pow 2) 1 2
    · exact isHomogeneous_mul_X_mul_X ((isHomogeneous_C (Fin 5) b).pow 2) 0 3
  · simp only [Ptw, Work.MotK.kleinTwP, Work.MotK.kleinTwP3]
    refine IsHomogeneous.sub (IsHomogeneous.add ?_ ?_) ?_
    · exact isHomogeneous_mul_X_sq (((isHomogeneous_C (Fin 5) a).neg).mul (isHomogeneous_C (Fin 5) b)) 1
    · exact isHomogeneous_mul_X_mul_X (((isHomogeneous_C (Fin 5) a).pow 2).mul (isHomogeneous_C (Fin 5) (h ^ 2))) 3 4
    · exact isHomogeneous_mul_X_mul_X ((isHomogeneous_C (Fin 5) b).pow 2) 0 2
  · simp only [Ptw, Work.MotK.kleinTwP, Work.MotK.kleinTwP4]
    refine IsHomogeneous.sub (IsHomogeneous.add ?_ ?_) ?_
    · exact isHomogeneous_mul_X_sq ((((isHomogeneous_C (Fin 5) a).neg).mul (isHomogeneous_C (Fin 5) b)).mul (isHomogeneous_C (Fin 5) (h ^ 2))) 3
    · exact isHomogeneous_mul_X_mul_X ((isHomogeneous_C (Fin 5) a).pow 2) 0 1
    · exact isHomogeneous_mul_X_mul_X (((isHomogeneous_C (Fin 5) b).pow 2).mul (isHomogeneous_C (Fin 5) (h ^ 2))) 2 4

theorem QidealHomogeneous (K : Type) [Field K] (a b h : K)
    (p : MvPolynomial (Fin 5) K) (hp : p ∈ Work.MotK.TwCensus.Qideal a b (h ^ 2)) (d : ℕ) :
    MvPolynomial.homogeneousComponent d p ∈ Work.MotK.TwCensus.Qideal a b (h ^ 2) := by
  rw [Work.MotK.TGen.Qideal_eq_radical_span_Ptw a b h] at hp ⊢
  have hspan : (Ideal.span (Set.range (Ptw a b h))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 5) K) :=
    Ideal.homogeneous_span _ _ fun x hx => by
      obtain ⟨k, rfl⟩ := hx
      exact ⟨2, isHomogeneous_Ptw a b h k⟩
  exact MvPolynomial.homogeneousComponent_mem_of_mem hspan.radical hp d

end Work.MotK.TGen
