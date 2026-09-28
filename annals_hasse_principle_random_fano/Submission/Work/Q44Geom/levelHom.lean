import Mathlib
import Submission.Work.Q44Geom.defs
import Submission.Work.Q44Geom.coeffCoeffSumAlgEquiv

/-!
# Homogeneity of the level forms

For `f : ℚ[X₀,…,X₄]` homogeneous of degree `4`, a parametrisation `w : Fin 3 → ℚ⁵` and two
vectors `b₁ b₂`, the `α`-th level form `levelForm w b₁ b₂ f α` (the coefficient of `u^α` in
`f(Σ p_a w_a + u₀ b₁ + u₁ b₂)`) is homogeneous of degree `4 - |α|`.

The proof flattens the nested polynomial ring
`ℚ[X₀,X₁][Y₀,Y₁,Y₂] ≃ₐ ℚ[X₀,X₁,Y₀,Y₁,Y₂]` via `MvPolynomial.sumAlgEquiv`.  Under this
equivalence `sigma w b₁ b₂` becomes a substitution whose images are homogeneous of degree `1`,
so `sigma w b₁ b₂ f` is "bigraded homogeneous" of total degree `4`; the coefficient of the
outer monomial `X^α` is then homogeneous of the remaining degree `4 - |α|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-- Applying an algebra equivalence commutes with `aeval`. -/
lemma algEquiv_aeval {R : Type*} [CommSemiring R] {σ : Type*} {A B : Type*}
    [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (g : σ → A) (f : MvPolynomial σ R) :
    e (aeval g f) = aeval (fun i => e (g i)) f := by
  have h : e.toAlgHom.comp (aeval g) = aeval (fun i => e (g i)) := by
    apply algHom_ext; intro i; simp
  exact DFunLike.congr_fun h f

/-- **Key coefficient fact.**  If `q` is homogeneous of degree `n` in the flattened ring
`ℚ[X₀,X₁,Y₀,Y₁,Y₂]`, then the coefficient of the outer monomial `X^α` in `sumAlgEquiv q` is a
polynomial in the `Y`-variables that is homogeneous of the remaining degree `n - |α|`. -/
lemma sumAlgEquiv_coeff_isHomogeneous {σ τ : Type*}
    (q : MvPolynomial (σ ⊕ τ) ℚ) (n : ℕ) (hq : q.IsHomogeneous n) (α : σ →₀ ℕ) :
    ((sumAlgEquiv ℚ σ τ q).coeff α).IsHomogeneous (n - α.degree) := by
  change (sumAlgEquiv ℚ σ τ q).coeff α ∈ homogeneousSubmodule τ ℚ (n - α.degree)
  rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.mem_supported']
  intro m hm
  rw [coeffCoeffSumAlgEquiv]
  have hm' : m.degree ≠ n - α.degree := by simpa using hm
  by_cases h : Finsupp.sumElim α m ∈ q.support
  · exfalso
    have hdeg : (Finsupp.sumElim α m).degree = n := by
      by_contra hne
      exact (mem_support_iff.mp h) (hq.coeff_eq_zero hne)
    have hsplit : (Finsupp.sumElim α m).degree = α.degree + m.degree := by
      rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]
    omega
  · exact Finsupp.notMem_support_iff.mp h

/-- The flattening of the nested polynomial ring `ℚ[X₀,X₁][Y₀,Y₁,Y₂]` into the single
polynomial ring `ℚ[X₀,X₁,Y₀,Y₁,Y₂]`: the outer variables `X j` go to `X (inl j)` and the
inner variables `Y a` go to `X (inr a)`. -/
def flatEquiv : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ) ≃ₐ[ℚ]
    MvPolynomial (Fin 2 ⊕ Fin 3) ℚ :=
  (sumAlgEquiv ℚ (Fin 2) (Fin 3)).symm

lemma flatEquiv_C (g : MvPolynomial (Fin 3) ℚ) : flatEquiv (C g) = rename Sum.inr g := by
  have h : flatEquiv.toAlgHom.comp (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ)
      (MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))) = rename Sum.inr := by
    apply algHom_ext
    intro a
    show flatEquiv (C (X a)) = rename Sum.inr (X a)
    rw [rename_X]
    rw [show (C (X a) : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))
        = (sumAlgEquiv ℚ (Fin 2) (Fin 3)) (X (Sum.inr a)) from
      (sumAlgEquiv_X_inr (R := ℚ) (S₁ := Fin 2) (S₂ := Fin 3) a).symm]
    exact AlgEquiv.symm_apply_apply _ _
  exact DFunLike.congr_fun h g

lemma flatEquiv_X (j : Fin 2) : flatEquiv (X j) = X (Sum.inl j) := by
  rw [show (X j : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))
      = (sumAlgEquiv ℚ (Fin 2) (Fin 3)) (X (Sum.inl j)) from
    (sumAlgEquiv_X_inl (R := ℚ) (S₁ := Fin 2) (S₂ := Fin 3) j).symm]
  exact AlgEquiv.symm_apply_apply _ _

lemma flatEquiv_C_C (r : ℚ) : flatEquiv (C (C r)) = C r := by
  rw [show (C (C r) : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))
      = (sumAlgEquiv ℚ (Fin 2) (Fin 3)) (C r) from
    (sumAlgEquiv_C_inl (R := ℚ) (S₁ := Fin 2) (S₂ := Fin 3) r).symm]
  exact AlgEquiv.symm_apply_apply _ _

/-- The `i`-th variable of `sigma w b₁ b₂`, i.e. the image
`linForm w i + u₀ b₁ i + u₁ b₂ i` of the parametrised coordinate. -/
def sigmaArg (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (i : Fin 5) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ) :=
  C (linForm w i) + X 0 * C (C (b₁ i)) + X 1 * C (C (b₂ i))

lemma flatEquiv_sigmaArg_isHomogeneous (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (i : Fin 5) :
    (flatEquiv (sigmaArg w b₁ b₂ i)).IsHomogeneous 1 := by
  have hlin : (linForm w i).IsHomogeneous 1 := by
    rw [linForm]
    refine IsHomogeneous.sum _ _ _ (fun a _ => ?_)
    exact isHomogeneous_C_mul_X (w a i) a
  show (flatEquiv (C (linForm w i) + X 0 * C (C (b₁ i))
    + X 1 * C (C (b₂ i)))).IsHomogeneous 1
  have hC : flatEquiv (C (linForm w i)) = rename Sum.inr (linForm w i) := flatEquiv_C _
  have hX0 : flatEquiv (X (0 : Fin 2)) = X (Sum.inl (0 : Fin 2)) := flatEquiv_X 0
  have hX1 : flatEquiv (X (1 : Fin 2)) = X (Sum.inl (1 : Fin 2)) := flatEquiv_X 1
  have hCC1 : flatEquiv (C (C (b₁ i))) = C (b₁ i) := flatEquiv_C_C _
  have hCC2 : flatEquiv (C (C (b₂ i))) = C (b₂ i) := flatEquiv_C_C _
  rw [map_add, map_add, map_mul, map_mul, hC, hX0, hX1, hCC1, hCC2]
  refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
  · exact hlin.rename_isHomogeneous
  · exact (isHomogeneous_X _ _).mul (isHomogeneous_C _ _)
  · exact (isHomogeneous_X _ _).mul (isHomogeneous_C _ _)

theorem levelHom (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4) (α : Fin 2 → ℕ)
    (hα : α 0 + α 1 ≤ 4) :
    (Work.Q44Geom.levelForm w b₁ b₂ f α).IsHomogeneous (4 - (α 0 + α 1)) := by
  rw [levelForm_def]
  have hdeg : (Finsupp.equivFunOnFinite.symm α).degree = α 0 + α 1 := by
    rw [Finsupp.degree_eq_sum]; simp [Fin.sum_univ_two]
  have hq : (flatEquiv (sigma w b₁ b₂ f)).IsHomogeneous 4 := by
    rw [show sigma w b₁ b₂ f = aeval (sigmaArg w b₁ b₂) f from rfl]
    rw [algEquiv_aeval]
    have h := MvPolynomial.IsHomogeneous.aeval (σ := Fin 5) hf
      (fun i => flatEquiv (sigmaArg w b₁ b₂ i)) (flatEquiv_sigmaArg_isHomogeneous w b₁ b₂)
    simpa using h
  have hkey := sumAlgEquiv_coeff_isHomogeneous (flatEquiv (sigma w b₁ b₂ f)) 4 hq
    (Finsupp.equivFunOnFinite.symm α)
  rw [show (sumAlgEquiv ℚ (Fin 2) (Fin 3)) (flatEquiv (sigma w b₁ b₂ f))
      = sigma w b₁ b₂ f from AlgEquiv.apply_symm_apply _ _] at hkey
  rw [hdeg] at hkey
  exact hkey

end Work.Q44Geom
