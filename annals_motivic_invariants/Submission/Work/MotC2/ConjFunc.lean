import Mathlib
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

variable {L : Type*} [Field L]

/-- The negation formula on `genY` in the form used by `ConjFunc`: the linear coefficient is
grouped as `a₁x + a₃`. -/
lemma negAlgEquiv_genY_ConjFunc (E : WeierstrassCurve L) :
    (negAlgEquiv E).toAlgHom (genY E) =
      -genY E - (algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃) := by
  have h : (negAlgEquiv E).toAlgHom (genY E) = -genY E -
      algebraMap L (Func E) E.a₁ * genX E - algebraMap L (Func E) E.a₃ := negAlgEquiv_genY E
  rw [h]
  first | refl_ring1 | ring

/-- The negation `[-1]` of the function field maps the affine coordinate ring `affRing E = L[x,y]`
into itself: `affRing E = L[genX E, genY E]` by `Work.MotC2.affRing_eq_adjoin`, the negation fixes
`genX E` and sends `genY E` to `-genY E - (a₁x + a₃)`, an `L`-linear combination of `genX E` and
`genY E`. -/
lemma map_negAlgEquiv_affRing_le (E : WeierstrassCurve L) :
    Subalgebra.map (negAlgEquiv E).toAlgHom (affRing E) ≤ affRing E := by
  have hx : (negAlgEquiv E).toAlgHom (genX E) = genX E := negAlgEquiv_genX E
  have hy := negAlgEquiv_genY_ConjFunc E
  rw [affRing_eq_adjoin, AlgHom.map_adjoin]
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro y ⟨z, hz, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · rw [hx]
    exact Algebra.subset_adjoin (by simp)
  · rw [hy]
    exact sub_mem (neg_mem (Algebra.subset_adjoin (by simp)))
      (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin (by simp)))
        (Subalgebra.algebraMap_mem _ _))

/-- The "conjugation" of the function field of a Weierstrass curve: the `L`-algebra
automorphism `σ` with `σ x = x` and `σ y = -(y + e)`, where `e = a₁x + a₃`.  It is an
involution, because `-(y+e)` again satisfies the Weierstrass equation, and it preserves the
affine coordinate ring `affRing E = L[x,y]`.

This is `Work.MotC2.negAlgEquiv E` (already constructed in `Submission/Work/MotC2/Negation.lean`,
with `negAlgEquiv_mul_self`, `negAlgEquiv_genX`, `negAlgEquiv_genY`); the only new content is the
last conjunct, which follows from `affRing E = Algebra.adjoin L {genX E, genY E}`
(`Work.MotC2.affRing_eq_adjoin`) since `σ` fixes `genX E`, sends `genY E` to
`-genY E - (algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃) ∈ affRing E`, and
`σ ∘ σ = id`. -/
theorem ConjFunc (L : Type*) [Field L] (E : WeierstrassCurve L) :
    ∃ σ : Func E ≃ₐ[L] Func E,
      (∀ z : Func E, σ (σ z) = z) ∧
      (∀ P : Polynomial L, σ (Polynomial.aeval (genX E) P) = Polynomial.aeval (genX E) P) ∧
      (σ (genY E) =
        -genY E - (algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃)) ∧
      (∀ z : Func E, z ∈ affRing E ↔ σ z ∈ affRing E) := by
  refine ⟨negAlgEquiv E, ?_, ?_, ?_, ?_⟩
  · -- the negation is an involution
    intro z
    have h := AlgEquiv.congr_fun (negAlgEquiv_mul_self E) z
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply] at h
    exact h
  · -- it fixes the subring `L[x]`
    intro P
    change (negAlgEquiv E).toAlgHom (Polynomial.aeval (genX E) P) = Polynomial.aeval (genX E) P
    rw [← Polynomial.aeval_algHom_apply (negAlgEquiv E).toAlgHom (genX E) P]
    exact congrArg (fun w => Polynomial.aeval w P) (negAlgEquiv_genX E)
  · -- the formula on `y`
    exact negAlgEquiv_genY_ConjFunc E
  · -- preservation of the affine coordinate ring
    have hle := map_negAlgEquiv_affRing_le E
    intro z
    refine ⟨fun hz => hle (Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩), fun hz => ?_⟩
    have h := hle (Subalgebra.mem_map.mpr ⟨negAlgEquiv E z, hz, rfl⟩)
    have hinv : (negAlgEquiv E).toAlgHom (negAlgEquiv E z) = z := by
      have h2 := AlgEquiv.congr_fun (negAlgEquiv_mul_self E) z
      rw [AlgEquiv.mul_apply, AlgEquiv.one_apply] at h2
      exact h2
    rwa [hinv] at h

end Work.MotC2
