import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Thom.Pair
import Submission.Work.Cohomology.cupLeibniz
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cut-off class of a relative cup (shared module)

This module collects the two reusable pieces of the "cut-off class" route to
`Work.Whitney.rankOne_cup_model` (see `rankOne_cup_model_NOTES.md`):

* `Work.Cohomology.cup_one_right`: the cup with a `0`-cochain that is `1` on every vertex is the
  identity (the workspace had this only on homology, `cupH'_one_right`);
* `Work.Cohomology.cup_cochainDiff_leibniz`: `cup a (d g) = (-1)^deg a • d (cup a g)` for a cocycle
  `a` -- the atomic Leibniz content, which is the source of the sign `(-1)^n` of the target;
* `Work.Whitney.pairδC_class_of_lift`: a lift `gammat` of a `0`-cocycle `gamma` on `C` represents
  the transgression `(pairδC C 0).hom [gamma]`, i.e. `d gammat` is a representative of it.  This is
  a wrapper of `Work.Sph3Disc.pdmc_pairδ_lift`; the point is that `pairδC A n` is *definitionally*
  `Work.Cohomology.pairδ ℤ (TopCat.of X) A n`.

They live in a module of their own so that downstream work can import them without pulling in the
whole of `rankOne_cup_model.lean` (importing that file was observed to perturb the resolution of the
unqualified names `relComplex`, `relDiffLM`, `relClassOf`, `cohomologyClassOf`, `cocycleOfK`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

variable {R : Type} [CommRing R]

/-- **The cup with a degree-zero cochain that is constant `1` on vertices is the identity.** -/
theorem cup_one_right (X : SSet) {n : ℕ} (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (γ : (X.chainComplex (ModuleCat.of R R)).X 0 →ₗ[R] R)
    (hγ : ∀ σ : X _⦋0⦌, genEval R X γ σ = 1) :
    cup R X α γ = α := by
  apply cup_ext R X
  intro σ
  rw [cup_apply R X]
  rw [frontFace_self X n (Nat.le_add_right n 0) σ, hγ]
  ring

/-- **The atomic Leibniz step**: the cup with a transgression `d gamma_t` is `(-1)^m` times the
differential of the cup, `m = deg alpha`.  This is `cupLeibniz` with `cochainDiff alpha = 0`; it is
the source of the whole sign `(-1)^n`. -/
theorem cup_cochainDiff_leibniz (X : SSet) {m n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R)
    (hα : cochainDiff R X α = 0)
    (γt : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) :
    cup R X α (cochainDiff R X γt) = ((-1 : R) ^ m) • cochainDiff R X (cup R X α γt) := by
  have h := cupLeibniz R X α γt
  rw [hα] at h
  rw [cup_zero_left' R X, eqRec_zero R X, zero_add] at h
  rw [h, smul_smul, ← pow_add, Even.neg_one_pow (⟨m, by ring⟩ : Even (m + m)), one_smul]

end Work.Cohomology

namespace Work.Cohomology

/-- **The singular chain complex of a topological space is the chain complex of its singular
simplicial set.**  Mathlib builds `singularChainComplexFunctor C` as
`SSet.chainComplexFunctor C ⋙ (whiskeringLeft _ _ _).obj TopCat.toSSet`, so after unfolding both
definitions the two sides differ only by the functor-composition `rfl`.

This is the identification that lets `Work.Whitney.ssB X`-spelled statements and
`Work.Cohomology.singularChains`-spelled statements be compared (see
`rankOne_cup_model_NOTES.md` sections 16 and 17). -/
theorem singularChains_eq_chainComplex (R : Type) [CommRing R] (X : TopCat) :
    Work.Cohomology.singularChains R X
      = (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R) := by
  simp only [Work.Cohomology.singularChains, AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplex]
  rfl

end Work.Cohomology


namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section

/-- **A lift of a `0`-cocycle on `C` represents the transgression `(pairδC C 0).hom gamma`.** -/
theorem pairδC_class_of_lift {X : Type} [TopologicalSpace X] (C : Set X)
    (γ : Cochain ℤ (ssB ↥C) 0) (hγ : cochainDiff ℤ (ssB ↥C) γ = 0)
    (γt : Cochain ℤ (ssB X) 0)
    (hγt : (ModuleCat.Hom.hom ((restr ℤ (TopCat.of X) C).f 0)) γt = γ) :
    ∃ (hmem : ((singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt
        ∈ Work.Cohomology.relKern ℤ (TopCat.of X) C 1)
      (hcoc : relDiffLM ℤ (TopCat.of X) C 1
        ⟨((singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmem⟩ = 0),
      (pairδC C 0).hom (cohomologyClassOf ℤ (ssB ↥C) γ hγ)
        = relClassOf ℤ (TopCat.of X) C
            ⟨((singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmem⟩ hcoc :=
  Work.Sph3Disc.pdmc_pairδ_lift (TopCat.of X) C 0 γ hγ γt hγt

end

end Work.Whitney
