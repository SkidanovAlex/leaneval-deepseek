import Mathlib
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Tubular.RelAPI
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.relChainsProjective

/-!
# The relative Kronecker pairing is the dual universal coefficient isomorphism

The relative Kronecker pairing `Work.Tubular.relKronH` is the pairing

`H^n(X,A;ℤ) ⟶ (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)`

of the relative cohomology of a pair with the `ℤ`-dual of its relative homology, defined by the
computation rule `Work.Tubular.relKronH_apply`.  This module proves that it is an *isomorphism*
whenever the relative homology is degreewise free: the dual universal coefficient theorem for the
relative chain complex `C_*(X,A)` (`Work.Cohomology.uctDual_evaluation`, which applies because
`C_*(X,A)` is degreewise projective, `Work.Cohomology.relChainsProjective`) identifies the
cohomology of the dual complex `Hom_ℤ(C_*(X,A), ℤ)` with the dual of `H_*(X,A)`, and the relative
cochains are the duals of the relative chains (`Work.Cohomology.relCochainDual`).

The result is the exact shape needed in the tubular chapter: the mixed cap/cup adjunction
`Work.Tubular.kronH_mixedCup_relKronH` computes a pairing of a class of `H^*(X;ℤ)` with a class of
`H_*(X,A;ℤ)` through `relKronH`, and the present theorem makes `relKronH` an identification, so
that the computation can be transferred to the canonical identification of `H^n(X,A;ℤ)` with the
dual of `H_n(X,A;ℤ)`.

## Main result

* `Work.Tubular.exists_relKronH_eval_iso` — if `H_j(X,A;ℤ)` is free for all `j`, then there is a
  linear equivalence `H^n(X,A;ℤ) ≃ₗ[ℤ] (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)` which *is* the relative Kronecker
  pairing `relKronH` (i.e. it agrees with it on every pair of classes).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Tubular

noncomputable section

open Work.Cohomology

/-! ## The duality isomorphism of complexes, with computable components -/

/-- **The relative cochains are the duals of the relative chains**, with the degreewise
isomorphisms `relDualIso` as components.  (The underlying statement
`Work.Cohomology.relCochainDual` only records existence; here we need the components.) -/
def relCochainDualComponents (X : TopCat) (A : Set X) :
    dualComplex ℤ (relChains X A) ≅ relComplex ℤ X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => relDualIso X A n) (fun i j hij => by
    rw [← hij]
    exact relDualIso_comm X A i)

/-- The same isomorphism in the other direction: relative cochains to the dual of the relative
chains. -/
def relDualComponents (X : TopCat) (A : Set X) :
    relComplex ℤ X A ≅ dualComplex ℤ (relChains X A) :=
  (relCochainDualComponents X A).symm

/-- The `n`-th component of `relDualComponents` is the inverse of `relDualIso`. -/
@[simp] lemma relDualComponents_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relDualComponents X A).hom.f n = (relDualIso X A n).inv := by
  rw [relDualComponents, CategoryTheory.Iso.symm_hom]
  exact HomologicalComplex.Hom.isoOfComponents_inv_f _ _ n

/-- The inverse of `relDualIso` is the linear equivalence `relDualEquiv`, i.e. the chain-level
relative Kronecker pairing `relKronLM`. -/
lemma relDualIso_inv_eq (X : TopCat) (A : Set X) (n : ℕ) :
    (relDualIso X A n).inv = ModuleCat.ofHom ((relDualEquiv X A n).symm).toLinearMap := by
  rw [relDualIso, LinearEquiv.toModuleIso_inv]

/-! ## The class of a relative cycle -/

/-- **The class of a relative cycle** of the relative cochain complex is the class of the
underlying relative cocycle. -/
lemma relClassOf_relOfCycle (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    relClassOf ℤ X A (relOfCycle X A n z) (relDiffLM_relOfCycle X A n z)
      = ((relComplex ℤ X A).homologyπ n) z := by
  show ((relComplex ℤ X A).homologyπ n)
      (relCocycleOf ℤ X A (relOfCycle X A n z) (relDiffLM_relOfCycle X A n z)) = _
  congr 1
  exact iCycles_injective_K (relComplex ℤ X A) n
    (by rw [iCycles_relCocycleOf]; rfl)

/-! ## The pairing is the dual universal coefficient isomorphism -/

theorem exists_relKronH_eval_iso (X : TopCat) (A : Set X) (n : ℕ)
    (hfree : ∀ j, Module.Free ℤ ↥((Work.Cohomology.relChains X A).homology j)) :
    ∃ e : (Work.Cohomology.relComplex ℤ X A).homology n ≃ₗ[ℤ]
        (↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ),
      ∀ (α : (Work.Cohomology.relComplex ℤ X A).homology n)
        (c : ↥((Work.Cohomology.relChains X A).homology n)),
        e α c = Work.Tubular.relKronH X A n α c := by
  obtain ⟨e₀, he₀⟩ := uctDual_evaluation (relChains X A)
    (fun k => relChainsProjective X A k) hfree n
  -- the transport of the dual universal coefficient isomorphism of `C_*(X,A)` to `C^*(X,A)`
  let eF : ↥((relComplex ℤ X A).homology n) ≃ₗ[ℤ]
      ↥((dualComplex ℤ (relChains X A)).homology n) :=
    LinearEquiv.ofBijective
      (HomologicalComplex.homologyMap (relDualComponents X A).hom n).hom
      (ConcreteCategory.bijective_of_isIso
        (HomologicalComplex.homologyMapIso (relDualComponents X A) n).hom)
  let eD : ↥((dualComplex ℤ (relChains X A)).homology n) ≃ₗ[ℤ]
      (↥((relChains X A).homology n) →ₗ[ℤ] ℤ) :=
    LinearEquiv.ofBijective (e₀.hom.hom)
      (ConcreteCategory.bijective_of_isIso e₀.hom)
  refine ⟨eF.trans eD, ?_⟩
  intro α c
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relComplex ℤ X A).homologyπ n)).mp inferInstance α
  obtain ⟨cc, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relChains X A).homologyπ n)).mp inferInstance c
  obtain ⟨zhat, hzhat⟩ := relDualProj_surjective X A n
    ((relChains X A).iCycles n cc)
  -- the transport of a class is the class of the transported cycle
  have key : (HomologicalComplex.homologyMap (relDualComponents X A).hom n).hom
        (((relComplex ℤ X A).homologyπ n) z)
      = ((dualComplex ℤ (relChains X A)).homologyπ n)
          ((HomologicalComplex.cyclesMap (relDualComponents X A).hom n) z) := by
    have h := congrArg (fun (g : (relComplex ℤ X A).cycles n ⟶
        (dualComplex ℤ (relChains X A)).homology n) => ModuleCat.Hom.hom g z)
      (HomologicalComplex.homologyπ_naturality (relDualComponents X A).hom n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  -- the transported cycle is the chain-level pairing functional
  have hz' : (HomologicalComplex.iCycles (dualComplex ℤ (relChains X A)) n).hom
        ((HomologicalComplex.cyclesMap (relDualComponents X A).hom n) z)
      = relKronLM X A n (relOfCycle X A n z) := by
    have h := congrArg (fun (g : (relComplex ℤ X A).cycles n ⟶
        (dualComplex ℤ (relChains X A)).X n) => g.hom z)
      (HomologicalComplex.cyclesMap_i (relDualComponents X A).hom n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, relDualComponents_hom_f, relDualIso_inv_eq]
    simp only [ModuleCat.hom_ofHom, relKronLM, relOfCycle]
    rfl
  -- the value of the transported universal coefficient isomorphism
  have hL : (eF.trans eD) (((relComplex ℤ X A).homologyπ n) z)
        (((relChains X A).homologyπ n) cc)
      = (dval (relChains X A) n
          ((HomologicalComplex.iCycles (dualComplex ℤ (relChains X A)) n).hom
            ((HomologicalComplex.cyclesMap (relDualComponents X A).hom n) z))
          ((HomologicalComplex.iCycles (relChains X A) n) cc)) := by
    rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
      LinearEquiv.ofBijective_apply, key]
    exact he₀ ((HomologicalComplex.cyclesMap (relDualComponents X A).hom n) z) cc
  have hL' : (dval (relChains X A) n
        ((HomologicalComplex.iCycles (dualComplex ℤ (relChains X A)) n).hom
          ((HomologicalComplex.cyclesMap (relDualComponents X A).hom n) z))
        ((HomologicalComplex.iCycles (relChains X A) n) cc))
      = relDualLM X n (relOfCycle X A n z).1 zhat := by
    simp only [dval]
    rw [hz', ← hzhat, relKronLM_relDualProj]
  -- the value of the relative Kronecker pairing
  have hR : relKronH X A n (((relComplex ℤ X A).homologyπ n) z)
        (((relChains X A).homologyπ n) cc)
      = relDualLM X n (relOfCycle X A n z).1 zhat := by
    rw [← relClassOf_relOfCycle X A n z]
    rw [relKronH_apply_of_relDualProj n (relOfCycle X A n z)
      (relDiffLM_relOfCycle X A n z) cc zhat hzhat]
    rfl
  rw [hL, hL', hR]

end

end Work.Tubular
