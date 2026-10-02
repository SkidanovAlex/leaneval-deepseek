import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Tubular.RelAPI
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.Thom.MixedCup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The relative Kronecker pairing of a relativised absolute class

`Work.Tubular.relKronH X A n` is the pairing of the *relative* cohomology `H^n(X,A;ℤ)` with the
relative homology `H_n(X,A;ℤ)`, computed by evaluating the underlying cochain of the class on any
lift of the relative cycle to an absolute chain
(`Work.Tubular.relKronH_apply_of_relDualProj`).  If the relative class `α` is the *image* of an
absolute class `u` under the forgetful map `relToAbs : H^n(X,A) → H^n(X)` — with `X = ↥B` — then the
relative pairing of `α` with a relative cycle is the *absolute* pairing of `u` with any absolute
cycle whose class maps to it:

  `relKronH X A n α (π_* c') = ⟨relToAbs α, c'⟩`.

This is the transfer that turns a computation in the relative world into one in the absolute world;
it is what lets the local degree `U_ν ⌢ c = z_*[V]`, proved in the relative group of the normal
bundle, compute the absolute Hurewicz pairing `⟨J^*(a), h(collapse)⟩` of the Pontryagin–Thom class.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {B : Type} [TopologicalSpace B] {A : Set B}

/-- **The relative Kronecker pairing of a relativised absolute class.** -/
theorem relKronH_relToAbs (A : Set B) (n : ℕ)
    (α : relCohomology ℤ (TopCat.of B) A n)
    (c : (relChains (TopCat.of B) A).homology n)
    (c' : (singularChains ℤ (TopCat.of B)).homology n)
    (hc : HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of B) A)) n c' = c) :
    relKronH (TopCat.of B) A n α c
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of B)) n
          ((Work.Thom.relToAbs ℤ A n).hom α) c' := by
  obtain ⟨α₀, hα₀, hα₀eq⟩ := exists_relClassOf ℤ (TopCat.of B) A n α
  subst hα₀eq
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective
    ((singularChains ℤ (TopCat.of B)).homologyπ n)).mp inferInstance c'
  subst hw
  set cc : (relChains (TopCat.of B) A).cycles n :=
    (HomologicalComplex.cyclesMap (CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of B) A)) n).hom w with hcc
  have hcc_i : ((relChains (TopCat.of B) A).iCycles n).hom cc
      = (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of B) A)).f n
          (((singularChains ℤ (TopCat.of B)).iCycles n).hom w) := by
    rw [hcc]
    exact congrArg (fun (g : (singularChains ℤ (TopCat.of B)).cycles n ⟶
      (relChains (TopCat.of B) A).X n) => g.hom w)
      (HomologicalComplex.cyclesMap_i (CategoryTheory.Limits.cokernel.π
        (inclChains (TopCat.of B) A)) n)
  have hclass : (relChains (TopCat.of B) A).homologyπ n cc = c := by
    rw [← hc, hcc]
    exact (homologyMap_homologyπ_apply (CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of B) A)) n w).symm
  rw [← hclass, relKronH_apply_of_relDualProj (X := TopCat.of B) (A := A) n α₀ hα₀ cc
    (((singularChains ℤ (TopCat.of B)).iCycles n).hom w) hcc_i.symm]
  rw [Work.Thom.relToAbs_relClassOf (X := B) A α₀ hα₀]
  exact (kronH_apply ℤ (TopCat.toSSet.obj (TopCat.of B)) α₀.1
    (relClassOf_cochainDiff ℤ (TopCat.of B) A α₀ hα₀) w).symm

/-- **The transfer in the form in which it is used**: the relative pairing of a class with the
*image* of an absolute homology class is the absolute pairing of the forgotten class with that
class.  (This is `relKronH_relToAbs` with `c := π_* c'`, so the hypothesis of that lemma holds by
`rfl`; unlike `relKronH_relToAbs` it is *not* vacuous when `H_n(X,A)` is nonzero but the relative
class is not in the image of `H_n(X)` — which is the situation of the Pontryagin–Thom collapse of
the *one-point compactification* `ν⁺`.) -/
theorem relKronH_relToAbs_apply {B : Type} [TopologicalSpace B] (A : Set B) (n : ℕ)
    (α : relCohomology ℤ (TopCat.of B) A n)
    (c' : (singularChains ℤ (TopCat.of B)).homology n) :
    relKronH (TopCat.of B) A n α
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of B) A)) n c')
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of B)) n
          ((Work.Thom.relToAbs ℤ A n).hom α) c' :=
  relKronH_relToAbs A n α _ c' rfl

end

end Work.Tubular
