import Mathlib
import Submission.Work.ThomBordism.coorFibre_fibreGeneratorAux
import Submission.Work.ThomBordism.keyLocal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! **Module split note (session 53).**

Everything of this file except the final theorem now lives in
`Submission/Work/ThomBordism/coorFibre_fibreGeneratorAux.lean` (module
`Submission.Work.ThomBordism.coorFibre_fibreGeneratorAux`), which does **not** import
`keyLocal.lean`.  This was necessary because `Work.ThomBordism.keyLocal` is proved at the end of a
chain (`KeyLocal/perDatum`, `KeyLocal/tubeCompare`, `keyLocalProof`) that needs the *auxiliary*
content of this file (`admissibleUnique`, `KeyLocalWitness`, `keyLocalData_of_witness'`), so the
final theorem had to leave the cycle.  All the names formerly declared here are still visible to
every importer of this module (this file imports the aux module), so nothing else in the tree
changed.

The statement of the theorem is unchanged. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-- **The requested lemma.**

The statement is exactly `Work.ThomBordism.PieceP2` of `localDegree_localisation.lean` and is
equivalent, over the tree, to the cross-datum uniformity of the branch sign
(`Work.ThomBordism.branchSign_uniform_gauss`); the assembly step
`coorFibre_fibreGenerator_of_uniformF2` above reduces it to the uniform fibre-reading statement UF2,
which is the project's remaining obligation (see this file's header). -/
theorem coorFibre_fibreGenerator (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        (x : V.pt)
        (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
        (z : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
          (Work.ThomBordism.nfPunct E x)).homology k),
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
        Submodule.span ℤ ({z} : Set _) = ⊤ →
        (∀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E),
          Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
              (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z
            = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
                (Work.Tubular.normalNonzero E) (k + 8)
                ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
                  (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U))
                (Work.Tubular.collapseRelK8 C g hg hR hbox)) →
        Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
            (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z = t :=
  coorFibre_fibreGenerator_of_keyLocalData k hk (Work.ThomBordism.keyLocal k hk)


end

end Work.ThomBordism
