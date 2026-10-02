import Mathlib
import Submission.Work.Kunneth.Assembly.Defs
import Submission.Work.Kunneth.cpn_kunneth_hypotheses
import Submission.Work.Kunneth.Bridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Künneth hypotheses for `ℂP^n = P(ε^{n+1} over the point)`

The cohomological Künneth theorem (`Work.Kunneth.kunnethCoh_value`, and its supported form
`Work.Kunneth.Asm.kunnethCoh_value_full`) requires three hypotheses on the second factor: the chain
modules are projective and the homology is free and finitely generated in every degree.  For
`Y = Sing ℂP^n = ssB (Qb (n+1))` these are `Work.Kunneth.cpn_kunneth_hypotheses`, transported along
the homeomorphism `ℂP^n ≃ₜ Qb (n+1) = P(ε^{n+1} over the point)`
(`Work.Kunneth.wkHomeo` and `Work.LerayHirsch.projUnivHomeo`).

The transport is the standard one: a homeomorphism of spaces induces an isomorphism of singular
chain complexes, hence of their homology.
-/

namespace Work.Kunneth.Asm

open CategoryTheory Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

/-- A homeomorphism of spaces induces an isomorphism of their singular homology.  (Lightweight
local version of `Work.Cohomology.homologyIsoOfHomeomorph`, to avoid importing the heavy
`free_and_vanishing_ball_compl`.) -/
theorem homologyIsoOfHomeomorph (X Y : TopCat) (e : X ≃ₜ Y) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ X).homology n
      ≅ (Work.Cohomology.singularChains ℤ Y).homology n) :=
  ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo e))⟩

theorem kunnethHypQb (n : ℕ) :
    (∀ q, Module.Projective ℤ ↥((Work.Kunneth.sChain (ssB (Qb (n + 1)))).X q)) ∧
    (∀ q, Module.Free ℤ ↥((Work.Kunneth.sChain (ssB (Qb (n + 1)))).homology q)) ∧
    (∀ q, Module.Finite ℤ ↥((Work.Kunneth.sChain (ssB (Qb (n + 1)))).homology q)) := by
  have hproj : ∀ q, Module.Projective ℤ ↥((Work.Kunneth.sChain (ssB (Qb (n + 1)))).X q) :=
    fun q => by
      haveI : Module.Free ℤ ↥((Work.Kunneth.sChain (ssB (Qb (n + 1)))).X q) :=
        Work.Cohomology.singularChains_free (TopCat.of (Qb (n + 1))) q
      exact Module.Projective.of_free
  have hhomeo : Work.Projective.CP n ≃ₜ Qb (n + 1) :=
    (Work.Kunneth.wkHomeo n).symm.trans (Work.LerayHirsch.projUnivHomeo (n + 1))
  have hiso : ∀ q, Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of
      (Work.Projective.CP n))).homology q) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Qb (n + 1)))).homology q)) :=
    fun q => homologyIsoOfHomeomorph (TopCat.of (Work.Projective.CP n))
      (TopCat.of (Qb (n + 1))) hhomeo q
  refine ⟨hproj, fun q => ?_, fun q => ?_⟩
  · exact Module.Free.of_equiv' (cpn_kunneth_hypotheses n q).2.1
      (Classical.choice (hiso q)).toLinearEquiv
  · haveI : Module.Finite ℤ ↥((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Projective.CP n))).homology q) :=
      (cpn_kunneth_hypotheses n q).2.2
    exact Module.Finite.equiv (Classical.choice (hiso q)).toLinearEquiv

end

end Work.Kunneth.Asm
