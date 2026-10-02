import Mathlib
import Submission.Work.Cohomology.Chains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Freeness of singular homology is a homeomorphism invariant

A homeomorphism `e : X ≃ₜ Y` is an isomorphism in `TopCat`, and the singular chain complex is a
functor on `TopCat`; hence it carries `e` to an isomorphism of chain complexes and, taking `n`-th
homology, to an isomorphism of `ℤ`-modules `Hₙ(X;ℤ) ≅ Hₙ(Y;ℤ)`.  Freeness of a module is
transported along a linear equivalence, which gives the stated equivalence of `Module.Free` for the
two homology modules.
-/

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

theorem free_homology_homeomorph {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ) :
    Module.Free ℤ ↥((singularChains ℤ X).homology n) ↔
      Module.Free ℤ ↥((singularChains ℤ Y).homology n) := by
  refine Module.Free.iff_of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ) ?_
  exact Iso.toLinearEquiv
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo e)))

end

end Work.Cohomology
