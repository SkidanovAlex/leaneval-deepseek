import Mathlib
import Submission.Work.Cohomology.Endgame.transgressionIso
import Submission.Work.Cohomology.Endgame.overlapCap
import Submission.Work.Cohomology.Endgame.capCompare
import Submission.Work.Cohomology.Endgame.vkTransgressionCapWeak
import Submission.Work.Cohomology.Endgame.dshDelta
import Submission.Work.Cohomology.Endgame.relMVUVQuasiIso
import Submission.Work.Cohomology.Crux.vkInternalTransgression

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology.Endgame

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

-- Transgression identity on the overlap (U|V, (U|V)|A) for an open cover U|V = X:
-- there are T0 : H_8(X,A) = H_7(U|V, (U|V)|A) and U0 : H_4(X) = H_3(U|V) such that
-- U0 (a cap c) = +/- (rho a) cap (T0 c) for all a, c, where rho is the restriction of pairs
-- induced by subtypeIncl X (U|V).
-- This is Hatcher 3.36 (naturality of the snake connecting map under the chain map
-- "cap product with a relative 4-cocycle").
-- Construction: T0 := ovlT X A U V hU hV hcov hd (Endgame/transgressionIso.lean);
-- U0 := ovlU X U V hU hV hcov deltaMv where deltaMv is the canonical connecting iso
-- (asIso of (mvSmall_shortExact U V).d 4 3 hrel, using hdeltaMv).
-- Proof route: with alpha a relative 4-cocycle representing a, and c' a preimage of c under the
-- quasi-isomorphism relMV_quasiIso, apply transgression_cruxδ
-- (Endgame/vkTransgressionCapWeak.lean, the cruxδ-form of transgression_capUvCanon obtained from
-- dshShort_cruxShort_delta), rewrite both sides with exists_capTopCanon_relCapHalf
-- (Endgame/capCompare.lean) and exists_capUvCanon_relCapHalf (Endgame/overlapCap.lean), and
-- convert to relCapPair using relCapPair_apply / relCapPairZ_iCycles, the representative choices
-- exists_relClassOf, the surjectivity of the quasi-isomorphisms, and ovlT_eq / ovlU_eq.
theorem transgression_identity_overlap (X : TopCat) (A U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hδ : CategoryTheory.IsIso (cruxδ X A U V 7))
    (hrel : (ComplexShape.down ℕ).Rel 4 3)
    (hδmv : CategoryTheory.IsIso ((mvSmall_shortExact U V).δ 4 3 hrel)) :
    ∃ (T₀ : (relChains X A).homology 8 ≃ₗ[ℤ]
            (relChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V)).homology 7)
      (U₀ : (singularChains ℤ X).homology 4 ≃ₗ[ℤ]
            (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology 3),
      ∀ (a : relCohomology ℤ X A 4) (c : (relChains X A).homology 8),
        U₀ (relCapPair X A 4 4 a c)
          = relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
              ((HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
                  (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4).hom a) (T₀ c)
        ∨ U₀ (relCapPair X A 4 4 a c)
          = - relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
              ((HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
                  (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4).hom a) (T₀ c) := by
  classical
  haveI : IsIso ((mvSmall_shortExact U V).δ 4 3 hrel) := hδmv
  refine ⟨ovlT X A U V hU hV hcov hδ,
    ovlU X U V hU hV hcov (asIso ((mvSmall_shortExact U V).δ 4 3 hrel)).toLinearEquiv, ?_⟩
  intro a c
  refine Or.imp id id (Crux.InternalTransgression.transgression_identity X A U V hU hV hcov hδ
    (fun _ hx => hx) (asIso ((mvSmall_shortExact U V).δ 4 3 hrel)).toLinearEquiv ?_ a c)
  intro x
  change (ModuleCat.Hom.hom ((mvSmall_shortExact U V).δ 4 3 hrel)) x
    = (ModuleCat.Hom.hom ((mvSmall_shortExact U V).δ 4 3
        (by simp [ComplexShape.down_Rel]))) x
  rw [show (mvSmall_shortExact U V).δ 4 3 hrel
      = (mvSmall_shortExact U V).δ 4 3 (by simp [ComplexShape.down_Rel]) from
    congrArg (fun hh => (mvSmall_shortExact U V).δ 4 3 hh) (Subsingleton.elim hrel _)]

end Work.Cohomology.Endgame
