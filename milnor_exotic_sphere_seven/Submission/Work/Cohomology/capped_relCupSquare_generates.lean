import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.Crux.vk_relCupSquare_generates_of_surjective
import Submission.Work.Cohomology.Endgame.cappedTransferClean
import Submission.Work.Endgame.cappedTransferIso
import Submission.Work.Endgame.vkUnimodularClean

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cup square of the capped manifold generates `H⁸(X,A)`

Let `D = cappedDatum F hF`, `X = cappedSpace D` and `A = Set.range D.ιY` (the cap, an open disc).
The map of pairs `ιX : (Vk (-2), Mk (-2)) → (X, A)` induces a map of relative cochain complexes
`Work.Cohomology.Endgame.CappedTransfer.capRelMap D hU`, which is an isomorphism on relative
cohomology in every degree (`Work.Endgame.cappedTransferIso`), and — being induced by a map of pairs
— is compatible with the relative cup products
(`Work.Cohomology.Endgame.CappedTransfer.relCupHNatural_capPair`).

The generator statement for the disc-bundle pair `(Vk(-2), Mk(-2))` — Lefschetz duality in the
middle degree, proved in `Work.Cohomology.Crux.vk_relCapPair_unimodular` and converted to the
cup-square-generator form by `Work.Cohomology.Crux.vk_relCupSquare_generates_of_surjective` —
therefore transfers verbatim to the capped pair:  if `u₀` is a generator of `H⁴(Vk,Mk) ≅ ℤ` whose
relative cup square generates `H⁸(Vk,Mk) ≅ ℤ`, then

  `u := (capRelMap)^{-1} u₀`  generates `H⁴(X,A)`,  and  `u ⌣ u = (capRelMap)^{-1}(u₀ ⌣ u₀)`
  generates `H⁸(X,A)`

(the inverses exist because `capRelMap` is an isomorphism in degrees `4` and `8`).

This is the mirror image of `Submission/Work/Cohomology/capped_cupSquare_generates.lean`, which
transfers this relative statement to the *absolute* cohomology of `X` (there along `relIncl`).
-/

set_option maxHeartbeats 1600000

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- A generator of `M` is carried to a generator by a surjective linear map. -/
lemma span_singleton_map_eq_top {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span]; simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

theorem capped_relCupSquare_generates (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    ∃ u : Work.Cohomology.relCohomology ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
        (Set.range (Work.Milnor.cappedDatum F hF).ιY) 4,
      Submodule.span ℤ {u} = ⊤ ∧
      Submodule.span ℤ {(Work.Cohomology.relCupH' ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
        (Set.range (Work.Milnor.cappedDatum F hF).ιY) 4 4 u u)} = ⊤ := by
  obtain ⟨u₀, hu₀, hu₀u₀⟩ :=
    Crux.vk_relCupSquare_generates_of_surjective Work.Endgame.vkUnimodularClean
  let D : Work.Milnor.CapData := Work.Milnor.cappedDatum F hF
  let hU : D.U = Work.Milnor.collar (-2) := Work.Milnor.cappedDatum_U F hF
  let φ4 := HomologicalComplex.homologyMap
    (Work.Cohomology.Endgame.CappedTransfer.capRelMap D hU) 4
  let φ8 := HomologicalComplex.homologyMap
    (Work.Cohomology.Endgame.CappedTransfer.capRelMap D hU) 8
  haveI hi4 : IsIso φ4 := Work.Endgame.cappedTransferIso D hU 4
  haveI hi8 : IsIso φ8 := Work.Endgame.cappedTransferIso D hU 8
  refine ⟨(inv φ4).hom u₀, ?_, ?_⟩
  · exact span_singleton_map_eq_top _
      (Work.Cohomology.Endgame.CappedTransfer.surjective_of_isIso (inv φ4)) hu₀
  · have hnat := Work.Cohomology.Endgame.CappedTransfer.relCupHNatural_capPair D hU
      ((inv φ4).hom u₀) ((inv φ4).hom u₀)
    have hφ4u := CategoryTheory.IsIso.inv_hom_id_apply φ4 u₀
    have hsq : φ8.hom (relCupH' ℤ (TopCat.of (Work.Milnor.cappedSpace D))
          (Set.range D.ιY) 4 4 ((inv φ4).hom u₀) ((inv φ4).hom u₀))
        = relCupH' ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
            (Set.range (Work.Milnor.mkToVkFun (-2))) 4 4 u₀ u₀ := by
      rw [hnat, hφ4u]
    rw [← CategoryTheory.IsIso.hom_inv_id_apply φ8
      (relCupH' ℤ (TopCat.of (Work.Milnor.cappedSpace D)) (Set.range D.ιY) 4 4
        ((inv φ4).hom u₀) ((inv φ4).hom u₀)), hsq]
    exact span_singleton_map_eq_top _
      (Work.Cohomology.Endgame.CappedTransfer.surjective_of_isIso (inv φ8)) hu₀u₀

end

end Work.Cohomology
