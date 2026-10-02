import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.TangentClasses.DiscSplitting
import Submission.Work.Thom.ThomAPI
import Submission.Work.Agree.S4Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

AREA AGREE. Prove `Work.Drive.AgreeAll`: for the capped manifold X = D(ξ) ∪_F D⁸ (any capping datum F, hF),
the Chern-defined class `Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) X` (= −c₂(TX ⊗ ℂ), Submission/Work/Thom/manifoldP1.lean)
equals ± `Work.Milnor.cappedPontryaginClass F hF` (the unique class of H⁴(X;ℤ) ≅ ℤ restricting to 6·τ).
Read Submission/Work/Thom/cappedAgreement.lean, TangentClasses/README.md (DiscSplitting, p1Tangent F hF S,
p1Tangent_eq_cappedPontryaginClass) and Thom/README.md ADDENDA 20-24.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- The inclusion of the disc bundle `D(ξ) = Vk (-2)` into the capped manifold
`X = D(ξ) ∪_F D⁸`, as a continuous map.  It is the underlying continuous map of
`Work.Milnor.cappedIncl`, so that `Work.Thom.CohMap (incl F hF) ℤ 4 = Work.Milnor.cappedRestriction F hF`
(`cappedRestriction_eq_CohMap` below). -/
def incl (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    C(Submission.Milnor.Vk (-2), Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
  (Work.Milnor.cappedIncl F hF).hom

@[simp] theorem cappedRestriction_eq_CohMap
    (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F) :
    Work.Milnor.cappedRestriction F hF = Work.Thom.CohMap (incl F hF) ℤ 4 := rfl

attribute [local instance] Work.Milnor.cappedChartedSpace Work.Milnor.capped_isManifold
attribute [local instance] Work.Milnor.isCompact_capped

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

/-- **The restriction of `p₁(TX)` to the disc bundle, as the Chern class of the restricted bundle.**
The pullback of a Chern class along a continuous map is the Chern class of the pulled-back bundle
(`Work.Thom.chernClass_comap`), so the restriction of the *defined* class
`p₁(TX) = - c₂(TX ⊗_ℝ ℂ)` to the disc bundle is `- c₂` of the pullback of the complexified tangent
bundle of `X` along `incl`. -/
theorem cappedRestriction_p1Tangent' :
    (Work.Milnor.cappedRestriction F hF).hom
        (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
      = - Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 2
          (Work.Thom.bundleComap
            (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
              (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            (incl F hF)) := by
  rw [Work.Thom.p1Tangent'_def, cappedRestriction_eq_CohMap, Work.Thom.chernClass_comap]
  rw [map_neg]

/-- The canonical geometric input has the positive normalisation, so its `p1Disc` is `6 · τ`
exactly (not only up to sign). -/
theorem p1Disc_discTangentSplitting :
    p1Disc (discTangentSplitting) = (6 : ℤ) • Work.Milnor.tauD := by
  rw [p1Disc, p1Pulled_tangent_sum_xi, discTangentSplitting_G_pullback]

/-- **The reduction of `CappedAgreement'` to the restriction of `p1Tangent'` to the disc bundle.**
It suffices to know the restriction of the *defined* class `p₁(TX)` to the disc bundle `D(ξ)`,
up to sign: it is `± 6 · τ`, and `6 · τ` is exactly the restriction of the class
`Work.TangentClasses.p1Tangent F hF discTangentSplitting = Work.Milnor.cappedPontryaginClass F hF`
(`p1Tangent_discTangentSplitting`), which is determined by its restriction
(`Work.TangentClasses.p1Tangent_unique`). -/
theorem cappedAgreement'_of_restriction
    (h : (Work.Milnor.cappedRestriction F hF).hom
          (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
          = (6 : ℤ) • Work.Milnor.tauD ∨
         (Work.Milnor.cappedRestriction F hF).hom
          (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
          = -((6 : ℤ) • Work.Milnor.tauD)) :
    Work.Thom.CappedAgreement' F hF := by
  rcases h with h | h
  · left
    have hkey : Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) =
          p1Tangent F hF discTangentSplitting := by
      refine p1Tangent_unique F hF _ discTangentSplitting ?_
      rw [h, ← p1Disc_discTangentSplitting]
    rw [hkey, p1Tangent_discTangentSplitting]
  · right
    have hkey : -Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) =
          p1Tangent F hF discTangentSplitting := by
      refine p1Tangent_unique F hF _ discTangentSplitting ?_
      rw [map_neg, h, neg_neg, ← p1Disc_discTangentSplitting]
    have h2 : p1Tangent F hF discTangentSplitting
        = Work.Milnor.cappedPontryaginClass F hF := p1Tangent_discTangentSplitting F hF
    have h3 : -Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) =
          Work.Milnor.cappedPontryaginClass F hF := by rw [hkey, h2]
    exact (neg_eq_iff_eq_neg).mp h3

/-- **The remaining content of the AREA AGREE**: the restriction of the *defined* class
`p₁(TX) = Work.Thom.p1Tangent'` of the capped manifold `X = D(ξ) ∪_F D⁸` to the disc bundle
`D(ξ) = Vk (-2)` is `± 6 · τ`, where `τ = Work.Milnor.tauD` is the chosen generator of
`H⁴(D(ξ);ℤ) ≅ ℤ`.

This is the statement that the Chern-defined first Pontryagin class agrees, on the disc bundle, with
the class constructed by the `CharacteristicClasses`/`TangentClasses` chapters (which is `6 · τ`
there by definition of `Work.Milnor.cappedPontryaginClass`).  `agreeAll_of_discRestriction` below
shows that it implies `Work.Drive.AgreeAll`. -/
def DiscRestriction : Prop :=
  ∀ (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F),
    (Work.Milnor.cappedRestriction F hF).hom
        (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
      = (6 : ℤ) • Work.Milnor.tauD ∨
    (Work.Milnor.cappedRestriction F hF).hom
        (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
          (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
      = -((6 : ℤ) • Work.Milnor.tauD)

/-- **The remaining content of AGREE implies the target.** -/
theorem agreeAll_of_discRestriction (h : DiscRestriction) : Work.Drive.AgreeAll :=
  fun F hF => cappedAgreement'_of_restriction F hF (h F hF)


/-- **Plumbing**: the pullback of the *canonical* complexified tangent bundle presentation
(`Work.Thom.complexifiedTangentBundleFinite`, the `tangentBundle → mapFibre → reindex → complexify`
tower of `Submission/Work/Thom/manifoldP1.lean`) is the complexification of the pulled-back real
tangent bundle: the reindexing can be dropped and the `mapFibre` moved outside. -/
def Plumb (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) : Prop :=
  letI := Work.Milnor.cappedChartedSpace (Work.Milnor.cappedDatum F hF)
  letI : IsManifold Work.Milnor.mE8 1
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    (Work.Milnor.capped_isManifold (Work.Milnor.cappedDatum F hF)).of_le (by simp)
  letI : CompactSpace (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.isCompact_capped F hF
  Nonempty (Work.Thom.BundleIso
    (Work.Thom.bundleComap
      (Work.Thom.complexifiedTangentBundleFinite Work.Milnor.mE8
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) (incl F hF))
    (Work.Thom.complexificationCore
      (Work.TangentClasses.RealBundle.mapFibre
        (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))
        (Work.Thom.bundleComap
          (Work.TangentClasses.tangentBundle Work.Milnor.mE8
            (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) (incl F hF)))))

/-- **Model transfer**: the tangent bundle of `X` in the `ℝ⁸`-charting
(`Work.Milnor.cappedChartedSpace`) is the `Work.Milnor.vkModelIso`-transport of the tangent bundle in
the `MSpace8`-charting of the glueing. -/
def ModelTransfer (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) : Prop :=
  letI := Work.Milnor.cappedChartedSpace (Work.Milnor.cappedDatum F hF)
  letI : IsManifold Work.Milnor.mE8 1
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    (Work.Milnor.capped_isManifold (Work.Milnor.cappedDatum F hF)).of_le (by simp)
  Nonempty (Work.Thom.BundleIso
    (Work.TangentClasses.RealBundle.mapFibre Work.Milnor.vkModelIso
      (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))))
    (Work.TangentClasses.tangentBundle Work.Milnor.mE8
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))))

end

end Work.Agree

namespace Work.Agree


end Work.Agree
