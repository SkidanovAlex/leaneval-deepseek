import Mathlib
import Submission.Work.CoreTopology.Transport
import Submission.Work.CoreTopology.IntersectionNumberStandard

namespace Work.CoreTopology

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## Transport of the surface and of the curves

Everything in this file is a transport statement for the homeomorphism `ψ` of `ℝ³`:
the standard torus and the curves on it are carried to `ParamTorus.mapHomeomorph ψ`
and the curves on *that* torus, and the three properties entering `pardonsI`
(`IsSimple`, `IsEssential`, `BoundsDiskInComplement`) as well as the intersection
cardinality `Set.encard (range α ∩ range β)` are preserved. -/

/-- A homeomorphism of `ℝ³` regarded as a continuous map, used to push discs forward. -/
def homeomorphCMap (ψ : R3 ≃ₜ R3) : C(R3, R3) := ⟨fun x => ψ x, ψ.continuous⟩

@[simp] theorem homeomorphCMap_apply (ψ : R3 ≃ₜ R3) (x : R3) : homeomorphCMap ψ x = ψ x := rfl

/-- The carrier of the image torus is the image under `ψ` of the carrier of the
standard torus. -/
theorem carrier_mapHomeomorph (ψ : R3 ≃ₜ R3) :
    (ParamTorus.mapHomeomorph ψ).carrier = ψ '' standard.carrier := by
  ext X
  simp only [ParamTorus.mem_carrier_iff, Set.mem_image, ParamTorus.mapHomeomorph_psi,
    standard_psi]
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨Work.Core.torusMap x y, ⟨x, y, rfl⟩, hxy⟩
  · rintro ⟨Y, ⟨x, y, rfl⟩, hY⟩
    exact ⟨x, y, hY⟩

/-- Membership in the carrier of the image torus, in terms of `ψ`. -/
theorem mem_carrier_mapHomeomorph_iff (ψ : R3 ≃ₜ R3) (Y : R3) :
    ψ Y ∈ (ParamTorus.mapHomeomorph ψ).carrier ↔ Y ∈ standard.carrier := by
  rw [carrier_mapHomeomorph, Set.mem_image]
  constructor
  · rintro ⟨Y', hY', hYY'⟩
    rwa [ψ.injective hYY'] at hY'
  · exact fun hY => ⟨Y, hY, rfl⟩

/-- The inverse form of `mem_carrier_mapHomeomorph_iff`. -/
theorem mem_carrier_mapHomeomorph_iff' (ψ : R3 ≃ₜ R3) (X : R3) :
    X ∈ (ParamTorus.mapHomeomorph ψ).carrier ↔ ψ.symm X ∈ standard.carrier := by
  have h := mem_carrier_mapHomeomorph_iff ψ (ψ.symm X)
  rwa [ψ.apply_symm_apply] at h

/-- `mapHomeomorph` followed by `mapHomeomorphInv` is the identity. -/
theorem ClosedCurve.mapHomeomorphInv_mapHomeomorph (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve standard) :
    ClosedCurve.mapHomeomorphInv ψ (ClosedCurve.mapHomeomorph ψ γ) = γ := by
  apply ClosedCurve.ext
  funext t
  simp only [ClosedCurve.mapHomeomorphInv_apply, ClosedCurve.mapHomeomorph_apply]
  exact ψ.symm_apply_apply (γ.γ t)

/-- `mapHomeomorphInv` followed by `mapHomeomorph` is the identity. -/
theorem ClosedCurve.mapHomeomorph_mapHomeomorphInv (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) :
    ClosedCurve.mapHomeomorph ψ (ClosedCurve.mapHomeomorphInv ψ γ) = γ := by
  apply ClosedCurve.ext
  funext t
  simp only [ClosedCurve.mapHomeomorphInv_apply, ClosedCurve.mapHomeomorph_apply]
  exact ψ.apply_symm_apply (γ.γ t)

/-- The range of a pushed-forward curve is the image of the range. -/
theorem ClosedCurve.range_mapHomeomorph (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard) :
    Set.range (ClosedCurve.mapHomeomorph ψ γ).γ = ψ '' Set.range γ.γ := by
  ext X
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨γ.γ t, ⟨t, rfl⟩, ht⟩
  · rintro ⟨Y, ⟨t, rfl⟩, hY⟩
    exact ⟨t, hY⟩

/-- Pushing a closed curve forward along `ψ` preserves simpleness. -/
theorem ClosedCurve.isSimple_mapHomeomorph_iff (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard) :
    IsSimple (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ γ) ↔
      IsSimple standard γ := by
  unfold IsSimple
  constructor
  · intro h a ha b hb hab
    refine h ha hb ?_
    show ψ (γ.γ a) = ψ (γ.γ b)
    rw [hab]
  · intro h a ha b hb hab
    exact h ha hb (ψ.injective hab)

/-- Pushing a closed curve forward along `ψ` preserves essentiality. -/
theorem ClosedCurve.isEssential_mapHomeomorph_iff (ψ : R3 ≃ₜ R3) (γ : ClosedCurve standard) :
    IsEssential (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ γ) ↔
      IsEssential standard γ := by
  refine ⟨fun h => ?_, ClosedCurve.isEssential_mapHomeomorph ψ γ⟩
  obtain ⟨L', hL'⟩ := h
  have hlifts : ∀ t : ℝ, standard.psi (L'.Θ t) (L'.Φ t) = γ.γ t := by
    intro t
    refine ψ.injective ?_
    have h := L'.lifts t
    simp only [ParamTorus.mapHomeomorph_psi, ClosedCurve.mapHomeomorph_apply] at h
    exact h
  let L : LiftOf standard γ :=
    { Θ := L'.Θ, Φ := L'.Φ, contΘ := L'.contΘ, contΦ := L'.contΦ, lifts := hlifts }
  refine ⟨L, ?_⟩
  have hw : L'.winding = L.winding := LiftOf.winding_congr L L' (fun _ => rfl) (fun _ => rfl)
  rw [← hw]
  exact hL'

/-- A curve on the image torus is simple iff its pull-back on the standard torus is. -/
theorem ClosedCurve.isSimple_mapHomeomorphInv_iff (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) :
    IsSimple standard (ClosedCurve.mapHomeomorphInv ψ γ) ↔
      IsSimple (ParamTorus.mapHomeomorph ψ) γ := by
  have h := ClosedCurve.isSimple_mapHomeomorph_iff ψ (ClosedCurve.mapHomeomorphInv ψ γ)
  rw [ClosedCurve.mapHomeomorph_mapHomeomorphInv ψ γ] at h
  exact h.symm

/-- A curve on the image torus is essential iff its pull-back on the standard torus is. -/
theorem ClosedCurve.isEssential_mapHomeomorphInv_iff (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) :
    IsEssential standard (ClosedCurve.mapHomeomorphInv ψ γ) ↔
      IsEssential (ParamTorus.mapHomeomorph ψ) γ := by
  have h := ClosedCurve.isEssential_mapHomeomorph_iff ψ (ClosedCurve.mapHomeomorphInv ψ γ)
  rw [ClosedCurve.mapHomeomorph_mapHomeomorphInv ψ γ] at h
  exact h.symm

/-- Pushing the bounding disc of `α` forward along `ψ` gives a bounding disc of the
image curve. -/
theorem isBoundingDisk_mapHomeomorph (ψ : R3 ≃ₜ R3) (α : ClosedCurve standard)
    (e : C(Metric.closedBall (0 : ℂ) 1, R3)) (he : IsBoundingDisk standard α e) :
    IsBoundingDisk (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ α)
      ((homeomorphCMap ψ).comp e) := by
  obtain ⟨hinj, hcircle, hint⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · intro z₁ z₂ h
    refine hinj (ψ.injective ?_)
    simpa only [ContinuousMap.comp_apply, homeomorphCMap_apply] using h
  · intro θ
    show ψ (e (circlePoint θ)) = ψ (α.γ θ)
    rw [hcircle θ]
  · intro z hz
    show ψ (e z) ∉ (ParamTorus.mapHomeomorph ψ).carrier
    rw [mem_carrier_mapHomeomorph_iff]
    exact hint z hz

/-- Pulling a bounding disc of the image curve back along `ψ` gives a bounding disc of `α`. -/
theorem isBoundingDisk_mapHomeomorph_inv (ψ : R3 ≃ₜ R3) (α : ClosedCurve standard)
    (e : C(Metric.closedBall (0 : ℂ) 1, R3))
    (he : IsBoundingDisk (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ α) e) :
    IsBoundingDisk standard α ((homeomorphCMap ψ.symm).comp e) := by
  obtain ⟨hinj, hcircle, hint⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · intro z₁ z₂ h
    refine hinj (ψ.symm.injective ?_)
    simpa only [ContinuousMap.comp_apply, homeomorphCMap_apply] using h
  · intro θ
    have h : e (circlePoint θ) = ψ (α.γ θ) := by
      simpa only [ClosedCurve.mapHomeomorph_apply] using hcircle θ
    show ψ.symm (e (circlePoint θ)) = α.γ θ
    rw [h, ψ.symm_apply_apply]
  · intro z hz
    show ψ.symm (e z) ∉ standard.carrier
    intro hmem
    exact hint z hz ((mem_carrier_mapHomeomorph_iff' ψ (e z)).mpr hmem)

/-- Bounding a disc in the complement of the torus transports along `ψ`. -/
theorem boundsDiskInComplement_mapHomeomorph_iff (ψ : R3 ≃ₜ R3) (α : ClosedCurve standard) :
    BoundsDiskInComplement (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ α) ↔
      BoundsDiskInComplement standard α := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨(homeomorphCMap ψ.symm).comp e, isBoundingDisk_mapHomeomorph_inv ψ α e he⟩
  · rintro ⟨e, he⟩
    exact ⟨(homeomorphCMap ψ).comp e, isBoundingDisk_mapHomeomorph ψ α e he⟩

/-- A curve on the image torus bounds a disc in the complement iff its pull-back does. -/
theorem boundsDiskInComplement_mapHomeomorphInv_iff (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) :
    BoundsDiskInComplement standard (ClosedCurve.mapHomeomorphInv ψ γ) ↔
      BoundsDiskInComplement (ParamTorus.mapHomeomorph ψ) γ := by
  have h := boundsDiskInComplement_mapHomeomorph_iff ψ (ClosedCurve.mapHomeomorphInv ψ γ)
  rw [ClosedCurve.mapHomeomorph_mapHomeomorphInv ψ γ] at h
  exact h.symm

/-- `ψ` carries the intersection of `α` and `β` to the intersection of their images, so
the cardinality of the intersection is unchanged. -/
theorem encard_inter_mapHomeomorph (ψ : R3 ≃ₜ R3) (α β : ClosedCurve standard) :
    Set.encard (Set.range (ClosedCurve.mapHomeomorph ψ α).γ ∩
        Set.range (ClosedCurve.mapHomeomorph ψ β).γ) =
      Set.encard (Set.range α.γ ∩ Set.range β.γ) := by
  rw [ClosedCurve.range_mapHomeomorph, ClosedCurve.range_mapHomeomorph,
    ← Set.image_inter ψ.injective]
  exact ψ.injective.encard_image _

/-- The same statement with the roles of a curve and its pull-back exchanged. -/
theorem encard_inter_mapHomeomorphInv (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) (β : ClosedCurve standard) :
    Set.encard (Set.range (ClosedCurve.mapHomeomorphInv ψ γ).γ ∩ Set.range β.γ) =
      Set.encard (Set.range γ.γ ∩ Set.range (ClosedCurve.mapHomeomorph ψ β).γ) := by
  have h := (encard_inter_mapHomeomorph ψ (ClosedCurve.mapHomeomorphInv ψ γ) β).symm
  rw [ClosedCurve.mapHomeomorph_mapHomeomorphInv ψ γ] at h
  exact h

/-- **Pardon's invariant `I(F, β)` is invariant under an ambient homeomorphism of `ℝ³`.**

For a homeomorphism `ψ` of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, the parametrised torus
`ParamTorus.mapHomeomorph ψ` (`(x,y) ↦ ψ (torusMap x y)`) is the image of the standard torus,
and the image curve `ClosedCurve.mapHomeomorph ψ β` lies on it.  Then
`I(ψ(F), ψ(β)) = I(F, β)`.

Proof: `ClosedCurve.mapHomeomorph` and its inverse `ClosedCurve.mapHomeomorphInv` give a
bijection between the closed curves on the two tori, and each of the three properties used in
the definition of `pardonsI` transports across it: `IsSimple` (injectivity),
`IsEssential`/winding vector (`ClosedCurve.isEssential_mapHomeomorph` and its inverse, via
`LiftOf.winding_congr`), and `BoundsDiskInComplement` (push the bounding disc forward by `ψ`;
pull it back by `ψ.symm` using that the carrier of `ParamTorus.mapHomeomorph ψ` is the image of
the carrier of `standard` under `ψ`).  Finally `Set.encard (range α ∩ range β)` is invariant
because a homeomorphism is a bijection on the ambient space. -/
theorem pardonsI_mapHomeomorph (ψ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (β : ClosedCurve standard) :
    pardonsI (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ β) =
      pardonsI standard β := by
  refine le_antisymm ?_ ?_
  · unfold pardonsI
    refine le_iInf fun α => ?_
    refine le_trans (pardonsI_le (P := ParamTorus.mapHomeomorph ψ)
      (β := ClosedCurve.mapHomeomorph ψ β)
      ((ClosedCurve.isSimple_mapHomeomorph_iff ψ α.1).mpr α.2.1)
      ((ClosedCurve.isEssential_mapHomeomorph_iff ψ α.1).mpr α.2.2.1)
      ((boundsDiskInComplement_mapHomeomorph_iff ψ α.1).mpr α.2.2.2)) ?_
    exact le_of_eq (encard_inter_mapHomeomorph ψ α.1 β)
  · unfold pardonsI
    refine le_iInf fun α' => ?_
    refine le_trans (pardonsI_le (P := standard) (β := β)
      ((ClosedCurve.isSimple_mapHomeomorphInv_iff ψ α'.1).mpr α'.2.1)
      ((ClosedCurve.isEssential_mapHomeomorphInv_iff ψ α'.1).mpr α'.2.2.1)
      ((boundsDiskInComplement_mapHomeomorphInv_iff ψ α'.1).mpr α'.2.2.2)) ?_
    exact le_of_eq (encard_inter_mapHomeomorphInv ψ α'.1 β)

end

end Work.CoreTopology
