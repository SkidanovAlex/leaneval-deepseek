import Mathlib
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.lensSpace_homeomorph_projective

namespace Work.Drive

noncomputable section

open scoped Topology

/-!
# The capping model of `Y` as `(0,∞) × ℝP³`, with the *same* projection map

`Submission.Work.Drive.cappingSpace_homeomorph_prod` exhibits the four-dimensional capping space of
Hugelmeyer's fifth auxiliary result as `(0,∞) × LensSpace` (the explicit homeomorphism `Φ`, with
inverse `Ψ`), and `Submission.Work.Drive.lensSpace_homeomorph_projective` shows that the slice
`LensSpace = L(2,1)` is `ℝP³ = Projectivization ℝ (EuclideanSpace ℝ (Fin 4))`.  What those two files
do *not* provide is a *single* homeomorphism whose second coordinate is the map `F : LensSpace → ℝP³`
that the rest of the capping chapter uses, namely the one that makes the square

`S³ --phi--> LensSpace --F--> ℝP³`  and  `S³ --projOfUnitSphere--> ℝP³`

commute.  Here `phi` and `projOfUnitSphere` are quotient maps with the same fibres (the antipodal
pairs of `S³`), so such an `F` exists, is unique, continuous and bijective; and it is exactly the
`F` of the statement `exists_cappingModel_projectivization`.

The construction is explicit: on a class `q ∈ LensSpace` we choose a representative `surjInv` of `q`
under `phi` and project it to `ℝP³`, and conversely.

Together with `Φ` this gives the homeomorphism
`CappingSpace ≃ₜ (0,∞) × ℝP³`, `x ↦ ((Φ x).1, F ((Φ x).2))`, which is the precise form of
Hugelmeyer's Lemma 5 needed downstream: the `ℝP³`-coordinate is *the same* map `F` as on the slice.
-/

/-- **The fibres of `phi` and of `projOfUnitSphere` (the projection of the unit sphere) agree.**  Both
are `S³/{±1}`: `phi` is a quotient map for `LensSpace = L(2,1)` and `projOfUnitSphere` for `ℝP³`, and
the two identifications are the same antipodal identification of `S³`. -/
lemma phi_eq_iff_projOfUnitSphere (v w : unitSphere 3) :
    phi v = phi w ↔ projOfUnitSphere v = projOfUnitSphere w := by
  rw [phi_eq_iff, projOfUnitSphere_eq_iff]

/-- The descent of `projOfUnitSphere` through the quotient map `phi : S³ → LensSpace`: the map
`F : LensSpace → ℝP³` making `F ∘ phi = projOfUnitSphere`. -/
def lensToProj (q : LensSpace) : Projectivization ℝ (Eucl 3) :=
  projOfUnitSphere (Function.surjInv phi_surjective q)

/-- The inverse descent `ℝP³ → LensSpace`, obtained the same way from `projOfUnitSphere`. -/
def projToLens (p : Projectivization ℝ (Eucl 3)) : LensSpace :=
  phi (Function.surjInv surjective_projOfUnitSphere p)

/-- **`F` commutes with the two projections of `S³`.** -/
lemma lensToProj_phi (v : unitSphere 3) : lensToProj (phi v) = projOfUnitSphere v := by
  unfold lensToProj
  exact (phi_eq_iff_projOfUnitSphere _ _).mp (Function.surjInv_eq phi_surjective (phi v))

/-- `projToLens` is a right inverse of `lensToProj`. -/
lemma lensToProj_projToLens (p : Projectivization ℝ (Eucl 3)) :
    lensToProj (projToLens p) = p := by
  have hphi : phi (Function.surjInv phi_surjective (projToLens p))
      = phi (Function.surjInv surjective_projOfUnitSphere p) := by
    rw [Function.surjInv_eq phi_surjective (projToLens p)]
    rfl
  unfold lensToProj
  rw [(phi_eq_iff_projOfUnitSphere _ _).mp hphi]
  exact Function.surjInv_eq surjective_projOfUnitSphere p

/-- `projToLens` is a left inverse of `lensToProj`. -/
lemma projToLens_lensToProj (q : LensSpace) : projToLens (lensToProj q) = q := by
  have hproj : projOfUnitSphere (Function.surjInv surjective_projOfUnitSphere (lensToProj q))
      = projOfUnitSphere (Function.surjInv phi_surjective q) := by
    rw [Function.surjInv_eq surjective_projOfUnitSphere (lensToProj q)]
    rfl
  unfold projToLens
  rw [(phi_eq_iff_projOfUnitSphere _ _).mpr hproj]
  exact Function.surjInv_eq phi_surjective q

/-- `lensToProj` is continuous: it descends the continuous `projOfUnitSphere` through the quotient map
`phi`. -/
lemma continuous_lensToProj : Continuous lensToProj := by
  rw [isQuotientMap_phi.continuous_iff]
  exact continuous_projOfUnitSphere.congr (fun v => (lensToProj_phi v).symm)

/-- **`projToLens` commutes with the two projections of `S³`**, the mirror image of
`lensToProj_phi`. -/
lemma projToLens_projOfUnitSphere (v : unitSphere 3) : projToLens (projOfUnitSphere v) = phi v := by
  unfold projToLens
  exact (phi_eq_iff_projOfUnitSphere _ _).mpr
    (Function.surjInv_eq surjective_projOfUnitSphere (projOfUnitSphere v))

/-- `projToLens` is continuous: it descends the continuous `phi` through the quotient map
`projOfUnitSphere`. -/
lemma continuous_projToLens : Continuous projToLens := by
  rw [isQuotientMap_projOfUnitSphere.continuous_iff]
  exact continuous_phi.congr (fun v => (projToLens_projOfUnitSphere v).symm)

/-- **The slice of the capping is `ℝP³`, through the map `lensToProj`** that is compatible with the
projections of `S³`. -/
def lensSpaceHomeoProj : LensSpace ≃ₜ Projectivization ℝ (Eucl 3) :=
  Homeomorph.mk ⟨lensToProj, projToLens, projToLens_lensToProj, lensToProj_projToLens⟩
    continuous_lensToProj continuous_projToLens

/-- The capping space as `(0,∞) × LensSpace`, through the explicit maps `Φ` and `Ψ` of
`Submission.Work.Drive.cappingSpace_homeomorph_prod`. -/
def cappingSpaceHomeoSlice : CappingSpace ≃ₜ Set.Ioi (0 : ℝ) × LensSpace :=
  Homeomorph.mk ⟨Φ, Ψ, Ψ_Φ, Φ_Ψ⟩ continuous_Φ continuous_Ψ

/-- **The four-dimensional capping space is `(0,∞) × ℝP³`, the projective coordinate being read off
by the same map `F` as on the slice.** -/
def cappingSpaceHomeoProj :
    CappingSpace ≃ₜ Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3) :=
  cappingSpaceHomeoSlice.trans
    ((Homeomorph.refl (Set.Ioi (0 : ℝ))).prodCongr lensSpaceHomeoProj)

theorem exists_cappingModel_projectivization :
    ∃ (F : Work.Drive.LensSpace → Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (e : Work.Drive.CappingSpace ≃ₜ
        (Set.Ioi (0:ℝ)) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))),
      (∀ v : Work.Drive.unitSphere 3, F (Work.Drive.phi v) = Work.Drive.projOfUnitSphere v) ∧
      (∀ x : Work.Drive.CappingSpace, e x = ((Work.Drive.Φ x).1, F ((Work.Drive.Φ x).2))) ∧
      Continuous F ∧ Function.Bijective F := by
  refine ⟨lensToProj, cappingSpaceHomeoProj, lensToProj_phi, ?_, continuous_lensToProj, ?_⟩
  · intro x
    rfl
  · refine ⟨?_, ?_⟩
    · intro q₁ q₂ h
      obtain ⟨v₁, rfl⟩ := phi_surjective q₁
      obtain ⟨v₂, rfl⟩ := phi_surjective q₂
      rw [lensToProj_phi, lensToProj_phi] at h
      exact (phi_eq_iff_projOfUnitSphere _ _).mpr h
    · intro p
      obtain ⟨v, hv⟩ := surjective_projOfUnitSphere p
      exact ⟨phi v, by rw [lensToProj_phi, hv]⟩

end

end Work.Drive
