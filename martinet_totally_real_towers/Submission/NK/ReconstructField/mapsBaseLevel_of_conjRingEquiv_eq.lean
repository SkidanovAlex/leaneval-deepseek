import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.Reconstruct.Transport

namespace NK.ReconstructField

/-- **Packaging `MapsBaseLevel` from the conjugation identity.**

Let `M ⊆ K₁'` be a finite normal level with `τ : M ≃+* levelMap ϕ M` a ring isomorphism.
If conjugating the Galois group `Gal(M/K₁)` by `τ` reproduces the isomorphism of levels
`levelMapEquiv hϕ M : Gal(M/K₁) ≃* Gal(levelMap ϕ M/K₂)` induced by `ϕ` itself, then `τ` must
carry the embedded copy of `K₁` into the embedded copy of `K₂` and vice versa.

The point is that, by Galois theory, an element of `M` lies in `K₁` exactly when it is fixed by all
of `Gal(M/K₁)` (and similarly an element of `levelMap ϕ M` lies in `K₂` exactly when it is fixed by
all of `Gal(levelMap ϕ M/K₂)`); the conjugation identity transfers the fixed-point statement from one
side to the other. -/
theorem mapsBaseLevel_of_conjRingEquiv_eq {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (M : IntermediateField K₁ K₁') [FiniteDimensional K₁ M] [Normal K₁ M] [NumberField ↥M]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ M)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ M)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ M)]
    (τ : ↥M ≃+* ↥(NK.Reconstruct.levelMap ϕ M))
    (hconj : ∀ g : Gal(↥M/K₁),
      NK.Reconstruct.conjRingEquiv τ g.toRingEquiv =
        (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv) :
    NK.Reconstruct.MapsBaseLevel M (NK.Reconstruct.levelMap ϕ M) τ := by
  have hgalM : IsGalois K₁ ↥M :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hgalL : IsGalois K₂ ↥(NK.Reconstruct.levelMap ϕ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  constructor
  · -- `τ` sends the copy of `K₁` inside `M` into the copy of `K₂` inside `levelMap ϕ M`.
    intro a
    have hmem : τ (algebraMap K₁ ↥M a) ∈
        Set.range (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ M)) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro f
      obtain ⟨g, rfl⟩ := (NK.Reconstruct.levelMapEquiv hϕ M).surjective f
      have hpt := DFunLike.congr_fun (hconj g) (τ (algebraMap K₁ ↥M a))
      rw [show ((NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv) (τ (algebraMap K₁ ↥M a))
            = (NK.Reconstruct.levelMapEquiv hϕ M g) (τ (algebraMap K₁ ↥M a)) from rfl,
          NK.Reconstruct.conjRingEquiv_apply, RingEquiv.symm_apply_apply,
          AlgEquiv.coe_ringEquiv, g.commutes a] at hpt
      exact hpt.symm
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  · -- Conversely, `τ⁻¹` sends the copy of `K₂` inside `levelMap ϕ M` into the copy of `K₁` inside `M`.
    intro b
    have hmem : τ.symm (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ M) b) ∈
        Set.range (algebraMap K₁ ↥M) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro g
      have key : τ (g (τ.symm (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ M) b))) =
          algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ M) b := by
        have h := DFunLike.congr_fun (hconj g)
          (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ M) b)
        simp only [NK.Reconstruct.conjRingEquiv_apply, AlgEquiv.coe_ringEquiv] at h
        rw [(NK.Reconstruct.levelMapEquiv hϕ M g).commutes b] at h
        exact h
      apply τ.injective
      rw [key, RingEquiv.apply_symm_apply]
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩

end NK.ReconstructField
