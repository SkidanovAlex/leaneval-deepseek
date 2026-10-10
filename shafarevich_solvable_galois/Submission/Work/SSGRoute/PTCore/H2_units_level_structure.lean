import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.SSGRoute.PT.H2Transfer
import Submission.Work.SSGRoute.PTCore.H2_level_cover_alt
import Submission.Work.SSGRoute.PTCore.H2_level_mono
import Submission.Work.SSGRoute.PTCore.H2_level_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTCore

open Work.AbsoluteKummer

/-- The comparison isomorphism between Mathlib's `H²` and the cocycle model `LevelH2`. -/
noncomputable def h2LevelEquiv {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2 ≃+ LevelH2 L :=
  Classical.choice (Work.SSGRoute.groupCohomology_two_iso_cocycles ℤ (LevelGal L)
    (Rep.ofAlgebraAutOnUnits F ↥L))

theorem H2_units_level_structure {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)] :
    ∃ φ : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
        groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2 →+
          Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F) (Additive (AlgebraicClosure F)ˣ),
      (∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
        Function.Injective (φ L)) ∧
      (∀ (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F))
        (h : (L : IntermediateField F (AlgebraicClosure F)) ≤ L'),
        Set.range (φ L) ⊆ Set.range (φ L')) ∧
      (∀ x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F)
          (Additive (AlgebraicClosure F)ˣ),
        ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F), x ∈ Set.range (φ L)) := by
  classical
  refine ⟨fun L => (psiTilde L).comp ((h2LevelEquiv L).toAddMonoidHom), ?_, ?_, ?_⟩
  · intro L
    show Function.Injective (fun x => psiTilde L (h2LevelEquiv L x))
    exact (H2_level_injective L (H2_level_hilbert90 L)).comp (h2LevelEquiv L).injective
  · intro L L' h y hy
    have hy' : y ∈ Set.range (psiTilde L) := by
      obtain ⟨z, hz⟩ := hy
      exact ⟨h2LevelEquiv L z, hz⟩
    obtain ⟨y', hy''⟩ := H2_level_mono L L' h hy'
    obtain ⟨w, hw⟩ := (h2LevelEquiv L').surjective y'
    refine ⟨w, ?_⟩
    show psiTilde L' (h2LevelEquiv L' w) = y
    rw [hw, hy'']
  · intro x
    obtain ⟨L, hL⟩ := H2_level_cover_alt x
    obtain ⟨y, hy⟩ := hL
    obtain ⟨z, hz⟩ := (h2LevelEquiv L).surjective y
    exact ⟨L, z, by
      show psiTilde L (h2LevelEquiv L z) = x
      rw [hz, hy]⟩

end Work.SSGRoute.PTCore
