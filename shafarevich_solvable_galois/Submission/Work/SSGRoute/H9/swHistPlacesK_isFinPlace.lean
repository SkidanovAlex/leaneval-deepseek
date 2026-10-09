import Mathlib
import Submission.Work.SSGRoute.H9.swHistK
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise

/-- **A representative of a `K`-class above a finite place is finite.**  The elements of
`kleadReps K S` are the `K`-conjugates of the elements of `S`, and conjugation by `G_k` does not
change the prime of `k` a place lies over (`Work.SSGRoute.comap_algebraMap_smul`), hence preserves
finiteness (`Work.SSGRoute.isFinPlace_smul_iff`). -/
theorem kleadReps_isFinPlace {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    ∀ A ∈ Work.SSGRoute.ZDataMup.kleadReps K S, SSGRoute.IsFinPlace k A := by
  classical
  intro A hA
  obtain ⟨p', hp'mem, hp'eq⟩ := Finset.mem_image.mp hA
  obtain ⟨hQmem, -⟩ := Finset.mem_product.mp hp'mem
  rw [← hp'eq]
  exact (Work.SSGRoute.isFinPlace_smul_iff p'.1 (Work.SSGRoute.ZDataMup.galLift K p'.2)).mpr
    (hS p'.1 hQmem)

/-- **Every element of the place set `T_n = histPlaces K S f` is a finite place**, provided the
places of `S` and the first components of the classes `f j` are finite.  This is because `T_n` is the
union of the `K`-conjugates of the elements of `S` and of the `(f j).1`. -/
theorem histPlaces_isFinPlace {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) {n : ℕ}
    (g : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hS : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hf : ∀ j : Fin n, SSGRoute.IsFinPlace k ((g j).1)) :
    ∀ A ∈ Work.SSGRoute.ZDataMup.histPlaces K S g, SSGRoute.IsFinPlace k A := by
  classical
  intro A hA
  simp only [Work.SSGRoute.ZDataMup.histPlaces] at hA
  rcases Finset.mem_union.mp hA with hA | hA
  · exact kleadReps_isFinPlace K S hS A hA
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hA
    exact kleadReps_isFinPlace K {((g j).1)} (fun B hB => by
      rw [Finset.mem_singleton.mp hB]
      exact hf j) A hj

theorem swHistPlacesK_isFinPlace {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hf : ∀ j < m, SSGRoute.IsFinPlace k ((f j).1)) :
    ∀ A ∈ Work.SSGRoute.H9.histPlacesK (p := p) K S ζ hζK hζ m f,
      SSGRoute.IsFinPlace k A := by
  classical
  intro A hA
  rw [Work.SSGRoute.H9.histPlacesK] at hA
  exact histPlaces_isFinPlace K S
    (Work.SSGRoute.H9.histClass (p := p) K ζ hζK hζ (fun j : Fin m => f j)) hSfin
    (fun j => hf (j : ℕ) j.2) A hA

end Work.SSGRoute.H9
