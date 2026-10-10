import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.H9.swHistK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise

theorem swHistPlacesK_covers {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) {B : ValuationSubring Ω}
    (hB : (∃ A ∈ S, SSGRoute.IsConjPlace k A B) ∨
      (∃ j : Fin m, SSGRoute.IsConjPlace k ((f j).1) B)) :
    ∃ A' ∈ Work.SSGRoute.H9.histPlacesK (p := p) K S ζ hζK hζ m f,
      Work.SSGRoute.gesKConj K A' B := by
  classical
  -- `histPlacesK` is the union of `kleadReps K S` with the `K`-classes above the prefix of escape
  -- primes, so it suffices to find a `k`-conjugate of `B` inside one of those pieces.
  rcases hB with ⟨A, hA, hAB⟩ | ⟨j, hj⟩
  · obtain ⟨A', hA', hKA'⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA hAB
    refine ⟨A', ?_, hKA'⟩
    simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, histClass,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inl hA'
  · obtain ⟨A', hA', hKA'⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K
      ({((f j).1)} : Finset (ValuationSubring Ω)) (Finset.mem_singleton_self _) hj
    refine ⟨A', ?_, hKA'⟩
    simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, histClass,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, hA'⟩

end Work.SSGRoute.H9
