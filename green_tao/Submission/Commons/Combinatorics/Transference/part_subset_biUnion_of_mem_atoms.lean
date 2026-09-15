import Mathlib.Data.Finset.Union

namespace Commons.Combinatorics.Transference

theorem part_subset_biUnion_of_mem_atoms {X : Type*} [Fintype X] [DecidableEq X]
    (part : X → Finset X) (heq : ∀ x y : X, y ∈ part x → part y = part x)
    {s : Finset (Finset X)} (hs : ∀ A ∈ s, A ∈ Finset.univ.image part) :
    ∀ x ∈ s.biUnion (fun A => A), part x ⊆ s.biUnion (fun A => A) := by
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨A, hAs, hxA⟩ := hx
  obtain ⟨a, -, hAa⟩ := Finset.mem_image.mp (hs A hAs)
  -- hAa : part a = A
  have hxpa : x ∈ part a := by rw [hAa]; exact hxA
  have hpx : part x = A := by rw [heq a x hxpa, hAa]
  intro y hy
  rw [Finset.mem_biUnion]
  exact ⟨part x, by rw [hpx]; exact hAs, hy⟩

end Commons.Combinatorics.Transference