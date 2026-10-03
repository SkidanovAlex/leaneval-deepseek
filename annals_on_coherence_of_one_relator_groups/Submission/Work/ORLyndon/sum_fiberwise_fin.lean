import Mathlib

namespace Work.ORLyndon

theorem sum_fiberwise_fin {ι κ M : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
    (s : Finset ι) (r : ι → κ) {n : ℕ} (g : Fin n → κ)
    (hinj : Function.Injective g) (hcover : ∀ x ∈ s, ∃ i, g i = r x) (f : ι → M) :
    ∑ i : Fin n, ∑ x ∈ s.filter (fun x => r x = g i), f x = ∑ x ∈ s, f x := by
  -- Every `r x` with `x ∈ s` lies in the image of `g`.
  have hrt : ∀ x ∈ s, r x ∈ Finset.univ.image g := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  -- Reindex the sum over the image of `g` (injective) back to `Fin n`.
  have hinjOn : Set.InjOn g ↑(Finset.univ : Finset (Fin n)) :=
    fun a _ b _ h => hinj h
  have h2 := Finset.sum_image (s := (Finset.univ : Finset (Fin n))) (g := g) hinjOn
      (f := fun j : κ => ∑ x ∈ s.filter (fun x => r x = j), f x)
  -- Partition `s` into the fibers of `r` over the image of `g`.
  have h1 := Finset.sum_fiberwise_of_maps_to (s := s) (g := r) hrt f
  exact h2.symm.trans h1

end Work.ORLyndon
