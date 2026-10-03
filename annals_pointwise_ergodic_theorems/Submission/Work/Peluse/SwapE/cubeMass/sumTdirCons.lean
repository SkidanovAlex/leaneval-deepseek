import Mathlib
import Submission.Work.Peluse.SwapE.cubeMass.Defs

namespace Work.Peluse.SwapE.cubeMass

open scoped BigOperators

/-- Reindexing lemma for the product ``Fintype.piFinset``: the bijection
`(δ, n) ↦ Fin.cons δ n` between `s × (Fin d → ℤ)` and `Fin (d+1) → ℤ` (with inverse
`u ↦ (u 0, Fin.tail u)`) identifies the `(d+1)`-fold product with the `d`-fold product,
carrying the first coordinate out. -/
lemma sum_piFinset_succ {s : Finset ℤ} {M : Type} [AddCommMonoid M] (d : ℕ)
    (F : (Fin (d + 1) → ℤ) → M) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin (d + 1) => s), F u)
      = ∑ δ ∈ s, ∑ n ∈ Fintype.piFinset (fun _ : Fin d => s), F (Fin.cons δ n) := by
  rw [show Fintype.piFinset (fun _ : Fin (d + 1) => s)
      = (s ×ˢ Fintype.piFinset (fun _ : Fin d => s)).image
          (fun p : ℤ × (Fin d → ℤ) => Fin.cons p.1 p.2) from ?_]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
    · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
      simp only [Prod.mk.injEq]
      exact ⟨by have := congrFun h 0; simpa [Fin.cons_zero] using this,
        by funext i; have := congrFun h i.succ; simpa [Fin.cons_succ] using this⟩
  · ext u
    simp only [Finset.mem_image, Finset.mem_product, Fintype.mem_piFinset]
    constructor
    · intro hu
      exact ⟨(u 0, Fin.tail u), ⟨hu 0, fun i => hu i.succ⟩,
        by simpa using (Fin.cons_self_tail u).symm⟩
    · rintro ⟨⟨δ, n⟩, ⟨hδ, hn⟩, rfl⟩ i
      refine Fin.cases ?_ ?_ i
      · simpa using hδ
      · intro j; simpa using hn j

theorem sumTdirCons (Card d : ℕ) {M : Type} [AddCommMonoid M] (F : (Fin (d + 1) → ℤ) → M) :
    (∑ u ∈ Work.Peluse.SwapE.Tdir Card (d + 1), F u)
      = ∑ δ ∈ Work.Peluse.SwapE.sCard Card,
          ∑ n ∈ Work.Peluse.SwapE.Tdir Card d, F (Fin.cons δ n) := by
  simp only [Work.Peluse.SwapE.Tdir]
  exact sum_piFinset_succ d F

end Work.Peluse.SwapE.cubeMass
