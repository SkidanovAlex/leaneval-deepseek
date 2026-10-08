import Mathlib
import Submission.Work.BG.Defs

namespace Work.BG

theorem l41iiiInvSum {α : Type*} [DecidableEq α] (s : Finset α) (g : α → α)
    (f : α → ℂ) (p : α → Prop) [DecidablePred p]
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) (hp : ∀ a ∈ s, p (g a) ↔ ¬ p a) :
    ∑ a ∈ s, f a = ∑ a ∈ s.filter p, (f a + f (g a)) := by
  -- `g` pairs the elements of `s.filter p` with those of `s.filter (¬ p)`.
  have hfilter : s.filter (fun x => ¬ p x) = (s.filter p).image g := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hxs, hpx⟩
      exact ⟨g x, ⟨hmem x hxs, (hp x hxs).mpr hpx⟩, hinv x hxs⟩
    · rintro ⟨a, ⟨has, hpa⟩, rfl⟩
      exact ⟨hmem a has, fun h => (hp a has).mp h hpa⟩
  -- On `s.filter p` the map `g` is injective (it is an involution on `s`).
  have hinj : Set.InjOn g (↑(s.filter p) : Set α) := by
    intro a ha a' ha' h
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ha'
    rw [← hinv a ha.1, h, hinv a' ha'.1]
  rw [Finset.sum_add_distrib, ← Finset.sum_image hinj, ← hfilter]
  exact (Finset.sum_filter_add_sum_filter_not s p f).symm

end Work.BG
