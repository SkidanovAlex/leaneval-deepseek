import Mathlib
import Submission.Work.BG.Defs

/-!
# Area BG: `l41iiiInvAlg` — the mod-2 integrality step behind Lemma 4.1 (iii)

A finite set `s` carrying a fixed-point-free involutive pairing `g` (`g ∘ g = id` on `s`,
`g s ⊆ s`) with a sign condition `p (g a) ↔ ¬ p a` splits into the two halves
`s.filter p` and `s.filter (¬p)`, exchanged by `g`.  Consequently, for any `g`-invariant
`f : α → ℂ` whose values on `s` are algebraic integers,

`∑_{a ∈ s} f a = 2 * ∑_{a ∈ s.filter p} f a`,

a sum of algebraic integers doubled, so the total is `0` modulo `2` in the sense of
`Work.BG.AlgIntModTwo`.  This is the arithmetic content of the congruence
`χ ≡ ∑_{ν ∈ 𝒮'(χ)} ν̂ (mod 2)` of Bender–Glauberman 1981, Lemma 4.1 (iii), reduced to the
fact that the index set `𝒮'(χ)` meets every `g`-orbit in exactly one point.
-/

namespace Work.BG

theorem l41iiiInvAlg {α : Type*} [DecidableEq α] (s : Finset α) (g : α → α)
    (f : α → ℂ) (p : α → Prop) [DecidablePred p]
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) (hp : ∀ a ∈ s, p (g a) ↔ ¬ p a)
    (hf : ∀ a ∈ s, f (g a) = f a) (hint : ∀ a ∈ s, IsIntegral ℤ (f a)) :
    AlgIntModTwo (∑ a ∈ s, f a) 0 := by
  classical
  -- `g` is injective on `s.filter p`, its own inverse being `g` again.
  have hinj : Set.InjOn g ↑(s.filter p) := by
    intro x hx y hy hxy
    have hx' : x ∈ s := (Finset.mem_filter.mp hx).1
    have hy' : y ∈ s := (Finset.mem_filter.mp hy).1
    calc x = g (g x) := (hinv x hx').symm
      _ = g (g y) := by rw [hxy]
      _ = y := hinv y hy'
  -- `g` exchanges the two halves of the partition of `s` by `p`.
  have himage : s.filter (fun a => ¬ p a) = (s.filter p).image g := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ s := (Finset.mem_filter.mp hx).1
      have hnx : ¬ p x := (Finset.mem_filter.mp hx).2
      exact Finset.mem_image.mpr
        ⟨g x, Finset.mem_filter.mpr ⟨hmem x hx', (hp x hx').mpr hnx⟩, hinv x hx'⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      have hy' : y ∈ s := (Finset.mem_filter.mp hy).1
      have hyp : p y := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [← hyx]; exact hmem y hy'
      · rw [← hyx]; exact fun hg => (hp y hy').mp hg hyp
  -- Split the sum along `p`; the `¬p` half is the `g`-image of the `p` half.
  have hmain : ∑ a ∈ s, f a = 2 * ∑ a ∈ s.filter p, f a := by
    rw [← Finset.sum_filter_add_sum_filter_not s p f]
    rw [himage, Finset.sum_image hinj, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have ha' : a ∈ s := (Finset.mem_filter.mp ha).1
    rw [hf a ha']
    ring
  rw [hmain]
  exact AlgIntModTwo.mul_two
    (IsIntegral.sum (fun a => f a) (fun a ha => hint a (Finset.mem_filter.mp ha).1))

end Work.BG
