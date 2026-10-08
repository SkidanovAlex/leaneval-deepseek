import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_l22c1Defs

namespace Work.BG

/-- **Fibre-counting identity** (pure `Finset` bookkeeping, no group structure needed).

For a `Finset` `s`, a function `f : α → β` into a finite type and any `h : β → ℂ`, the sum of
`h` over the values `f a` (`a ∈ s`) equals the sum over `b : β` of `h b` weighted by the number
of `a ∈ s` with `f a = b`.

Proof: `Finset.sum_fiberwise` writes `∑ a ∈ s, h (f a)` as `∑ b, ∑ a ∈ s.filter (f · = b), h (f a)`,
and on each fibre `f a = b`, so `h (f a) = h b` and the inner sum is
`(s.filter (f · = b)).card` copies of `h b`. -/
lemma sum_card_fiber_mul {α β : Type} [Fintype β] [DecidableEq β] (s : Finset α)
    (f : α → β) (h : β → ℂ) :
    ∑ b : β, ((s.filter (fun a => f a = b)).card : ℂ) * h b = ∑ a ∈ s, h (f a) := by
  rw [← Finset.sum_fiberwise s f (fun a => h (f a))]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Pair counting for a `Finset` in a finite group.**  For a `Finset` `X` of a finite group
`G` and a class function `ψ` on `G`, the double sum `Σ_{x,y ∈ X} ψ(x*y)` is the sum over
`g : G` of `ψ g` weighted by the number of pairs `(x,y) ∈ X × X` with `x*y = g`.

Pure `Finset` bookkeeping: expand `X ×ˢ X` with `Finset.sum_product`, then regroup by the
fibre of `p ↦ p.1 * p.2` with `Finset.sum_fiberwise`. -/
theorem s02_pairCount_sum {G : Type} [Group G] [Fintype G] (X : Finset G)
    (ψ : OddOrder.RepresentationTheory.ClassFunction G ℂ) :
    ∑ x ∈ X, ∑ y ∈ X, ψ (x * y) =
      ∑ g : G, ((Work.BG.pairSet X g).card : ℂ) * ψ g := by
  classical
  -- Step 1: collect the double sum over `X × X`.
  have hL : (∑ x ∈ X, ∑ y ∈ X, ψ (x * y)) = ∑ p ∈ X ×ˢ X, ψ (p.1 * p.2) := by
    rw [Finset.sum_product]
  -- Step 2: regroup `∑ p ∈ X ×ˢ X, ψ (p.1 * p.2)` by the value of `p ↦ p.1 * p.2`.
  rw [hL, ← sum_card_fiber_mul (X ×ˢ X) (fun p : G × G => p.1 * p.2) (fun g => ψ g)]
  -- Step 3: identify the fibre `{p ∈ X ×ˢ X | p.1 * p.2 = g}` with `pairSet X g`.
  apply Finset.sum_congr rfl
  intro g _
  congr 1

end Work.BG
