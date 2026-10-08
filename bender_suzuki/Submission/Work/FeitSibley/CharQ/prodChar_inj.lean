import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.CharCore.irr_orthonormal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.prodChar_inj`

The tensor character `prodChar h lam theta` of `Q = S × Q₁` determines its two factors when
`lam ∈ Irr S` and `theta ∈ Irr Q₁`.  Indeed, transported along the isomorphism
`prodIso : ↥h.S × ↥h.Q1 ≃* ↥h.Q`, the character inner product *factors*:

`⟨prodChar lam theta, prodChar lam' theta'⟩ = ⟨lam, lam'⟩ * ⟨theta, theta'⟩`.

Since `⟨lam, lam'⟩` and `⟨theta, theta'⟩` are each `1` when the arguments are equal and `0`
otherwise (orthonormality of the irreducible characters, `Work.CharCore.irr_orthonormal`), the
product is `1` only when both factors agree.

The two generic ingredients are proved below:
* `cfInner_comp_equiv` — `cfInner` is invariant under reindexing along an equivalence;
* `cfInner_prod` — `cfInner` is multiplicative on a product of two finite types.
-/

noncomputable section

namespace Work.FeitSibley.CharQ

/-- Reindexing the character inner product along a bijection: if `f, f'` are functions on `α`
and `e : α ≃ β`, then the inner product of the pullbacks `f ∘ e.symm`, `f' ∘ e.symm` on `β`
equals the inner product of `f, f'` on `α`. -/
theorem cfInner_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f f' : α → ℂ) :
    Work.CharCore.cfInner (fun b => f (e.symm b)) (fun b => f' (e.symm b))
      = Work.CharCore.cfInner f f' := by
  have hsum : (∑ b : β, f (e.symm b) * starRingEnd ℂ (f' (e.symm b)))
      = ∑ a : α, f a * starRingEnd ℂ (f' a) :=
    Equiv.sum_comp e.symm (fun a => f a * starRingEnd ℂ (f' a))
  rw [Work.CharCore.cfInner, Work.CharCore.cfInner, Fintype.card_congr e, hsum]

/-- The character inner product is multiplicative on a product of two finite types:
`⟨f ⊗ g, f' ⊗ g'⟩ = ⟨f, f'⟩ * ⟨g, g'⟩`, where `(f ⊗ g) (a, b) = f a * g b`. -/
theorem cfInner_prod {α β : Type*} [Fintype α] [Fintype β]
    (f f' : α → ℂ) (g g' : β → ℂ) :
    Work.CharCore.cfInner (fun p : α × β => f p.1 * g p.2)
      (fun p : α × β => f' p.1 * g' p.2)
      = Work.CharCore.cfInner f f' * Work.CharCore.cfInner g g' := by
  have hsum : (∑ p : α × β, (f p.1 * g p.2) * starRingEnd ℂ (f' p.1 * g' p.2))
      = (∑ a : α, f a * starRingEnd ℂ (f' a)) * (∑ b : β, g b * starRingEnd ℂ (g' b)) := by
    rw [Fintype.sum_prod_type]
    simp only [map_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Work.CharCore.cfInner, Work.CharCore.cfInner, Work.CharCore.cfInner, Fintype.card_prod, hsum,
    Nat.cast_mul, mul_inv]
  ring

theorem prodChar_inj {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {lam lam' : ↥h.S → ℂ} {theta theta' : ↥h.Q1 → ℂ}
    (hl : lam ∈ Work.CharCore.Irr ↥h.S) (hl' : lam' ∈ Work.CharCore.Irr ↥h.S)
    (ht : theta ∈ Work.CharCore.Irr ↥h.Q1) (ht' : theta' ∈ Work.CharCore.Irr ↥h.Q1)
    (heq : h.prodChar lam theta = h.prodChar lam' theta') : lam = lam' ∧ theta = theta' := by
  -- `prodChar` transported along `prodIso` is the pointwise product of the two factors, so the
  -- inner product of two such characters factors into the inner product of the factors.
  have hfac : ∀ (l l' : ↥h.S → ℂ) (t t' : ↥h.Q1 → ℂ),
      Work.CharCore.cfInner (h.prodChar l t) (h.prodChar l' t')
        = Work.CharCore.cfInner l l' * Work.CharCore.cfInner t t' := by
    intro l l' t t'
    have h1 := cfInner_comp_equiv (e := h.prodIso.toEquiv)
      (f := fun p : ↥h.S × ↥h.Q1 => l p.1 * t p.2)
      (f' := fun p : ↥h.S × ↥h.Q1 => l' p.1 * t' p.2)
    exact h1.trans (cfInner_prod l l' t t')
  -- Evaluating on the diagonal, the left-hand side is `1` (orthonormality), so the product of
  -- the two pairwise inner products is `1`.
  have hprod : Work.CharCore.cfInner lam lam' * Work.CharCore.cfInner theta theta' = 1 := by
    rw [← hfac lam lam' theta theta', heq, hfac lam' lam' theta' theta',
      Work.CharCore.irr_orthonormal lam' lam' hl' hl',
      Work.CharCore.irr_orthonormal theta' theta' ht' ht']
    simp
  -- Each factor is `1` (equal) or `0` (unequal): their product being `1` forces both equal.
  rw [Work.CharCore.irr_orthonormal lam lam' hl hl',
      Work.CharCore.irr_orthonormal theta theta' ht ht'] at hprod
  by_cases hll : lam = lam'
  · by_cases htt : theta = theta'
    · exact ⟨hll, htt⟩
    · rw [if_pos hll, if_neg htt, mul_zero] at hprod
      exact absurd hprod zero_ne_one
  · rw [if_neg hll, zero_mul] at hprod
    exact absurd hprod zero_ne_one

end Work.FeitSibley.CharQ
