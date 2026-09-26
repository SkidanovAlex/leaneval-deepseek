import Submission.Work.ImageAggregate
import Submission.Work.NielsenEndCancel
import Submission.Work.AggregateCoordinate

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# The strict-phase attachment (strict sibling of `balanced_attach_*`)

`ImageAggregate.aggregate_element_dichotomy` gives, for a confined interior
factor of the aggregate, the *strict* disjunct
`norm (es[j-1] · es[j]) < norm (es[j-1])` (or the right-handed mirror):
a product of two adjacent factors is strictly shorter than one of them.  When
the two factors are basis images up to sign, `es[j-1] = ±w_p`, `es[j] = ±w_q`
(`p ≠ q`), this inequality is one of the four end-cancellation inequalities of
`NielsenEndCancel.end_cancel_shortens` (up to inverting the whole product,
which preserves the norm): each case attaches exactly one elementary move
(`rho`/`rhoNeg`/`lam`/`lamNeg` on the shortened coordinate) that strictly
decreases `N`.

* `strict_attach_left` — from the strict-left disjunct at `(es[j-1], es[j])`
  and the factor orientations, `∃ γ ∈ AutClosure n, N (α·γ) < N α`;
* `strict_attach_right` — the mirror at `(es[j], es[j+1])`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The norm is unchanged when the whole product is inverted:
`|a · b| = |b⁻¹ · a⁻¹|`. -/
lemma norm_mul_flip {n : ℕ} (a b : FreeGroup (Fin n)) :
    FreeGroup.norm (a * b) = FreeGroup.norm (b⁻¹ * a⁻¹) := by
  rw [← norm_inv_eq (x := a * b)]
  rw [mul_inv_rev]

/-- **Strict attachment (left).**  Strictly more than enough of `es[j]`'s
letters cancel against `es[j-1]` (`norm (es[j-1]·es[j]) < norm (es[j-1])`).
If the two factors are basis images up to sign, `es[j-1] = ±w_p`,
`es[j] = ±w_q` with `p ≠ q`, then one of the four elementary moves shortens
`w_p`: `∃ γ ∈ AutClosure n, N (α·γ) < N α`. -/
theorem strict_attach_left {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hmj : j - 1 < es.length)
    {p q : Fin n} (hneq : p ≠ q)
    (hp : es[j - 1] = α (FreeGroup.of p) ∨ es[j - 1] = (α (FreeGroup.of p))⁻¹)
    (hq : es[j] = α (FreeGroup.of q) ∨ es[j] = (α (FreeGroup.of q))⁻¹)
    (hstrict : FreeGroup.norm ((es[j - 1]) * (es[j])) < FreeGroup.norm (es[j - 1])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · -- es[j-1] = w_p, es[j] = w_q : |w_p · w_q| < |w_p|
      have h2 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact end_cancel_shortens n α (i := p) (j := q) hneq (Or.inr (Or.inl h2))
    · -- es[j-1] = w_p, es[j] = w_q⁻¹ : |w_p · w_q⁻¹| < |w_p|
      have h1 : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact end_cancel_shortens n α (i := p) (j := q) hneq (Or.inl h1)
  · rcases hq with hq | hq
    · -- es[j-1] = w_p⁻¹, es[j] = w_q : |w_p⁻¹ · w_q| < |w_p|
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hp, hq] at hstrict
        rwa [norm_inv_eq] at hstrict
      have h3 : FreeGroup.norm ((α (FreeGroup.of q))⁻¹ * α (FreeGroup.of p))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        have hflip : FreeGroup.norm ((α (FreeGroup.of q))⁻¹ * α (FreeGroup.of p)) =
            FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of q)) := by
          simpa using (norm_mul_flip (a := (α (FreeGroup.of p))⁻¹)
            (b := α (FreeGroup.of q))).symm
        rw [hflip]
        exact hs
      exact end_cancel_shortens n α (i := p) (j := q) hneq (Or.inr (Or.inr (Or.inl h3)))
    · -- es[j-1] = w_p⁻¹, es[j] = w_q⁻¹ : |w_p⁻¹ · w_q⁻¹| < |w_p|
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hp, hq] at hstrict
        rwa [norm_inv_eq] at hstrict
      have h4 : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        have hflip : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p)) =
            FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹) :=
          norm_mul_flip (a := α (FreeGroup.of q)) (b := α (FreeGroup.of p))
        rw [hflip]
        exact hs
      exact end_cancel_shortens n α (i := p) (j := q) hneq (Or.inr (Or.inr (Or.inr h4)))

/-- **Strict attachment (right).**  Mirror of `strict_attach_left` at the
junction `(es[j], es[j+1])`: `norm (es[j]·es[j+1]) < norm (es[j+1])` with
`es[j] = ±w_p`, `es[j+1] = ±w_q`, `p ≠ q`, yields
`∃ γ ∈ AutClosure n, N (α·γ) < N α` (an elementary move shortens `w_q`). -/
theorem strict_attach_right {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hjp : j + 1 < es.length)
    {p q : Fin n} (hneq : p ≠ q)
    (hp : es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹)
    (hq : es[j + 1] = α (FreeGroup.of q) ∨ es[j + 1] = (α (FreeGroup.of q))⁻¹)
    (hstrict : FreeGroup.norm ((es[j]) * (es[j + 1])) < FreeGroup.norm (es[j + 1])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · -- es[j] = w_p, es[j+1] = w_q : |w_p · w_q| < |w_q|  -> v4 at (q, p)
      have hs : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hp, hq] at hstrict
        exact hstrict
      -- variant: w_j · w_i with i := q, j := p
      have h4 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of q)) := hs
      exact end_cancel_shortens n α (i := q) (j := p) (by exact fun h => hneq h.symm)
        (Or.inr (Or.inr (Or.inr h4)))
    · -- es[j] = w_p, es[j+1] = w_q⁻¹ : |w_p · w_q⁻¹| < |w_q| -> v1 at (q,p)
      have hs : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hp, hq] at hstrict
        rwa [norm_inv_eq] at hstrict
      have h1 : FreeGroup.norm (α (FreeGroup.of q) * (α (FreeGroup.of p))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        have hflip : FreeGroup.norm (α (FreeGroup.of q) * (α (FreeGroup.of p))⁻¹) =
            FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of q))⁻¹) := by
          simpa using (norm_mul_flip (a := α (FreeGroup.of p))
            (b := (α (FreeGroup.of q))⁻¹)).symm
        rw [hflip]
        exact hs
      exact end_cancel_shortens n α (i := q) (j := p) (by exact fun h => hneq h.symm)
        (Or.inl h1)
  · rcases hq with hq | hq
    · -- es[j] = w_p⁻¹, es[j+1] = w_q : |w_p⁻¹ · w_q| < |w_q| -> v3 at (q,p)
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact end_cancel_shortens n α (i := q) (j := p) (by exact fun h => hneq h.symm)
        (Or.inr (Or.inr (Or.inl hs)))
    · -- es[j] = w_p⁻¹, es[j+1] = w_q⁻¹ : |w_p⁻¹·w_q⁻¹| < |w_q| -> v2 at (q,p)
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hp, hq] at hstrict
        rwa [norm_inv_eq] at hstrict
      have h2 : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p))
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        have hflip : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p)) =
            FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹) :=
          norm_mul_flip (a := α (FreeGroup.of q)) (b := α (FreeGroup.of p))
        rw [hflip]
        exact hs
      exact end_cancel_shortens n α (i := q) (j := p) (by exact fun h => hneq h.symm)
        (Or.inr (Or.inl h2))

end Submission.Nielsen
