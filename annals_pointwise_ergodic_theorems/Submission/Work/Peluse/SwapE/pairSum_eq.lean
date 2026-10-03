import Mathlib
import Submission.Work.Peluse.SwapE.linearInLawAux

/-!
# `SwapE` — the fibre-sum identity for the slot-difference map

The double sum over pairs of slot points `(h, h') ∈ ([M]×[M])^d × ([M]×[M])^d` of a function of
the slot-difference vector `slotVec d q₁ q₂ M (h, h')` depends on `(h, h')` only through that
vector, hence collapses to a single sum over the *values* of the vector, weighted by the number of
pairs producing each value (`pairCount`).  This is the elementary regrouping step of the
linear-in-law identity (`linearInLawAux`'s docstring, ingredient 2).

The only care needed is the passage between the iterated sum over `(h, h') ∈ [M]^d × [M]^d` and
the sum over the product type `(Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)`
(`Fintype.sum_prod_type`), since `Finset.sum_fiberwise_of_maps_to` is stated for a sum over a
single `Finset`.
-/

open scoped BigOperators

namespace Work.Peluse.SwapE

/-- **The fibre sum.**  For any finite set `T` of slot vectors containing the whole image of the
slot-difference map, the doubly-indexed sum over slot-point pairs of `G ∘ slotVec` equals the sum
over `T` of `G` weighted by the number of pairs realising each slot vector. -/
theorem pairSum_eq (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (G : (Fin d → ℤ) → ℂ)
    (T : Finset (Fin d → ℤ))
    (hT : ∀ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
      Work.Peluse.SwapE.slotVec d q₁ q₂ M p ∈ T) :
    (Finset.univ.sum (fun h : Fin d → Fin M × Fin M => Finset.univ.sum
        (fun h' : Fin d → Fin M × Fin M => G (Work.Peluse.SwapE.slotVec d q₁ q₂ M (h, h')))))
      = T.sum (fun n : Fin d → ℤ => (Work.Peluse.SwapE.pairCount d q₁ q₂ M n : ℂ) * G n) := by
  classical
  -- Rewrite the iterated sum over `(h, h')` as a sum over the product type.
  have h1 : (Finset.univ.sum (fun h : Fin d → Fin M × Fin M => Finset.univ.sum
        (fun h' : Fin d → Fin M × Fin M => G (Work.Peluse.SwapE.slotVec d q₁ q₂ M (h, h')))))
      = ∑ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
          G (Work.Peluse.SwapE.slotVec d q₁ q₂ M p) :=
    (Fintype.sum_prod_type (fun p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M) =>
      G (Work.Peluse.SwapE.slotVec d q₁ q₂ M p))).symm
  rw [h1]
  -- Group the sum over pairs by the value of the slot vector.
  rw [← Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))))
        (t := T) (g := Work.Peluse.SwapE.slotVec d q₁ q₂ M) (fun p _ => hT p)
        (fun p => G (Work.Peluse.SwapE.slotVec d q₁ q₂ M p))]
  -- Inside a fibre the summand is constant, and the fibre has `pairCount` elements.
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have h2 : (∑ p ∈ (Finset.univ : Finset ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))).filter
        (fun p => Work.Peluse.SwapE.slotVec d q₁ q₂ M p = n),
          G (Work.Peluse.SwapE.slotVec d q₁ q₂ M p))
      = ∑ _p ∈ (Finset.univ : Finset ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))).filter
        (fun p => Work.Peluse.SwapE.slotVec d q₁ q₂ M p = n), G n := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [Finset.mem_filter] at hp
    rw [hp.2]
  rw [h2, Finset.sum_const, nsmul_eq_mul]
  simp only [Work.Peluse.SwapE.pairCount]

end Work.Peluse.SwapE
