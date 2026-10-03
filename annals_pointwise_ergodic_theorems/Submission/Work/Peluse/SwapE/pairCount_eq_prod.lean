import Mathlib
import Submission.Work.Peluse.SwapE.linearInLawAux

/-!
`pairCount` factors over the coordinates: the set of pairs of slot points whose slot-difference
vector is `n` is the product, over the coordinates `k : Fin d`, of the sets of pairs of
one-dimensional slot points whose slot difference is `n k`.  Hence its cardinality is the product
of the one-dimensional slot counts.

Proof sketch: the `Finset`-filter defining `pairCount` is the preimage under the coordinate-wise
equivalence `(Fin d → C) × (Fin d → C) ≃ (Fin d → C × C)` (with `C = Fin M × Fin M`) of the
coordinate-wise filter, which is the product of the one-dimensional filters; cardinalities of
fibres of a `Fintype` product are computed by `Fintype.card_pi` and `Fintype.card_subtype`.
-/

set_option autoImplicit false

namespace Work.Peluse.SwapE

open Work.Peluse.LadderP.Swap (pdir)

theorem pairCount_eq_prod (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (n : Fin d → ℤ) :
    Work.Peluse.SwapE.pairCount d q₁ q₂ M n
      = Finset.univ.prod (fun k : Fin d => Work.Peluse.SwapE.slotCount (q₁ k) (q₂ k) M (n k)) := by
  classical
  -- The coordinate-wise equivalence between filters: a pair `(h, h')` of slot-point vectors has
  -- slot-difference vector `n` iff at every coordinate `k` the pair `(h k, h' k)` has slot
  -- difference `n k`.
  have e : {p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M) //
        Work.Peluse.SwapE.slotVec d q₁ q₂ M p = n} ≃
      ((k : Fin d) → {q : (Fin M × Fin M) × (Fin M × Fin M) //
          pdir (q₁ k) (q₂ k) q.1 - pdir (q₁ k) (q₂ k) q.2 = n k}) :=
    { toFun := fun p k => ⟨(p.1.1 k, p.1.2 k), congrFun p.2 k⟩
      invFun := fun g => ⟨(fun k => (g k).1.1, fun k => (g k).1.2), funext (fun k => (g k).2)⟩
      left_inv := fun p => Subtype.ext (Prod.ext (funext fun k => rfl) (funext fun k => rfl))
      right_inv := fun g => funext fun k => Subtype.ext rfl }
  -- Cardinalities: the fibre over `n` of the slot-difference map is the product of the fibres of
  -- the one-dimensional maps.
  have hcard : Fintype.card {p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M) //
        Work.Peluse.SwapE.slotVec d q₁ q₂ M p = n}
      = ∏ k : Fin d, Work.Peluse.SwapE.slotCount (q₁ k) (q₂ k) M (n k) := by
    rw [Fintype.card_congr e, Fintype.card_pi]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [Fintype.card_subtype, Work.Peluse.SwapE.slotCount]
    rfl
  rw [Work.Peluse.SwapE.pairCount_eq_card, ← Fintype.card_subtype]
  exact hcard

end Work.Peluse.SwapE
