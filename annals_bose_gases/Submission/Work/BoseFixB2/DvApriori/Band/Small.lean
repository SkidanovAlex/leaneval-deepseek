import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.DvApriori.Band.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.Small`

The restricted slot projections `projOn ℓ A U` for the slot sets `A` of size one and two,
in the explicit `aP`/`aQ` form in which the corpus words `q1word`, `q3word` are written:

* `projOn_singleton` — a single slot is projected by `aP ℓ i` or `aQ ℓ i`;
* `projOn_pair` — two distinct slots are projected by the corresponding product (in either
  order, the operators of distinct slots commuting).
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- The restricted projection onto a single slot is the corresponding `aP`/`aQ`. -/
theorem projOn_singleton {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin n) (U : Finset ℕ)
    {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    projOn ℓ {i.val} U Φ = (if i.val ∈ U then aQ ℓ i else aP ℓ i) Φ := by
  have hnd' : ([i.val] : List ℕ).Nodup := by simp
  rw [projOn_eq_slotProd,
    slotProd_reorder hℓ (slotList_nodup n {i.val}) hnd'
      (fun k hk => slotList_lt hk)
      (by
        intro k hk
        rw [List.mem_singleton] at hk
        rw [hk]
        exact i.isLt)
      (by
        intro k
        rw [mem_slotList, List.mem_singleton]
        constructor
        · rintro ⟨_, hk⟩
          simpa using hk
        · intro hk
          subst hk
          exact ⟨i.isLt, by simp⟩)
      U hΦ,
    slotProd_cons i.isLt [] U Φ, slotProd_nil]
  try simp only [Fin.eta]

/-- The restricted projection onto two distinct slots is the corresponding product of
`aP`/`aQ` (the operators of distinct slots commute, so either order gives the same state). -/
theorem projOn_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (U : Finset ℕ) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    projOn ℓ {i.val, j.val} U Φ
      = (if i.val ∈ U then aQ ℓ i else aP ℓ i)
          ((if j.val ∈ U then aQ ℓ j else aP ℓ j) Φ) := by
  have hnd' : ([i.val, j.val] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil,
      not_false_eq_true, true_and]
    exact ⟨fun h => hij (Fin.ext h), by simp⟩
  rw [projOn_eq_slotProd,
    slotProd_reorder hℓ (slotList_nodup n {i.val, j.val}) hnd'
      (fun k hk => slotList_lt hk)
      (by
        intro k hk
        rw [List.mem_cons, List.mem_singleton] at hk
        rcases hk with h | h
        · rw [h]; exact i.isLt
        · rw [h]; exact j.isLt)
      (by
        intro k
        rw [mem_slotList, Finset.mem_insert, Finset.mem_singleton, List.mem_cons,
          List.mem_singleton]
        constructor
        · rintro ⟨_, h | h⟩
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact ⟨by rw [h]; exact i.isLt, Or.inl h⟩
          · exact ⟨by rw [h]; exact j.isLt, Or.inr h⟩)
      U hΦ,
    slotProd_cons i.isLt [j.val] U Φ, slotProd_cons j.isLt [] U Φ, slotProd_nil]
  try simp only [Fin.eta]

end

end Work.BoseFixB2.DvApriori
