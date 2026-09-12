import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi

namespace Commons.Combinatorics.Finset

/-- Counting the functions `Fin (d+1) → α` whose restriction to `Fin d` along `Fin.succAbove j`
lands in a prescribed finset `S`: there are exactly `S.card * Fintype.card α` of them.

Equivalently: the map `x ↦ (fun k => x (Fin.succAbove j k))` is a projection all of whose
fibres have size `Fintype.card α`. -/
theorem card_filter_succAbove (d : ℕ) {α : Type*} [Fintype α] [DecidableEq α]
    (j : Fin (d+1)) (S : Finset (Fin d → α)) :
    ((Finset.univ : Finset (Fin (d+1) → α)).filter
      (fun x => (fun k : Fin d => x (Fin.succAbove j k)) ∈ S)).card = S.card * Fintype.card α := by
  classical
  -- The equivalence `α × (Fin d → α) ≃ (Fin (d+1) → α)` whose inverse sends `x` to
  -- `(x j, fun k => x (succAbove j k))`.
  let ee : α × (Fin d → α) ≃ (Fin (d+1) → α) := Fin.insertNthEquiv (fun _ : Fin (d+1) => α) j
  have hsymm : ∀ x : Fin (d+1) → α,
      ee.symm x = (x j, fun k : Fin d => x (Fin.succAbove j k)) := by
    intro x
    rw [Fin.insertNthEquiv_symm_apply]
    rfl
  have key : ∀ (a : α) (f : Fin d → α),
      (fun k : Fin d =>
        (@Fin.insertNth d (fun _ : Fin (d+1) => α) j a f) (Fin.succAbove j k)) = f := by
    intro a f
    funext k
    exact @Fin.insertNth_apply_succAbove d (fun _ : Fin (d+1) => α) j a f k
  have hep : ∀ p : α × (Fin d → α),
      ee p = @Fin.insertNth d (fun _ : Fin (d+1) => α) j p.1 p.2 := by
    intro p
    rfl
  -- The filtered set is the image under `ee` of `univ ×ˢ S`.
  have hset : (Finset.univ : Finset (Fin (d+1) → α)).filter
        (fun x => (fun k : Fin d => x (Fin.succAbove j k)) ∈ S)
      = ((Finset.univ : Finset α) ×ˢ S).map ee.toEmbedding := by
    ext x
    rw [Finset.mem_filter, Finset.mem_map]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨ee.symm x, ?_, by simp⟩
      rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hsymm x]
      exact hx
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨-, hp2⟩ := Finset.mem_product.mp hp
      have hpe : (fun k : Fin d => (ee.toEmbedding p) (Fin.succAbove j k)) = p.2 := by
        change (fun k : Fin d => (ee p) (Fin.succAbove j k)) = p.2
        rw [hep p]
        exact key p.1 p.2
      rw [hpe]
      exact hp2
  rw [hset, Finset.card_map, Finset.card_product, Finset.card_univ]
  exact Nat.mul_comm _ _

end Commons.Combinatorics.Finset