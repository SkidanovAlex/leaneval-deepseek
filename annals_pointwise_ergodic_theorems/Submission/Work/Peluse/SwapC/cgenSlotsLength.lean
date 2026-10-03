import Mathlib
import Submission.Work.Peluse.SwapC.concatState

namespace Work.Peluse.SwapC

/-- A generic bound for the length of a `flatMap`: if every value of `f` on the elements of `l`
has length at most `n`, then `l.flatMap f` has length at most `n * l.length`. -/
private lemma length_flatMap_le_mul {α β : Type*} :
    ∀ (l : List α) (f : α → List β) (n : ℕ),
      (∀ a ∈ l, (f a).length ≤ n) → (l.flatMap f).length ≤ n * l.length
  | [], f, n, _ => by simp
  | a :: l, f, n, h => by
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have ha : (f a).length ≤ n := h a (by simp)
      have hl : (l.flatMap f).length ≤ n * l.length :=
        length_flatMap_le_mul l f n (fun b hb => h b (by simp [hb]))
      calc (f a).length + (l.flatMap f).length ≤ n + n * l.length :=
            Nat.add_le_add ha hl
        _ = n * (l.length + 1) := by ring

/-- **Length bound for the slot list of a subdivision** (used in `Work.Peluse.SwapC.concatAll` to
feed the uniform constants of the step lemma).  Each leaf contributes at most `s` raw slots
(`CLeaf.raws` is a filtered `List.finRange s`) and each ordered pair of leaves at most `s`
differences (`genuineDiffs` is a flatMap over `Λ.product Λ` of a filtered `List.finRange s`), so the
bound follows from `List.length_product`, `List.length_flatten`, `List.length_flatMap_le` and
`List.length_filter_le`. -/
theorem cgenSlotsLength {s : ℕ} (Λ : List (CLeaf s)) :
    (genuineSlots Λ).length ≤ s * Λ.length + s * Λ.length * Λ.length := by
  -- each leaf contributes at most `s` raw slots
  have hraw : ∀ l ∈ Λ, (CLeaf.raws l).length ≤ s := by
    intro l _
    rw [CLeaf.raws, List.length_map]
    exact le_trans (List.length_filter_le _ _) (le_of_eq List.length_finRange)
  -- each ordered pair of leaves contributes at most `s` differences
  have hprod : ∀ p ∈ Λ.product Λ,
      ((List.finRange s).filterMap fun j : Fin s =>
        if (∀ i : Fin s, i.val < s - 1 - j.val → p.1.str i = p.2.str i)
            ∧ p.1.str ⟨s - 1 - j.val, by omega⟩ = true
            ∧ p.2.str ⟨s - 1 - j.val, by omega⟩ = false
        then some (CC.dff j p.1.str p.2.str) else none).length ≤ s := by
    intro p _
    exact le_trans (List.length_filterMap_le _ _) (le_of_eq List.length_finRange)
  -- the raw part
  have h1 : ((Λ.map CLeaf.raws).flatten).length ≤ s * Λ.length := by
    rw [List.flatten_eq_flatMap, List.flatMap_map]
    exact length_flatMap_le_mul Λ CLeaf.raws s hraw
  -- the pair list has length `Λ.length * Λ.length`
  have hplen : (Λ.product Λ).length ≤ Λ.length * Λ.length := by
    show (Λ.flatMap (fun a => Λ.map (Prod.mk a))).length ≤ Λ.length * Λ.length
    refine length_flatMap_le_mul Λ (fun a => Λ.map (Prod.mk a)) Λ.length ?_
    intro a _
    simp
  -- the difference part
  have h2 : (genuineDiffs Λ).length ≤ s * Λ.length * Λ.length := by
    rw [genuineDiffs]
    have h := length_flatMap_le_mul (Λ.product Λ) _ s hprod
    calc (List.flatMap _ (Λ.product Λ)).length ≤ s * (Λ.product Λ).length := h
      _ ≤ s * (Λ.length * Λ.length) := Nat.mul_le_mul_left s hplen
      _ = s * Λ.length * Λ.length := by ring
  rw [genuineSlots, List.length_append]
  exact Nat.add_le_add h1 h2

end Work.Peluse.SwapC
