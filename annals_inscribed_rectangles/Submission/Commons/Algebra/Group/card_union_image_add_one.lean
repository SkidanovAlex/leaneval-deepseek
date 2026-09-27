import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

namespace Commons.Algebra.Group

/-- In a cyclic group of order `n`, a nonempty proper subset `U` satisfies
`|U ∪ (U+1)| ≥ |U| + 1`. -/
theorem card_union_image_add_one (n : ℕ) [NeZero n] (U : Finset (ZMod n)) (hU : U.Nonempty)
    (hU' : U ≠ Finset.univ) : U.card + 1 ≤ (U ∪ U.image (fun x => x + 1)).card := by
  set V : Finset (ZMod n) := U.image (fun x => x + 1) with hV
  have hinj : Function.Injective (fun x : ZMod n => x + 1) := add_left_injective 1
  have hVcard : V.card = U.card := by
    rw [hV]; exact Finset.card_image_of_injective _ hinj
  -- `V ≠ U`: otherwise `U` would be invariant under `+1`, hence all of `ZMod n`.
  have hne : V ≠ U := by
    intro h
    have hstep : ∀ x : ZMod n, x ∈ U → x + 1 ∈ U := by
      intro x hx
      have hx' : x + 1 ∈ V := by
        rw [hV]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rwa [h] at hx'
    obtain ⟨a, ha⟩ := hU
    refine hU' (Finset.eq_univ_of_forall ?_)
    intro y
    have hyval : y = a + (((y - a).val : ℕ) : ZMod n) := by
      rw [ZMod.natCast_zmod_val]; abel
    rw [hyval]
    have hmem : ∀ k : ℕ, a + (k : ZMod n) ∈ U := by
      intro k
      induction k with
      | zero => simpa using ha
      | succ m ih =>
          have hsucc : a + ((m + 1 : ℕ) : ZMod n) = (a + (m : ZMod n)) + 1 := by
            push_cast; abel
          rw [hsucc]
          exact hstep _ ih
    exact hmem _
  have hle : U.card ≤ (U ∪ V).card := Finset.card_le_card Finset.subset_union_left
  have hnecard : (U ∪ V).card ≠ U.card := by
    intro h
    have hWU : U = U ∪ V :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (le_of_eq h)
    have hVsub : V ⊆ U := by rw [hWU]; exact Finset.subset_union_right
    exact hne (Finset.eq_of_subset_of_card_le hVsub (le_of_eq hVcard.symm))
  exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hle (Ne.symm hnecard))

end Commons.Algebra.Group