import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Data.ZMod

/-- Counting elements of a subtype of `ZMod n` by their natural representatives
`0, 1, ..., n - 1`: the number of `r < n` whose residue `r : ZMod n` satisfies `ψ`
equals the total number of `x : ZMod n` with `ψ x`. -/
theorem range_card_eq_subtype (n : ℕ) [NeZero n] (ψ : ZMod n → Prop) [DecidablePred ψ] :
    ((Finset.range n).filter (fun r : ℕ => ψ (r : ZMod n))).card =
      Fintype.card {x : ZMod n // ψ x} := by
  let B : Finset ℕ := (Finset.range n).filter (fun r : ℕ => ψ (r : ZMod n))
  let A : Finset {x : ZMod n // ψ x} := Finset.univ
  have hA : A.card = Fintype.card {x : ZMod n // ψ x} := by
    simp [A]
  calc
    ((Finset.range n).filter (fun r : ℕ => ψ (r : ZMod n))).card = B.card := rfl
    _ = A.card := by
      refine Finset.card_bij (s := B) (t := A) ?i ?hi ?i_inj ?i_surj
      · intro a ha
        exact ⟨(a : ZMod n), (Finset.mem_filter.mp ha).2⟩
      · intro a ha
        simp [A]
      · intro a₁ ha₁ a₂ ha₂ h
        have hcast : (a₁ : ZMod n) = (a₂ : ZMod n) := congrArg Subtype.val h
        have hval₁ : ZMod.val (a₁ : ZMod n) = a₁ :=
          ZMod.val_cast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1)
        have hval₂ : ZMod.val (a₂ : ZMod n) = a₂ :=
          ZMod.val_cast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1)
        exact (hval₁.symm.trans (congrArg ZMod.val hcast)).trans hval₂
      · intro b hb
        refine ⟨ZMod.val (b : ZMod n), ?_, ?_⟩
        · rw [Finset.mem_filter]
          constructor
          · exact Finset.mem_range.mpr (ZMod.val_lt (b : ZMod n))
          · simp
            exact b.2
        · apply Subtype.ext
          simp
    _ = Fintype.card {x : ZMod n // ψ x} := hA

end Commons.Data.ZMod