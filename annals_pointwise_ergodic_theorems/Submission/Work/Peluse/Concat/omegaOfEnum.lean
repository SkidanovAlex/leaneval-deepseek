import Mathlib
import Submission.Work.Peluse.Concat.Defs

/-!
# The enumeration of the nonzero sign patterns

`Work.Peluse.Concat.ExpansionPET` and `Work.Peluse.Concat.ConcatBridge` both ask for an
`ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)` which is injective and avoids `0` (the nonzero sign
patterns of the PET/box-norm expansion).  This module supplies that witness.

Since `Fin s → Bool` has `2 ^ s` elements and exactly one of them is `0`, the subtype
`{ω : Fin s → Bool // ω ≠ 0}` has `2 ^ s - 1` elements, so it is equivalent to `Fin (2 ^ s - 1)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-- The subtype of nonzero sign patterns has `2 ^ s - 1` elements. -/
theorem card_ne_zero_bool_fun (s : ℕ) :
    Fintype.card {ω : Fin s → Bool // ω ≠ 0} = 2 ^ s - 1 := by
  classical
  have hfil : (Finset.univ.filter (fun ω : Fin s → Bool => ω ≠ 0))
      = (Finset.univ.erase (0 : Fin s → Bool)) := by
    ext ω
    simp [Finset.mem_filter, Finset.mem_erase, and_comm]
  rw [Fintype.card_subtype, hfil, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- **The enumeration of the nonzero sign patterns.** -/
theorem exists_omegaOf (s : ℕ) (hs : 1 ≤ s) :
    ∃ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool),
      Function.Injective ωOf ∧ ∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0 := by
  classical
  have _ := hs
  have hcard : Fintype.card {ω : Fin s → Bool // ω ≠ 0} = Fintype.card (Fin (2 ^ s - 1)) := by
    rw [card_ne_zero_bool_fun, Fintype.card_fin]
  let e : Fin (2 ^ s - 1) ≃ {ω : Fin s → Bool // ω ≠ 0} := (Fintype.equivOfCardEq hcard).symm
  exact ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij), fun i => (e i).2⟩

end

end Work.Peluse.Concat
