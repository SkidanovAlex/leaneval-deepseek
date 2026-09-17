import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Data.Set.Card

/-!
# Counting the isotypic components of a semisimple module

If a semisimple module `M` is the supremum of a finite family `N i` of pairwise non-isomorphic
simple submodules, then `M` has exactly `Fintype.card ι` isotypic components.  This is the
combinatorial half of the count `(isotypicComponents U (V ⊗ V)).ncard = 40`: one only has to
exhibit forty pairwise non-isomorphic simple summands spanning `V ⊗ V`.
-/

set_option maxHeartbeats 1000000

namespace Submission.IsotypicCount

open scoped BigOperators

theorem ncard_isotypicComponents_eq_card {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] {ι : Type*} [Fintype ι] (N : ι → Submodule R M)
    (hsimp : ∀ i, IsSimpleModule R (N i))
    (hne : ∀ i j, i ≠ j → IsEmpty (N i ≃ₗ[R] N j))
    (hsup : sSup (Set.range N) = ⊤) :
    (isotypicComponents R M).ncard = Fintype.card ι := by
  classical
  set c : ι → Submodule R M := fun i => isotypicComponent R M (N i) with hc
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hneij
    have hle : N j ≤ c i := by
      rw [hc] at hij ⊢
      calc N j ≤ isotypicComponent R M (N j) := Submodule.le_isotypicComponent _
        _ = isotypicComponent R M (N i) := hij.symm
    haveI := hsimp j
    have h := (isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent R M (S := N i))) (N j) hle
    obtain ⟨e⟩ := h
    haveI := hne j i (fun hh => hneij hh.symm)
    exact isEmptyElim e
  have hset : isotypicComponents R M = Set.range c := by
    ext x
    constructor
    · intro hx
      obtain ⟨S, hS, rfl⟩ := hx
      have hle : S ≤ sSup (Set.range N) := by rw [hsup]; exact le_top
      obtain ⟨m, ⟨i, rfl⟩, S', hle', ⟨e⟩⟩ :=
        Submodule.le_linearEquiv_of_sSup_eq_top S (Set.range N) hsup
      haveI : IsSimpleModule R S' := IsSimpleModule.congr e.symm
      haveI : IsSimpleModule R (N i) := hsimp i
      have hEq : S' = N i := by
        rcases (IsAtom.le_iff (IsSimpleModule.isAtom (m := N i))).mp hle' with h | h
        · exact absurd h (Submodule.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial R S'))
        · exact h
      refine ⟨i, ?_⟩
      obtain rfl : N i = S' := hEq.symm
      rw [hc]
      dsimp only
      exact (LinearEquiv.isotypicComponent_eq e).symm
    · rintro ⟨i, rfl⟩
      exact ⟨N i, hsimp i, rfl⟩
  rw [hset, Set.ncard_range_of_injective hcinj]
  exact Nat.card_eq_fintype_card

end Submission.IsotypicCount
