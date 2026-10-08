import Mathlib

namespace Work.CORE3.MData

theorem odd_relIndex_sup_of_card {G : Type} [Group G] [Finite G] (b : ℕ)
    {S E K M : Subgroup G} (hSM : S ≤ M) (hEM : E ≤ M) (hKM : K ≤ M)
    (hS : Nat.card S = 8) (hE : Nat.card E = 8 * b) (hb : Odd b)
    (hSodd : Odd (S.relIndex M)) : Odd ((E ⊔ K).relIndex M) := by
  have _ : Odd b := hb
  -- `E ⊔ K ≤ M`, so `(E ⊔ K).relIndex M` is the index `[M : E ⊔ K]`.
  have hHleM : E ⊔ K ≤ M := sup_le hEM hKM
  have hEH : E ≤ E ⊔ K := le_sup_left
  -- `Nat.card M = 8 * [M : S]`, and `[M : S]` is odd.
  have hSM' : S ⊓ M = S := inf_eq_left.mpr hSM
  have hScard : S.relIndex M * 8 = Nat.card M := by
    have h := Subgroup.relIndex_mul_card S M
    rw [hSM', hS] at h
    exact h
  -- `Nat.card M = [M : E] * (8 * b)`.
  have hEM' : E ⊓ M = E := inf_eq_left.mpr hEM
  have hEcard : E.relIndex M * (8 * b) = Nat.card M := by
    have h := Subgroup.relIndex_mul_card E M
    rw [hEM', hE] at h
    exact h
  -- Hence `[M : E] * b = [M : S]`, so `[M : E]` is odd.
  have hEq : E.relIndex M * (8 * b) = S.relIndex M * 8 := hEcard.trans hScard.symm
  have hEb : E.relIndex M * b = S.relIndex M := by
    apply Nat.mul_right_cancel (show 0 < (8 : ℕ) by norm_num)
    calc (E.relIndex M * b) * 8 = E.relIndex M * (8 * b) := by ring
      _ = S.relIndex M * 8 := hEq
  have hEodd : Odd (E.relIndex M) := by
    have h' : Odd (E.relIndex M * b) := hEb ▸ hSodd
    exact Nat.Odd.of_mul_left h'
  -- `[M : E ⊔ K]` divides `[M : E]`, hence is odd as well.
  have hrel : E.relIndex (E ⊔ K) * (E ⊔ K).relIndex M = E.relIndex M :=
    Subgroup.relIndex_mul_relIndex E (E ⊔ K) M hEH hHleM
  have h' : Odd (E.relIndex (E ⊔ K) * (E ⊔ K).relIndex M) := hrel ▸ hEodd
  exact Nat.Odd.of_mul_right h'

end Work.CORE3.MData
