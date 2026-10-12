import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.FibreProjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false

/-- **The alternating subset sum**: for a finset `T`, the sum of `(-1)^{|T| − |S|}` over the
subsets `S ⊆ T` vanishes unless `T = ∅`.  This is `Finset.sum_powerset_neg_one_pow_card` after the
reindexing `S ↦ T \ S` of `T.powerset` (`(T \ S).card = T.card - S.card` for `S ⊆ T`), transported
from `ℤ` to `ℂ`. -/
theorem sum_powerset_neg_one_pow_card_sub {α : Type*} [DecidableEq α] (T : Finset α) :
    (∑ S ∈ T.powerset, (-1 : ℂ) ^ (T.card - S.card)) = if T = ∅ then 1 else 0 := by
  have h1 : (∑ S ∈ T.powerset, (-1 : ℂ) ^ (T.card - S.card))
      = ∑ S ∈ T.powerset, (-1 : ℂ) ^ (S.card) := by
    refine Finset.sum_nbij (fun S : Finset α => T \ S) ?_ ?_ ?_ ?_
    · intro S hS
      exact Finset.mem_powerset.mpr Finset.sdiff_subset
    · intro S1 hS1 S2 hS2 h
      change T \ S1 = T \ S2 at h
      calc S1 = T \ (T \ S1) := (Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hS1)).symm
        _ = T \ (T \ S2) := by rw [h]
        _ = S2 := Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hS2)
    · intro U hU
      exact ⟨T \ U, Finset.mem_powerset.mpr Finset.sdiff_subset,
        Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)⟩
    · intro S hS
      rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hS)]
  rw [h1]
  have h2 : (∑ S ∈ T.powerset, (-1 : ℂ) ^ (S.card))
      = (((∑ m ∈ T.powerset, (-1 : ℤ) ^ (m.card)) : ℤ) : ℂ) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Int.cast_pow]
    norm_num
  rw [h2, Finset.sum_powerset_neg_one_pow_card]
  by_cases hT : T = ∅ <;> simp [hT]

-- Resolution of the identity for the S-sectors: `slotExact e S Φ = ∑ T ∈ univ.filter (S ⊆ T),
-- (-1)^{|T|-|S|} • slotProj e T Φ`.  Interchange the two finite sums (`Finset.sum_comm`) and use
-- `∑ S ∈ T.powerset, (-1)^{|T|-|S|} = if T = ∅ then 1 else 0` (reindex `S ↦ T \ S` inside
-- `T.powerset` and apply `Finset.sum_powerset_neg_one_pow_card`); the only surviving term is
-- `slotProj e ∅ Φ = Φ` (`slotInt_empty` in `SlotProjAux`).  No hypotheses on `e` or `Φ` are
-- needed.
theorem slotExact_sum_eq {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) :
    ∑ S : Finset (Fin n), slotExact e S Φ = Φ := by
  classical
  calc ∑ S : Finset (Fin n), slotExact e S Φ
      = ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          if S ⊆ T then (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ else 0 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [slotExact, Finset.sum_filter]
    _ = ∑ T : Finset (Fin n), ∑ S : Finset (Fin n),
          if S ⊆ T then (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ else 0 :=
        Finset.sum_comm
    _ = ∑ T : Finset (Fin n),
          (∑ S ∈ T.powerset, (-1 : ℂ) ^ (T.card - S.card)) • slotProj e T Φ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.sum_smul, ← Finset.sum_filter]
        have : (Finset.univ.filter (fun S : Finset (Fin n) => S ⊆ T)) = T.powerset := by
          ext S; simp [Finset.mem_powerset]
        rw [this]
    _ = ∑ T : Finset (Fin n), (if T = ∅ then (1 : ℂ) else 0) • slotProj e T Φ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [sum_powerset_neg_one_pow_card_sub T]
    _ = slotProj e (∅ : Finset (Fin n)) Φ := by
        rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
        · simp
        · intro T _ hT; simp [hT]
        · intro h; exact absurd (Finset.mem_univ (∅ : Finset (Fin n))) h
    _ = Φ := slotInt_empty e Φ

end Work.BoseBoxFock
