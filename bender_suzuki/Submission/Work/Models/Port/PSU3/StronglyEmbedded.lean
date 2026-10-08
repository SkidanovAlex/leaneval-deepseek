/-
The Bruhat decomposition `SU(3,2^n) = B ∪ B w B` and the strong embedding of the Borel subgroup.

Counting the double coset `B w B` (using `B ∩ w B w = T` and the double-coset cardinality
formula) shows `|B| + |B w B| = |SU(3,2^n)|`; hence `B ∪ B w B = SU(3,2^n)`.  It follows
that `SU(3,2^n) = B ∪ B g B` for every `g ∉ B`, so `B ∩ B^g` is conjugate to
`B ∩ w B w = T`, which has odd order `q^2 - 1`.  Thus `B` is strongly embedded.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Bruhat
import Submission.Work.Models.Port.Commons.GroupTheory.DoubleCoset.card_mul_singleton_mul_mul_card_inf
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.stabilizer_eq_map_conj_of_smul_eq
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.DoubleCoset.card_inf_map_conj_eq_of_mem_doubleCoset
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_subgroupOf_inf_map_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise LinearAlgebra.Projectivization

namespace Submission.PSU3

/-! ## Cardinality of the double coset `B w B` -/

lemma ncard_eq_natCard {α : Type*} [Finite α] (s : Set α) : s.ncard = Nat.card ↥s := by
  haveI : Fintype ↥s := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card, Set.Finite.card_toFinset, Nat.card_eq_fintype_card]

lemma two_pow_sub_one_pos (n : ℕ) (hn : 1 ≤ n) : 0 < 2 ^ (2 * n) - 1 := by
  have h2 : 2 ≤ 2 * n := by omega
  have : 2 ^ 2 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) h2
  omega

lemma ncard_union_of_inter_empty {α : Type*} [Finite α] (s t : Set α) (h : s ∩ t = ∅) :
    (s ∪ t).ncard = s.ncard + t.ncard := by
  have h1 := Set.ncard_union_add_ncard_inter s t
  rw [h, Set.ncard_empty, add_zero] at h1
  exact h1

theorem card_suBwB (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ((suB n : Set (GL (Fin 3) (F n))) * ({suSg n} : Set (GL (Fin 3) (F n))) *
      (suB n : Set (GL (Fin 3) (F n)))) = 2 ^ (6 * n) * (2 ^ (2 * n) - 1) := by
  have h := Commons.GroupTheory.DoubleCoset.card_mul_singleton_mul_mul_card_inf
    (B := suB n) (suSg n)
  rw [suB_inf_map_conj_suSg n, card_suB n hn, card_suT n hn] at h
  have hy : 0 < 2 ^ (2 * n) - 1 := two_pow_sub_one_pos n hn
  have h3 : 2 ^ (3 * n) * 2 ^ (3 * n) = 2 ^ (6 * n) := by rw [← pow_add]; ring
  have key : (2 ^ (3 * n) * (2 ^ (2 * n) - 1)) ^ 2 =
      (2 ^ (6 * n) * (2 ^ (2 * n) - 1)) * (2 ^ (2 * n) - 1) := by
    rw [pow_two, ← h3]; ring
  rw [key] at h
  exact Nat.mul_right_cancel hy h

lemma suB_inter_BwB_eq_empty (n : ℕ) :
    (suB n : Set (GL (Fin 3) (F n))) ∩
      ((suB n : Set (GL (Fin 3) (F n))) * ({suSg n} : Set (GL (Fin 3) (F n))) *
        (suB n : Set (GL (Fin 3) (F n)))) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hxB, hxw⟩
  rw [Set.mem_mul] at hxw
  obtain ⟨y, hy, b, hb, hxyb⟩ := hxw
  rw [Set.mem_mul] at hy
  obtain ⟨a, ha, z, hz, hyaz⟩ := hy
  rw [Set.mem_singleton_iff] at hz
  have hmem : a⁻¹ * x * b⁻¹ ∈ suB n :=
    (suB n).mul_mem ((suB n).mul_mem ((suB n).inv_mem ha) hxB) ((suB n).inv_mem hb)
  have hw : suSg n = a⁻¹ * x * b⁻¹ := by rw [← hxyb, ← hyaz, hz]; group
  exact suSg_notMem_suB n (hw ▸ hmem)

theorem suB_union_BwB_eq (n : ℕ) (hn : 1 ≤ n) :
    (suB n : Set (GL (Fin 3) (F n))) ∪ ((suB n : Set (GL (Fin 3) (F n))) *
      ({suSg n} : Set (GL (Fin 3) (F n))) * (suB n : Set (GL (Fin 3) (F n)))) =
      (SU3 n : Set (GL (Fin 3) (F n))) := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ ?_
  · rintro x (hx | hx)
    · exact suB_le_SU3 n hx
    · rw [Set.mem_mul] at hx
      obtain ⟨y, hy, b, hb, rfl⟩ := hx
      rw [Set.mem_mul] at hy
      obtain ⟨a, ha, z, hz, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (SU3 n).mul_mem ((SU3 n).mul_mem (suB_le_SU3 n ha) (suSg_mem_SU3 n))
        (suB_le_SU3 n hb)
  · have h1 : (SU3 n : Set (GL (Fin 3) (F n))).ncard =
        2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
      rw [ncard_eq_natCard]
      exact card_SU3 n hn
    have h2 : ((suB n : Set (GL (Fin 3) (F n))) ∪ ((suB n : Set (GL (Fin 3) (F n))) *
        ({suSg n} : Set (GL (Fin 3) (F n))) * (suB n : Set (GL (Fin 3) (F n))))).ncard =
        2 ^ (3 * n) * (2 ^ (2 * n) - 1) + 2 ^ (6 * n) * (2 ^ (2 * n) - 1) := by
      rw [ncard_union_of_inter_empty _ _ (suB_inter_BwB_eq_empty n), ncard_eq_natCard,
        ncard_eq_natCard]
      exact congrArg₂ (· + ·) (card_suB n hn) (card_suBwB n hn)
    rw [h1, h2]
    apply le_of_eq
    have hsq : 2 ^ (6 * n) = 2 ^ (3 * n) * 2 ^ (3 * n) := by rw [← pow_add]; ring
    rw [hsq]
    ring
  · exact Set.toFinite _

theorem suSg_bruhat_cover (n : ℕ) (hn : 1 ≤ n) {A : GL (Fin 3) (F n)} (hA : A ∈ SU3 n) :
    A ∈ suB n ∨ ∃ b₁ ∈ suB n, ∃ b₂ ∈ suB n, A = b₁ * suSg n * b₂ := by
  have hu : A ∈ (suB n : Set (GL (Fin 3) (F n))) ∪ ((suB n : Set (GL (Fin 3) (F n))) *
      ({suSg n} : Set (GL (Fin 3) (F n))) * (suB n : Set (GL (Fin 3) (F n)))) := by
    rw [suB_union_BwB_eq n hn]; exact hA
  rcases hu with h | h
  · exact Or.inl h
  · rw [Set.mem_mul] at h
    obtain ⟨y, hy, b₂, hb₂, hyb⟩ := h
    rw [Set.mem_mul] at hy
    obtain ⟨b₁, hb₁, z, hz, hb₁z⟩ := hy
    rw [Set.mem_singleton_iff] at hz
    have heq : b₁ * suSg n * b₂ = A := by rw [← hz, hb₁z, hyb]
    exact Or.inr ⟨b₁, hb₁, b₂, hb₂, heq.symm⟩

lemma odd_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨2 ^ j - 1, ?_⟩
  rw [pow_succ]
  have h : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

/-- The Borel subgroup `B` is strongly embedded in `SU(3,2^n)`. -/
theorem suB_stronglyEmbedded (n : ℕ) (hn : 1 ≤ n) :
    IsStronglyEmbedded ((suB n).subgroupOf (SU3 n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact suSg_notMem_suB n (h (suSg_mem_SU3 n))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suB_le_SU3 n)).toEquiv, card_suB n hn]
    refine ⟨2 ^ (3 * n - 1) * (2 ^ (2 * n) - 1), ?_⟩
    rw [show 2 ^ (3 * n) = 2 * 2 ^ (3 * n - 1) by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 3 * n)]]
    ring
  · intro g hg
    have hgB : (g : GL (Fin 3) (F n)) ∉ suB n :=
      fun h => hg (Subgroup.mem_subgroupOf.mpr h)
    obtain ⟨b₁, hb₁, b₂, hb₂, hg'⟩ := (suSg_bruhat_cover n hn g.2).resolve_left hgB
    rw [Commons.GroupTheory.Subgroup.card_subgroupOf_inf_map_conj (suB n) (SU3 n) (suB_le_SU3 n) g,
      Commons.GroupTheory.DoubleCoset.card_inf_map_conj_eq_of_mem_doubleCoset (suB n) (suSg n) b₁ b₂
        (g : GL (Fin 3) (F n)) hb₁ hb₂ hg', suB_inf_map_conj_suSg n, card_suT n hn]
    exact odd_two_pow_sub_one (2 * n) (by omega)

end Submission.PSU3
