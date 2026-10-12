import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.Sector.secPermReorder
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Conjugation of the joint sector projections by a particle permutation

For a permutation `σ` of the particles, the joint sector projection
`E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j = jointProj ℓ S` satisfies

  `E_S Φ ∘ actPerm σ = E_{σ • S} Φ ,   σ • S = slotMap σ S`

for a permutation invariant `Φ`.  The proof is the chain

* `jointProj ℓ S Φ = blockOp ℓ S n Φ = blockOpL ℓ (stdList S n) Φ` (`Defs`, `secPermDefs`);
* transporting the slots along `σ` (`blockOpL_conj`): the conjugated operator is the
  iterated operator of the list `conjList σ (stdList S n)`, whose slots are the
  images `σ(m)`, `m < n`, with the flag of `m ∈ S`;
* `Φ ∘ actPerm σ = Φ` (the state is permutation invariant);
* reordering (`blockOpL_reorder`) turns that list into `blockOp ℓ (kindSet L) n`,
  and the flags of that set are `j ∈ slotMap σ S` for every `j < n`.
-/

noncomputable section

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The slot permutation as a map on slot numbers -/

/-- The slot permutation `σ` read as a map on slot numbers, extended by the identity
outside `{0, …, n−1}` (so that it is injective on all of `ℕ`). -/
noncomputable def slotNat {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) : ℕ :=
  if h : m < n then (σ ⟨m, h⟩).val else m

lemma slotNat_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : m < n) :
    slotNat σ m = (σ ⟨m, hm⟩).val := by
  rw [slotNat, dif_pos hm]

lemma slotNat_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : m < n) :
    slotNat σ m < n := by
  rw [slotNat_eq σ hm]
  exact (σ ⟨m, hm⟩).isLt

lemma slotNat_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) : Function.Injective (slotNat σ) := by
  intro a b h
  rcases lt_or_ge a n with ha | ha
  · rcases lt_or_ge b n with hb | hb
    · rw [slotNat_eq σ ha, slotNat_eq σ hb] at h
      have h2 : (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := σ.injective (Fin.ext h)
      exact congrArg Fin.val h2
    · rw [slotNat_eq σ ha, slotNat, dif_neg (by omega)] at h
      have := (σ ⟨a, ha⟩).isLt
      omega
  · rcases lt_or_ge b n with hb | hb
    · rw [slotNat, dif_neg (by omega), slotNat_eq σ hb] at h
      have := (σ ⟨b, hb⟩).isLt
      omega
    · rw [slotNat, dif_neg (by omega), slotNat, dif_neg (by omega)] at h
      exact h

/-! ## 2. Bookkeeping for the conjugated list -/

lemma map_conjList_fst {n : ℕ} (σ : Equiv.Perm (Fin n)) {L : List (ℕ × Bool)}
    (hL : ∀ p ∈ L, p.1 < n) :
    (conjList σ L).map (fun p => p.1) = (L.map (fun p => p.1)).map (slotNat σ) := by
  rw [conjList, List.map_map, List.map_map]
  refine List.map_congr_left (fun p hp => ?_)
  show (if h : p.1 < n then ((σ ⟨p.1, h⟩).val, p.2) else p).1 = slotNat σ p.1
  rw [dif_pos (hL p hp), slotNat_eq σ (hL p hp)]

lemma conjList_nodup_fst {n : ℕ} (σ : Equiv.Perm (Fin n)) {L : List (ℕ × Bool)}
    (hnd : (L.map (fun p => p.1)).Nodup) (hL : ∀ p ∈ L, p.1 < n) :
    ((conjList σ L).map (fun p => p.1)).Nodup := by
  rw [map_conjList_fst σ hL]
  exact List.Nodup.map (slotNat_injective σ) hnd

lemma conjList_slot_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {L : List (ℕ × Bool)}
    (hL : ∀ p ∈ L, p.1 < n) : ∀ p ∈ conjList σ L, p.1 < n := by
  intro p hp
  rw [conjList, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [dif_pos (hL q hq)]
  exact (σ ⟨q.1, hL q hq⟩).isLt

lemma conjList_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (L : List (ℕ × Bool)) :
    (conjList σ L).length = L.length := by
  simp [conjList]

/-! ## 3. The flags of the conjugated list -/

lemma mem_kindSet_conjList {n : ℕ} (σ : Equiv.Perm (Fin n)) {L : List (ℕ × Bool)}
    (hL : ∀ p ∈ L, p.1 < n) {j : ℕ} :
    j ∈ kindSet (conjList σ L) ↔ ∃ q ∈ L, q.2 = true ∧ slotNat σ q.1 = j := by
  rw [mem_kindSet]
  constructor
  · rintro ⟨p, hp, hp2, hp1⟩
    rw [conjList, List.mem_map] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    rw [dif_pos (hL q hq)] at hqp
    subst hqp
    exact ⟨q, hq, hp2, by rw [slotNat_eq σ (hL q hq)]; exact hp1⟩
  · rintro ⟨q, hq, hq2, hq1⟩
    refine ⟨((σ ⟨q.1, hL q hq⟩).val, q.2), ?_, hq2, ?_⟩
    · rw [conjList, List.mem_map]
      exact ⟨q, hq, by rw [dif_pos (hL q hq)]⟩
    · rw [slotNat_eq σ (hL q hq)] at hq1
      exact hq1

/-- For `S ⊆ {0,…,n−1}` the flags of the conjugated standard list are the membership
of the slots in the image set `slotMap σ S`. -/
lemma kindSet_conjList_stdList {n : ℕ} (σ : Equiv.Perm (Fin n)) {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) {j : ℕ} (hj : j < n) :
    j ∈ kindSet (conjList σ (stdList S n)) ↔ j ∈ slotMap σ S := by
  rw [mem_kindSet_conjList σ (fun p hp => stdList_slot_lt hp), mem_slotMap]
  constructor
  · rintro ⟨q, hq, hq2, hq1⟩
    obtain ⟨m, hm, rfl⟩ := mem_stdList.mp hq
    exact ⟨m, of_decide_eq_true hq2, hm, by rw [← slotNat_eq σ hm]; exact hq1⟩
  · rintro ⟨m, hmS, hm, hmj⟩
    exact ⟨(m, decide (m ∈ S)), by rw [mem_stdList]; exact ⟨m, hm, rfl⟩, by simp [hmS],
      by rw [slotNat_eq σ hm]; exact hmj⟩

/-! ## 4. The conjugation of the joint projection -/

/-- The conjugated standard list is the iterated operator of the image slot set. -/
lemma blockOpL_conjList_stdList_slotMap {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (σ : Equiv.Perm (Fin n))
    {S : Finset ℕ} (hS : S ⊆ Finset.range n) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    blockOpL ℓ (conjList σ (stdList S n)) Φ = blockOp ℓ (slotMap σ S) n Φ := by
  have hlt : ∀ p ∈ stdList S n, p.1 < n := fun p hp => stdList_slot_lt hp
  have hnd : ((conjList σ (stdList S n)).map (fun p => p.1)).Nodup :=
    conjList_nodup_fst σ (stdList_nodup_fst S n) (fun p hp => stdList_slot_lt hp)
  have hlen : (conjList σ (stdList S n)).length = n := by
    rw [conjList_length, stdList_length]
  rw [blockOpL_reorder hℓ hnd (fun p hp => conjList_slot_lt σ hlt p hp) hlen hΦ]
  exact blockOp_congr_set (fun j hj => kindSet_conjList_stdList σ hS hj) n le_rfl Φ

/-- **Conjugation of the joint sector projection.**  For a permutation invariant state
`Φ`, relabelling the particles by `σ` transports the slot set `S` to `slotMap σ S`. -/
theorem jointProj_actPerm' {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (σ : Equiv.Perm (Fin n))
    {S : Finset ℕ} (hS : S ⊆ Finset.range n) {Φ : X n → ℝ} (hΦ : Continuous Φ)
    (hσ : PermInvariant n Φ) (x : X n) :
    Work.BoseFixB2.jointProj ℓ S Φ (Submission.BoseGases.actPerm n σ x)
      = Work.BoseFixB2.jointProj ℓ (slotMap σ S) Φ x := by
  rw [Work.BoseFixB2.jointProj_eq_blockOp, blockOp_eq_blockOpL S n]
  rw [show blockOpL ℓ (stdList S n) Φ (Submission.BoseGases.actPerm n σ x)
      = blockOpL ℓ (conjList σ (stdList S n)) (fun y => Φ (Submission.BoseGases.actPerm n σ y)) x
      from congrFun (blockOpL_conj ℓ σ Φ (stdList S n)) x]
  rw [show (fun y => Φ (Submission.BoseGases.actPerm n σ y)) = Φ from funext (hσ σ)]
  rw [blockOpL_conjList_stdList_slotMap hℓ σ hS hΦ]
  rfl

end Work.BoseFixB2.Sector
