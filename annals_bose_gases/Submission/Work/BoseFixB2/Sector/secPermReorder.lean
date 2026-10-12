import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.Sector.secPermDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Reordering the iterated slot operators

`blockOpL ℓ L` composes the slot operators of a list `L` in the order of the list
(head applied last).  The purpose of this file is the **reordering** fact: at slots
of *different* slots the operators commute (`aP_comm`, `aP_aQ_comm`, `aQ_comm`), so
the composite depends only on the multiset of `(slot, flag)` pairs, and a list that
uses each slot of `{0,…,N−1}` exactly once composes to `blockOp ℓ (kindSet L) N`.

Main results:

* `blockOpL_peel` — a list `A ++ p :: B` acts as `slotOp p` applied last, provided
  no slot of `A` is the slot of `p`;
* `blockOpL_congr_set` — lists with the same set of `(slot, flag)` pairs (and
  distinct slots) give the same operator;
* `blockOpL_reorder` — `blockOpL ℓ L Φ = blockOp ℓ (kindSet L) N Φ` for a list `L`
  with distinct slots, all slots `< N` and `L.length = N`.
-/

noncomputable section

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. List decomposition -/

/-- A list containing `a` splits as `A ++ a :: B`. -/
lemma exists_append_of_mem {α : Type*} {a : α} {L : List α} (h : a ∈ L) :
    ∃ A B : List α, L = A ++ a :: B := by
  induction L with
  | nil => simp at h
  | cons c L ih =>
      rcases eq_or_ne c a with rfl | hca
      · exact ⟨[], L, rfl⟩
      · obtain ⟨A, B, hAB⟩ := ih (by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hca
          · exact h)
        exact ⟨c :: A, B, by rw [hAB]; rfl⟩

/-! ## 2. Continuity of the iterated operator -/

/-- The iterated slot operator preserves continuity. -/
lemma continuous_blockOpL {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} :
    ∀ (L : List (ℕ × Bool)) {Φ : X N → ℝ}, Continuous Φ → Continuous (blockOpL ℓ L Φ) := by
  intro L
  induction L with
  | nil => intro Φ hΦ; simpa using hΦ
  | cons p L ih =>
      intro Φ hΦ
      rcases p with ⟨m, b⟩
      rw [blockOpL_cons]
      by_cases hm : m < N
      · rw [dif_pos hm]
        cases b
        · simpa using aP_continuous hℓ ⟨m, hm⟩ (ih hΦ)
        · simpa using aQ_continuous hℓ ⟨m, hm⟩ (ih hΦ)
      · rw [dif_neg hm]
        exact ih hΦ

/-! ## 3. Slot operators of distinct slots commute -/

/-- The single-slot operators of distinct slots commute. -/
lemma slotOp_comm {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {j₁ j₂ : Fin N} (hne : j₁ ≠ j₂)
    {b₁ b₂ : Bool} {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    slotOp ℓ j₁ b₁ (slotOp ℓ j₂ b₂ Ψ) = slotOp ℓ j₂ b₂ (slotOp ℓ j₁ b₁ Ψ) := by
  cases b₁ <;> cases b₂ <;> simp only [slotOp_true, slotOp_false]
  · exact funext fun x => aP_comm hℓ j₁ j₂ hΨ x
  · exact funext fun x => aP_aQ_comm hℓ hne hΨ x
  · exact funext fun x => (aP_aQ_comm hℓ hne.symm hΨ x).symm
  · exact funext fun x => aQ_comm hℓ hne hΨ x

/-- **Moving a slot operator past an iterated one.**  If no slot of the list `A` is
the slot `j`, the operator `slotOp ℓ j b` commutes with `blockOpL ℓ A`. -/
lemma blockOpL_comm_slotOp {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {j : ℕ} (hj : j < N) {b : Bool} :
    ∀ (A : List (ℕ × Bool)) {Ψ : X N → ℝ}, Continuous Ψ → (∀ p ∈ A, p.1 ≠ j) →
      blockOpL ℓ A (slotOp ℓ ⟨j, hj⟩ b Ψ) = slotOp ℓ ⟨j, hj⟩ b (blockOpL ℓ A Ψ) := by
  intro A
  induction A with
  | nil => intro Ψ _ _; rfl
  | cons p A ih =>
      intro Ψ hΨ hA
      rcases p with ⟨m, b'⟩
      rw [blockOpL_cons, blockOpL_cons]
      by_cases hm : m < N
      · rw [dif_pos hm, dif_pos hm, ih hΨ (fun q hq => hA q (by simp [hq]))]
        refine slotOp_comm hℓ ?_ (continuous_blockOpL hℓ A hΨ)
        intro h
        exact hA (m, b') (by simp) (congrArg Fin.val h)
      · rw [dif_neg hm, dif_neg hm]
        exact ih hΨ (fun q hq => hA q (by simp [hq]))

/-- `blockOpL` of a concatenation. -/
lemma blockOpL_append {ℓ : ℝ} {N : ℕ} (A C : List (ℕ × Bool)) (Φ : X N → ℝ) :
    blockOpL ℓ (A ++ C) Φ = blockOpL ℓ A (blockOpL ℓ C Φ) := by
  induction A with
  | nil => rfl
  | cons p A ih =>
      rw [List.cons_append, blockOpL_cons, blockOpL_cons, ih]

/-- **The head of a list of slot operators is applied last.**  Peeling an entry
`p` out of the middle of a list: `blockOpL ℓ (A ++ p :: B) = slotOp p ∘ blockOpL ℓ (A ++ B)`,
as long as no slot of `A` equals the slot of `p`. -/
lemma blockOpL_peel {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {A B : List (ℕ × Bool)} {p : ℕ × Bool}
    (hpN : p.1 < N) (hA : ∀ q ∈ A, q.1 ≠ p.1) {Φ : X N → ℝ} (hΦ : Continuous Φ) :
    blockOpL ℓ (A ++ p :: B) Φ = slotOp ℓ ⟨p.1, hpN⟩ p.2 (blockOpL ℓ (A ++ B) Φ) := by
  rw [blockOpL_append, blockOpL_cons_of_lt hpN,
    blockOpL_comm_slotOp hℓ hpN A (continuous_blockOpL hℓ B hΦ) hA, ← blockOpL_append]

/-! ## 4. The iterated operator depends only on the set of `(slot, flag)` pairs -/

/-- **`blockOpL` depends only on the set of pairs.**  Two lists with distinct slots
and the same set of `(slot, flag)` pairs give the same iterated operator. -/
lemma blockOpL_congr_set {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} :
    ∀ (L₁ L₂ : List (ℕ × Bool)), (L₁.map (fun p => p.1)).Nodup →
      (L₂.map (fun p => p.1)).Nodup → (∀ p ∈ L₁, p.1 < N) → (∀ p, p ∈ L₁ ↔ p ∈ L₂) →
      ∀ {Φ : X N → ℝ}, Continuous Φ → blockOpL ℓ L₁ Φ = blockOpL ℓ L₂ Φ := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ hnd₁ hnd₂ hlt₁ hset Φ hΦ
      have hL₂ : L₂ = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro p
        rw [← hset p]
        simp
      rw [hL₂]
  | cons p L₁ ih =>
      intro L₂ hnd₁ hnd₂ hlt₁ hset Φ hΦ
      obtain ⟨m, b⟩ := p
      have hpL₂ : (m, b) ∈ L₂ := (hset (m, b)).mp (by simp)
      obtain ⟨A, B, hAB⟩ := exists_append_of_mem hpL₂
      -- hypotheses
      have hmN : m < N := hlt₁ (m, b) (by simp)
      have hnd₁' : (L₁.map (fun p => p.1)).Nodup := by
        have := hnd₁
        rw [List.map_cons] at this
        exact (List.nodup_cons.mp this).2
      have hlt₁' : ∀ q ∈ L₁, q.1 < N := fun q hq => hlt₁ q (List.mem_cons_of_mem _ hq)
      have hm_notin : (m, b) ∉ L₁ := by
        intro hmem
        have h1 := (List.nodup_cons.mp hnd₁).1
        exact h1 (List.mem_map_of_mem (f := fun p : ℕ × Bool => p.1) hmem)
      have hnd₂pairs : L₂.Nodup := List.Nodup.of_map (fun p : ℕ × Bool => p.1) hnd₂
      have hdisj : List.Disjoint A ((m, b) :: B) := by
        rw [hAB] at hnd₂pairs
        exact List.disjoint_of_nodup_append hnd₂pairs
      have hm_notin_AB : (m, b) ∉ A ++ B := by
        have hmid : ((m, b) :: (A ++ B)).Nodup := by
          have h := hnd₂pairs
          rw [hAB] at h
          exact (List.nodup_middle (a := (m, b))).mp h
        exact (List.nodup_cons.mp hmid).1
      have hnd₂' : ((A ++ B).map (fun p => p.1)).Nodup := by
        have h1 : (A.map (fun p => p.1) ++ m :: B.map (fun p => p.1)).Nodup := by
          rw [hAB, List.map_append, List.map_cons] at hnd₂
          exact hnd₂
        have h2 : (m :: (A.map (fun p => p.1) ++ B.map (fun p => p.1))).Nodup :=
          (List.nodup_middle (a := m)).mp h1
        have h3 := (List.nodup_cons.mp h2).2
        simpa only [List.map_append] using h3
      have hA : ∀ q ∈ A, q.1 ≠ m := by
        intro q hq hqm
        have inj₂ : ∀ q' ∈ L₂, ∀ q'' ∈ L₂, q'.1 = q''.1 → q' = q'' :=
          List.inj_on_of_nodup_map hnd₂
        have hqL₂ : q ∈ L₂ := by
          rw [hAB]
          exact List.mem_append_left _ hq
        have hqeq : q = (m, b) :=
          inj₂ q hqL₂ (m, b) (by rw [hAB]; exact List.mem_append_right _ (by simp)) hqm
        rw [hqeq] at hq
        exact hdisj hq (by simp)
      have hset' : ∀ q, q ∈ L₁ ↔ q ∈ A ++ B := by
        intro q
        constructor
        · intro hq
          have h2 : q ∈ L₂ := (hset q).mp (List.mem_cons_of_mem _ hq)
          rw [hAB, List.mem_append, List.mem_cons] at h2
          rcases h2 with h2 | h2 | h2
          · exact List.mem_append_left _ h2
          · subst h2
            exact absurd hq hm_notin
          · exact List.mem_append_right _ h2
        · intro hq
          have h2 : q ∈ L₂ := by
            rw [hAB, List.mem_append]
            rw [List.mem_append] at hq
            rcases hq with hq | hq
            · exact Or.inl hq
            · exact Or.inr (List.mem_cons_of_mem _ hq)
          have h3 : q ∈ (m, b) :: L₁ := (hset q).mpr h2
          rcases List.mem_cons.mp h3 with h3 | h3
          · subst h3
            exact absurd hq hm_notin_AB
          · exact h3
      rw [blockOpL_cons, dif_pos hmN, hAB, blockOpL_peel hℓ hmN hA hΦ,
        ih (A ++ B) hnd₁' hnd₂' hlt₁' hset' hΦ]

/-! ## 5. The standard list has distinct slots -/

lemma stdList_nodup_fst (S : Finset ℕ) : ∀ k, ((stdList S k).map (fun p => p.1)).Nodup
  | 0 => by simp
  | (k + 1) => by
      rw [stdList_succ, List.map_cons]
      refine List.Nodup.cons ?_ (stdList_nodup_fst S k)
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨q, hq, hq1⟩ := hmem
      have := stdList_slot_lt hq
      omega

/-! ## 6. The reordering lemma -/

/-- **Reordering.**  A list of slot operators that uses every slot of
`{0, …, N−1}` exactly once composes to `blockOp ℓ (kindSet L) N`. -/
lemma blockOpL_reorder {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {L : List (ℕ × Bool)}
    (hnd : (L.map (fun p => p.1)).Nodup) (hlt : ∀ p ∈ L, p.1 < N) (hlen : L.length = N)
    {Φ : X N → ℝ} (hΦ : Continuous Φ) :
    blockOpL ℓ L Φ = blockOp ℓ (kindSet L) N Φ := by
  -- every slot `< N` occurs in `L`
  have hcover : ∀ j < N, ∃ p ∈ L, p.1 = j := by
    intro j hj
    have hcard : (L.map (fun p => p.1)).toFinset.card = N := by
      rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen]
    have hsub : (L.map (fun p => p.1)).toFinset ⊆ Finset.range N := by
      intro i hi
      rw [List.mem_toFinset, List.mem_map] at hi
      obtain ⟨q, hq, rfl⟩ := hi
      exact Finset.mem_range.mpr (hlt q hq)
    have heq : (L.map (fun p => p.1)).toFinset = Finset.range N :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
    have hmem : j ∈ (L.map (fun p => p.1)).toFinset := by
      rw [heq]
      exact Finset.mem_range.mpr hj
    rw [List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨q, hq, hq1⟩ := hmem
    exact ⟨q, hq, hq1⟩
  -- the flag of an entry of `L` is the membership of its slot in `kindSet L`
  have hfwd : ∀ p ∈ L, p.2 = decide (p.1 ∈ kindSet L) := by
    rintro ⟨j, b⟩ hp
    cases b
    · have hjS : ¬ (j ∈ kindSet L) := by
        intro hjS
        rw [mem_kindSet] at hjS
        obtain ⟨q, hq, hq2, hq1⟩ := hjS
        have hqeq : q = (j, false) := List.inj_on_of_nodup_map hnd hq hp hq1
        rw [hqeq] at hq2
        exact Bool.noConfusion hq2
      simp [hjS]
    · have hjS : j ∈ kindSet L := by
        rw [mem_kindSet]
        exact ⟨(j, true), hp, rfl, rfl⟩
      simp [hjS]
  have hmem : ∀ p : ℕ × Bool, p ∈ L ↔ p ∈ stdList (kindSet L) N := by
    rintro ⟨j, b⟩
    rw [mem_stdList]
    constructor
    · intro hp
      have hjN : j < N := hlt (j, b) hp
      have hb : b = decide (j ∈ kindSet L) := hfwd (j, b) hp
      exact ⟨j, hjN, by rw [hb]⟩
    · rintro ⟨k, hkN, hkb⟩
      rw [Prod.mk.injEq] at hkb
      obtain ⟨hjk, hbk⟩ := hkb
      subst hjk
      obtain ⟨q, hq, hq1⟩ := hcover j hkN
      have h2 : q.2 = decide (j ∈ kindSet L) := by
        have := hfwd q hq
        rwa [hq1] at this
      have hqeq : q = (j, b) := Prod.ext hq1 (h2.trans hbk.symm)
      rw [hqeq] at hq
      exact hq
  have h1 : blockOpL ℓ L Φ = blockOpL ℓ (stdList (kindSet L) N) Φ :=
    blockOpL_congr_set hℓ L (stdList (kindSet L) N) hnd (stdList_nodup_fst (kindSet L) N)
      hlt hmem hΦ
  rw [h1, ← blockOp_eq_blockOpL (kindSet L) N]

end Work.BoseFixB2.Sector
