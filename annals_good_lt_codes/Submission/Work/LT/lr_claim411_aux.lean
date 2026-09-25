import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.local_search_defs

open Classical
namespace Work.LT
set_option maxHeartbeats 800000
variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

noncomputable def E411 (A : Fin Δ → G) (v : Vtx G) : Finset (EIdx G Δ) :=
  Finset.univ.image (fun i => aIdx A v i)

noncomputable def Eb411 (B : Fin Δ → G) (v : Vtx G) : Finset (EIdx G Δ) :=
  Finset.univ.image (fun j => bIdx B v j)

lemma aIdx_inj411 (A : Fin Δ → G) (v : Vtx G) : Function.Injective (fun i : Fin Δ => aIdx A v i) := by
  intro i i' h
  have hh := congrArg (fun p : EIdx G Δ => p.2.2) h
  simp only [aIdx] at hh
  split_ifs at hh <;> simpa using hh

lemma bIdx_inj411 (B : Fin Δ → G) (v : Vtx G) : Function.Injective (fun j : Fin Δ => bIdx B v j) := by
  intro j j' h
  have hh := congrArg (fun p : EIdx G Δ => p.2.2) h
  simp only [bIdx] at hh
  split_ifs at hh <;> simpa using hh

lemma mem_E411_iff (A : Fin Δ → G) (v : Vtx G) (p : EIdx G Δ) :
    p ∈ E411 A v ↔ aEnd A p 0 = v ∨ aEnd A p 1 = v := by
  obtain ⟨a, b, gg⟩ := v
  constructor
  · intro hp
    rw [E411, Finset.mem_image] at hp
    obtain ⟨i, -, hi⟩ := hp
    rw [← hi]
    fin_cases a
    · left; exact aEnd_aIdx A (0, b, gg) i
    · right; exact aEnd_aIdx A (1, b, gg) i
  · intro hp
    rw [E411, Finset.mem_image]
    rcases hp with h | h
    · exact ⟨p.2.2, Finset.mem_univ _, by rw [← h]; exact aIdx_aEnd A p 0⟩
    · exact ⟨p.2.2, Finset.mem_univ _, by rw [← h]; exact aIdx_aEnd A p 1⟩

lemma mem_Eb411_iff (B : Fin Δ → G) (v : Vtx G) (p : EIdx G Δ) :
    p ∈ Eb411 B v ↔ bEnd B p 0 = v ∨ bEnd B p 1 = v := by
  obtain ⟨a, b, gg⟩ := v
  constructor
  · intro hp
    rw [Eb411, Finset.mem_image] at hp
    obtain ⟨j, -, hj⟩ := hp
    rw [← hj]
    fin_cases b
    · left; exact bEnd_bIdx B (a, 0, gg) j
    · right; exact bEnd_bIdx B (a, 1, gg) j
  · intro hp
    rw [Eb411, Finset.mem_image]
    rcases hp with h | h
    · exact ⟨p.2.2, Finset.mem_univ _, by rw [← h]; exact bIdx_bEnd B p 0⟩
    · exact ⟨p.2.2, Finset.mem_univ _, by rw [← h]; exact bIdx_bEnd B p 1⟩

lemma disputeA_view411 (A : Fin Δ → G) (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (p : EIdx G Δ) :
    disputeA A W p.1 p.2.1 p.2.2 ↔
      ∃ j, view W (aEnd A p 0) (p.2.2, j) ≠ view W (aEnd A p 1) (p.2.2, j) := by
  simp [disputeA, view, aEnd]

lemma disputeB_view411 (B : Fin Δ → G) (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (p : EIdx G Δ) :
    disputeB B W p.1 p.2.1 p.2.2 ↔
      ∃ i, view W (bEnd B p 0) (i, p.2.2) ≠ view W (bEnd B p 1) (i, p.2.2) := by
  simp [disputeB, view, bEnd]

lemma view_updateAt411 (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (u v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    view (updateAt W v.1 v.2.1 v.2.2 w) u = if u = v then w else view W u := by
  by_cases h : u = v
  · subst h
    rw [if_pos rfl]
    simp [view, updateAt]
  · rw [if_neg h]
    obtain ⟨a,b,g⟩ := u
    obtain ⟨a',b',g'⟩ := v
    have hne : ¬(a = a' ∧ b = b' ∧ g = g') := by
      rintro ⟨h1,h2,h3⟩; exact h (by simp [h1,h2,h3])
    simp only [view]
    rw [updateAt_of_ne _ _ _ _ _ hne]

lemma disputeA_updateAt_of_not_mem_E411 (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) (p : EIdx G Δ) (hp : p ∉ E411 A v) :
    disputeA A (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2 ↔
      disputeA A W p.1 p.2.1 p.2.2 := by
  have hv0 : aEnd A p 0 ≠ v := fun h => hp ((mem_E411_iff A v p).mpr (Or.inl h))
  have hv1 : aEnd A p 1 ≠ v := fun h => hp ((mem_E411_iff A v p).mpr (Or.inr h))
  rw [disputeA_view411, disputeA_view411]
  have e0 : view (updateAt W v.1 v.2.1 v.2.2 w) (aEnd A p 0) = view W (aEnd A p 0) := by
    rw [view_updateAt411, if_neg hv0]
  have e1 : view (updateAt W v.1 v.2.1 v.2.2 w) (aEnd A p 1) = view W (aEnd A p 1) := by
    rw [view_updateAt411, if_neg hv1]
  rw [e0, e1]

lemma disputeB_updateAt_of_not_mem_Eb411 (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) (p : EIdx G Δ) (hp : p ∉ Eb411 B v) :
    disputeB B (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2 ↔
      disputeB B W p.1 p.2.1 p.2.2 := by
  have hv0 : bEnd B p 0 ≠ v := fun h => hp ((mem_Eb411_iff B v p).mpr (Or.inl h))
  have hv1 : bEnd B p 1 ≠ v := fun h => hp ((mem_Eb411_iff B v p).mpr (Or.inr h))
  rw [disputeB_view411, disputeB_view411]
  have e0 : view (updateAt W v.1 v.2.1 v.2.2 w) (bEnd B p 0) = view W (bEnd B p 0) := by
    rw [view_updateAt411, if_neg hv0]
  have e1 : view (updateAt W v.1 v.2.1 v.2.2 w) (bEnd B p 1) = view W (bEnd B p 1) := by
    rw [view_updateAt411, if_neg hv1]
  rw [e0, e1]

lemma disputeA_aIdx_updateAt411 (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) (i : Fin Δ) :
    disputeA A (updateAt W v.1 v.2.1 v.2.2 w) (aIdx A v i).1 (aIdx A v i).2.1 (aIdx A v i).2.2 ↔
      ∃ j, view W (nA A v i) (i, j) ≠ w (i, j) := by
  rw [disputeA_view411]
  obtain ⟨a, b, g⟩ := v
  fin_cases a <;>
    simp [aIdx, aEnd, nA, view, updateAt, ne_comm]

lemma disputeB_bIdx_updateAt411 (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) (j : Fin Δ) :
    disputeB B (updateAt W v.1 v.2.1 v.2.2 w) (bIdx B v j).1 (bIdx B v j).2.1 (bIdx B v j).2.2 ↔
      ∃ i, view W (nB B v j) (i, j) ≠ w (i, j) := by
  rw [disputeB_view411]
  obtain ⟨a, b, g⟩ := v
  fin_cases b <;>
    simp [bIdx, bEnd, nB, view, updateAt, ne_comm]

lemma E411_filter_dA_card (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    ((E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2)).card = rA A W v := by
  have h : (E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2) =
      (Finset.univ.filter (fun i : Fin Δ => dispAE A W v i)).image (fun i => aIdx A v i) := by
    rw [E411, Finset.filter_image]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact disputeA_aIdx A W v i
  rw [h, Finset.card_image_of_injective _ (aIdx_inj411 A v)]
  rfl

lemma Eb411_filter_dB_card (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    ((Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2)).card = rB B W v := by
  have h : (Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2) =
      (Finset.univ.filter (fun j : Fin Δ => dispBE B W v j)).image (fun j => bIdx B v j) := by
    rw [Eb411, Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact disputeB_bIdx B W v j
  rw [h, Finset.card_image_of_injective _ (bIdx_inj411 B v)]
  rfl

lemma E411_filter_dA'_card (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    ((E411 A v).filter (fun p => disputeA A (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2)).card =
      (Finset.univ.filter (fun i : Fin Δ => ∃ j, view W (nA A v i) (i, j) ≠ w (i, j))).card := by
  have h : (E411 A v).filter
        (fun p => disputeA A (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2) =
      (Finset.univ.filter (fun i : Fin Δ => ∃ j, view W (nA A v i) (i, j) ≠ w (i, j))).image
        (fun i => aIdx A v i) := by
    rw [E411, Finset.filter_image]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact disputeA_aIdx_updateAt411 A W v w i
  rw [h, Finset.card_image_of_injective _ (aIdx_inj411 A v)]

lemma Eb411_filter_dB'_card (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    ((Eb411 B v).filter (fun p => disputeB B (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2)).card =
      (Finset.univ.filter (fun j : Fin Δ => ∃ i, view W (nB B v j) (i, j) ≠ w (i, j))).card := by
  have h : (Eb411 B v).filter
        (fun p => disputeB B (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2) =
      (Finset.univ.filter (fun j : Fin Δ => ∃ i, view W (nB B v j) (i, j) ≠ w (i, j))).image
        (fun j => bIdx B v j) := by
    rw [Eb411, Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact disputeB_bIdx_updateAt411 B W v w j
  rw [h, Finset.card_image_of_injective _ (bIdx_inj411 B v)]

lemma Adisp411_split (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    (Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2)).card =
      ((E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2)).card +
      ((Finset.univ \ E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2)).card := by
  have hA : (Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2)).filter
        (fun x => x ∈ E411 A v) =
      (E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hA' : (Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2)).filter
        (fun x => x ∉ E411 A v) =
      (Finset.univ \ E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    tauto
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2))
    (fun x => x ∈ E411 A v)
  rw [hA, hA'] at h
  exact h.symm

lemma Bdisp411_split (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    (Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2)).card =
      ((Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2)).card +
      ((Finset.univ \ Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2)).card := by
  have hA : (Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2)).filter
        (fun x => x ∈ Eb411 B v) =
      (Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hA' : (Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2)).filter
        (fun x => x ∉ Eb411 B v) =
      (Finset.univ \ Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    tauto
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2))
    (fun x => x ∈ Eb411 B v)
  rw [hA, hA'] at h
  exact h.symm

lemma Adisp411_id (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    (Finset.univ.filter (fun p : EIdx G Δ =>
        disputeA A (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2)).card + rA A W v =
      (Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2)).card +
        (Finset.univ.filter (fun i : Fin Δ => ∃ j, view W (nA A v i) (i, j) ≠ w (i, j))).card := by
  have hs1 := Adisp411_split A W v
  have hs2 := Adisp411_split A (updateAt W v.1 v.2.1 v.2.2 w) v
  have hcard := E411_filter_dA_card A W v
  have hcard' := E411_filter_dA'_card A W v w
  have hEq : (Finset.univ \ E411 A v).filter
        (fun p => disputeA A (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2) =
      (Finset.univ \ E411 A v).filter (fun p => disputeA A W p.1 p.2.1 p.2.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxE, hd⟩
      exact ⟨hxE, (disputeA_updateAt_of_not_mem_E411 A W v w x hxE).mp hd⟩
    · rintro ⟨hxE, hd⟩
      exact ⟨hxE, (disputeA_updateAt_of_not_mem_E411 A W v w x hxE).mpr hd⟩
  rw [hs1, hs2, hcard, hcard', hEq]
  omega

lemma Bdisp411_id (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    (Finset.univ.filter (fun p : EIdx G Δ =>
        disputeB B (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2)).card + rB B W v =
      (Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2)).card +
        (Finset.univ.filter (fun j : Fin Δ => ∃ i, view W (nB B v j) (i, j) ≠ w (i, j))).card := by
  have hs1 := Bdisp411_split B W v
  have hs2 := Bdisp411_split B (updateAt W v.1 v.2.1 v.2.2 w) v
  have hcard := Eb411_filter_dB_card B W v
  have hcard' := Eb411_filter_dB'_card B W v w
  have hEq : (Finset.univ \ Eb411 B v).filter
        (fun p => disputeB B (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2) =
      (Finset.univ \ Eb411 B v).filter (fun p => disputeB B W p.1 p.2.1 p.2.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxE, hd⟩
      exact ⟨hxE, (disputeB_updateAt_of_not_mem_Eb411 B W v w x hxE).mp hd⟩
    · rintro ⟨hxE, hd⟩
      exact ⟨hxE, (disputeB_updateAt_of_not_mem_Eb411 B W v w x hxE).mpr hd⟩
  rw [hs1, hs2, hcard, hcard', hEq]
  omega

theorem dispCount_updateAt_add_lr411 {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    dispCount A B (updateAt W v.1 v.2.1 v.2.2 w) + (rA A W v + rB B W v) =
      dispCount A B W +
        (Finset.univ.filter (fun i : Fin Δ => ∃ j, view W (nA A v i) (i, j) ≠ w (i, j))).card +
        (Finset.univ.filter (fun j : Fin Δ => ∃ i, view W (nB B v j) (i, j) ≠ w (i, j))).card := by
  have hA := Adisp411_id A W v w
  have hB := Bdisp411_id B W v w
  have hdW : dispCount A B W =
      (Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2)).card +
      (Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2)).card := rfl
  have hdW' : dispCount A B (updateAt W v.1 v.2.1 v.2.2 w) =
      (Finset.univ.filter (fun p : EIdx G Δ =>
          disputeA A (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2)).card +
      (Finset.univ.filter (fun p : EIdx G Δ =>
          disputeB B (updateAt W v.1 v.2.1 v.2.2 w) p.1 p.2.1 p.2.2)).card := rfl
  rw [hdW, hdW']
  omega

end Work.LT
