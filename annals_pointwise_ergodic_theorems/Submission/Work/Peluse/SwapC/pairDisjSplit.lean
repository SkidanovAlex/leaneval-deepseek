import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

set_option autoImplicit false

variable {s : ℕ}

/-- A child of `m` agrees with `m` off the split coordinate `⟨m.dep, h⟩`. -/
theorem children_str_eq_of_ne {m : CLeaf s} {h : m.dep < s} {a : CLeaf s}
    (ha : a ∈ m.children h) {i : Fin s} (hi : i ≠ ⟨m.dep, h⟩) : a.str i = m.str i := by
  rw [CLeaf.children] at ha
  rcases List.mem_cons.mp ha with h' | h'
  · rw [h']
  · rw [List.mem_singleton] at h'
    rw [h']
    change Function.update m.str ⟨m.dep, h⟩ true i = m.str i
    rw [Function.update_of_ne hi]

/-- Two children of `m` whose cells meet are equal. -/
theorem children_agree_eq {m : CLeaf s} {h : m.dep < s} {a b : CLeaf s}
    (ha : a ∈ m.children h) (hb : b ∈ m.children h) {x : Fin s → Bool}
    (hxa : Agree x a) (hxb : Agree x b) : a = b := by
  have hda := children_dep_eq ha
  have hdb := children_dep_eq hb
  refine CLeaf.eq_iff.mpr ⟨?_, by omega⟩
  funext i
  by_cases hi : i = ⟨m.dep, h⟩
  · rw [hi]
    have h1 : a.str ⟨m.dep, h⟩ = x ⟨m.dep, h⟩ := hxa _ (by rw [hda]; exact Nat.lt_succ_self _)
    have h2 : b.str ⟨m.dep, h⟩ = x ⟨m.dep, h⟩ := hxb _ (by rw [hdb]; exact Nat.lt_succ_self _)
    rw [h1, h2]
  · rw [children_str_eq_of_ne ha hi, children_str_eq_of_ne hb hi]

/-- A child of `m` and an element of `P` cannot have meeting cells when `m ∉ P`. -/
theorem not_agree_child_mem_left {P Q : List (CLeaf s)} {m : CLeaf s} {h : m.dep < s}
    (hpd : PairDisj (P ++ m :: Q)) (hmP : m ∉ P) {a l : CLeaf s}
    (ha : a ∈ m.children h) (hl : l ∈ P) {x : Fin s → Bool}
    (hxa : Agree x a) (hxl : Agree x l) : False := by
  have hxm : Agree x m := Agree.of_children ha hxa
  have heq : m = l := hpd m (by simp) l (by simp [hl]) ⟨x, hxm, hxl⟩
  exact hmP (by rw [heq]; exact hl)

/-- A child of `m` and an element of `Q` cannot have meeting cells when `m ∉ Q`. -/
theorem not_agree_child_mem_right {P Q : List (CLeaf s)} {m : CLeaf s} {h : m.dep < s}
    (hpd : PairDisj (P ++ m :: Q)) (hmQ : m ∉ Q) {a l : CLeaf s}
    (ha : a ∈ m.children h) (hl : l ∈ Q) {x : Fin s → Bool}
    (hxa : Agree x a) (hxl : Agree x l) : False := by
  have hxm : Agree x m := Agree.of_children ha hxa
  have heq : m = l := hpd m (by simp) l (by simp [hl]) ⟨x, hxm, hxl⟩
  exact hmQ (by rw [heq]; exact hl)

theorem pairDisjSplit {s : ℕ} {P Q : List (Work.Peluse.SwapC.CLeaf s)} {m : Work.Peluse.SwapC.CLeaf s}
    (h : m.dep < s) (hmP : m ∉ P) (hmQ : m ∉ Q) :
    Work.Peluse.SwapC.PairDisj (P ++ m :: Q) → Work.Peluse.SwapC.PairDisj (P ++ m.children h ++ Q) := by
  intro hpd l₁ hl₁ l₂ hl₂ hx
  obtain ⟨x, hx₁, hx₂⟩ := hx
  simp only [List.mem_append] at hl₁ hl₂
  rcases hl₁ with (hl₁ | hl₁) | hl₁
  · rcases hl₂ with (hl₂ | hl₂) | hl₂
    · exact hpd l₁ (by simp [hl₁]) l₂ (by simp [hl₂]) ⟨x, hx₁, hx₂⟩
    · exact (not_agree_child_mem_left hpd hmP hl₂ hl₁ hx₂ hx₁).elim
    · exact hpd l₁ (by simp [hl₁]) l₂ (by simp [hl₂]) ⟨x, hx₁, hx₂⟩
  · rcases hl₂ with (hl₂ | hl₂) | hl₂
    · exact (not_agree_child_mem_left hpd hmP hl₁ hl₂ hx₁ hx₂).elim
    · exact children_agree_eq hl₁ hl₂ hx₁ hx₂
    · exact (not_agree_child_mem_right hpd hmQ hl₁ hl₂ hx₁ hx₂).elim
  · rcases hl₂ with (hl₂ | hl₂) | hl₂
    · exact hpd l₁ (by simp [hl₁]) l₂ (by simp [hl₂]) ⟨x, hx₁, hx₂⟩
    · exact (not_agree_child_mem_right hpd hmQ hl₂ hl₁ hx₂ hx₁).elim
    · exact hpd l₁ (by simp [hl₁]) l₂ (by simp [hl₂]) ⟨x, hx₁, hx₂⟩

end Work.Peluse.SwapC
