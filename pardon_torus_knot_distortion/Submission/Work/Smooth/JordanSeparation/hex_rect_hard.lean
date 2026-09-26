import Mathlib
import Submission.Work.Smooth.JordanSeparation.wall_LR

namespace Work.Smooth.JordanSeparation

/-- Two cells of a `W × H` grid share an edge. -/
def Adj4r {W H : ℕ} (a b : Fin W × Fin H) : Prop :=
  (a.1 = b.1 ∧ (a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)) ∨
  (a.2 = b.2 ∧ (a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1))

/-- Two cells of a `W × H` grid share an edge or a corner. -/
def Adj8r {W H : ℕ} (a b : Fin W × Fin H) : Prop :=
  (a.1 = b.1 ∨ a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1) ∧
  (a.2 = b.2 ∨ a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)

/-- The `Fin W × Fin H` cell underlying an integer cell known to be in the grid. -/
noncomputable def toCell {W H : ℕ} (c : Cell) (h : inGrid W H c) : Fin W × Fin H :=
  (⟨c.1.toNat, by obtain ⟨h1, h2, _, _⟩ := h; omega⟩,
   ⟨c.2.toNat, by obtain ⟨_, _, h3, h4⟩ := h; omega⟩)

@[simp] lemma toCell_fst_val {W H : ℕ} (c : Cell) (h : inGrid W H c) :
    ((toCell c h).1 : ℕ) = c.1.toNat := rfl

@[simp] lemma toCell_snd_val {W H : ℕ} (c : Cell) (h : inGrid W H c) :
    ((toCell c h).2 : ℕ) = c.2.toNat := rfl

lemma toCell_fst_eq {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : a.1 = b.1) : (toCell a ha).1 = (toCell b hb).1 := by
  apply Fin.ext; simp only [toCell_fst_val, h]

lemma toCell_snd_eq {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : a.2 = b.2) : (toCell a ha).2 = (toCell b hb).2 := by
  apply Fin.ext; simp only [toCell_snd_val, h]

lemma toCell_fst_le {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : a.1 + 1 = b.1) : (toCell a ha).1.1 + 1 = (toCell b hb).1.1 := by
  have e1 : ((toCell a ha).1.1 : ℤ) = a.1 := by
    simp only [toCell_fst_val]; exact Int.toNat_of_nonneg ha.1
  have e2 : ((toCell b hb).1.1 : ℤ) = b.1 := by
    simp only [toCell_fst_val]; exact Int.toNat_of_nonneg hb.1
  omega

lemma toCell_fst_le' {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : b.1 + 1 = a.1) : (toCell b hb).1.1 + 1 = (toCell a ha).1.1 := by
  have e1 : ((toCell a ha).1.1 : ℤ) = a.1 := by
    simp only [toCell_fst_val]; exact Int.toNat_of_nonneg ha.1
  have e2 : ((toCell b hb).1.1 : ℤ) = b.1 := by
    simp only [toCell_fst_val]; exact Int.toNat_of_nonneg hb.1
  omega

lemma toCell_snd_le {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : a.2 + 1 = b.2) : (toCell a ha).2.1 + 1 = (toCell b hb).2.1 := by
  have e1 : ((toCell a ha).2.1 : ℤ) = a.2 := by
    simp only [toCell_snd_val]; exact Int.toNat_of_nonneg ha.2.2.1
  have e2 : ((toCell b hb).2.1 : ℤ) = b.2 := by
    simp only [toCell_snd_val]; exact Int.toNat_of_nonneg hb.2.2.1
  omega

lemma toCell_snd_le' {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : b.2 + 1 = a.2) : (toCell b hb).2.1 + 1 = (toCell a ha).2.1 := by
  have e1 : ((toCell a ha).2.1 : ℤ) = a.2 := by
    simp only [toCell_snd_val]; exact Int.toNat_of_nonneg ha.2.2.1
  have e2 : ((toCell b hb).2.1 : ℤ) = b.2 := by
    simp only [toCell_snd_val]; exact Int.toNat_of_nonneg hb.2.2.1
  omega

lemma adj4_toCell {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : adj4 a b) : Adj4r (toCell a ha) (toCell b hb) := by
  rw [adj4] at h
  rcases h with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · left
    refine ⟨toCell_fst_eq ha hb h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inr (toCell_snd_le' ha hb h2.symm)
    · exact Or.inl (toCell_snd_le ha hb h2.symm)
  · right
    refine ⟨toCell_snd_eq ha hb h2, ?_⟩
    rcases h1 with h1 | h1
    · exact Or.inr (toCell_fst_le' ha hb h1.symm)
    · exact Or.inl (toCell_fst_le ha hb h1.symm)

/-- `8`-adjacency of integer cells transports to `Adj8r`. -/
lemma adj8_toCell {W H : ℕ} {a b : Cell} (ha : inGrid W H a) (hb : inGrid W H b)
    (h : adj8 a b) : Adj8r (toCell a ha) (toCell b hb) := by
  obtain ⟨hm, hn⟩ := h
  have hm' : a.1 = b.1 ∨ a.1 + 1 = b.1 ∨ a.1 = b.1 + 1 := by
    rw [abs_le] at hm; omega
  have hn' : a.2 = b.2 ∨ a.2 + 1 = b.2 ∨ a.2 = b.2 + 1 := by
    rw [abs_le] at hn; omega
  refine ⟨?_, ?_⟩
  · rcases hm' with h | h | h
    · exact Or.inl (toCell_fst_eq ha hb h)
    · exact Or.inr (Or.inl (toCell_fst_le ha hb h))
    · exact Or.inr (Or.inr (toCell_fst_le' ha hb h.symm))
  · rcases hn' with h | h | h
    · exact Or.inl (toCell_snd_eq ha hb h)
    · exact Or.inr (Or.inl (toCell_snd_le ha hb h))
    · exact Or.inr (Or.inr (toCell_snd_le' ha hb h.symm))

/-- A free integer cell gives a `blocked`-free grid cell. -/
lemma toCell_free {W H : ℕ} {blocked : Fin W × Fin H → Prop} {c : Cell}
    (h : freeCell W H blocked c) : ¬ blocked (toCell c h.1) := by
  have h2 := h.2
  rw [blockedZ, dif_pos h.1] at h2
  simpa only [toCell] using h2

/-- A blocked integer cell gives a `blocked` grid cell. -/
lemma toCell_blocked {W H : ℕ} {blocked : Fin W × Fin H → Prop} {c : Cell}
    (h : inGrid W H c) (hb : blockedZ W H blocked c) : blocked (toCell c h) := by
  rw [blockedZ, dif_pos h] at hb
  simpa only [toCell] using hb

lemma toCell_col0 {W H : ℕ} {c : Cell} (h : inGrid W H c) (hc : c.1 = 0) :
    (toCell c h).1.1 = 0 := by
  simp only [toCell_fst_val]; omega

lemma toCell_colW {W H : ℕ} {c : Cell} (h : inGrid W H c) (hc : c.1 + 1 = W) :
    (toCell c h).1.1 + 1 = W := by
  simp only [toCell_fst_val]
  have h1 : (c.1.toNat : ℤ) = c.1 := Int.toNat_of_nonneg h.1
  omega

lemma toCell_row0 {W H : ℕ} {c : Cell} (h : inGrid W H c) (hc : c.2 = 0) :
    (toCell c h).2.1 = 0 := by
  simp only [toCell_snd_val]; omega

lemma toCell_rowH {W H : ℕ} {c : Cell} (h : inGrid W H c) (hc : c.2 + 1 = H) :
    (toCell c h).2.1 + 1 = H := by
  simp only [toCell_snd_val]
  have h1 : (c.2.toNat : ℤ) = c.2 := Int.toNat_of_nonneg h.2.2.1
  omega

theorem hex_rect_hard {W H : ℕ} (hW : 0 < W) (hH : 0 < H) (blocked : Fin W × Fin H → Prop)
    (hno : ¬ ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin W × Fin H, (∀ i, blocked (f i)) ∧
        (∀ i : Fin m, Adj8r (f i.castSucc) (f i.succ)) ∧
        (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = W) :
    ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin W × Fin H, (∀ i, ¬ blocked (f i)) ∧
        (∀ i : Fin m, Adj4r (f i.castSucc) (f i.succ)) ∧
        (f 0).2.1 = 0 ∧ (f (Fin.last m)).2.1 + 1 = H := by
  classical
  -- Step 1: some cell of the top row `H - 1` belongs to the free bottom component `Areg`.
  have key : ∃ c : Cell, Areg W H blocked c ∧ c.2 = (H : ℤ) - 1 := by
    by_contra hcon
    have htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1 := by
      intro c hc hceq
      exact hcon ⟨c, hc, hceq⟩
    obtain ⟨m, g, hcells, hadj, h0, hlast⟩ := wall_LR hW hH blocked htop
    exact hno ⟨m, (fun k => toCell (g k) (hcells k).1),
      (fun k => toCell_blocked (hcells k).1 (chainCell_blocked blocked hW (hcells k))),
      (fun k => adj8_toCell (hcells k.castSucc).1 (hcells k.succ).1 (hadj k)),
      toCell_col0 (hcells 0).1 h0,
      toCell_colW (hcells (Fin.last m)).1 hlast⟩
  obtain ⟨c, hc, hcH⟩ := key
  obtain ⟨hfree, m, f, hf0, hflast, hffree, hfadj⟩ := hc
  exact ⟨m, (fun k => toCell (f k) (hffree k).1),
    (fun k => toCell_free (hffree k)),
    (fun k => adj4_toCell (hffree k.castSucc).1 (hffree k.succ).1 (hfadj k)),
    toCell_row0 (hffree 0).1 hf0,
    toCell_rowH (hffree (Fin.last m)).1 (by rw [hflast]; omega)⟩

end Work.Smooth.JordanSeparation
