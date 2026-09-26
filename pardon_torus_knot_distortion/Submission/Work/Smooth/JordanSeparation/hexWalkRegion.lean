import Mathlib
import Submission.Work.Smooth.JordanSeparation.hexWalk

/-!
# The region `A` and the wall walk

`A` is the union of the free `4`-components touching the bottom row; `Sext` is `A` together with
a virtual free row of cells just below the grid.  `walkN` is the wall-following walk on the
boundary of `Sext` (which keeps `Sext` on its left).
-/

open Classical

namespace Work.Smooth.JordanSeparation

/-- `c` lies inside the `W × H` grid (integer coordinates). -/
def inGrid (W H : ℕ) (c : Cell) : Prop := 0 ≤ c.1 ∧ c.1 < W ∧ 0 ≤ c.2 ∧ c.2 < H

/-- The `blocked` predicate, transported to integer cells (false outside the grid). -/
noncomputable def blockedZ (W H : ℕ) (blocked : Fin W × Fin H → Prop) (c : Cell) : Prop :=
  if h : inGrid W H c then
    blocked (⟨c.1.toNat, by obtain ⟨h1, h2, _, _⟩ := h; omega⟩,
             ⟨c.2.toNat, by obtain ⟨_, _, h3, h4⟩ := h; omega⟩)
  else False

/-- `c` is a free cell of the grid. -/
def freeCell (W H : ℕ) (blocked : Fin W × Fin H → Prop) (c : Cell) : Prop :=
  inGrid W H c ∧ ¬ blockedZ W H blocked c

/-- Two integer cells are `4`-adjacent. -/
def adj4 (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 = b.2 + 1 ∨ b.2 = a.2 + 1)) ∨
  (a.2 = b.2 ∧ (a.1 = b.1 + 1 ∨ b.1 = a.1 + 1))

lemma adj4_symm {a b : Cell} (h : adj4 a b) : adj4 b a := by
  rw [adj4] at h ⊢; tauto

/-- One step of free `4`-connectivity. -/
def freeStep (W H : ℕ) (blocked : Fin W × Fin H → Prop) (a b : Cell) : Prop :=
  freeCell W H blocked a ∧ freeCell W H blocked b ∧ adj4 a b

lemma freeStep_symm {W H : ℕ} {blocked : Fin W × Fin H → Prop} {a b : Cell}
    (h : freeStep W H blocked a b) : freeStep W H blocked b a :=
  ⟨h.2.1, h.1, adj4_symm h.2.2⟩

/-- The free `4`-component of the bottom row: `c` is free and there is a free `4`-chain from a
cell of row `0` to `c`. -/
def Areg (W H : ℕ) (blocked : Fin W × Fin H → Prop) (c : Cell) : Prop :=
  freeCell W H blocked c ∧
    ∃ (m : ℕ) (f : Fin (m + 1) → Cell),
      (f 0).2 = 0 ∧ f (Fin.last m) = c ∧
      (∀ k, freeCell W H blocked (f k)) ∧
      (∀ k : Fin m, adj4 (f k.castSucc) (f k.succ))

/-- The region `Sext = A ∪ (virtual bottom row)`. -/
def Sext (W H : ℕ) (blocked : Fin W × Fin H → Prop) (c : Cell) : Prop :=
  Areg W H blocked c ∨ (0 ≤ c.1 ∧ c.1 < W ∧ c.2 = -1)

/-- The starting crack of the walk. -/
noncomputable def startCrack : Cell × HDir := ((0, -1), HDir.E)

/-- The `n`-th state of the wall-following walk for the region `Sext`. -/
noncomputable def walkN (W H : ℕ) (blocked : Fin W × Fin H → Prop) : ℕ → Cell × HDir
  | 0 => startCrack
  | (n + 1) => step (Sext W H blocked) (walkN W H blocked n)

lemma valid_startCrack {W H : ℕ} (blocked : Fin W × Fin H → Prop) (hW : 0 < W) :
    valid (Sext W H blocked) startCrack.1 startCrack.2 := by
  rw [valid]
  constructor
  · show Sext W H blocked (0, -1)
    exact Or.inr ⟨le_refl 0, by omega, rfl⟩
  · show ¬ Sext W H blocked (0, -2)
    intro h
    exact h.elim (fun hA => by obtain ⟨h1, h2, h3, h4⟩ := hA.1.1; omega)
      (fun hV => by obtain ⟨_, _, hj⟩ := hV; omega)

lemma walkN_valid {W H : ℕ} (blocked : Fin W × Fin H → Prop) (hW : 0 < W) (n : ℕ) :
    valid (Sext W H blocked) (walkN W H blocked n).1 (walkN W H blocked n).2 := by
  induction n with
  | zero => exact valid_startCrack blocked hW
  | succ n ih => exact valid_step _ _ _ ih

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

/-- Two cells are `8`-adjacent (including equal). -/
def adj8 (a b : Cell) : Prop := |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1

/-- A cell lying immediately to the right of one of the cracks of the walk. -/
def chainCell (W H : ℕ) (blocked : Fin W × Fin H → Prop) (c : Cell) : Prop :=
  inGrid W H c ∧ ∃ n : ℕ, rcell (walkN W H blocked n).1 (walkN W H blocked n).2 = c

lemma adj4_lcell_rcell (p : Cell) (d : HDir) : adj4 (lcell p d) (rcell p d) := by
  cases d <;> simp only [lcell, rcell]
  · exact Or.inl ⟨rfl, Or.inl (by omega)⟩
  · exact Or.inr ⟨rfl, Or.inr (by omega)⟩
  · exact Or.inl ⟨rfl, Or.inr (by omega)⟩
  · exact Or.inr ⟨rfl, Or.inl (by omega)⟩

/-- `Areg` is closed under `4`-adjacency inside the free cells. -/
lemma Areg_closed {W H : ℕ} {blocked : Fin W × Fin H → Prop} {a b : Cell}
    (ha : Areg W H blocked a) (hb : freeCell W H blocked b) (h : adj4 a b) :
    Areg W H blocked b := by
  obtain ⟨hfa, m, f, hf0, hflast, hffree, hfadj⟩ := ha
  refine ⟨hb, m + 1, fun i => if hi : i.1 < m + 1 then f ⟨i.1, hi⟩ else b, ?_, ?_, ?_, ?_⟩
  · have h0 : (0 : Fin (m + 1 + 1)).1 < m + 1 := by simp
    simp only [h0, dif_pos]
    exact hf0
  · have hlast : (Fin.last (m + 1)).1 = m + 1 := by simp [Fin.last]
    simp only [hlast]
    rw [dif_neg (lt_irrefl _)]
  · intro k
    by_cases hk : k.1 < m + 1
    · simp only [hk, dif_pos]; exact hffree _
    · simp only [hk, dif_neg, not_false_iff]; exact hb
  · intro k
    have hk1 : k.castSucc.1 = k.1 := rfl
    have hk2 : k.succ.1 = k.1 + 1 := rfl
    by_cases hk : k.1 + 1 < m + 1
    · -- strictly inside: use f's adjacency
      have hkm : k.1 < m := by omega
      have h1 : k.castSucc.1 < m + 1 := by omega
      have h2 : k.succ.1 < m + 1 := hk
      simp only [h1, h2, dif_pos]
      exact hfadj ⟨k.1, hkm⟩
    · -- last step: a → b
      have hkm : k.1 = m := by have := k.2; omega
      have h1 : k.castSucc.1 < m + 1 := by omega
      have h2 : ¬ k.succ.1 < m + 1 := hk
      have he : (⟨k.castSucc.1, h1⟩ : Fin (m + 1)) = Fin.last m := by
        apply Fin.ext; simp [Fin.last]; omega
      simp only [h1, h2, dif_pos, dif_neg, he, hflast]
      first | exact h | simp_all

/-- `Sext` is closed under `4`-adjacency inside the free cells. -/
lemma Sext_closed {W H : ℕ} {blocked : Fin W × Fin H → Prop} {a b : Cell}
    (ha : Sext W H blocked a) (hb : freeCell W H blocked b) (h : adj4 a b) :
    Sext W H blocked b := by
  rcases ha with ha | ha
  · exact Or.inl (Areg_closed ha hb h)
  · obtain ⟨h1, h2, h3⟩ := ha
    have gin : inGrid W H b := hb.1
    obtain ⟨g1, g2, g3, g4⟩ := gin
    rw [adj4] at h
    rcases h with ⟨hb1, hb2⟩ | ⟨hb2, hb1⟩
    · have hb0 : b.2 = 0 := by rcases hb2 with hh | hh <;> omega
      exact Or.inl ⟨hb, 0, (fun _ => b), hb0, rfl, (fun k => hb), (fun k => k.elim0)⟩
    · have hneg : b.2 = -1 := by omega
      omega

/-- The cells on the right of the walk are blocked. -/
lemma chainCell_blocked {W H : ℕ} (blocked : Fin W × Fin H → Prop)
    (hW : 0 < W) {c : Cell} (hc : chainCell W H blocked c) : blockedZ W H blocked c := by
  obtain ⟨hg, n, hn⟩ := hc
  have hv := walkN_valid blocked hW n
  rw [valid] at hv
  obtain ⟨hL, hR⟩ := hv
  by_contra hb
  have hfree : freeCell W H blocked c := ⟨hg, hb⟩
  have hadj : adj4 (lcell (walkN W H blocked n).1 (walkN W H blocked n).2) c := by
    rw [← hn]; exact adj4_lcell_rcell _ _
  have hS := Sext_closed hL hfree hadj
  rw [hn] at hR
  exact hR hS

end Work.Smooth.JordanSeparation
