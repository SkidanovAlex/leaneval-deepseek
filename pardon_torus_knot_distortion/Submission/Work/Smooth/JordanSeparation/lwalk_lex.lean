import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic
import Submission.Work.Smooth.JordanSeparation.lwalk_decomp

/-!
# The lexicographic order on the lattice, and the extremal vertices of a walk
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- The lexicographic strict order on `ℤ × ℤ`. -/
def LexLt (a b : ℤ × ℤ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- The lexicographic (non-strict) order on `ℤ × ℤ`. -/
def LexLe (a b : ℤ × ℤ) : Prop := LexLt a b ∨ a = b

theorem lexLt_iff (a b : ℤ × ℤ) : LexLt a b ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := Iff.rfl

attribute [local instance] Classical.propDecidable

theorem lexLe_iff (a b : ℤ × ℤ) :
    LexLe a b ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  constructor
  · rintro (h | rfl)
    · exact h.imp id (fun ⟨h1, h2⟩ => ⟨h1, le_of_lt h2⟩)
    · exact Or.inr ⟨rfl, le_rfl⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · rcases lt_or_eq_of_le h2 with h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr (Prod.ext h1 h2)

theorem lexLt_irrefl (a : ℤ × ℤ) : ¬ LexLt a a := by
  rintro (h | ⟨-, h⟩) <;> exact absurd h (lt_irrefl _)

theorem lexLt_trans {a b c : ℤ × ℤ} (h1 : LexLt a b) (h2 : LexLt b c) : LexLt a c := by
  rcases h1 with h1 | ⟨h1a, h1b⟩
  · rcases h2 with h2 | ⟨h2a, h2b⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2a ▸ h1)
  · rcases h2 with h2 | ⟨h2a, h2b⟩
    · exact Or.inl (h1a ▸ h2)
    · exact Or.inr ⟨h1a.trans h2a, h1b.trans h2b⟩

theorem lexLe_refl (a : ℤ × ℤ) : LexLe a a := Or.inr rfl

theorem lexLe_trans {a b c : ℤ × ℤ} (h1 : LexLe a b) (h2 : LexLe b c) : LexLe a c := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (lexLt_trans h1 h2)
    · exact Or.inl h1
  · exact h2

theorem lexLe_antisymm {a b : ℤ × ℤ} (h1 : LexLe a b) (h2 : LexLe b a) : a = b := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd (lexLt_trans h1 h2) (lexLt_irrefl a)
    · exact h2.symm
  · exact h1

theorem lexLt_or_lexLt_of_ne {a b : ℤ × ℤ} (h : a ≠ b) : LexLt a b ∨ LexLt b a := by
  rcases lt_trichotomy a.1 b.1 with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_trichotomy a.2 b.2 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact absurd (Prod.ext h1 h2) h
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
  · exact Or.inr (Or.inl h1)

theorem lexLe_or_lexLt (a b : ℤ × ℤ) : LexLe a b ∨ LexLt b a := by
  rcases eq_or_ne a b with h | h
  · exact Or.inl (Or.inr h)
  · rcases lexLt_or_lexLt_of_ne h with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inr h'

theorem lexLt_of_lexLe_of_ne {a b : ℤ × ℤ} (h : LexLe a b) (hne : a ≠ b) : LexLt a b :=
  h.resolve_right hne

theorem lexLe_of_lexLt {a b : ℤ × ℤ} (h : LexLt a b) : LexLe a b := Or.inl h

theorem lexLt_of_lt_left {a b : ℤ × ℤ} (h : a.1 < b.1) : LexLt a b := Or.inl h

@[simp] theorem lexLt_sub_one_self (a : ℤ × ℤ) : LexLt (a - (1, 1)) a := by
  left
  simp

theorem lexLe_sub_one {a b : ℤ × ℤ} (h : LexLe a b) : LexLe (a - (1, 1)) (b - (1, 1)) := by
  rw [lexLe_iff] at h ⊢
  rcases h with h | ⟨h1, h2⟩
  · left; simp; omega
  · right; refine ⟨by simp; omega, by simp; omega⟩


/-! ### The extremal vertices of a walk -/

/-- The maximal first coordinate of a vertex of the walk. -/
def vmax1 (W : LWalk) : ℤ :=
  (Finset.range (W.n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun k => (W.v k).1)

theorem le_vmax1 (W : LWalk) {k : ℕ} (hk : k ≤ W.n) : (W.v k).1 ≤ vmax1 W :=
  Finset.le_sup' (fun k => (W.v k).1) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem exists_vmax1 (W : LWalk) : ∃ k ≤ W.n, (W.v k).1 = vmax1 W := by
  obtain ⟨k, hk, hk'⟩ :=
    Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun k => (W.v k).1)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hk'.symm⟩

theorem filter_vmax1_nonempty (W : LWalk) :
    ((Finset.range (W.n + 1)).filter (fun k => (W.v k).1 = vmax1 W)).Nonempty := by
  obtain ⟨k, hk, hk'⟩ := exists_vmax1 W
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hk'⟩⟩

/-- The maximal second coordinate among the vertices with maximal first coordinate. -/
def vmax2 (W : LWalk) : ℤ :=
  ((Finset.range (W.n + 1)).filter (fun k => (W.v k).1 = vmax1 W)).sup'
    (filter_vmax1_nonempty W) (fun k => (W.v k).2)

/-- The lexicographically maximal vertex of the walk. -/
def vmax (W : LWalk) : ℤ × ℤ := (vmax1 W, vmax2 W)

theorem le_vmax2 (W : LWalk) {k : ℕ} (hk : k ≤ W.n) (h : (W.v k).1 = vmax1 W) :
    (W.v k).2 ≤ vmax2 W :=
  Finset.le_sup' (fun k => (W.v k).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), h⟩)

theorem le_vmax (W : LWalk) {k : ℕ} (hk : k ≤ W.n) : LexLe (W.v k) (vmax W) := by
  rw [lexLe_iff]
  rcases lt_or_eq_of_le (le_vmax1 W hk) with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, le_vmax2 W hk heq⟩

theorem exists_vmax (W : LWalk) : ∃ k ≤ W.n, W.v k = vmax W := by
  obtain ⟨k, hk, hk'⟩ :=
    Finset.exists_mem_eq_sup' (filter_vmax1_nonempty W) (fun k => (W.v k).2)
  have hk1 : (W.v k).1 = vmax1 W := (Finset.mem_filter.mp hk).2
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1),
    Prod.ext hk1 hk'.symm⟩

theorem vmax_upper (W : LWalk) {q : ℤ × ℤ} (h : ∀ k, k ≤ W.n → LexLe (W.v k) q) :
    LexLe (vmax W) q := by
  obtain ⟨j, hj, hj'⟩ := exists_vmax W
  rw [← hj']
  exact h j hj

/-- The minimal first coordinate of a vertex of the walk. -/
def vmin1 (W : LWalk) : ℤ :=
  (Finset.range (W.n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun k => (W.v k).1)

theorem vmin1_le (W : LWalk) {k : ℕ} (hk : k ≤ W.n) : vmin1 W ≤ (W.v k).1 :=
  Finset.inf'_le (fun k => (W.v k).1) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem exists_vmin1 (W : LWalk) : ∃ k ≤ W.n, (W.v k).1 = vmin1 W := by
  obtain ⟨k, hk, hk'⟩ :=
    Finset.exists_mem_eq_inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun k => (W.v k).1)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hk'.symm⟩

theorem filter_vmin1_nonempty (W : LWalk) :
    ((Finset.range (W.n + 1)).filter (fun k => (W.v k).1 = vmin1 W)).Nonempty := by
  obtain ⟨k, hk, hk'⟩ := exists_vmin1 W
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hk'⟩⟩

/-- The minimal second coordinate among the vertices with minimal first coordinate. -/
def vmin2 (W : LWalk) : ℤ :=
  ((Finset.range (W.n + 1)).filter (fun k => (W.v k).1 = vmin1 W)).inf'
    (filter_vmin1_nonempty W) (fun k => (W.v k).2)

/-- The lexicographically minimal vertex of the walk. -/
def vmin (W : LWalk) : ℤ × ℤ := (vmin1 W, vmin2 W)

theorem vmin2_le (W : LWalk) {k : ℕ} (hk : k ≤ W.n) (h : (W.v k).1 = vmin1 W) :
    vmin2 W ≤ (W.v k).2 :=
  Finset.inf'_le (fun k => (W.v k).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), h⟩)

theorem vmin_le (W : LWalk) {k : ℕ} (hk : k ≤ W.n) : LexLe (vmin W) (W.v k) := by
  rw [lexLe_iff]
  rcases lt_or_eq_of_le (vmin1_le W hk) with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, vmin2_le W hk heq.symm⟩

theorem exists_vmin (W : LWalk) : ∃ k ≤ W.n, W.v k = vmin W := by
  obtain ⟨k, hk, hk'⟩ :=
    Finset.exists_mem_eq_inf' (filter_vmin1_nonempty W) (fun k => (W.v k).2)
  have hk1 : (W.v k).1 = vmin1 W := (Finset.mem_filter.mp hk).2
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1),
    Prod.ext hk1 hk'.symm⟩

theorem vmin_lower (W : LWalk) {q : ℤ × ℤ} (h : ∀ k, k ≤ W.n → LexLe q (W.v k)) :
    LexLe q (vmin W) := by
  obtain ⟨j, hj, hj'⟩ := exists_vmin W
  rw [← hj']
  exact h j hj

/-! ### Vertices stay in the box around the starting point -/

theorem gridStep_coord {a b : ℤ × ℤ} (h : GridStep a b) :
    b.1 ≤ a.1 + 1 ∧ a.1 ≤ b.1 + 1 ∧ b.2 ≤ a.2 + 1 ∧ a.2 ≤ b.2 + 1 := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp_all <;> omega

theorem coord_bound_left (W : LWalk) : ∀ k, k ≤ W.n → (W.v 0).1 - (k : ℤ) ≤ (W.v k).1 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := (gridStep_coord (W.step k (by omega))).2.1
    push_cast
    omega

theorem coord_bound_right (W : LWalk) : ∀ k, k ≤ W.n → (W.v k).1 ≤ (W.v 0).1 + (k : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := (gridStep_coord (W.step k (by omega))).1
    push_cast
    omega

theorem coord_bound_left2 (W : LWalk) : ∀ k, k ≤ W.n → (W.v 0).2 - (k : ℤ) ≤ (W.v k).2 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := (gridStep_coord (W.step k (by omega))).2.2.2
    have h3 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [h3]
    omega

theorem coord_bound_right2 (W : LWalk) : ∀ k, k ≤ W.n → (W.v k).2 ≤ (W.v 0).2 + (k : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := (gridStep_coord (W.step k (by omega))).2.2.1
    have h3 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [h3]
    omega

/-! ### The number of steps of a closed lattice walk is even -/

theorem gridStep_parity {a b : ℤ × ℤ} (h : GridStep a b) :
    ((b.1 + b.2) - (a.1 + a.2) = 1) ∨ ((b.1 + b.2) - (a.1 + a.2) = -1) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp_all <;> omega

theorem parity_of_walk (W : LWalk) : ∀ k (hk : k ≤ W.n),
    ∃ m : ℤ, (W.v k).1 + (W.v k).2 = (W.v 0).1 + (W.v 0).2 + 2 * m + (k : ℤ) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, by ring⟩
  | succ k ih =>
    intro hk
    obtain ⟨m, hm⟩ := ih (by omega)
    rcases gridStep_parity (W.step k (by omega)) with h | h
    · exact ⟨m, by push_cast; omega⟩
    · exact ⟨m - 1, by push_cast; omega⟩

theorem even_n_of_closed (W : LWalk) : Even W.n := by
  obtain ⟨m, hm⟩ := parity_of_walk W W.n le_rfl
  rw [W.closed] at hm
  have hm' : (W.n : ℤ) = -2 * m := by omega
  have h3 : (W.n : ℤ) = ((-m).toNat : ℤ) + ((-m).toNat : ℤ) := by
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    omega
  exact ⟨(-m).toNat, by exact_mod_cast h3⟩

end

end Work.Smooth.JordanSeparation
