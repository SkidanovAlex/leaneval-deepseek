import Mathlib
import Submission.Work.Smooth.JordanSeparation.hexWalkRegion

/-!
# `wall_LR`: the wall-following walk of `Sext` yields an in-grid `8`-chain

The walk `walkN` of `hexWalkRegion` starts at the crack below the bottom-left corner of the
virtual free row, keeping `Sext` on its left.  We prove that it climbs the right frame up to
the top row of `Sext` in the last column, then enters the grid and traces the upper boundary of
`Sext` until it leaves the grid on the left.  The right-hand cells of this in-grid portion are
`8`-connected, start in column `W-1` and end in column `0`.
-/

open Classical

namespace Work.Smooth.JordanSeparation

open HDir

/-! ## Bounds on `Sext` and on the walk positions -/

lemma Sext_fst_bound {W H : ℕ} {blocked : Fin W × Fin H → Prop} {c : Cell}
    (hc : Sext W H blocked c) : 0 ≤ c.1 ∧ c.1 < (W : ℤ) := by
  rcases hc with hc | ⟨h1, h2, -⟩
  · obtain ⟨h1, h2, -, -⟩ := hc.1.1
    exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

lemma Sext_snd_lower {W H : ℕ} {blocked : Fin W × Fin H → Prop} {c : Cell}
    (hc : Sext W H blocked c) : -1 ≤ c.2 := by
  rcases hc with hc | ⟨-, -, h3⟩
  · obtain ⟨-, -, h3, -⟩ := hc.1.1
    omega
  · omega

lemma Sext_bounds {W H : ℕ} (hH : 0 < H) {blocked : Fin W × Fin H → Prop}
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1) {c : Cell}
    (hc : Sext W H blocked c) :
    0 ≤ c.1 ∧ c.1 < (W : ℤ) ∧ -1 ≤ c.2 ∧ c.2 ≤ (H : ℤ) - 2 := by
  rcases hc with h | ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.1.1
    refine ⟨h1, h2, by omega, ?_⟩
    have hne := htop c h
    omega
  · exact ⟨h1, h2, by omega, by omega⟩

lemma Sext_virtual {W H : ℕ} {blocked : Fin W × Fin H → Prop} {x : ℤ}
    (h1 : 0 ≤ x) (h2 : x < (W : ℤ)) : Sext W H blocked (x, -1) :=
  Or.inr ⟨h1, h2, rfl⟩

lemma not_Sext_of_snd_lt {W H : ℕ} {blocked : Fin W × Fin H → Prop} {a b : ℤ}
    (h : b < -1) : ¬ Sext W H blocked (a, b) := by
  intro hc
  have := Sext_snd_lower hc
  omega

lemma not_Sext_of_fst {W H : ℕ} {blocked : Fin W × Fin H → Prop} {c : Cell}
    (h : c.1 < 0 ∨ (W : ℤ) ≤ c.1) : ¬ Sext W H blocked c := by
  intro hc
  have := Sext_fst_bound hc
  omega

/-- The positions visited by the walk stay in the box `[0,W] × [-1,H-1]`. -/
lemma valid_pos_bounds {W H : ℕ} (hH : 0 < H) {blocked : Fin W × Fin H → Prop}
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1)
    {p : Cell} {d : HDir} (hv : valid (Sext W H blocked) p d) :
    0 ≤ p.1 ∧ p.1 ≤ (W : ℤ) ∧ -1 ≤ p.2 ∧ p.2 ≤ (H : ℤ) - 1 := by
  obtain ⟨hL, -⟩ := hv
  obtain ⟨h1, h2, h3, h4⟩ := Sext_bounds hH htop hL
  cases d <;> simp only [lcell] at h1 h2 h3 h4 <;> omega

lemma walkN_pos_bounds {W H : ℕ} (hH : 0 < H) (blocked : Fin W × Fin H → Prop)
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1) (hW : 0 < W) (n : ℕ) :
    0 ≤ (walkN W H blocked n).1.1 ∧ (walkN W H blocked n).1.1 ≤ (W : ℤ) ∧
    -1 ≤ (walkN W H blocked n).1.2 ∧ (walkN W H blocked n).1.2 ≤ (H : ℤ) - 1 :=
  valid_pos_bounds hH htop (walkN_valid blocked hW n)

/-! ## Consecutive right cells are `8`-adjacent -/

lemma adj8_rcell_nxt (p : Cell) (d : HDir) :
    adj8 (rcell p d) (rcell (nxt p d) (rotL d)) ∧
    adj8 (rcell p d) (rcell (nxt p d) d) ∧
    adj8 (rcell p d) (rcell (nxt p d) (rotR d)) := by
  cases d <;> refine ⟨?_, ?_, ?_⟩ <;>
    simp only [rcell, nxt, HDir.rotL, HDir.rotR, HDir.vec, adj8] <;>
    constructor <;> rw [abs_le] <;> omega

lemma adj8_rcell_walkN {W H : ℕ} (blocked : Fin W × Fin H → Prop) (n : ℕ) :
    adj8 (rcell (walkN W H blocked n).1 (walkN W H blocked n).2)
      (rcell (walkN W H blocked (n + 1)).1 (walkN W H blocked (n + 1)).2) := by
  obtain ⟨h1, h2, h3⟩ := adj8_rcell_nxt (walkN W H blocked n).1 (walkN W H blocked n).2
  have hstep : walkN W H blocked (n + 1) = step (Sext W H blocked) (walkN W H blocked n) :=
    rfl
  rw [hstep]
  simp only [step]
  unfold nextD
  split_ifs with h
  · exact h1
  · exact h2
  · exact h3

lemma adj8_symm {a b : Cell} (h : adj8 a b) : adj8 b a := ⟨by rw [abs_sub_comm]; exact h.1,
  by rw [abs_sub_comm]; exact h.2⟩

/-! ## The bottom arc of the walk -/

lemma valid_bottom_E {W H : ℕ} {blocked : Fin W × Fin H → Prop} {x : ℤ}
    (h1 : 0 ≤ x) (h2 : x + 1 < (W : ℤ)) : valid (Sext W H blocked) (x + 1, -1) HDir.E := by
  rw [valid]
  simp only [lcell, rcell]
  exact ⟨Sext_virtual (by omega) h2, not_Sext_of_snd_lt (by norm_num)⟩

lemma valid_bottom_rotL_iff {W H : ℕ} {blocked : Fin W × Fin H → Prop} {x : ℤ}
    (h1 : 0 ≤ x) (h2 : x < (W : ℤ)) :
    valid (Sext W H blocked) (x + 1, -1) (rotL HDir.E) ↔ (W : ℤ) ≤ x + 1 := by
  rw [valid]
  simp only [lcell, rcell, HDir.rotL]
  constructor
  · rintro ⟨hL, hR⟩
    have hL' : Sext W H blocked (x, -1) := by simpa only [add_sub_cancel_right] using hL
    by_contra hlt
    rw [not_le] at hlt
    exact hR (Sext_virtual (by omega) hlt)
  · intro h
    refine ⟨by simpa only [add_sub_cancel_right] using Sext_virtual h1 h2, ?_⟩
    exact not_Sext_of_fst (Or.inr h)

lemma nextD_bottom {W H : ℕ} {blocked : Fin W × Fin H → Prop} {x : ℤ}
    (h1 : 0 ≤ x) (h2 : x < (W : ℤ)) :
    nextD (Sext W H blocked) (x + 1, -1) HDir.E =
      if x + 1 < (W : ℤ) then HDir.E else HDir.N := by
  rcases lt_or_ge (x + 1) (W : ℤ) with h | h
  · rw [if_pos h]
    have hvE : valid (Sext W H blocked) (x + 1, -1) HDir.E := valid_bottom_E h1 (by omega)
    have hvN : ¬ valid (Sext W H blocked) (x + 1, -1) (rotL HDir.E) := by
      rw [valid_bottom_rotL_iff h1 h2]
      omega
    rw [nextD_eq_self (Sext W H blocked) (x+1, -1) HDir.E hvN hvE]
  · rw [if_neg (not_lt.mpr h)]
    have hv : valid (Sext W H blocked) (x + 1, -1) (rotL HDir.E) :=
      (valid_bottom_rotL_iff h1 h2).mpr h
    rw [nextD_eq_rotL (Sext W H blocked) (x+1, -1) HDir.E hv]
    rfl

lemma step_bottom_E {W H : ℕ} {blocked : Fin W × Fin H → Prop} {x : ℤ}
    (h1 : 0 ≤ x) (h2 : x + 1 < (W : ℤ)) :
    step (Sext W H blocked) ((x, -1), HDir.E) = ((x + 1, -1), HDir.E) := by
  have hp : nxt (x, (-1:ℤ)) HDir.E = (x + 1, (-1:ℤ)) := by
    simp only [nxt, HDir.vec]
    exact Prod.ext (by ring) (by ring)
  show (nxt (x,-1) HDir.E, nextD (Sext W H blocked) (nxt (x,-1) HDir.E) HDir.E) = _
  rw [hp, nextD_bottom h1 (by omega), if_pos h2]

lemma step_bottom_N {W H : ℕ} {blocked : Fin W × Fin H → Prop} {x : ℤ}
    (h1 : 0 ≤ x) (h2 : x + 1 = (W : ℤ)) :
    step (Sext W H blocked) ((x, -1), HDir.E) = ((x + 1, -1), HDir.N) := by
  have hp : nxt (x, (-1:ℤ)) HDir.E = (x + 1, (-1:ℤ)) := by
    simp only [nxt, HDir.vec]
    exact Prod.ext (by ring) (by ring)
  show (nxt (x,-1) HDir.E, nextD (Sext W H blocked) (nxt (x,-1) HDir.E) HDir.E) = _
  rw [hp, nextD_bottom h1 (by omega), if_neg (by omega)]

lemma walkN_bottom_E {W H : ℕ} (hW : 0 < W) (blocked : Fin W × Fin H → Prop) :
    ∀ n, n < W → walkN W H blocked n = (((n : ℤ), (-1 : ℤ)), HDir.E) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hn' : n < W := by omega
      have hrec : walkN W H blocked (n + 1) = step (Sext W H blocked) (walkN W H blocked n) :=
        rfl
      rw [hrec, ih hn', step_bottom_E (by omega : (0:ℤ) ≤ (n:ℤ)) (by omega)]
      have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast]

lemma walkN_bottom_N {W H : ℕ} (hW : 0 < W) (blocked : Fin W × Fin H → Prop) :
    walkN W H blocked W = (((W : ℤ), (-1 : ℤ)), HDir.N) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : W ≠ 0)
  have hrec : walkN (m + 1) H blocked (m + 1) =
      step (Sext (m + 1) H blocked) (walkN (m + 1) H blocked m) := rfl
  rw [hrec, walkN_bottom_E (W := m + 1) (by omega) blocked m (by omega),
      step_bottom_N (x := (m : ℤ)) (by omega) (by push_cast; ring)]
  have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast]

/-! ## Classification of a few states -/

/-- A valid state whose right cell lies in column `W` is the climbing state `((W,y),N)`. -/
lemma rcell_col_W {W H : ℕ} {blocked : Fin W × Fin H → Prop} {p : Cell} {d : HDir} {y : ℤ}
    (hv : valid (Sext W H blocked) p d) (h : rcell p d = ((W : ℤ), y)) :
    p = ((W : ℤ), y) ∧ d = HDir.N := by
  obtain ⟨hL, hR⟩ := hv
  cases d
  · exfalso
    simp only [rcell, Prod.mk.injEq] at h
    have hb := (Sext_fst_bound hL).2
    simp only [lcell] at hb
    omega
  · simp only [rcell, Prod.mk.injEq] at h
    exact ⟨Prod.ext h.1 h.2, rfl⟩
  · exfalso
    simp only [rcell, Prod.mk.injEq] at h
    have hL' : Sext W H blocked ((W : ℤ), p.2 - 1) := by
      simpa only [lcell, h.1] using hL
    exact absurd hL' (not_Sext_of_fst (Or.inr (le_refl (W : ℤ))))
  · exfalso
    simp only [rcell, Prod.mk.injEq] at h
    have hL' : Sext W H blocked (p.1, p.2 - 1) := by
      simpa only [lcell] using hL
    exact absurd hL' (not_Sext_of_fst (Or.inr (by omega : (W : ℤ) ≤ p.1)))


/-! ## The position `y = -1` and the right cell `(W,y)` determine the state -/

lemma valid_snd_eq_neg_one {W H : ℕ} {blocked : Fin W × Fin H → Prop} {p : Cell} {d : HDir}
    (hv : valid (Sext W H blocked) p d) (h : p.2 = -1) :
    (d = HDir.E ∧ 0 ≤ p.1 ∧ p.1 < (W : ℤ)) ∨ (d = HDir.N ∧ p.1 = (W : ℤ)) := by
  obtain ⟨hL, hR⟩ := hv
  cases d
  · left
    have hb := Sext_fst_bound hL
    simp only [lcell, h] at hb
    exact ⟨rfl, hb⟩
  · right
    have hb := Sext_fst_bound hL
    simp only [lcell, h] at hb
    have hR' : ¬ Sext W H blocked (p.1, -1) := by simpa only [rcell, h] using hR
    refine ⟨rfl, ?_⟩
    by_contra hc
    exact hR' (Sext_virtual (by omega) (by omega))
  · exfalso
    exact absurd hL (not_Sext_of_snd_lt (a := p.1 - 1) (b := p.2 - 1) (by omega))
  · exfalso
    exact absurd hL (not_Sext_of_snd_lt (a := p.1) (b := p.2 - 1) (by omega))

/-- A valid state whose position is in the upper-left part of the grid has its right cell in
the grid, unless that right cell is the virtual cell `(-1,·)`. -/
lemma inGrid_rcell_of_pos {W H : ℕ} {blocked : Fin W × Fin H → Prop} {p : Cell} {d : HDir}
    (hv : valid (Sext W H blocked) p d) (h1 : 0 ≤ p.1) (h2 : p.1 ≤ (W : ℤ) - 1)
    (h3 : 0 ≤ p.2) (h4 : p.2 ≤ (H : ℤ) - 1) (h5 : (rcell p d).1 ≠ -1) :
    inGrid W H (rcell p d) := by
  obtain ⟨hL, hR⟩ := hv
  cases d
  · simp only [rcell] at h5 ⊢
    refine ⟨by omega, by omega, ?_, by omega⟩
    by_contra hc
    rw [not_le] at hc
    have hy : p.2 - 1 = -1 := by omega
    exact hR (by rw [rcell, hy]; exact Sext_virtual (by omega) (by omega))
  · simp only [rcell]
    exact ⟨by omega, by omega, h3, by omega⟩
  · simp only [rcell] at h5 ⊢
    refine ⟨by omega, by omega, h3, by omega⟩
  · simp only [rcell] at h5 ⊢
    refine ⟨by omega, by omega, ?_, by omega⟩
    by_contra hc
    rw [not_le] at hc
    have hy : p.2 - 1 = -1 := by omega
    exact hR (by rw [rcell, hy]; exact Sext_virtual (by omega) (by omega))

/-! ## The unique predecessor of the starting crack -/

lemma step_eq_start {W H : ℕ} {blocked : Fin W × Fin H → Prop} {p : Cell} {d : HDir}
    (hv : valid (Sext W H blocked) p d)
    (h : step (Sext W H blocked) (p, d) = (((0 : ℤ), (-1 : ℤ)), HDir.E)) :
    (p, d) = (((0 : ℤ), (0 : ℤ)), HDir.S) := by
  have hn : nxt p d = ((0 : ℤ), (-1 : ℤ)) := by
    have := congrArg Prod.fst h
    simpa only [step] using this
  cases d
  · exfalso
    simp only [nxt, HDir.vec, Prod.mk.injEq] at hn
    have hb := Sext_fst_bound hv.1
    simp only [lcell] at hb
    omega
  · exfalso
    simp only [nxt, HDir.vec, Prod.mk.injEq] at hn
    have hb := Sext_fst_bound hv.1
    simp only [lcell] at hb
    omega
  · exfalso
    simp only [nxt, HDir.vec, Prod.mk.injEq] at hn
    have hb := Sext_snd_lower hv.1
    simp only [lcell] at hb
    omega
  · simp only [nxt, HDir.vec, Prod.mk.injEq] at hn
    have hp : p = ((0 : ℤ), (0 : ℤ)) := Prod.ext (by omega) (by omega)
    rw [hp]

/-- A valid state whose position lies on the column boundary `W` is directed `W` or `N`. -/
lemma state_at_W {W H : ℕ} {blocked : Fin W × Fin H → Prop} {s : Cell × HDir}
    (hv : valid (Sext W H blocked) s.1 s.2) (hx : s.1.1 = (W : ℤ)) :
    s.2 = HDir.W ∨ s.2 = HDir.N := by
  cases hd : s.2
  · exfalso
    have hb := (Sext_fst_bound hv.1).2
    simp only [hd, lcell] at hb
    omega
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exfalso
    have hb := (Sext_fst_bound hv.1).2
    simp only [hd, lcell] at hb
    omega

/-! ## Periodicity of the walk -/

noncomputable def stateFinset (W H : ℕ) : Finset (Cell × HDir) :=
  ((Finset.Icc (0 : ℤ) (W : ℤ)) ×ˢ (Finset.Icc (-1 : ℤ) ((H : ℤ) - 1))) ×ˢ Finset.univ

lemma walkN_mem_stateFinset {W H : ℕ} (hH : 0 < H) (blocked : Fin W × Fin H → Prop)
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1) (hW : 0 < W) (n : ℕ) :
    walkN W H blocked n ∈ stateFinset W H := by
  obtain ⟨h1, h2, h3, h4⟩ := walkN_pos_bounds hH blocked htop hW n
  simp only [stateFinset, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

lemma walkN_cancel {W H : ℕ} (blocked : Fin W × Fin H → Prop) (hW : 0 < W) :
    ∀ i j : ℕ, i ≤ j → walkN W H blocked i = walkN W H blocked j →
      walkN W H blocked (j - i) = walkN W H blocked 0 := by
  intro i
  induction i with
  | zero => intro j _ h; simpa using h.symm
  | succ i ih =>
      intro j hij h
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hij' : i ≤ j' := by omega
      have h1 : walkN W H blocked (i + 1) = step (Sext W H blocked) (walkN W H blocked i) :=
        rfl
      have h2 : walkN W H blocked (j' + 1) =
          step (Sext W H blocked) (walkN W H blocked j') := rfl
      rw [h1, h2] at h
      have heq : walkN W H blocked i = walkN W H blocked j' :=
        step_inj (Sext W H blocked) _ _ _ _ (walkN_valid blocked hW i)
          (walkN_valid blocked hW j') h
      have := ih j' hij' heq
      rw [Nat.add_sub_add_right]
      exact this

lemma walkN_period_exists {W H : ℕ} (hH : 0 < H) (blocked : Fin W × Fin H → Prop)
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1) (hW : 0 < W) :
    ∃ k : ℕ, 0 < k ∧ walkN W H blocked k = walkN W H blocked 0 := by
  have hlt : (stateFinset W H).card < (Finset.range ((stateFinset W H).card + 1)).card := by
    rw [Finset.card_range]; omega
  obtain ⟨i, -, j, -, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range ((stateFinset W H).card + 1))
      (t := stateFinset W H) hlt (f := fun n => walkN W H blocked n)
      (fun n _ => walkN_mem_stateFinset hH blocked htop hW n)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨j - i, by omega, walkN_cancel blocked hW i j (le_of_lt h) heq⟩
  · exact ⟨i - j, by omega, (walkN_cancel blocked hW j i (le_of_lt h) heq.symm)⟩

lemma walkN_periodic {W H : ℕ} (hH : 0 < H) (blocked : Fin W × Fin H → Prop)
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1) (hW : 0 < W) :
    ∃ P : ℕ, 0 < P ∧ (∀ n, walkN W H blocked (n + P) = walkN W H blocked n) ∧
      (∀ i j : ℕ, i < j → j < P → walkN W H blocked i ≠ walkN W H blocked j) := by
  obtain ⟨k, hkpos, hk⟩ := walkN_period_exists hH blocked htop hW
  have hex : ∃ k, 0 < k ∧ walkN W H blocked k = walkN W H blocked 0 := ⟨k, hkpos, hk⟩
  have hfind := Nat.find_spec hex
  obtain ⟨hPpos, hP0, hPmin⟩ : 0 < Nat.find hex ∧
      walkN W H blocked (Nat.find hex) = walkN W H blocked 0 ∧
      ∀ m, 0 < m → m < Nat.find hex → walkN W H blocked m ≠ walkN W H blocked 0 :=
    ⟨hfind.1, hfind.2,
     fun m hm hmP hcon => absurd (Nat.find_min' hex ⟨hm, hcon⟩) (by omega)⟩
  set P : ℕ := Nat.find hex with hPdef
  refine ⟨P, hPpos, ?_, ?_⟩
  · intro n
    induction n with
    | zero => simpa using hP0
    | succ n ih =>
        have h1 : walkN W H blocked (n + 1 + P) =
            step (Sext W H blocked) (walkN W H blocked (n + P)) := by
          rw [show n + 1 + P = (n + P) + 1 by omega]; rfl
        have h2 : walkN W H blocked (n + 1) = step (Sext W H blocked) (walkN W H blocked n) :=
          rfl
        rw [h1, h2, ih]
  · intro i j hij hjP hcon
    have := walkN_cancel blocked hW i j (le_of_lt hij) hcon
    exact (hPmin (j - i) (by omega) (by omega)) this

/-! ## The wall chain -/

theorem wall_LR {W H : ℕ} (hW : 0 < W) (hH : 0 < H) (blocked : Fin W × Fin H → Prop)
    (htop : ∀ c : Cell, Areg W H blocked c → c.2 ≠ (H : ℤ) - 1) :
    ∃ (m : ℕ) (g : Fin (m + 1) → Cell),
      (∀ k, chainCell W H blocked (g k)) ∧
      (∀ k : Fin m, adj8 (g k.castSucc) (g k.succ)) ∧
      (g 0).1 = 0 ∧
      (g (Fin.last m)).1 + 1 = W := by
  classical
  obtain ⟨P, hPpos, hper, hdist⟩ := walkN_periodic hH blocked htop hW
  have hbotE := walkN_bottom_E hW blocked
  have hbotN := walkN_bottom_N hW blocked
  have hzero : walkN W H blocked 0 = (((0 : ℤ), (-1 : ℤ)), HDir.E) := rfl
  have hP0' : walkN W H blocked P = walkN W H blocked 0 := by simpa using hper 0
  -- `W < P`
  have hWltP : W < P := by
    rcases lt_trichotomy W P with h | h | h
    · exact h
    · exfalso
      have hcon := hP0'
      rw [← h, hbotN, hzero] at hcon
      simp only [Prod.mk.injEq] at hcon
      omega
    · exfalso
      have hcon := hP0'
      rw [hbotE P h, hzero] at hcon
      simp only [Prod.mk.injEq] at hcon
      omega
  -- last index at column boundary `W`
  let Sf : Finset ℕ := (Finset.range P).filter (fun n => (walkN W H blocked n).1.1 = (W : ℤ))
  have hSne : Sf.Nonempty := by
    refine ⟨W, ?_⟩
    simp only [Sf, Finset.mem_filter, Finset.mem_range]
    exact ⟨hWltP, by rw [hbotN]⟩
  set na : ℕ := Sf.max' hSne with hna
  have hna_in : na ∈ Sf := Finset.max'_mem Sf hSne
  have hna_ltP : na < P := Finset.mem_range.mp (Finset.mem_filter.mp hna_in).1
  have hna_x : (walkN W H blocked na).1.1 = (W : ℤ) := (Finset.mem_filter.mp hna_in).2
  have hna_max : ∀ n, n < P → na < n → (walkN W H blocked n).1.1 ≠ (W : ℤ) := by
    intro n hnP hlt hcon
    have hmem : n ∈ Sf := by
      simp only [Sf, Finset.mem_filter, Finset.mem_range]
      exact ⟨hnP, hcon⟩
    have := Finset.le_max' Sf n hmem
    omega
  -- the state at `na` enters the grid
  obtain ⟨ya, hna_entry⟩ : ∃ y : ℤ, walkN W H blocked na = (((W : ℤ), y), HDir.W) := by
    have hv := walkN_valid blocked hW na
    rcases state_at_W hv hna_x with hd | hd
    · exact ⟨(walkN W H blocked na).1.2,
        Prod.ext (Prod.ext hna_x rfl) hd⟩
    · exfalso
      have hsucc : (walkN W H blocked (na + 1)).1.1 = (W : ℤ) := by
        have hstep : walkN W H blocked (na + 1) =
            step (Sext W H blocked) (walkN W H blocked na) := rfl
        rw [hstep]
        change (nxt (walkN W H blocked na).1 (walkN W H blocked na).2).1 = (W : ℤ)
        rw [hd]
        simp only [nxt, HDir.vec, Prod.fst, Prod.snd]
        omega
      rcases lt_or_eq_of_le (show na + 1 ≤ P by omega) with h | h
      · exact absurd hsucc (hna_max _ h (by omega))
      · have hcon := hP0'
        rw [← h] at hcon
        have hc2 := congrArg (fun s : Cell × HDir => s.1.1) hcon
        rw [hzero] at hc2
        simp only [Prod.fst, Prod.snd] at hc2
        omega
  have hW_na : W < na := by
    have hWmem : W ∈ Sf := by
      simp only [Sf, Finset.mem_filter, Finset.mem_range]
      exact ⟨hWltP, by rw [hbotN]⟩
    have hle := Finset.le_max' Sf W hWmem
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hnaW : na = W := by rw [hna]; exact h.symm
      have hent := hna_entry
      rw [hnaW, hbotN] at hent
      simp only [Prod.mk.injEq] at hent
      exact absurd hent.2 (by decide)
  -- the first index after `na` whose right cell leaves the grid on the left
  have hP1 : walkN W H blocked (P - 1) = (((0 : ℤ), (0 : ℤ)), HDir.S) := by
    refine step_eq_start (walkN_valid blocked hW (P - 1)) ?_
    have h1 : walkN W H blocked ((P - 1) + 1) =
        step (Sext W H blocked) (walkN W H blocked (P - 1)) := rfl
    rw [show (P - 1) + 1 = P by omega] at h1
    rw [h1] at hP0'
    exact hP0'
  have hna_lt_P1 : na < P - 1 := by
    rcases lt_or_eq_of_le (show na ≤ P - 1 by omega) with h | h
    · exact h
    · exfalso
      have := congrArg (fun s : Cell × HDir => s.1.1) (h ▸ hna_entry)
      rw [hP1] at this
      simp only [Prod.fst, Prod.snd] at this
      omega
  let Tf : Finset ℕ := (Finset.Icc (na + 1) (P - 1)).filter
    (fun n => (rcell (walkN W H blocked n).1 (walkN W H blocked n).2).1 = (-1 : ℤ))
  have hTne : Tf.Nonempty := by
    refine ⟨P - 1, ?_⟩
    simp only [Tf, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, le_refl _⟩, ?_⟩
    rw [hP1]
    rfl
  set nb : ℕ := Tf.min' hTne with hnb
  have hnb_in : nb ∈ Tf := Finset.min'_mem Tf hTne
  have hnb_low : na + 1 ≤ nb := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnb_in).1).1
  have hnb_high : nb ≤ P - 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnb_in).1).2
  have hnb_rc : (rcell (walkN W H blocked nb).1 (walkN W H blocked nb).2).1 = (-1 : ℤ) :=
    (Finset.mem_filter.mp hnb_in).2
  have hnb_min : ∀ n, na + 1 ≤ n → n < nb →
      (rcell (walkN W H blocked n).1 (walkN W H blocked n).2).1 ≠ (-1 : ℤ) := by
    intro n h1 hnb' hcon
    have hmem : n ∈ Tf := by
      simp only [Tf, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, by omega⟩, hcon⟩
    have := Finset.min'_le Tf n hmem
    rw [← hnb] at this
    omega
  -- all right cells in `[na, nb)` are in the grid
  have hna_rcell : inGrid W H (rcell (walkN W H blocked na).1 (walkN W H blocked na).2) := by
    rw [hna_entry]
    simp only [rcell]
    have hvL := (walkN_valid blocked hW na).1
    rw [hna_entry] at hvL
    simp only [lcell] at hvL
    obtain ⟨l1, l2, l3, l4⟩ := Sext_bounds hH htop hvL
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hsnd_lower : ∀ n, n < P → (walkN W H blocked n).1.2 = -1 → n ≤ W := by
    intro n hnP hn
    have hv := walkN_valid blocked hW n
    rcases valid_snd_eq_neg_one hv hn with ⟨hd, h1, h2⟩ | ⟨hd, h1⟩
    · let k := (walkN W H blocked n).1.1.toNat
      have hk : (k : ℤ) = (walkN W H blocked n).1.1 := Int.toNat_of_nonneg h1
      have hkW : k < W := by omega
      have heq : walkN W H blocked n = walkN W H blocked k := by
        have hp : walkN W H blocked n = (((walkN W H blocked n).1.1, (-1 : ℤ)), HDir.E) := by
          refine Prod.ext ?_ hd
          exact Prod.ext rfl hn
        rw [hp, hbotE k hkW, hk]
      rcases lt_trichotomy n k with h | h | h
      · exact absurd heq (hdist n k h (by omega))
      · omega
      · exact absurd heq.symm (hdist k n h (by omega))
    · have heq : walkN W H blocked n = walkN W H blocked W := by
        have hp : walkN W H blocked n = (((W : ℤ), (-1 : ℤ)), HDir.N) := by
          refine Prod.ext ?_ hd
          exact Prod.ext h1 hn
        rw [hp, hbotN]
      rcases lt_trichotomy n W with h | h | h
      · exact absurd heq (hdist n W h hWltP)
      · omega
      · exact absurd heq.symm (hdist W n h (by omega))
  have hgrid : ∀ n, na ≤ n → n < nb → inGrid W H
      (rcell (walkN W H blocked n).1 (walkN W H blocked n).2) := by
    intro n hna hnb
    rcases lt_or_eq_of_le hna with hlt | heq
    · have hnP : n < P := by omega
      obtain ⟨q1, q2, q3, q4⟩ := walkN_pos_bounds hH blocked htop hW n
      have hx : (walkN W H blocked n).1.1 ≠ (W : ℤ) := hna_max n hnP hlt
      have hy : (walkN W H blocked n).1.2 ≠ -1 := by
        intro hcon
        have := hsnd_lower n hnP hcon
        omega
      have hrc : (rcell (walkN W H blocked n).1 (walkN W H blocked n).2).1 ≠ (-1 : ℤ) :=
        hnb_min n (by omega) hnb
      exact inGrid_rcell_of_pos (walkN_valid blocked hW n) q1 (by omega) (by omega) q4 hrc
    · subst heq
      exact hna_rcell
  -- endpoints
  have hcol_na : (rcell (walkN W H blocked na).1 (walkN W H blocked na).2).1 = (W : ℤ) - 1 := by
    rw [hna_entry]
    rfl
  have hcol_nb1 : (rcell (walkN W H blocked (nb - 1)).1 (walkN W H blocked (nb - 1)).2).1 = 0 := by
    have hadj := adj8_rcell_walkN blocked (nb - 1)
    rw [show nb - 1 + 1 = nb by omega] at hadj
    have hg := hgrid (nb - 1) (by omega) (by omega)
    obtain ⟨hg1, -⟩ := hg
    have := hadj.1
    rw [abs_le] at this
    omega
  refine ⟨nb - na - 1, fun i => rcell (walkN W H blocked (nb - 1 - (i : ℕ))).1
      (walkN W H blocked (nb - 1 - (i : ℕ))).2, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : (i : ℕ) ≤ nb - na - 1 := by have := i.2; omega
    refine ⟨hgrid _ (by omega) (by omega), ⟨nb - 1 - (i : ℕ), rfl⟩⟩
  · intro i
    have hi : (i : ℕ) + 1 ≤ nb - na - 1 := by have := i.2; omega
    have hidx : nb - 1 - (i : ℕ) = nb - 1 - ((i : ℕ) + 1) + 1 := by omega
    have hadj := adj8_rcell_walkN blocked (nb - 1 - ((i : ℕ) + 1))
    simp only [Fin.val_castSucc, Fin.val_succ, hidx]
    exact adj8_symm hadj
  · simp only [Fin.val_zero, Nat.sub_zero]
    exact hcol_nb1
  · simp only [Fin.val_last]
    rw [show nb - 1 - (nb - na - 1) = na by omega]
    rw [hcol_na]
    omega

end Work.Smooth.JordanSeparation
