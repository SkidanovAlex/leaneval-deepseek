import Mathlib
import Submission.Work.Resample.PB.Defs

/-!
# `pbApplyAlong`: the pure level theory of the transposition

`lv0 M C L` is the level-0 block list of the flat `M × C` array `L` (each row wrapped into singleton
columns); `lvlStep`/`lvlIter` are the pairing operations performed by `trPass`/`trLevelLoop`
(`grpStep`/`grpIter` are the same operations on the row-group decomposition, which is what the
correctness proof uses: `blksOf C (grpIter k gs) = lvlIter k (blksOf C gs)`).

The main result is `lvlIter_lv0`: after `M.size` level steps the block list is the singleton
`[colsOf M C L]` — the `C` columns of `L`, in order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Resample.PB

open HvdH
open Work.Layout
open Work.Layout.AA

/-! ## 1. Elementary list facts -/

/-- elementwise concatenation of two mapped lists -/
theorem mergeBlk_map (l : List ℕ) (F G : ℕ → List Val) :
    mergeBlk (l.map F) (l.map G) = l.map (fun i => F i ++ G i) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      show (F a ++ G a) :: mergeBlk (t.map F) (t.map G)
        = (F a ++ G a) :: t.map (fun i => F i ++ G i)
      rw [ih]

/-- `mergeBlk` of two `range C`-indexed lists -/
theorem mergeBlk_range (C : ℕ) (F G : ℕ → List Val) :
    mergeBlk ((List.range C).map F) ((List.range C).map G)
      = (List.range C).map (fun i => F i ++ G i) :=
  mergeBlk_map (List.range C) F G

theorem getD_append_right {α : Type} [Inhabited α] (l l' : List α) (d : α) {n : ℕ}
    (h : l.length ≤ n) : (l ++ l').getD n d = l'.getD (n - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append,
    if_neg (by omega)]

/-! ## 2. `colsOf` and the block of a group -/

/-- the columns of a concatenation of two flat arrays -/
theorem colsOf_append (m1 m2 C : ℕ) (L1 L2 : List Val) (hL : L1.length = m1 * C) :
    colsOf (m1 + m2) C (L1 ++ L2) = mergeBlk (colsOf m1 C L1) (colsOf m2 C L2) := by
  show (List.range C).map (fun i => (List.range (m1 + m2)).map
      (fun j => (L1 ++ L2).getD (j * C + i) default))
    = mergeBlk ((List.range C).map (fun i => (List.range m1).map
        (fun j => L1.getD (j * C + i) default)))
      ((List.range C).map (fun i => (List.range m2).map
        (fun j => L2.getD (j * C + i) default)))
  rw [mergeBlk_range]
  refine List.map_congr_left (fun i hi => ?_)
  simp only [List.mem_range] at hi
  rw [List.range_add]
  simp only [List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left (fun j hj => ?_)
    simp only [List.mem_range] at hj
    have hlt : j * C + i < m1 * C := by
      have h2 : (j + 1) * C ≤ m1 * C := Nat.mul_le_mul_right C (by omega)
      have h3 : j * C + i < (j + 1) * C := by rw [Nat.succ_mul]; omega
      omega
    exact List.getD_append L1 L2 default (j * C + i) (by omega)
  · refine List.map_congr_left (fun j hj => ?_)
    simp only [List.mem_range] at hj
    show (L1 ++ L2).getD ((m1 + j) * C + i) default = L2.getD (j * C + i) default
    have hle : m1 * C ≤ (m1 + j) * C := Nat.mul_le_mul_right C (by omega)
    rw [getD_append_right L1 L2 default (by omega)]
    congr 1
    have h1 : (m1 + j) * C + i = m1 * C + (j * C + i) := by ring
    omega

/-- the block of a single row -/
theorem colsOf_one (C : ℕ) (L : List Val) (h : L.length = C) :
    colsOf 1 C L = L.map (fun e => [e]) := by
  have hL : colsOf 1 C L = (List.range C).map (fun i => [L.getD i default]) := by
    show (List.range C).map (fun i => (List.range 1).map (fun j => L.getD (j * C + i) default))
      = (List.range C).map (fun i => [L.getD i default])
    refine List.map_congr_left (fun i _ => ?_)
    simp only [List.range_one, List.map_cons, List.map_nil, Nat.zero_mul, Nat.zero_add]
  rw [hL, ← h]
  conv_rhs => rw [← range_map_getD L default]
  rw [List.map_map]
  rfl

/-- the length of the flattening of a group of rows -/
theorem flatten_length (C : ℕ) (g : List (List Val)) (h : ∀ r ∈ g, r.length = C) :
    g.flatten.length = g.length * C := by
  induction g with
  | nil => simp
  | cons r rs ih =>
      rw [List.flatten_cons, List.length_append, List.length_cons,
        ih (fun x hx => h x (List.mem_cons_of_mem r hx)), h r (by simp)]
      ring

/-- the block of a concatenation of two groups -/
theorem grpBlk_append (C : ℕ) (g1 g2 : List (List Val)) (h1 : ∀ r ∈ g1, r.length = C)
    (h2 : ∀ r ∈ g2, r.length = C) :
    grpBlk C (g1 ++ g2) = mergeBlk (grpBlk C g1) (grpBlk C g2) := by
  show colsOf (g1 ++ g2).length C (g1 ++ g2).flatten = _
  simp only [grpBlk, List.length_append, List.flatten_append]
  exact colsOf_append g1.length g2.length C g1.flatten g2.flatten (flatten_length C g1 h1)

/-! ## 3. Group lists -/

/-- all rows of all groups have length `C` -/
def RowsOk (C : ℕ) (gs : List (List (List Val))) : Prop := ∀ g ∈ gs, ∀ r ∈ g, r.length = C

theorem RowsOk.cons {C : ℕ} {g : List (List Val)} {gs : List (List (List Val))}
    (hg : ∀ r ∈ g, r.length = C) (h : RowsOk C gs) : RowsOk C (g :: gs) := by
  intro g' hg' r hr
  rcases List.mem_cons.mp hg' with rfl | h'
  · exact hg r hr
  · exact h g' h' r hr

theorem RowsOk_grpStep : ∀ (C : ℕ) (gs : List (List (List Val))), RowsOk C gs →
    RowsOk C (grpStep gs)
  | C, [], _ => by simp [grpStep, RowsOk]
  | C, [g], h => by simpa [grpStep, RowsOk] using h
  | C, g1 :: g2 :: rest, h => by
      have h1 : ∀ r ∈ g1, r.length = C := fun r hr => h g1 (by simp) r hr
      have h2 : ∀ r ∈ g2, r.length = C := fun r hr => h g2 (by simp) r hr
      have hrest : RowsOk C rest := fun g hg r hr => h g (by simp [hg]) r hr
      show RowsOk C ((g1 ++ g2) :: grpStep rest)
      refine RowsOk.cons (fun r hr => ?_) (RowsOk_grpStep C rest hrest)
      rcases List.mem_append.mp hr with hr | hr
      · exact h1 r hr
      · exact h2 r hr

/-- one level step of the block list corresponds to one level step of the group list -/
theorem blksOf_grpStep (C : ℕ) : ∀ gs : List (List (List Val)), RowsOk C gs →
    blksOf C (grpStep gs) = lvlStep (blksOf C gs)
  | [], _ => by simp [grpStep, blksOf, lvlStep]
  | [g], _ => by simp [grpStep, blksOf, lvlStep]
  | g1 :: g2 :: rest, h => by
      have h1 : ∀ r ∈ g1, r.length = C := fun r hr => h g1 (by simp) r hr
      have h2 : ∀ r ∈ g2, r.length = C := fun r hr => h g2 (by simp) r hr
      have hrest : RowsOk C rest := fun g hg r hr => h g (by simp [hg]) r hr
      show grpBlk C (g1 ++ g2) :: blksOf C (grpStep rest)
        = mergeBlk (grpBlk C g1) (grpBlk C g2) :: lvlStep (blksOf C rest)
      rw [grpBlk_append C g1 g2 h1 h2, blksOf_grpStep C rest hrest]

/-- `k` level steps of the block list correspond to `k` level steps of the group list -/
theorem blksOf_grpIter (C : ℕ) : ∀ (k : ℕ) (gs : List (List (List Val))), RowsOk C gs →
    blksOf C (grpIter k gs) = lvlIter k (blksOf C gs)
  | 0, gs, _ => rfl
  | k + 1, gs, h => by
      show blksOf C (grpIter k (grpStep gs)) = lvlIter k (lvlStep (blksOf C gs))
      rw [blksOf_grpIter C k (grpStep gs) (RowsOk_grpStep C gs h),
        blksOf_grpStep C gs h]

/-! ## 4. Iteration lengths -/

theorem grpStep_length : ∀ gs : List (List (List Val)), (grpStep gs).length = (gs.length + 1) / 2
  | [] => by decide
  | [g] => by
      have h : grpStep [g] = [g] := rfl
      rw [h]
      simp
  | g1 :: g2 :: rest => by
      have h : grpStep (g1 :: g2 :: rest) = (g1 ++ g2) :: grpStep rest := rfl
      rw [h, List.length_cons, grpStep_length rest]
      simp only [List.length_cons]
      omega

theorem grpStep_flatten : ∀ gs : List (List (List Val)), (grpStep gs).flatten = gs.flatten
  | [] => rfl
  | [g] => by
      have h : grpStep [g] = [g] := rfl
      rw [h]
  | g1 :: g2 :: rest => by
      have h : grpStep (g1 :: g2 :: rest) = (g1 ++ g2) :: grpStep rest := rfl
      rw [h, List.flatten_cons, grpStep_flatten rest]
      simp only [List.flatten_cons, List.append_assoc]

theorem grpIter_flatten (k : ℕ) (gs : List (List (List Val))) :
    (grpIter k gs).flatten = gs.flatten := by
  induction k generalizing gs with
  | zero => rfl
  | succ k ih => rw [grpIter, ih, grpStep_flatten]

/-- a list of groups whose flattening is `l` and whose length is `1` is `[l]` -/
theorem eq_singleton_of_flatten (gs : List (List (List Val))) (h : gs.length = 1) :
    gs = [gs.flatten] := by
  rcases gs with _ | ⟨g, t⟩
  · simp at h
  · rcases t with _ | ⟨g2, t2⟩
    · simp
    · simp at h

/-- `grpIter` reaches the single group `gs.flatten` -/
theorem grpIter_single (k : ℕ) (gs : List (List (List Val))) (hpos : 1 ≤ gs.length)
    (h : gs.length ≤ 2 ^ k) : grpIter k gs = [gs.flatten] := by
  have hlen : (grpIter k gs).length = 1 := by
    induction k generalizing gs with
    | zero => simp only [grpIter]; norm_num at h; omega
    | succ k ih =>
        have hgs : 1 ≤ (grpStep gs).length := by rw [grpStep_length]; omega
        have hlt : (grpStep gs).length ≤ 2 ^ k := by
          rw [grpStep_length]
          have h2 : gs.length ≤ 2 ^ k * 2 := by
            simpa [pow_succ] using h
          omega
        simpa only [grpIter] using ih (grpStep gs) hgs hlt
  rw [eq_singleton_of_flatten _ hlen, grpIter_flatten]

/-! ## 5. The level-0 block list of a flat array -/

theorem gs0_length (M C : ℕ) (L : List Val) : (gs0 M C L).length = M := by
  simp [gs0, rowsOf]

theorem flatten_map_singleton {α : Type} (l : List α) : (l.map (fun x => [x])).flatten = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.flatten_cons, List.singleton_append, ih]

theorem gs0_flatten (M C : ℕ) (L : List Val) : (gs0 M C L).flatten = rowsOf M C L := by
  show ((rowsOf M C L).map (fun r => [r])).flatten = rowsOf M C L
  exact flatten_map_singleton (rowsOf M C L)

theorem gs0_RowsOk (M C : ℕ) (L : List Val) (h : L.length = M * C) : RowsOk C (gs0 M C L) := by
  obtain ⟨-, hr, -⟩ := rowsOf_facts M C L h
  intro g hg r hr'
  obtain ⟨r0, hr0, hg0⟩ := List.mem_map.mp hg
  have hmem : r = r0 := by
    have h' : r ∈ [r0] := by rw [hg0]; exact hr'
    simpa using h'
  rw [hmem]
  exact hr r0 hr0

/-- the level-0 block list is the block list of the level-0 group list -/
theorem lv0_eq_blksOf_gs0 (M C : ℕ) (L : List Val) (h : L.length = M * C) :
    lv0 M C L = blksOf C (gs0 M C L) := by
  obtain ⟨-, hr, -⟩ := rowsOf_facts M C L h
  show ((rowsOf M C L).map (fun r => r.map (fun e => [e]))) =
    ((gs0 M C L).map (grpBlk C))
  simp only [gs0, List.map_map, Function.comp_apply]
  refine List.map_congr_left (fun r hr' => ?_)
  have hlen : r.length = C := hr r hr'
  show r.map (fun e => [e]) = grpBlk C [r]
  have hg : grpBlk C [r] = colsOf 1 C r := by
    show colsOf [r].length C [r].flatten = colsOf 1 C r
    simp only [List.length_cons, List.length_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
  rw [hg]
  exact (colsOf_one C r hlen).symm

theorem blksOf_single (C : ℕ) (g : List (List Val)) : blksOf C [g] = [grpBlk C g] := rfl

theorem grpBlk_rowsOf (M C : ℕ) (L : List Val) (h : L.length = M * C) :
    grpBlk C (rowsOf M C L) = colsOf M C L := by
  obtain ⟨h1, -, h3⟩ := rowsOf_facts M C L h
  show colsOf (rowsOf M C L).length C (rowsOf M C L).flatten = colsOf M C L
  rw [h1, h3]

/-! ## 6. Main pure statement -/

/-- After `M.size` level steps the block list of the flat `M × C` array `L` is the singleton of its
columns. -/
theorem lvlIter_lv0 (M C : ℕ) (L : List Val) (hL : L.length = M * C) (hM : 1 ≤ M) :
    ∃ k ≤ M.size, lvlIter k (lv0 M C L) = [colsOf M C L] := by
  refine ⟨M.size, le_rfl, ?_⟩
  rw [lv0_eq_blksOf_gs0 M C L hL,
    ← blksOf_grpIter C M.size (gs0 M C L) (gs0_RowsOk M C L hL),
    grpIter_single M.size (gs0 M C L) (by rw [gs0_length]; exact hM)
      (by rw [gs0_length]; exact le_of_lt (Nat.size_le.mp (le_refl M.size))),
    gs0_flatten, blksOf_single, grpBlk_rowsOf M C L hL]

/-- The block list reached by the level loop is the singleton of the columns, whenever it has length
one (this is the exit condition of `trLevelLoop`). -/
theorem lvlIter_eq_colsOf (M C : ℕ) (L : List Val) (hL : L.length = M * C) (k : ℕ)
    (h : (lvlIter k (lv0 M C L)).length = 1) :
    lvlIter k (lv0 M C L) = [colsOf M C L] := by
  have hlen : (grpIter k (gs0 M C L)).length = 1 := by
    have h' := h
    rw [lv0_eq_blksOf_gs0 M C L hL, ← blksOf_grpIter C k (gs0 M C L) (gs0_RowsOk M C L hL)] at h'
    simpa [blksOf] using h'
  rw [lv0_eq_blksOf_gs0 M C L hL, ← blksOf_grpIter C k (gs0 M C L) (gs0_RowsOk M C L hL),
    eq_singleton_of_flatten (grpIter k (gs0 M C L)) hlen, grpIter_flatten, gs0_flatten,
    blksOf_single, grpBlk_rowsOf M C L hL]

end Work.Resample.PB
