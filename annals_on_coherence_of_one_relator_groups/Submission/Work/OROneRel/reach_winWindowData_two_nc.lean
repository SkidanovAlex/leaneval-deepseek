-- **Namespaced copy** (`Work.OROneRel.NC`) of a colleague's module, made so that the
-- window-data pipeline can be imported *together with* the Freiheitssatz pipeline:
-- `Work.OROneRel.decor_replicate_true` (declared in `Submission.Work.OROneRel.decor_wordOf_zpow_of`)
-- clashes with the declaration of the same name in
-- `Submission.Work.OROneRel.twoLetter_cycle_decor`, so no module can import both
-- `exists_window_support_data_cycred` and `bandFreiheitssatz_of_windowData`.  The copy lives in
-- the namespace `Work.OROneRel.NC`, where `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true`
-- and no longer clashes.  Nothing here is new mathematics.
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.band_one_lift
import Submission.Work.OROneRel.reach_of_closed_walk
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.reach_unit_weight_nc
import Submission.Work.OROneRel.steps_of_chain
import Submission.Work.OROneRel.exists_word_of_confined_steps
import Submission.Work.OROneRel.decor_winE_of_red

/-!
# Reachability of the levels of the window

`Work.OROneRel.NC.reach_winWindowData_two`: if `c : α → ℤ` is a weight supported on two generators `x0`,
`y0` of coprime weights (`p * c x0 + q * c y0 = 1`), `cohom c u = 1` (so the walk of `u` in the
`ℤ`-cover is closed at the level `0`), every letter of `u` has non-zero exponent sum, and `[lo,hi]` is
a window containing the walk of `u` with no non-zero translate of the walk inside it, then **every**
level of the window is reached from `0` by a word of the free group whose whole walk stays in the
window.

The proof has three parts.

* The window contains the level `0` (`zero_mem_window`), because the walk of `u` starts there.
* The walk of `u`, with its steps of weight `0` deleted, is a closed `±A,±B` walk (`A = |c x0|`,
  `B = |c y0|`) in which the `+A` and `-A` steps occur a different number of times (their difference
  is `±(eps x0 u) ≠ 0`).  The arithmetic theorem `band_le` of
  `Submission.Work.OROneRel.reach_of_closed_walk` then bounds the window (`A + B - 2 ≤ hi - lo`) and
  `interval_connected` supplies, for every level `i` of the window, a chain of `±A`/`±B` steps from
  `0` to `i` inside the window.
* `steps_of_chain` turns that chain into a list of steps, `exists_word_of_confined_steps` into the
  word list spelling out those steps, and `decor_winE_of_red` transports the window property from the
  spelled-out word list to the reduced word of the group element it represents.

When `|c x0| = 1` or `|c y0| = 1` the single generator of weight `±1` already walks monotonically to
the wanted level (`reach_unit_weight`).
-/

namespace Work.OROneRel.NC

universe u

set_option linter.unusedVariables false

/-! ## List and walk plumbing -/

/-- The partial sums of the weights of a word are the levels of its walk. -/
private theorem scanl_map_linc_eq_running {α : Type u} (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (L.map (linc c)).scanl (fun a b => a + b) i = running c i L := by
  induction L generalizing i with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.map_cons, List.scanl_cons, show linc c (a, false) = -c a from rfl,
        ih (i + -c a)]
      rfl
    · rw [List.map_cons, List.scanl_cons, show linc c (a, true) = c a from rfl, ih (i + c a)]
      rfl

/-- Deleting the zero steps of a list of weights leaves every partial sum a partial sum of the
original list. -/
private theorem filter_ne_zero_scanl_subset (l : List ℤ) (i x : ℤ)
    (hx : x ∈ (l.filter (fun s => s ≠ 0)).scanl (fun a b => a + b) i) :
    x ∈ l.scanl (fun a b => a + b) i := by
  induction l generalizing i with
  | nil => simpa using hx
  | cons s t ih =>
    by_cases hs : s = 0
    · rw [List.filter_cons_of_neg (by simp [hs])] at hx
      rw [List.scanl_cons, List.mem_cons]
      refine Or.inr ?_
      rw [hs, add_zero]
      exact ih i hx
    · rw [List.filter_cons_of_pos (by simp [hs])] at hx
      rw [List.scanl_cons, List.mem_cons] at hx
      rw [List.scanl_cons]
      rcases hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (i + s) hx)

/-- Deleting the zero steps of a list of weights does not change the total weight. -/
private theorem sum_filter_ne_zero (l : List ℤ) :
    (l.filter (fun s => s ≠ 0)).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons s t ih =>
    by_cases hs : s = 0
    · rw [List.filter_cons_of_neg (by simp [hs]), ih, hs, List.sum_cons, zero_add]
    · rw [List.filter_cons_of_pos (by simp [hs]), List.sum_cons, ih, List.sum_cons]

/-- The weight of a word is the sum of the weights of its letters. -/
private theorem lsig_eq_map_linc {α : Type u} (c : α → ℤ) (L : List (α × Bool)) :
    lsig c L = (L.map (linc c)).sum := rfl

/-- Every level of the walk of a word whose decorated letters all lie in the window is in the
window (given that the starting level `0` is). -/
private theorem running_mem_window {α : Type u} (c : α → ℤ) {lo hi : ℤ} {L : List (α × Bool)}
    (h0 : lo ≤ 0 ∧ 0 ≤ hi)
    (hW : ∀ q ∈ decor c 0 L, coverEdge q ∈ winE c lo hi) :
    ∀ x ∈ running c 0 L, lo ≤ x ∧ x ≤ hi := by
  intro x hx
  rw [← running_eq_cons_tail c 0 L, List.mem_cons] at hx
  rcases hx with hx | hx
  · subst hx; exact h0
  · rw [← decor_map_coverTgt] at hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
    have hq' := (coverEdge_mem_winE_iff c lo hi q).mp (hW q hq)
    rw [← hqx]
    exact ⟨hq'.2.2.1, hq'.2.2.2⟩

/-- **The window contains the level `0`.**  The walk of `u` starts at the level `0`; by `hwin` the
first edge of that walk is an edge of the window, so `0`, one of its two endpoints, lies in it.

The hypothesis `hone` is used only to rule out the degenerate case `u = 1`, where the walk is empty
and the first edge does not exist. -/
private theorem zero_mem_window {α : Type u} [DecidableEq α] {c : α → ℤ} {u : FreeGroup α}
    {lo hi : ℤ}
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ decor c 0 (wordOf u),
      lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
        p.1.2 + c p.1.1 + k ≤ hi)) :
    lo ≤ 0 ∧ 0 ≤ hi := by
  have hdecor : decor c 0 ([] : List (α × Bool)) = [] := rfl
  have hne : wordOf u ≠ [] := by
    intro hw
    refine hone 1 one_ne_zero ?_
    rw [hw, hdecor]
    simp
  obtain ⟨a, b, L', hL⟩ : ∃ (a : α) (b : Bool) (L' : List (α × Bool)),
      wordOf u = (a, b) :: L' := by
    cases h : wordOf u with
    | nil => exact absurd h hne
    | cons p L' => exact ⟨p.1, p.2, L', rfl⟩
  cases b
  · have hqmem : ((a, (0 : ℤ) - c a), false) ∈ decor c 0 (wordOf u) := by
      rw [hL]; exact List.mem_cons_self ..
    have hmem := hwin _ hqmem
    rw [mem_winE] at hmem
    obtain ⟨h1, h2, h3, h4⟩ := hmem
    simp only [coverEdge, Prod.snd, Prod.fst] at h1 h2 h3 h4
    constructor <;> omega
  · have hqmem : ((a, (0 : ℤ)), true) ∈ decor c 0 (wordOf u) := by
      rw [hL]; exact List.mem_cons_self ..
    have hmem := hwin _ hqmem
    rw [mem_winE] at hmem
    obtain ⟨h1, h2, h3, h4⟩ := hmem
    simp only [coverEdge, Prod.snd, Prod.fst] at h1 h2 h3 h4
    constructor <;> omega


/-- The number of letters of `L` whose increment is `A`, minus the number of letters whose increment
is `-A`, is `±(eps x0 u)`.  When `c x0 = A` an `x0`-letter contributes positively to the difference
exactly when it is positive, and `x0` is the only generator whose increment can be `±A`. -/
private theorem count_signed_A_steps_aux {α : Type u} [DecidableEq α] (c : α → ℤ) (x0 y0 : α)
    (A B : ℤ) (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B)
    (hsup2 : ∀ x : α, x ≠ x0 → x ≠ y0 → c x = 0)
    (hx0 : |c x0| = A) (hy0 : |c y0| = B) (L : List (α × Bool)) :
    (((L.map (linc c)).filter (fun s => s = A)).length : ℤ)
      - (((L.map (linc c)).filter (fun s => s = -A)).length : ℤ)
      = (if 0 < c x0 then (1 : ℤ) else -1) * wordEps x0 L := by
  -- a filtered length is the sum of the `0`/`1` indicators of the predicate
  have hind : ∀ {β : Type u} (l : List β) (q : β → Prop) [DecidablePred q],
      ((l.filter q).length : ℤ) = (l.map (fun s => if q s then (1 : ℤ) else 0)).sum := by
    intro β l q _
    induction l with
    | nil => simp
    | cons s t ih =>
      by_cases h : q s
      · rw [List.filter_cons_of_pos (by simp [h]), List.length_cons, List.map_cons, List.sum_cons,
          if_pos h, Nat.cast_add, Nat.cast_one, ih]
        ring
      · rw [List.filter_cons_of_neg (by simp [h]), List.map_cons, List.sum_cons, if_neg h, ih]
        ring
  have hsub : ∀ {β : Type u} (l : List β) (f g : β → ℤ),
      (l.map (fun s => f s - g s)).sum = (l.map f).sum - (l.map g).sum := by
    intro β l f g
    induction l with
    | nil => simp
    | cons s t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        ih]
      ring
  have hpt : ∀ p : α × Bool,
      (if linc c p = A then (1 : ℤ) else 0) - (if linc c p = -A then (1 : ℤ) else 0)
        = (if 0 < c x0 then (1 : ℤ) else -1) *
            (if p.1 = x0 then (if p.2 then (1 : ℤ) else -1) else 0) := by
    intro p
    obtain ⟨a, b⟩ := p
    have hxa : c x0 = A ∨ c x0 = -A := (abs_eq (le_of_lt hA)).mp hx0
    have hya : c y0 = B ∨ c y0 = -B := (abs_eq (le_of_lt hB)).mp hy0
    by_cases ha : a = x0
    · rw [ha]
      rcases hxa with hx | hx
      · have hpos : 0 < c x0 := by rw [hx]; exact hA
        have hcA : c x0 = A := hx
        have hcA' : ¬ (c x0 = -A) := by rw [hx]; omega
        have hcnA : ¬ (-c x0 = A) := by rw [hx]; omega
        have hcnA' : -c x0 = -A := by rw [hx]
        cases b
        · rw [show linc c (x0, false) = -c x0 from rfl, if_neg hcnA, if_pos hcnA',
            if_pos (rfl : (x0 : α) = x0), if_pos hpos]
          simp
        · rw [show linc c (x0, true) = c x0 from rfl, if_pos hcA, if_neg hcA',
            if_pos (rfl : (x0 : α) = x0), if_pos hpos]
          simp
      · have hneg : ¬ (0 < c x0) := by rw [hx]; omega
        have hcA : c x0 = -A := hx
        have hcA' : ¬ (c x0 = A) := by rw [hx]; omega
        have hcnA : -c x0 = A := by rw [hx]; ring
        have hcnA' : ¬ (-c x0 = -A) := by rw [hx]; omega
        cases b
        · rw [show linc c (x0, false) = -c x0 from rfl, if_pos hcnA, if_neg hcnA',
            if_pos (rfl : (x0 : α) = x0), if_neg hneg]
          simp
        · rw [show linc c (x0, true) = c x0 from rfl, if_neg hcA', if_pos hcA,
            if_pos (rfl : (x0 : α) = x0), if_neg hneg]
          simp
    · by_cases hy : a = y0
      · rw [hy]
        have ha' : ¬ (y0 = x0) := by rw [← hy]; exact ha
        have hb1 : linc c (y0, b) = c y0 ∨ linc c (y0, b) = -c y0 := by
          cases b <;> simp [linc]
        have hbA1 : linc c (y0, b) ≠ A := by
          intro hc
          rcases hb1 with h | h <;> rcases hya with hy' | hy' <;> rw [hy'] at h <;> omega
        have hbA2 : linc c (y0, b) ≠ -A := by
          intro hc
          rcases hb1 with h | h <;> rcases hya with hy' | hy' <;> rw [hy'] at h <;> omega
        rw [if_neg hbA1, if_neg hbA2, if_neg ha']
        ring
      · have hca : c a = 0 := hsup2 a ha hy
        have hl0 : linc c (a, b) = 0 := by cases b <;> simp [linc, hca]
        have e1 : linc c (a, b) ≠ A := by rw [hl0]; omega
        have e2 : linc c (a, b) ≠ -A := by rw [hl0]; omega
        rw [if_neg e1, if_neg e2, if_neg ha]
        ring
  have hL1 : (((L.map (linc c)).filter (fun s => s = A)).length : ℤ)
      = (L.map (fun p => if linc c p = A then (1 : ℤ) else 0)).sum := by
    rw [List.filter_map, List.length_map]
    exact hind L (fun p => linc c p = A)
  have hL2 : (((L.map (linc c)).filter (fun s => s = -A)).length : ℤ)
      = (L.map (fun p => if linc c p = -A then (1 : ℤ) else 0)).sum := by
    rw [List.filter_map, List.length_map]
    exact hind L (fun p => linc c p = -A)
  rw [hL1, hL2, ← hsub L (fun p => if linc c p = A then (1 : ℤ) else 0)
        (fun p => if linc c p = -A then (1 : ℤ) else 0)]
  rw [show L.map (fun p => (if linc c p = A then (1 : ℤ) else 0)
        - (if linc c p = -A then (1 : ℤ) else 0))
      = L.map (fun p => (if 0 < c x0 then (1 : ℤ) else -1) *
          (if p.1 = x0 then (if p.2 then (1 : ℤ) else -1) else 0)) from
    List.map_congr_left (fun p _ => hpt p)]
  rw [List.sum_map_mul_left]
  rw [wordEps]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  by_cases h : p.2 <;> simp [h]

/-! ## The main theorem -/

theorem reach_winWindowData_two {α : Type u} [Fintype α] [DecidableEq α]
    (c : α → ℤ) (u : FreeGroup α) (x0 y0 : α) (lo hi : ℤ)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
        p.1.2 + c p.1.1 + k ≤ hi))
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    (hsup2 : ∀ x : α, x ≠ x0 → x ≠ y0 → c x = 0)
    (hcu : Work.OROneRel.cohom c u = 1)
    (hcx : c x0 ≠ 0) (hcy : c y0 ≠ 0) (hx0R : x0 ∈ Work.OROneRel.relatorLetters u)
    (hy0R : y0 ∈ Work.OROneRel.relatorLetters u)
    (hbez : ∃ p q : ℤ, p * c x0 + q * c y0 = 1) :
    ∀ i : ℤ, lo ≤ i → i ≤ hi → ∃ w : FreeGroup α,
      Work.OROneRel.cohom c w = Multiplicative.ofAdd i ∧
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi := by
  have h0 : lo ≤ 0 ∧ 0 ≤ hi := zero_mem_window hwin hone
  intro i hilo hihi
  by_cases hx1 : |c x0| = 1
  · have hz : c x0 = 1 ∨ c x0 = -1 := by
      by_cases h : 0 ≤ c x0
      · left; rw [abs_of_nonneg h] at hx1; exact hx1
      · right; push Not at h; rw [abs_of_neg h] at hx1; linarith
    exact reach_unit_weight c x0 lo hi i hz h0.1 h0.2 hilo hihi
  by_cases hy1 : |c y0| = 1
  · have hz : c y0 = 1 ∨ c y0 = -1 := by
      by_cases h : 0 ≤ c y0
      · left; rw [abs_of_nonneg h] at hy1; exact hy1
      · right; push Not at h; rw [abs_of_neg h] at hy1; linarith
    exact reach_unit_weight c y0 lo hi i hz h0.1 h0.2 hilo hihi
  -- the general case: both weights are at least `2`
  have hAx0 : 0 < |c x0| := abs_pos.mpr hcx
  have hAy0 : 0 < |c y0| := abs_pos.mpr hcy
  have hA2 : 2 ≤ |c x0| := by omega
  have hB2 : 2 ≤ |c y0| := by omega
  have hxs : c x0 = |c x0| ∨ c x0 = -|c x0| := (abs_eq (abs_nonneg _)).mp rfl
  have hys : c y0 = |c y0| ∨ c y0 = -|c y0| := (abs_eq (abs_nonneg _)).mp rfl
  have hAB : |c x0| ≠ |c y0| := by
    intro habs
    obtain ⟨p, q, hpq⟩ := hbez
    have hcy' : c y0 = c x0 ∨ c y0 = -c x0 := by
      rcases hys with hy | hy <;> rcases hxs with hx | hx
      · exact Or.inl (by linarith [hy, hx, habs])
      · exact Or.inr (by linarith [hy, hx, habs])
      · exact Or.inr (by linarith [hy, hx, habs])
      · exact Or.inl (by linarith [hy, hx, habs])
    have hdiv : |c x0| ∣ 1 := by
      rcases hcy' with h | h
      · have h1 : (p + q) * c x0 = 1 := by
          rw [h] at hpq
          ring_nf at hpq ⊢
          linarith
        rcases hxs with hx | hx
        · refine ⟨p + q, ?_⟩
          rw [hx] at h1
          rw [← h1, mul_comm]
        · refine ⟨-(p + q), ?_⟩
          have h2 : -(p + q) * |c x0| = 1 := by
            rw [hx] at h1
            ring_nf at h1 ⊢
            linarith
          rw [← h2, mul_comm]
      · have h1 : (p - q) * c x0 = 1 := by
          rw [h] at hpq
          ring_nf at hpq ⊢
          linarith
        rcases hxs with hx | hx
        · refine ⟨p - q, ?_⟩
          rw [hx] at h1
          rw [← h1, mul_comm]
        · refine ⟨-(p - q), ?_⟩
          have h2 : -(p - q) * |c x0| = 1 := by
            rw [hx] at h1
            ring_nf at h1 ⊢
            linarith
          rw [← h2, mul_comm]
    exact absurd (Int.le_of_dvd (by norm_num) hdiv) (by omega)
  have hbezAB : ∃ p q : ℤ, p * |c x0| + q * |c y0| = 1 := by
    obtain ⟨p, q, hpq⟩ := hbez
    refine ⟨p * (if c x0 = |c x0| then 1 else -1),
      q * (if c y0 = |c y0| then 1 else -1), ?_⟩
    have hx' : (if c x0 = |c x0| then (1 : ℤ) else -1) * |c x0| = c x0 := by
      rcases hxs with h | h
      · rw [if_pos h, one_mul]; linarith
      · have hne : ¬ (c x0 = |c x0|) := by intro hc; linarith
        rw [if_neg hne, neg_one_mul]; linarith
    have hy' : (if c y0 = |c y0| then (1 : ℤ) else -1) * |c y0| = c y0 := by
      rcases hys with h | h
      · rw [if_pos h, one_mul]; linarith
      · have hne : ¬ (c y0 = |c y0|) := by intro hc; linarith
        rw [if_neg hne, neg_one_mul]; linarith
    calc p * (if c x0 = |c x0| then (1 : ℤ) else -1) * |c x0|
          + q * (if c y0 = |c y0| then (1 : ℤ) else -1) * |c y0|
        = p * ((if c x0 = |c x0| then (1 : ℤ) else -1) * |c x0|)
          + q * ((if c y0 = |c y0| then (1 : ℤ) else -1) * |c y0|) := by ring
      _ = p * c x0 + q * c y0 := by rw [hx', hy']
      _ = 1 := hpq
  set L : List (α × Bool) := wordOf u with hLdef
  set ss : List ℤ := (L.map (linc c)).filter (fun s => s ≠ 0) with hssdef
  have hstep : ∀ s ∈ ss, s = |c x0| ∨ s = -|c x0| ∨ s = |c y0| ∨ s = -|c y0| := by
    intro s hs
    rw [hssdef] at hs
    obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hs1
    obtain ⟨a, b⟩ := q
    have hlne : linc c (a, b) ≠ 0 := by simpa using hs2
    have hane : c a ≠ 0 := fun hc0 => hlne (by cases b <;> simp [linc, hc0])
    have ha : a = x0 ∨ a = y0 := by
      by_contra h
      push Not at h
      exact hane (hsup2 a h.1 h.2)
    rcases ha with hax | hay
    · rw [hax]
      rcases hxs with hx | hx
      · cases b
        · exact Or.inr (Or.inl (by show -c x0 = -|c x0|; linarith))
        · exact Or.inl (by show c x0 = |c x0|; linarith)
      · cases b
        · exact Or.inl (by show -c x0 = |c x0|; linarith)
        · exact Or.inr (Or.inl (by show c x0 = -|c x0|; linarith))
    · rw [hay]
      rcases hys with hy | hy
      · cases b
        · exact Or.inr (Or.inr (Or.inr (by show -c y0 = -|c y0|; linarith)))
        · exact Or.inr (Or.inr (Or.inl (by show c y0 = |c y0|; linarith)))
      · cases b
        · exact Or.inr (Or.inr (Or.inl (by show -c y0 = |c y0|; linarith)))
        · exact Or.inr (Or.inr (Or.inr (by show c y0 = -|c y0|; linarith)))
  have hsum : ss.sum = 0 := by
    rw [hssdef, sum_filter_ne_zero, ← lsig_eq_map_linc]
    have hmk : FreeGroup.mk L = u := by rw [hLdef]; exact mk_wordOf u
    have hcoh : Work.OROneRel.cohom c (FreeGroup.mk L) = Multiplicative.ofAdd (lsig c L) :=
      cohom_mk c L
    rw [hmk, hcu] at hcoh
    have hlsig0 : lsig c L = 0 := by
      have := congrArg Multiplicative.toAdd hcoh
      simpa using this.symm
    exact hlsig0
  have hband : ∀ l ∈ ss.scanl (fun a b => a + b) 0, lo ≤ l ∧ l ≤ hi := by
    intro l hl
    rw [hssdef] at hl
    have h1 : l ∈ running c 0 L := by
      rw [← scanl_map_linc_eq_running c 0 L]
      exact filter_ne_zero_scanl_subset _ 0 l hl
    exact running_mem_window c h0 (by rw [hLdef]; exact hwin) l h1
  have hnet : (ss.filter (fun s => s = |c x0|)).length ≠
      (ss.filter (fun s => s = -|c x0|)).length := by
    have hplumb : ∀ v : ℤ, v ≠ 0 →
        (ss.filter (fun s => s = v)).length =
          ((L.map (linc c)).filter (fun s => s = v)).length := by
      intro v hv
      rw [hssdef]
      rw [List.filter_filter]
      congr 1
      apply List.filter_congr
      intro a _
      by_cases h : a = v <;> simp [h, hv]
    have hcnt := count_signed_A_steps_aux c x0 y0 |c x0| |c y0| hAx0 hAy0 hAB hsup2 rfl rfl L
    have hbadw : wordEps x0 L ≠ 0 := by
      have := hbad x0 hx0R
      simpa [eps, wordOf, hLdef] using this
    have hne_int : (((L.map (linc c)).filter (fun s => s = |c x0|)).length : ℤ) ≠
        (((L.map (linc c)).filter (fun s => s = -|c x0|)).length : ℤ) := by
      intro hz
      apply hbadw
      have hfac : (if 0 < c x0 then (1 : ℤ) else -1) ≠ 0 := by split <;> norm_num
      have hzero : (if 0 < c x0 then (1 : ℤ) else -1) * wordEps x0 L = 0 := by
        rw [← hcnt, hz]; ring
      rcases mul_eq_zero.mp hzero with h1 | h2
      · exact absurd h1 hfac
      · exact h2
    intro hcon
    apply hne_int
    have hN : ((L.map (linc c)).filter (fun s => s = |c x0|)).length =
        ((L.map (linc c)).filter (fun s => s = -|c x0|)).length := by
      rw [← hplumb |c x0| (by omega), ← hplumb (-|c x0|) (by omega)]
      exact hcon
    exact_mod_cast hN
  have hbandineq : |c x0| + |c y0| - 2 ≤ hi - lo :=
    band_le hA2 hB2 hbezAB ss hstep hsum hnet lo hi
      (fun l hl => (hband l hl).1) (fun l hl => (hband l hl).2)
  have hchain := interval_connected hA2 hB2 hbezAB lo hi hbandineq 0 i h0.1 h0.2 hilo hihi
  obtain ⟨ss', hstep', hsum', hband'⟩ := steps_of_chain hchain h0
  obtain ⟨L', hlsig', hWin'⟩ :=
    exists_word_of_confined_steps c x0 y0 |c x0| |c y0| (ne_of_gt hAx0) (ne_of_gt hAy0) hAB hxs
      hys ss' hstep' lo hi hband'
  refine ⟨FreeGroup.mk L', ?_, ?_⟩
  · rw [cohom_mk, hlsig', hsum']
    norm_num
  · exact decor_winE_of_red c lo hi
      (@FreeGroup.reduce.red α L' (Classical.decEq α)) hWin'

end Work.OROneRel.NC
