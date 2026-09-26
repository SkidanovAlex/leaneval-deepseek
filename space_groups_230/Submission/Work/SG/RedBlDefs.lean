import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# Plumbing for the echelon reduction `Data.reduceBl`

The cohomology certificate of the workspace reduces flat integer vectors modulo an upper-echelon
basis by `Data.reduceBl`.  All the facts needed to *soundly* extract the quotient structure from
that algorithm are pure `ℤ`-list linear algebra, collected here:

* `padL`, `addC`, `smulC`, `subC` -- coefficient arithmetic padded to a fixed length;
* `step`, `redF` -- the reduction algorithm as a single step and as a fold of prefixes;
* `rowl` -- row `c` of a block list (the same accessor the algorithm uses).

**Note on the intended statement.**  `InSpan rows L u → InSpan rows L v → InSpan rows L (vadd u v)`
is *false* without length hypotheses on `u` and `v`: `List.zipWith` truncates to the shorter list,
so the zero-padded sum can leave the span.  Counterexample: `rows = [[2,1]]`, `L = 2`,
`u = [0]`, `v = [2,1]`: both lie in the span, yet `vadd [0] [2,1] = [2]`, whose zero-padded form
`(2,0)` is not in `⟨(2,1)⟩` (and `vsub [2,1] [0] = [2]` likewise).  Every lemma below therefore
carries the length hypotheses that the intended statements have.
-/

namespace Work.SG

namespace RB

open Work.SG.RC

/-! ## Padding and coefficient arithmetic -/

/-- Pad a flat vector to length `N` by its own coordinates (missing entries read `0`). -/
def padL (N : ℕ) (x : List ℤ) : List ℤ := (List.range N).map (fun c => x.getD c 0)

theorem padL_length (N : ℕ) (x : List ℤ) : (padL N x).length = N := by simp [padL]

theorem padL_getElem (N : ℕ) (x : List ℤ) {c : ℕ} (hc : c < N) :
    (padL N x)[c]'(by simpa [padL] using hc) = x.getD c 0 := by
  show (List.map (fun c => x.getD c 0) (List.range N))[c]'(by simpa [padL] using hc) = x.getD c 0
  simp only [List.getElem_map]
  simp

theorem padL_getD (N : ℕ) (x : List ℤ) {c : ℕ} (hc : c < N) :
    (padL N x).getD c 0 = x.getD c 0 := by
  rw [List.getD_eq_getElem (padL N x) (0 : ℤ) (by have := padL_length N x; omega)]
  exact padL_getElem N x hc

theorem getD_zipWith {f : ℤ → ℤ → ℤ} {a b : List ℤ} {c : ℕ} (ha : c < a.length)
    (hb : c < b.length) : (List.zipWith f a b).getD c 0 = f (a.getD c 0) (b.getD c 0) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]

theorem getD_drop (l : List ℤ) (d : ℤ) (j : ℕ) : (l.drop j).getD 0 d = l.getD j d := by
  induction j generalizing l with
  | zero => rfl
  | succ j ih => cases l with
    | nil => rfl
    | cons a t => rw [List.drop_succ_cons, List.getD_cons_succ]; exact ih t

/-- Coefficientwise sum of two coefficient lists, padded to length `N`. -/
def addC (N : ℕ) (cs ds : List ℤ) : List ℤ := List.zipWith (· + ·) (padL N cs) (padL N ds)

/-- Coefficientwise scalar multiple of a coefficient list, padded to length `N`. -/
def smulC (N : ℕ) (k : ℤ) (cs : List ℤ) : List ℤ := (padL N cs).map (fun c => k * c)

/-- Coefficientwise difference of two coefficient lists, padded to length `N`. -/
def subC (N : ℕ) (cs ds : List ℤ) : List ℤ := addC N cs (smulC N (-1) ds)

theorem addC_length (N : ℕ) (cs ds : List ℤ) : (addC N cs ds).length = N := by
  rw [addC, List.length_zipWith, padL_length, padL_length, Nat.min_self]

theorem addC_getD (N : ℕ) (cs ds : List ℤ) {c : ℕ} (hc : c < N) :
    (addC N cs ds).getD c 0 = cs.getD c 0 + ds.getD c 0 := by
  rw [addC, getD_zipWith (by rw [padL_length]; exact hc) (by rw [padL_length]; exact hc),
    padL_getD N cs hc, padL_getD N ds hc]

theorem smulC_length (N : ℕ) (k : ℤ) (cs : List ℤ) : (smulC N k cs).length = N := by
  rw [smulC, List.length_map, padL_length]

theorem smulC_getD (N : ℕ) (k : ℤ) (cs : List ℤ) {c : ℕ} (hc : c < N) :
    (smulC N k cs).getD c 0 = k * cs.getD c 0 := by
  have hlen : c < (smulC N k cs).length := by rw [smulC_length]; exact hc
  rw [List.getD_eq_getElem _ _ hlen]
  show (List.map (fun c => k * c) (padL N cs))[c]'(by simpa [smulC] using hlen) = k * cs.getD c 0
  simp only [List.getElem_map]
  rw [padL_getElem N cs hc]

theorem subC_length (N : ℕ) (cs ds : List ℤ) : (subC N cs ds).length = N := by rw [subC, addC_length]

theorem subC_getD (N : ℕ) (cs ds : List ℤ) {c : ℕ} (hc : c < N) :
    (subC N cs ds).getD c 0 = cs.getD c 0 - ds.getD c 0 := by
  rw [subC, addC_getD N cs (smulC N (-1) ds) hc, smulC_getD N (-1) ds hc]; ring

/-! ## `linC` as a range sum -/

theorem linC_nil (cs : List ℤ) (q : ℕ) : linC [] cs q = 0 := by simp [linC]

theorem linC_nil_right (rows : List (List ℤ)) (q : ℕ) : linC rows ([] : List ℤ) q = 0 := by
  induction rows with
  | nil => simp [linC]
  | cons r rs ih => simp [linC]

theorem linC_cons (r : List ℤ) (rs : List (List ℤ)) (c : ℤ) (cs : List ℤ) (q : ℕ) :
    linC (r :: rs) (c :: cs) q = c * r.getD q 0 + linC rs cs q := by
  show ((List.range (rs.length + 1)).map
      (fun j => (c :: cs).getD j 0 * ((r :: rs).getD j []).getD q 0)).sum
    = c * r.getD q 0 + ((List.range rs.length).map
      (fun j => cs.getD j 0 * (rs.getD j []).getD q 0)).sum
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, List.getD_cons_zero,
    List.getD_cons_zero]
  apply congrArg (fun t => c * r.getD q 0 + t)
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp [Function.comp_apply]

theorem linC_append (rows₁ rows₂ : List (List ℤ)) (cs₁ cs₂ : List ℤ) (q : ℕ)
    (h : rows₁.length = cs₁.length) :
    linC (rows₁ ++ rows₂) (cs₁ ++ cs₂) q = linC rows₁ cs₁ q + linC rows₂ cs₂ q := by
  induction rows₁ generalizing cs₁ with
  | nil =>
      cases cs₁ with
      | nil => simp [linC]
      | cons c cs => simp at h
  | cons r rs ih =>
      cases cs₁ with
      | nil => simp at h
      | cons c cs =>
          rw [List.cons_append, List.cons_append, linC_cons, linC_cons, ih cs (by simpa using h)]
          ring

theorem linC_zero_of_coeffs (rows : List (List ℤ)) (cs : List ℤ) (q : ℕ)
    (h : ∀ j < rows.length, cs.getD j 0 = 0) : linC rows cs q = 0 := by
  induction rows generalizing cs with
  | nil => simp [linC]
  | cons r rs ih =>
      cases cs with
      | nil => simp [linC]
      | cons c cs =>
          have hc0 : c = 0 := by simpa using h 0 (by simp)
          rw [linC_cons, hc0, zero_mul, zero_add, ih cs]
          intro j hj
          rw [← List.getD_cons_succ (x := c) (xs := cs) (n := j) (d := (0 : ℤ))]
          exact h (j + 1) (by simpa using hj)

theorem linC_singleton (rows : List (List ℤ)) (k : ℤ) (q : ℕ) :
    linC rows [k] q = k * (rows.getD 0 []).getD q 0 := by
  cases rows with
  | nil => simp [linC]
  | cons r rs => rw [linC_cons, linC_nil_right, List.getD_cons_zero]; ring

theorem linC_padL (rows : List (List ℤ)) (cs : List ℤ) (q : ℕ) :
    linC rows (padL rows.length cs) q = linC rows cs q := by
  simp only [linC]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [padL_getD _ _ (List.mem_range.mp hc)]

theorem linC_addC (rows : List (List ℤ)) (cs ds : List ℤ) (q : ℕ) :
    linC rows (addC rows.length cs ds) q = linC rows cs q + linC rows ds q := by
  have hmap : (List.range rows.length).map
        (fun j => (addC rows.length cs ds).getD j 0 * (rows.getD j []).getD q 0)
      = (List.range rows.length).map
        (fun j => cs.getD j 0 * (rows.getD j []).getD q 0
          + ds.getD j 0 * (rows.getD j []).getD q 0) := by
    apply List.map_congr_left
    intro j hj
    rcases lt_or_ge j rows.length with h | h
    · rw [addC_getD rows.length cs ds h]; ring
    · rw [List.getD_eq_default (addC rows.length cs ds) (0 : ℤ) (by rw [addC_length]; exact h),
        List.getD_eq_default rows ([] : List ℤ) h]
      simp
  simp only [linC, hmap, List.sum_map_add]

theorem linC_smulC (rows : List (List ℤ)) (k : ℤ) (cs : List ℤ) (q : ℕ) :
    linC rows (smulC rows.length k cs) q = k * linC rows cs q := by
  have hmap : (List.range rows.length).map
        (fun j => (smulC rows.length k cs).getD j 0 * (rows.getD j []).getD q 0)
      = (List.range rows.length).map
        (fun j => k * (cs.getD j 0 * (rows.getD j []).getD q 0)) := by
    apply List.map_congr_left
    intro j hj
    rcases lt_or_ge j rows.length with h | h
    · rw [smulC_getD rows.length k cs h]; ring
    · rw [List.getD_eq_default (smulC rows.length k cs) (0 : ℤ) (by rw [smulC_length]; exact h),
        List.getD_eq_default rows ([] : List ℤ) h]
      simp
  simp only [linC, hmap, List.sum_map_mul_left]

theorem linC_subC (rows : List (List ℤ)) (cs ds : List ℤ) (q : ℕ) :
    linC rows (subC rows.length cs ds) q = linC rows cs q - linC rows ds q := by
  rw [subC, linC_addC, linC_smulC]; ring

/-! ## The flat vector operations -/

theorem vz_getD (k : ℤ) (x : List ℤ) (q : ℕ) : (vz k x).getD q 0 = k * x.getD q 0 := by
  simpa [vz] using List.getD_map x (0 : ℤ) (fun a => k * a) (n := q)

theorem vz_length (k : ℤ) (x : List ℤ) : (vz k x).length = x.length := by simp [vz]

theorem vadd_getD {x y : List ℤ} {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (vadd x y).getD q 0 = x.getD q 0 + y.getD q 0 := by
  rw [vadd]; exact getD_zipWith hx hy

theorem vsub_getD {x y : List ℤ} {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (vsub x y).getD q 0 = x.getD q 0 - y.getD q 0 := by
  rw [vsub]; exact getD_zipWith hx hy

theorem vadd_length (x y : List ℤ) : (vadd x y).length = min x.length y.length := by
  rw [vadd, List.length_zipWith]

theorem vsub_length (x y : List ℤ) : (vsub x y).length = min x.length y.length := by
  rw [vsub, List.length_zipWith]

theorem vzero_length (N : ℕ) : (vzero N).length = N := by simp [vzero]

theorem vzero_getD (N q : ℕ) : (vzero N).getD q 0 = 0 := by simp [vzero]

theorem ext_getD_of_length {x y : List ℤ} {L : ℕ} (hx : x.length = L) (hy : y.length = L)
    (h : ∀ q < L, x.getD q 0 = y.getD q 0) : x = y := by
  apply List.ext_getElem
  · omega
  · intro i h1 h2
    rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2]
    exact h i (by omega)

theorem eq_vzero_of_getD (w : List ℤ) (L : ℕ) (hw : w.length = L)
    (h : ∀ q < L, w.getD q 0 = 0) : w = vzero L := by
  apply ext_getD_of_length hw (vzero_length L)
  intro q hq
  rw [h q hq, vzero_getD]

theorem vsub_vzero (x : List ℤ) (L : ℕ) (hx : x.length = L) : vsub x (vzero L) = x := by
  apply ext_getD_of_length (L := L)
  · rw [vsub_length, hx, vzero_length, Nat.min_self]
  · exact hx
  · intro q hq
    rw [vsub_getD (by omega) (by rw [vzero_length]; omega), vzero_getD]
    ring

/-! ## The reduction algorithm as a prefix fold -/

/-- Row `c` of a block list, exactly as `Data.reduceBl` reads it. -/
def rowl (Bl : List (List ℤ × Data.V3)) (c : ℕ) : List ℤ := (Bl.getD c ([], Data.V3.zero)).1

theorem rowl_eq_BlR (Bl : List (List ℤ × Data.V3)) (c : ℕ) :
    (BlR Bl).getD c [] = rowl Bl c := BlR_getD Bl c

/-- A single reduction step with the row at `c`. -/
def step (Bl : List (List ℤ × Data.V3)) (c : ℕ) (x : List ℤ) : List ℤ :=
  let r := rowl Bl c
  let k := x.getD c 0 / r.getD c 1
  List.zipWith (fun a b => a - k * b) x r

/-- The first `j` reduction steps of `Data.reduceBl`. -/
def redF (Bl : List (List ℤ × Data.V3)) (j : ℕ) (x : List ℤ) : List ℤ :=
  (List.range j).foldl (fun x c => step Bl c x) x

theorem reduceBl_eq_redF (Bl : List (List ℤ × Data.V3)) (x : List ℤ) :
    Data.reduceBl Bl x = redF Bl Bl.length x := rfl

theorem redF_succ (Bl : List (List ℤ × Data.V3)) (j : ℕ) (x : List ℤ) :
    redF Bl (j + 1) x = step Bl j (redF Bl j x) := by
  rw [redF, List.range_succ, List.foldl_append, redF]
  rfl

theorem EchAt_zero {c : ℕ} {row : List ℤ} (h : EchAt c row) : ∀ q < c, row.getD q 0 = 0 := h.1

theorem EchAt_pos {c : ℕ} {row : List ℤ} (h : EchAt c row) : 0 < row.getD c 0 := h.2

end RB

end Work.SG
