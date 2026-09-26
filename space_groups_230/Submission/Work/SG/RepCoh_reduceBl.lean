import Mathlib
import Submission.Work.SG.RedBlDefs

/-!
# The echelon reduction `Data.reduceBl` is a lattice-quotient map

`Work.SG.RC.InSpan rows L v` says that `v` lies in the `ℤ`-span of `rows` (coordinates below `L`),
and `Data.reduceBl Bl x` is the "remainder" of `x` modulo the upper-echelon basis `Bl`.

## The requested statement is false as written

The requested lemma `Work.SG.RepCoh_reduceBl` asks, among other things, for

```
∀ (L) (rows) (u v), InSpan rows L u → InSpan rows L v → InSpan rows L (vadd u v)
```

*without any length hypotheses on `u` and `v`*.  That is false: `vadd`/`vsub` are `List.zipWith`,
which **truncates to the shorter list**, so the zero-padded sum need not stay in the span.
Counterexample: `rows = [[2,1]]`, `L = 2`, `u = [0]`, `v = [2,1]`.  Both `u` and `v` lie in the
span (their zero-padded forms are `(0,0)` and `(2,1) ∈ ⟨(2,1)⟩`), but `vadd [0] [2,1] = [2]`,
and `[2]` is *not* in the span, because at `q = 0` the witness would have to be
`cs 0 = 1`, while at `q = 1` one needs `0 = cs 0 · 1`.  Likewise `vsub [2,1] [0] = [2]`.
This is formalised below as `Work.SG.RB.not_InSpan_vadd` / `Work.SG.RB.not_InSpan_vsub`.

The statement is true once the missing hypotheses `u.length = L`, `v.length = L` are added --
which is the situation of every intended use, where all vectors have length `L`.  The corrected
statement is `Work.SG.RepCoh_reduceBl_corrected` at the end of this file, fully proved.
-/

namespace Work.SG

namespace RB

open Work.SG.RC

/-! ## Length-generic list helpers -/

theorem getD_drop_gen {α : Type} (l : List α) (d : α) (j : ℕ) :
    (l.drop j).getD 0 d = l.getD j d := by
  induction j generalizing l with
  | zero => rfl
  | succ j ih => cases l with
    | nil => rfl
    | cons a t => rw [List.drop_succ_cons, List.getD_cons_succ]; exact ih t

/-! ## `InSpan` closure

`vadd`/`vsub` truncate, so the closure statements need the lengths. -/

theorem InSpan_vadd {L : ℕ} {rows : List (List ℤ)} {u v : List ℤ} (hu : u.length = L)
    (hv : v.length = L) (hu' : InSpan rows L u) (hv' : InSpan rows L v) :
    InSpan rows L (vadd u v) := by
  obtain ⟨cs, hcs⟩ := hu'
  obtain ⟨ds, hds⟩ := hv'
  refine ⟨addC rows.length cs ds, fun q hq => ?_⟩
  rw [vadd_getD (by omega) (by omega), hcs q hq, hds q hq, linC_addC]

theorem InSpan_vsub {L : ℕ} {rows : List (List ℤ)} {u v : List ℤ} (hu : u.length = L)
    (hv : v.length = L) (hu' : InSpan rows L u) (hv' : InSpan rows L v) :
    InSpan rows L (vsub u v) := by
  obtain ⟨cs, hcs⟩ := hu'
  obtain ⟨ds, hds⟩ := hv'
  refine ⟨subC rows.length cs ds, fun q hq => ?_⟩
  rw [vsub_getD (by omega) (by omega), hcs q hq, hds q hq, linC_subC]

theorem InSpan_vz {L : ℕ} {rows : List (List ℤ)} {k : ℤ} {u : List ℤ} (hu' : InSpan rows L u) :
    InSpan rows L (vz k u) := by
  obtain ⟨cs, hcs⟩ := hu'
  refine ⟨smulC rows.length k cs, fun q hq => ?_⟩
  rw [vz_getD, hcs q hq, linC_smulC]

theorem replicate_getD (n i : ℕ) : (List.replicate n (0 : ℤ)).getD i 0 = 0 := by
  rcases lt_or_ge i n with h | h
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; exact h)]

/-- A multiple of row `j` of a block list is a combination of the rows. -/
theorem InSpan_vz_row (L : ℕ) (Bl : List (List ℤ × Data.V3)) (h1 : Bl.length = L) (j : ℕ)
    (hj : j < L) (k : ℤ) : InSpan (BlR Bl) L (vz k (rowl Bl j)) := by
  refine ⟨(List.replicate j 0) ++ [k], fun q hq => ?_⟩
  rw [vz_getD]
  rw [← List.take_append_drop j (BlR Bl)]
  have hlen : ((BlR Bl).take j).length = (List.replicate j (0 : ℤ)).length := by
    rw [List.length_take, List.length_replicate, BlR_length, h1]; omega
  rw [linC_append _ _ _ _ q hlen]
  rw [linC_zero_of_coeffs _ _ q (fun c hc => replicate_getD j c)]
  rw [linC_singleton, getD_drop_gen, rowl_eq_BlR]
  ring

/-! ## The reduction fold

`Data.reduceBl` is the fold of the single steps `step` over `List.range Bl.length`, i.e.
`redF Bl Bl.length`; the coordinate behaviour is proved for all prefixes `redF Bl j`. -/

theorem step_length {Bl : List (List ℤ × Data.V3)} {L : ℕ} {c : ℕ} {x : List ℤ}
    (hx : x.length = L) (hr : (rowl Bl c).length = L) : (step Bl c x).length = L := by
  show (List.zipWith (fun a b => a - x.getD c 0 / (rowl Bl c).getD c 1 * b) x
    (rowl Bl c)).length = L
  rw [List.length_zipWith, hx, hr, Nat.min_self]

theorem step_getD {Bl : List (List ℤ × Data.V3)} {L : ℕ} {c : ℕ} {x : List ℤ}
    (hx : x.length = L) (hr : (rowl Bl c).length = L) {q : ℕ} (hq : q < L) :
    (step Bl c x).getD q 0 =
      x.getD q 0 - (x.getD c 0 / (rowl Bl c).getD c 1) * (rowl Bl c).getD q 0 := by
  show (List.zipWith (fun a b => a - x.getD c 0 / (rowl Bl c).getD c 1 * b) x
      (rowl Bl c)).getD q 0 = _
  rw [getD_zipWith (by omega) (by omega)]

theorem redF_length {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x : List ℤ} (hx : x.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L) : ∀ (j : ℕ), j ≤ L → (redF Bl j x).length = L := by
  intro j
  induction j with
  | zero => intro _; simpa [redF] using hx
  | succ j ih => intro hj; rw [redF_succ]; exact step_length (ih (by omega)) (hr j (by omega))

/-- Steps with index above `q` never touch the `q`-th coordinate. -/
theorem redF_getD_stable {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x : List ℤ} (hx : x.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0) {q : ℕ} (hq : q < L) :
    ∀ (j : ℕ), q + 1 ≤ j → j ≤ L → (redF Bl j x).getD q 0 = (redF Bl (q + 1) x).getD q 0 := by
  intro j
  induction j with
  | zero => intro h _; omega
  | succ j ih =>
      intro hj hjL
      rcases Nat.lt_or_ge j (q + 1) with hlt | hge
      · have heq : j + 1 = q + 1 := by omega
        rw [heq]
      · have hlen : (redF Bl j x).length = L := redF_length hx hr j (by omega)
        rw [redF_succ, step_getD hlen (hr j (by omega)) hq, hz j (by omega) q (by omega), mul_zero,
          sub_zero]
        exact ih hge (by omega)

theorem rowl_piv_eq {Bl : List (List ℤ × Data.V3)} {L : ℕ} {c : ℕ} (hr : (rowl Bl c).length = L)
    (hc : c < L) : (rowl Bl c).getD c 1 = (rowl Bl c).getD c 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [hr]; exact hc),
    List.getD_eq_getElem _ _ (by rw [hr]; exact hc)]

theorem sub_ediv_mul (a b : ℤ) : a - a / b * b = a % b := by
  rw [Int.emod_def]; ring

/-- The `q`-th coordinate after `q + 1` steps is the residue of the `q`-th coordinate after `q`
steps, modulo the pivot. -/
theorem redF_piv {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x : List ℤ} (hx : x.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L) {q : ℕ} (hq : q < L) :
    (redF Bl (q + 1) x).getD q 0 = (redF Bl q x).getD q 0 % (rowl Bl q).getD q 1 := by
  have hlen : (redF Bl q x).length = L := redF_length hx hr q (by omega)
  rw [redF_succ, step_getD hlen (hr q hq) hq, rowl_piv_eq (hr q hq) hq, sub_ediv_mul]

theorem redF_L_getD_mod {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x : List ℤ} (hx : x.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0) {c : ℕ} (hc : c < L) :
    (redF Bl L x).getD c 0 = (redF Bl c x).getD c 0 % (rowl Bl c).getD c 1 := by
  rw [redF_getD_stable hx hr hz hc L (by omega) le_rfl]
  exact redF_piv hx hr hc

/-- Every coordinate of the fully reduced vector lies in `[0, pivot)`. -/
theorem redF_L_bounds {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x : List ℤ} (hx : x.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0)
    (hp : ∀ c < L, 0 < (rowl Bl c).getD c 1) {c : ℕ} (hc : c < L) :
    0 ≤ (redF Bl L x).getD c 0 ∧ (redF Bl L x).getD c 0 < (rowl Bl c).getD c 1 := by
  rw [redF_L_getD_mod hx hr hz hc]
  exact ⟨Int.emod_nonneg _ (ne_of_gt (hp c hc)), Int.emod_lt_of_pos _ (hp c hc)⟩

theorem reduceBl_length {Bl : List (List ℤ × Data.V3)} {L : ℕ} (h1 : Bl.length = L) {x : List ℤ}
    (hx : x.length = L) (hr : ∀ c < L, (rowl Bl c).length = L) :
    (Data.reduceBl Bl x).length = L := by
  rw [reduceBl_eq_redF, h1]; exact redF_length hx hr L le_rfl

theorem reduceBl_bounds {Bl : List (List ℤ × Data.V3)} {L : ℕ} (h1 : Bl.length = L) {x : List ℤ}
    (hx : x.length = L) (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0)
    (hp : ∀ c < L, 0 < (rowl Bl c).getD c 1) {c : ℕ} (hc : c < L) :
    0 ≤ (Data.reduceBl Bl x).getD c 0 ∧
      (Data.reduceBl Bl x).getD c 0 < (rowl Bl c).getD c 1 := by
  rw [reduceBl_eq_redF, h1]
  exact redF_L_bounds hx hr hz hp hc

/-- A vector all of whose coordinates are already residues is a fixed point of the reduction. -/
theorem redF_noop {Bl : List (List ℤ × Data.V3)} {L : ℕ} {y : List ℤ} (hy : y.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L)
    (hb : ∀ q < L, 0 ≤ y.getD q 0 ∧ y.getD q 0 < (rowl Bl q).getD q 1) :
    redF Bl L y = y := by
  have key : ∀ (j : ℕ), j ≤ L → redF Bl j y = y := by
    intro j
    induction j with
    | zero => intro _; simp [redF]
    | succ j ih =>
        intro hj
        have hstep : step Bl j y = y := by
          have h0 : y.getD j 0 / (rowl Bl j).getD j 1 = 0 :=
            Int.ediv_eq_zero_of_lt (hb j (by omega)).1 (hb j (by omega)).2
          show List.zipWith (fun a b => a - y.getD j 0 / (rowl Bl j).getD j 1 * b) y
            (rowl Bl j) = y
          rw [h0]
          have hrj : (rowl Bl j).length = L := hr j (by omega)
          apply ext_getD_of_length (L := L)
          · rw [List.length_zipWith, hy, hrj, Nat.min_self]
          · exact hy
          · intro q hq
            rw [getD_zipWith (by omega) (by omega)]
            ring
        rw [redF_succ, ih (by omega), hstep]
  exact key L le_rfl

/-! ## The telescoping argument: `x - reduce x` is a combination of the rows -/

theorem vsub_step_eq {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x z : List ℤ} {j : ℕ}
    (hx : x.length = L) (hz : z.length = L) (hr : (rowl Bl j).length = L) :
    vsub x (step Bl j z) =
      vadd (vsub x z) (vz (z.getD j 0 / (rowl Bl j).getD j 1) (rowl Bl j)) := by
  have hst : (step Bl j z).length = L := step_length hz hr
  have hsub : (vsub x z).length = L := by rw [vsub_length, hx, hz, Nat.min_self]
  have hvz : (vz (z.getD j 0 / (rowl Bl j).getD j 1) (rowl Bl j)).length = L := by
    rw [vz_length, hr]
  apply ext_getD_of_length (L := L)
  · rw [vsub_length, hx, hst, Nat.min_self]
  · rw [vadd_length, hsub, hvz, Nat.min_self]
  · intro q hq
    rw [vsub_getD (by omega) (by omega), step_getD hz hr hq, vadd_getD (by omega) (by omega),
      vsub_getD (by omega) (by omega), vz_getD]
    ring

theorem redF_diff_span {Bl : List (List ℤ × Data.V3)} {L : ℕ} (h1 : Bl.length = L) {x : List ℤ}
    (hx : x.length = L) (hr : ∀ c < L, (rowl Bl c).length = L) :
    ∀ (j : ℕ), j ≤ L → InSpan (BlR Bl) L (vsub x (redF Bl j x)) := by
  intro j
  induction j with
  | zero =>
      intro _
      have hxx : vsub x x = vzero L := by
        apply ext_getD_of_length (L := L)
        · rw [vsub_length, hx, Nat.min_self]
        · rw [vzero_length]
        · intro q hq
          rw [vsub_getD (by omega) (by omega), vzero_getD]
          ring
      rw [redF, List.range_zero, List.foldl_nil, hxx]
      exact ⟨[], fun q _ => by rw [vzero_getD, linC_nil_right]⟩
  | succ j ih =>
      intro hj
      have hz' : (redF Bl j x).length = L := redF_length hx hr j (by omega)
      rw [redF_succ, vsub_step_eq hx hz' (hr j (by omega))]
      have hsub : (vsub x (redF Bl j x)).length = L := by rw [vsub_length, hx, hz', Nat.min_self]
      have hvz : (vz ((redF Bl j x).getD j 0 / (rowl Bl j).getD j 1) (rowl Bl j)).length = L := by
        rw [vz_length, hr j (by omega)]
      exact InSpan_vadd hsub hvz (ih (by omega))
        (InSpan_vz_row L Bl h1 j (by omega) ((redF Bl j x).getD j 0 / (rowl Bl j).getD j 1))

/-! ## Evaluating a combination on an echelon basis -/

theorem linC_zero_of_rows (rows : List (List ℤ)) (cs : List ℤ) (q : ℕ)
    (h : ∀ j < rows.length, (rows.getD j []).getD q 0 = 0) : linC rows cs q = 0 := by
  induction rows generalizing cs with
  | nil => simp [linC]
  | cons r rs ih =>
      cases cs with
      | nil => simp [linC]
      | cons c cs =>
          have h0 : r.getD q 0 = 0 := h 0 (by simp)
          rw [linC_cons, h0, mul_zero, zero_add, ih cs]
          intro j hj
          simpa using h (j + 1) (by simpa using hj)

/-- Single-term extraction: if the coefficients below `c` all vanish and every row above `c`
vanishes at coordinate `q`, then the combination is the single `c`-th term. -/
theorem linC_single_term (rows : List (List ℤ)) (cs : List ℤ) (c q : ℕ)
    (ha : ∀ j < c, cs.getD j 0 = 0)
    (hb : ∀ j, c < j → j < rows.length → (rows.getD j []).getD q 0 = 0) :
    linC rows cs q = cs.getD c 0 * (rows.getD c []).getD q 0 := by
  induction rows generalizing cs c q with
  | nil => simp [linC]
  | cons r rs ih =>
      cases cs with
      | nil => rw [linC_nil_right]; simp
      | cons c0 cs =>
          rw [linC_cons]
          cases c with
          | zero =>
              have hz0 : linC rs cs q = 0 := by
                apply linC_zero_of_rows
                intro j hj
                exact hb (j + 1) (by omega) (by simpa using hj)
              rw [hz0, List.getD_cons_zero, List.getD_cons_zero]
              ring
          | succ k =>
              have hc0 : c0 = 0 := ha 0 (by omega)
              rw [hc0, zero_mul, zero_add, List.getD_cons_succ, List.getD_cons_succ]
              exact ih cs k q
                (fun j hj => by
                  have h := ha (j + 1) (by omega)
                  simpa [List.getD_cons_succ] using h)
                (fun j hkj hj => by
                  have h := hb (j + 1) (by omega) (by simpa using hj)
                  simpa [List.getD_cons_succ] using h)

/-- Pivot evaluation: for an upper-echelon row list, a combination with vanishing coefficients
below `c` has `c`-th coordinate `cs c · row_c c`. -/
theorem linC_echelon (rows : List (List ℤ)) (cs : List ℤ) (c : ℕ) (_hc : c < rows.length)
    (_hcs : cs.length = rows.length)
    (hech : ∀ j < rows.length, ∀ q < j, (rows.getD j []).getD q 0 = 0)
    (hz : ∀ j < c, cs.getD j 0 = 0) :
    linC rows cs c = cs.getD c 0 * (rows.getD c []).getD c 0 :=
  linC_single_term rows cs c c hz (fun j hcj hj => hech j hj c (by omega))

/-! ## Uniqueness: a span element with all coordinates strictly bounded by the pivots is `0` -/

theorem span_bounded_eq_zero {L : ℕ} {Bl : List (List ℤ × Data.V3)} (h1 : Bl.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0)
    (hp : ∀ c < L, 0 < (rowl Bl c).getD c 1) {w : List ℤ} (hw : w.length = L)
    (hspan : InSpan (BlR Bl) L w)
    (hb : ∀ q < L, -(rowl Bl q).getD q 1 < w.getD q 0 ∧ w.getD q 0 < (rowl Bl q).getD q 1) :
    w = vzero L := by
  obtain ⟨cs, hcs⟩ := hspan
  have hBL : (BlR Bl).length = L := by rw [BlR_length, h1]
  have hpad : ∀ q, linC (BlR Bl) (padL L cs) q = linC (BlR Bl) cs q := fun q => by
    rw [← hBL]; exact linC_padL (BlR Bl) cs q
  have hcs'len : (padL L cs).length = (BlR Bl).length := by rw [padL_length, hBL]
  have hcoef : ∀ c < L, (padL L cs).getD c 0 = 0 := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro hcL
      have hz' : ∀ j < c, (padL L cs).getD j 0 = 0 := fun j hj => ih j hj (by omega)
      have hwq : w.getD c 0 = (padL L cs).getD c 0 * (rowl Bl c).getD c 1 := by
        rw [hcs c hcL, ← hpad c,
          linC_echelon (BlR Bl) (padL L cs) c (by rw [hBL]; exact hcL) hcs'len
            (fun j hj q hq => by
              rw [rowl_eq_BlR]
              exact hz j (by rw [hBL] at hj; exact hj) q hq) hz',
          rowl_eq_BlR, rowl_piv_eq (hr c hcL) hcL]
      have hb1 := (hb c hcL).1
      have hb2 := (hb c hcL).2
      rw [hwq] at hb1 hb2
      have hpv := hp c hcL
      have hlt : (padL L cs).getD c 0 < 1 := by
        have h' : (padL L cs).getD c 0 * (rowl Bl c).getD c 1
            < 1 * (rowl Bl c).getD c 1 := by simpa using hb2
        exact (Int.mul_lt_mul_right hpv).mp h'
      have hgt : -1 < (padL L cs).getD c 0 := by
        have h' : (-1 : ℤ) * (rowl Bl c).getD c 1
            < (padL L cs).getD c 0 * (rowl Bl c).getD c 1 := by simpa using hb1
        exact (Int.mul_lt_mul_right hpv).mp h'
      omega
  have hzero : ∀ q < L, w.getD q 0 = 0 := by
    intro q hq
    rw [hcs q hq, ← hpad q]
    apply linC_zero_of_coeffs
    intro j hj
    rw [hBL] at hj
    exact hcoef j hj
  exact eq_vzero_of_getD w L hw hzero

/-! ## The quotient-map properties -/

theorem redF_L_idem {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x : List ℤ} (hx : x.length = L)
    (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0)
    (hp : ∀ c < L, 0 < (rowl Bl c).getD c 1) : redF Bl L (redF Bl L x) = redF Bl L x := by
  have hlen : (redF Bl L x).length = L := redF_length hx hr L le_rfl
  exact redF_noop hlen hr (fun q hq => redF_L_bounds hx hr hz hp hq)

theorem redF_L_inv {Bl : List (List ℤ × Data.V3)} {L : ℕ} {x y : List ℤ} (h1 : Bl.length = L)
    (hx : x.length = L) (hy : y.length = L) (hr : ∀ c < L, (rowl Bl c).length = L)
    (hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0)
    (hp : ∀ c < L, 0 < (rowl Bl c).getD c 1)
    (hxy : InSpan (BlR Bl) L (vsub x y)) : redF Bl L x = redF Bl L y := by
  set u := redF Bl L x with hu
  set v := redF Bl L y with hv
  have hux : u.length = L := redF_length hx hr L le_rfl
  have hvy : v.length = L := redF_length hy hr L le_rfl
  have hxv_len : (vsub x y).length = L := by rw [vsub_length, hx, hy, Nat.min_self]
  have hux_len : (vsub x u).length = L := by rw [vsub_length, hx, hux, Nat.min_self]
  have hyv_len : (vsub y v).length = L := by rw [vsub_length, hy, hvy, Nat.min_self]
  have h1' : InSpan (BlR Bl) L (vsub x u) := by
    rw [hu]; exact redF_diff_span h1 hx hr L le_rfl
  have h2' : InSpan (BlR Bl) L (vsub y v) := by
    rw [hv]; exact redF_diff_span h1 hy hr L le_rfl
  have hxv : InSpan (BlR Bl) L (vsub x v) := by
    have heq : vsub x v = vadd (vsub x y) (vsub y v) := by
      apply ext_getD_of_length (L := L)
      · rw [vsub_length, hx, hvy, Nat.min_self]
      · rw [vadd_length, hxv_len, hyv_len, Nat.min_self]
      · intro q hq
        rw [vsub_getD (by omega) (by omega), vadd_getD (by omega) (by omega),
          vsub_getD (by omega) (by omega), vsub_getD (by omega) (by omega)]
        ring
    rw [heq]
    exact InSpan_vadd hxv_len hyv_len hxy h2'
  have huv : InSpan (BlR Bl) L (vsub u v) := by
    have hxvu_len : (vsub x v).length = L := by rw [vsub_length, hx, hvy, Nat.min_self]
    have heq : vsub u v = vsub (vsub x v) (vsub x u) := by
      apply ext_getD_of_length (L := L)
      · rw [vsub_length, hux, hvy, Nat.min_self]
      · rw [vsub_length, hxvu_len, hux_len, Nat.min_self]
      · intro q hq
        rw [vsub_getD (by omega) (by omega), vsub_getD (by omega) (by omega),
          vsub_getD (by omega) (by omega), vsub_getD (by omega) (by omega)]
        ring
    rw [heq]
    exact InSpan_vsub hxvu_len hux_len hxv h1'
  have hb : ∀ q < L, -(rowl Bl q).getD q 1 < (vsub u v).getD q 0 ∧
      (vsub u v).getD q 0 < (rowl Bl q).getD q 1 := by
    intro q hq
    have hbu : 0 ≤ u.getD q 0 ∧ u.getD q 0 < (rowl Bl q).getD q 1 := by
      rw [hu]; exact redF_L_bounds hx hr hz hp hq
    have hbv : 0 ≤ v.getD q 0 ∧ v.getD q 0 < (rowl Bl q).getD q 1 := by
      rw [hv]; exact redF_L_bounds hy hr hz hp hq
    rw [vsub_getD (by omega) (by omega)]
    constructor <;> omega
  have hzero : vsub u v = vzero L :=
    span_bounded_eq_zero h1 hr hz hp (by rw [vsub_length, hux, hvy, Nat.min_self]) huv hb
  apply ext_getD_of_length hux hvy
  intro q hq
  have hcongr := congrArg (fun l => l.getD q 0) hzero
  rw [vsub_getD (by omega) (by omega), vzero_getD] at hcongr
  omega

end RB

/-! ## The requested statement is false -/

namespace RB

open Work.SG.RC

/-- The requested closure of `InSpan` under `vadd` is FALSE: `vadd` truncates to the shorter list,
so a zero-padded sum can leave the span. -/
theorem not_InSpan_vadd :
    ¬ (∀ (L : ℕ) (rows : List (List ℤ)) (u v : List ℤ),
        InSpan rows L u → InSpan rows L v → InSpan rows L (vadd u v)) := by
  intro h
  have hu : InSpan [[2, 1]] 2 [0] := ⟨[], by decide⟩
  have hv : InSpan [[2, 1]] 2 [2, 1] := ⟨[1], by decide⟩
  have hw := h 2 [[2, 1]] [0] [2, 1] hu hv
  obtain ⟨cs, hcs⟩ := hw
  have h0 := hcs 0 (by norm_num)
  have h1 := hcs 1 (by norm_num)
  simp [linC, vadd] at h0 h1
  omega

/-- Likewise the requested closure of `InSpan` under `vsub` is FALSE. -/
theorem not_InSpan_vsub :
    ¬ (∀ (L : ℕ) (rows : List (List ℤ)) (u v : List ℤ),
        InSpan rows L u → InSpan rows L v → InSpan rows L (vsub u v)) := by
  intro h
  have hu : InSpan [[2, 1]] 2 [2, 1] := ⟨[1], by decide⟩
  have hv : InSpan [[2, 1]] 2 [0] := ⟨[], by decide⟩
  have hw := h 2 [[2, 1]] [2, 1] [0] hu hv
  obtain ⟨cs, hcs⟩ := hw
  have h0 := hcs 0 (by norm_num)
  have h1 := hcs 1 (by norm_num)
  simp [linC, vsub] at h0 h1
  omega

end RB

/-! ## The corrected statement -/

open Work.SG.RC
open RB

/-- **The requested statement is false.**  This is the statement of `Work.SG.RepCoh_reduceBl`
*verbatim* (the `sorry` removed), and it is refuted by the counterexample to its second conjunct
(`Work.SG.RB.not_InSpan_vadd`): with `rows = [[2,1]]`, `L = 2`, `u = [0]`, `v = [2,1]` both
`u` and `v` lie in the span but `vadd [0] [2,1] = [2]` does not. -/
theorem RepCoh_reduceBl_requested_is_false :
    ¬ ((∀ (L : ℕ) (Bl : List (List ℤ × Data.V3)),
        Bl.length = L →
        (∀ c, c < L → ((BlR Bl).getD c []).length = L) →
        (∀ c, c < L → EchAt c ((BlR Bl).getD c [])) →
        ((∀ x : List ℤ, x.length = L →
            Data.reduceBl Bl (Data.reduceBl Bl x) = Data.reduceBl Bl x) ∧
         (∀ x : List ℤ, x.length = L →
            InSpan (BlR Bl) L (vsub x (Data.reduceBl Bl x))) ∧
         (∀ x : List ℤ, x.length = L → ∀ c, c < L →
            0 ≤ (Data.reduceBl Bl x).getD c 0 ∧
            (Data.reduceBl Bl x).getD c 0 < ((BlR Bl).getD c []).getD c 0) ∧
         (∀ x y : List ℤ, x.length = L → y.length = L →
            InSpan (BlR Bl) L (vsub x y) → Data.reduceBl Bl x = Data.reduceBl Bl y) ∧
         (∀ x : List ℤ, x.length = L → Data.reduceBl Bl x = vzero L →
            InSpan (BlR Bl) L x))) ∧
    (∀ (L : ℕ) (rows : List (List ℤ)) (u v : List ℤ),
        InSpan rows L u → InSpan rows L v → InSpan rows L (vadd u v)) ∧
    (∀ (L : ℕ) (rows : List (List ℤ)) (k : ℤ) (u : List ℤ),
        InSpan rows L u → InSpan rows L (vz k u)) ∧
    (∀ (L : ℕ) (rows : List (List ℤ)) (u v : List ℤ),
        InSpan rows L u → InSpan rows L v → InSpan rows L (vsub u v))) :=
  fun h => RB.not_InSpan_vadd h.2.1

/-- **Corrected version** of `Work.SG.RepCoh_reduceBl`: the same statement with the missing length
hypotheses `u.length = L`, `v.length = L` added to the two closure conjuncts (without them the
statement is false, see `Work.SG.RB.not_InSpan_vadd` and `Work.SG.RB.not_InSpan_vsub`). -/
theorem RepCoh_reduceBl_corrected :
    (∀ (L : ℕ) (Bl : List (List ℤ × Data.V3)),
        Bl.length = L →
        (∀ c, c < L → ((BlR Bl).getD c []).length = L) →
        (∀ c, c < L → EchAt c ((BlR Bl).getD c [])) →
        ((∀ x : List ℤ, x.length = L →
            Data.reduceBl Bl (Data.reduceBl Bl x) = Data.reduceBl Bl x) ∧
         (∀ x : List ℤ, x.length = L →
            InSpan (BlR Bl) L (vsub x (Data.reduceBl Bl x))) ∧
         (∀ x : List ℤ, x.length = L → ∀ c, c < L →
            0 ≤ (Data.reduceBl Bl x).getD c 0 ∧
            (Data.reduceBl Bl x).getD c 0 < ((BlR Bl).getD c []).getD c 0) ∧
         (∀ x y : List ℤ, x.length = L → y.length = L →
            InSpan (BlR Bl) L (vsub x y) → Data.reduceBl Bl x = Data.reduceBl Bl y) ∧
         (∀ x : List ℤ, x.length = L → Data.reduceBl Bl x = vzero L →
            InSpan (BlR Bl) L x))) ∧
    (∀ (L : ℕ) (rows : List (List ℤ)) (u v : List ℤ),
        u.length = L → v.length = L →
        InSpan rows L u → InSpan rows L v → InSpan rows L (vadd u v)) ∧
    (∀ (L : ℕ) (rows : List (List ℤ)) (k : ℤ) (u : List ℤ),
        InSpan rows L u → InSpan rows L (vz k u)) ∧
    (∀ (L : ℕ) (rows : List (List ℤ)) (u v : List ℤ),
        u.length = L → v.length = L →
        InSpan rows L u → InSpan rows L v → InSpan rows L (vsub u v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L Bl h1 h2 h3
    have hr : ∀ c < L, (rowl Bl c).length = L := fun c hc => by
      have h := h2 c hc; rwa [rowl_eq_BlR] at h
    have hz : ∀ c < L, ∀ q < c, (rowl Bl c).getD q 0 = 0 := fun c hc q hq => by
      have h := (h3 c hc).1 q hq; rwa [rowl_eq_BlR] at h
    have hp : ∀ c < L, 0 < (rowl Bl c).getD c 1 := fun c hc => by
      have h := (h3 c hc).2
      rw [rowl_piv_eq (hr c hc) hc, ← rowl_eq_BlR]
      exact h
    have hconv : ∀ x : List ℤ, x.length = L → Data.reduceBl Bl x = redF Bl L x :=
      fun x _ => by rw [reduceBl_eq_redF, h1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hlen : (Data.reduceBl Bl x).length = L := reduceBl_length h1 hx hr
      have hnoop : redF Bl L (Data.reduceBl Bl x) = Data.reduceBl Bl x :=
        redF_noop hlen hr (fun q hq => reduceBl_bounds h1 hx hr hz hp hq)
      rw [hconv (Data.reduceBl Bl x) hlen, hnoop]
    · intro x hx
      rw [hconv x hx]
      exact redF_diff_span h1 hx hr L le_rfl
    · intro x hx c hc
      have hb := reduceBl_bounds h1 hx hr hz hp hc
      refine ⟨hb.1, ?_⟩
      rw [rowl_piv_eq (hr c hc) hc, ← rowl_eq_BlR] at hb
      exact hb.2
    · intro x y hx hy hxy
      rw [hconv x hx, hconv y hy]
      exact redF_L_inv h1 hx hy hr hz hp hxy
    · intro x hx hker
      have hspan := redF_diff_span h1 hx hr L le_rfl
      rw [← hconv x hx, hker] at hspan
      rwa [vsub_vzero x L hx] at hspan
  · intro L rows u v hu hv hu' hv'
    exact InSpan_vadd hu hv hu' hv'
  · intro L rows k u hu'
    exact InSpan_vz hu'
  · intro L rows u v hu hv hu' hv'
    exact InSpan_vsub hu hv hu' hv'

end Work.SG
