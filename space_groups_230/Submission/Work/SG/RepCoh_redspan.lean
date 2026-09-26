import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RedSpanAux

/-!
# `x - Data.reduceBl Bl x` lies in the span of the rows of `Bl`

`Data.reduceBl Bl x` runs, for `c = 0, 1, …, Bl.length - 1`, the elimination step
`y ↦ y - ⌊y_c / (row_c)_c⌋ • row_c`, with rows read off `Bl`.  Every step therefore changes `y`
by an integral multiple of a row, so the total change `x - reduceBl Bl x` is an integral
combination of the rows: it lies in `Work.SG.RC.InSpan (BlR Bl) L`, as long as the rows and `x`
all have length `L` (so that no `List.zipWith` truncation loses information).

The proof exhibits the coefficients (`qsL`) and verifies the coordinate identity by induction on
the number of steps (`redN_spec`).
-/

namespace Work.SG

open Work.SG.RC (BlR linC vsub BlR_getD BlR_length)

namespace RS

/-- `linC` of the zero coefficient vector. -/
theorem linC_nil (rows : List (List ℤ)) (q : ℕ) : linC rows ([] : List ℤ) q = 0 := by
  simp [linC]

/-- Splitting off the first coefficient and the first row. -/
theorem linC_cons_aux (r : List ℤ) (rs : List (List ℤ)) (v : ℤ) (cs : List ℤ) (q : ℕ) :
    linC (r :: rs) (v :: cs) q = v * r.getD q 0 + linC rs cs q := by
  show ((List.range (rs.length + 1)).map
      (fun j => (v :: cs).getD j 0 * ((r :: rs).getD j []).getD q 0)).sum
    = v * r.getD q 0 + ((List.range rs.length).map
      (fun j => cs.getD j 0 * (rs.getD j []).getD q 0)).sum
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, List.getD_cons_zero,
    List.getD_cons_zero]
  apply congrArg (fun t => v * r.getD q 0 + t)
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp [Function.comp_apply]

/-- One step of the coefficient list is the appended quotient. -/
theorem qsL_succ (Bl : List (List ℤ × Data.V3)) (x : List ℤ) (n : ℕ) :
    qsL Bl x (n + 1) = qsL Bl x n ++ [quot Bl (redN Bl n x) n] := by
  simp only [qsL, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem qsL_length (Bl : List (List ℤ × Data.V3)) (x : List ℤ) (n : ℕ) :
    (qsL Bl x n).length = n := by
  simp [qsL]

/-- Coordinate form of one elimination step. -/
theorem redS_getD (Bl : List (List ℤ × Data.V3)) (y : List ℤ) (c q : ℕ)
    (hy : q < y.length) (hrow : q < (rowc Bl c).length) :
    (redS Bl y c).getD q 0 = y.getD q 0 - quot Bl y c * (rowc Bl c).getD q 0 := by
  have hz : q < (redS Bl y c).length := by
    simp only [redS, List.length_zipWith]; omega
  simp only [redS] at hz ⊢
  rw [List.getD_eq_getElem _ _ hz, List.getD_eq_getElem _ _ hy, List.getD_eq_getElem _ _ hrow,
    List.getElem_zipWith]

/-- The reduction of a vector of length `L` by rows of length `L` keeps length `L`. -/
theorem redN_length (Bl : List (List ℤ × Data.V3)) (L : ℕ)
    (hrow : ∀ c, c < L → (rowc Bl c).length = L) (x : List ℤ) (hx : x.length = L) :
    ∀ n ≤ L, (redN Bl n x).length = L := by
  intro n
  induction n with
  | zero => intro _; exact hx
  | succ n ih =>
      intro hn
      have hnL : n < L := by omega
      show (redS Bl (redN Bl n x) n).length = L
      rw [redS, List.length_zipWith, ih (by omega), hrow n hnL, Nat.min_self]

/-- Appending a coefficient adds its row contribution. -/
theorem linC_append_aux (rows : List (List ℤ)) (cs : List ℤ) (v : ℤ) (q : ℕ)
    (h : cs.length ≤ rows.length) :
    linC rows (cs ++ [v]) q = linC rows cs q + v * (rows.getD cs.length []).getD q 0 := by
  induction cs generalizing rows with
  | nil =>
      cases rows with
      | nil => simp [linC]
      | cons r rs =>
          simp only [List.nil_append, linC_cons_aux r rs v, linC_nil, List.length_nil,
            List.getD_cons_zero]
          ring
  | cons c cs' ih =>
      cases rows with
      | nil => simp at h
      | cons r rs =>
          have h' : cs'.length ≤ rs.length := by simp only [List.length_cons] at h; omega
          rw [List.cons_append, List.length_cons, List.getD_cons_succ]
          simp only [linC_cons_aux r rs c]
          rw [ih rs h']
          ring

/-- The telescoping coordinate identity for the first `n` elimination steps. -/
theorem redN_spec (Bl : List (List ℤ × Data.V3)) (L : ℕ) (hL : Bl.length = L)
    (hrow : ∀ c, c < L → (rowc Bl c).length = L) (x : List ℤ) (hx : x.length = L) :
    ∀ n, n ≤ L → ∀ q, q < L →
      (redN Bl n x).getD q 0 = x.getD q 0 - linC (BlR Bl) (qsL Bl x n) q := by
  intro n
  induction n with
  | zero =>
      intro _ q _
      simp [redN, qsL, linC]
  | succ n ih =>
      intro hn q hq
      have hnL : n < L := by omega
      have hnle : n ≤ L := by omega
      have hred_len : (redN Bl n x).length = L := redN_length Bl L hrow x hx n hnle
      have hrow_n : (rowc Bl n).length = L := hrow n hnL
      show (redS Bl (redN Bl n x) n).getD q 0 = x.getD q 0 - linC (BlR Bl) (qsL Bl x (n + 1)) q
      rw [redS_getD Bl (redN Bl n x) n q (by omega) (by omega), ih hnle q hq, qsL_succ]
      have hlen : (qsL Bl x n).length ≤ (BlR Bl).length := by
        rw [qsL_length, BlR_length, hL]; exact hnle
      rw [linC_append_aux (BlR Bl) (qsL Bl x n) (quot Bl (redN Bl n x) n) q hlen,
        qsL_length, ← rowc_eq_BlR Bl n]
      ring

end RS

theorem RepCoh_redspan :
    ∀ (L : ℕ) (Bl : List (List ℤ × Data.V3)),
      Bl.length = L →
      (∀ c, c < L → ((Work.SG.RC.BlR Bl).getD c []).length = L) →
      ∀ x : List ℤ, x.length = L →
        Work.SG.RC.InSpan (Work.SG.RC.BlR Bl) L (Work.SG.RC.vsub x (Data.reduceBl Bl x)) := by
  intro L Bl hL hBlR x hx
  have hrow : ∀ c, c < L → (RS.rowc Bl c).length = L := by
    intro c hc
    rw [RS.rowc_eq_BlR]; exact hBlR c hc
  refine ⟨RS.qsL Bl x L, ?_⟩
  intro q hq
  have hxq : q < x.length := by rw [hx]; exact hq
  have hred_len : (Data.reduceBl Bl x).length = L := by
    rw [RS.reduceBl_eq_redN]
    exact RS.redN_length Bl L hrow x hx Bl.length (by omega)
  have hredq : q < (Data.reduceBl Bl x).length := by rw [hred_len]; exact hq
  rw [RS.vsub_getD hxq hredq, RS.reduceBl_eq_redN, hL,
    RS.redN_spec Bl L hL hrow x hx L le_rfl q hq]
  ring

end Work.SG
