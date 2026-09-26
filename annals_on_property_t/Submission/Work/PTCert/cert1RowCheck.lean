import Mathlib
import Submission.Work.PTCert.cert1Aux
import Submission.Work.PTCert.Data.C1.RWAll

/-!
# Kernel row checks of the `C1` certificate, rep by rep

The kernel checks `Submission.PTCert.C1K.rw_ok{r}_{j}` verify the row-table check `rowCheck` on the
four contiguous chunks `[0,153)`, `[153,306)`, `[306,459)`, `[459,611)` of the `611`
`N`-representatives, for each of the `18` rows.  This file turns those chunk checks into the
singleton checks requested by `RowTabSound`:

`∀ r < 18, ∀ t < 611, rowCheck valT (olTs.getD r ..) (rowTs.getD r ..) r [t] = true`.

The proof is a pure bookkeeping argument: `rowCheck` unfolds to `allL ts (rowCheckBody ..)`, a chunk
check is `allL (List.range' lo n) P = true`, and the four ranges cover `[0, 611)`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K

noncomputable section

/-- The single-rep body of the kernel `rowCheck`: the Walsh–Hadamard transform of the `32` row
values equals the packed row `t`. -/
def rowCheckBody (valT' olT' rowT' : NT) (r : ℕ) : ℕ → Bool :=
  fun t =>
    let o := olT'.get t
    let vs := (List.range 32).map (fun sc => sv (p8 valT' (2048 * r + ((o >>> (11 * sc)) &&& 2047))))
    wht 5 vs == unpack32 (rowT'.get t)

/-- `rowCheck` is `allL` of `rowCheckBody`. -/
lemma rowCheck_eq_allL (valT' olT' rowT' : NT) (r : ℕ) (ts : List ℕ) :
    rowCheck valT' olT' rowT' r ts = allL ts (rowCheckBody valT' olT' rowT' r) := rfl

/-- `allL` on a singleton list is the predicate itself. -/
lemma allL_singleton (p : ℕ → Bool) (t : ℕ) : allL [t] p = p t := by
  simp [allL]

/-- The singleton `rowCheck` is the body at `t`. -/
lemma rowCheck_singleton (valT' olT' rowT' : NT) (r t : ℕ) :
    rowCheck valT' olT' rowT' r [t] = rowCheckBody valT' olT' rowT' r t := by
  rw [rowCheck_eq_allL, allL_singleton]

/-- **Combining the four chunk checks.**  If the predicate `P` holds on the four contiguous chunks
`[0,153)`, `[153,306)`, `[306,459)`, `[459,611)`, then it holds on every `t < 611`. -/
lemma rowCheckBody_of_chunks (P : ℕ → Bool)
    (h0 : allL (List.range' 0 153) P = true)
    (h1 : allL (List.range' 153 153) P = true)
    (h2 : allL (List.range' 306 153) P = true)
    (h3 : allL (List.range' 459 152) P = true) :
    ∀ t < 611, P t = true := by
  intro t ht
  rcases Nat.lt_or_ge t 153 with h | h
  · exact allL_iff.mp h0 t (List.mem_range'.mpr ⟨t, h, by omega⟩)
  rcases Nat.lt_or_ge t 306 with h' | h'
  · exact allL_iff.mp h1 t (List.mem_range'.mpr ⟨t - 153, by omega, by omega⟩)
  rcases Nat.lt_or_ge t 459 with h'' | h''
  · exact allL_iff.mp h2 t (List.mem_range'.mpr ⟨t - 306, by omega, by omega⟩)
  · exact allL_iff.mp h3 t (List.mem_range'.mpr ⟨t - 459, by omega, by omega⟩)

theorem cert1RowCheck : ∀ r < 18, ∀ t < 611,
    Submission.PTCert.rowCheck Submission.PTCert.D1.valT
      (Submission.PTCert.G.olTs.getD r (Submission.PTCert.NT.leaf 0))
      (Submission.PTCert.D1.rowTs.getD r (Submission.PTCert.NT.leaf 0)) r [t] = true := by
  intro r hr t ht
  interval_cases r
  · rw [show olTs.getD 0 (NT.leaf 0) = olT0 from rfl,
        show rowTs.getD 0 (NT.leaf 0) = rowT0 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT0 rowT0 0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok0_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok0_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok0_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok0_3)
      t ht
  · rw [show olTs.getD 1 (NT.leaf 0) = olT1 from rfl,
        show rowTs.getD 1 (NT.leaf 0) = rowT1 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT1 rowT1 1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok1_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok1_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok1_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok1_3)
      t ht
  · rw [show olTs.getD 2 (NT.leaf 0) = olT2 from rfl,
        show rowTs.getD 2 (NT.leaf 0) = rowT2 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT2 rowT2 2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok2_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok2_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok2_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok2_3)
      t ht
  · rw [show olTs.getD 3 (NT.leaf 0) = olT3 from rfl,
        show rowTs.getD 3 (NT.leaf 0) = rowT3 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT3 rowT3 3)
      (by rw [← rowCheck_eq_allL]; exact rw_ok3_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok3_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok3_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok3_3)
      t ht
  · rw [show olTs.getD 4 (NT.leaf 0) = olT4 from rfl,
        show rowTs.getD 4 (NT.leaf 0) = rowT4 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT4 rowT4 4)
      (by rw [← rowCheck_eq_allL]; exact rw_ok4_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok4_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok4_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok4_3)
      t ht
  · rw [show olTs.getD 5 (NT.leaf 0) = olT5 from rfl,
        show rowTs.getD 5 (NT.leaf 0) = rowT5 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT5 rowT5 5)
      (by rw [← rowCheck_eq_allL]; exact rw_ok5_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok5_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok5_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok5_3)
      t ht
  · rw [show olTs.getD 6 (NT.leaf 0) = olT6 from rfl,
        show rowTs.getD 6 (NT.leaf 0) = rowT6 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT6 rowT6 6)
      (by rw [← rowCheck_eq_allL]; exact rw_ok6_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok6_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok6_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok6_3)
      t ht
  · rw [show olTs.getD 7 (NT.leaf 0) = olT7 from rfl,
        show rowTs.getD 7 (NT.leaf 0) = rowT7 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT7 rowT7 7)
      (by rw [← rowCheck_eq_allL]; exact rw_ok7_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok7_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok7_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok7_3)
      t ht
  · rw [show olTs.getD 8 (NT.leaf 0) = olT8 from rfl,
        show rowTs.getD 8 (NT.leaf 0) = rowT8 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT8 rowT8 8)
      (by rw [← rowCheck_eq_allL]; exact rw_ok8_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok8_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok8_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok8_3)
      t ht
  · rw [show olTs.getD 9 (NT.leaf 0) = olT9 from rfl,
        show rowTs.getD 9 (NT.leaf 0) = rowT9 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT9 rowT9 9)
      (by rw [← rowCheck_eq_allL]; exact rw_ok9_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok9_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok9_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok9_3)
      t ht
  · rw [show olTs.getD 10 (NT.leaf 0) = olT10 from rfl,
        show rowTs.getD 10 (NT.leaf 0) = rowT10 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT10 rowT10 10)
      (by rw [← rowCheck_eq_allL]; exact rw_ok10_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok10_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok10_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok10_3)
      t ht
  · rw [show olTs.getD 11 (NT.leaf 0) = olT11 from rfl,
        show rowTs.getD 11 (NT.leaf 0) = rowT11 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT11 rowT11 11)
      (by rw [← rowCheck_eq_allL]; exact rw_ok11_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok11_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok11_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok11_3)
      t ht
  · rw [show olTs.getD 12 (NT.leaf 0) = olT12 from rfl,
        show rowTs.getD 12 (NT.leaf 0) = rowT12 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT12 rowT12 12)
      (by rw [← rowCheck_eq_allL]; exact rw_ok12_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok12_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok12_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok12_3)
      t ht
  · rw [show olTs.getD 13 (NT.leaf 0) = olT13 from rfl,
        show rowTs.getD 13 (NT.leaf 0) = rowT13 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT13 rowT13 13)
      (by rw [← rowCheck_eq_allL]; exact rw_ok13_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok13_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok13_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok13_3)
      t ht
  · rw [show olTs.getD 14 (NT.leaf 0) = olT14 from rfl,
        show rowTs.getD 14 (NT.leaf 0) = rowT14 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT14 rowT14 14)
      (by rw [← rowCheck_eq_allL]; exact rw_ok14_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok14_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok14_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok14_3)
      t ht
  · rw [show olTs.getD 15 (NT.leaf 0) = olT15 from rfl,
        show rowTs.getD 15 (NT.leaf 0) = rowT15 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT15 rowT15 15)
      (by rw [← rowCheck_eq_allL]; exact rw_ok15_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok15_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok15_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok15_3)
      t ht
  · rw [show olTs.getD 16 (NT.leaf 0) = olT16 from rfl,
        show rowTs.getD 16 (NT.leaf 0) = rowT16 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT16 rowT16 16)
      (by rw [← rowCheck_eq_allL]; exact rw_ok16_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok16_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok16_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok16_3)
      t ht
  · rw [show olTs.getD 17 (NT.leaf 0) = olT17 from rfl,
        show rowTs.getD 17 (NT.leaf 0) = rowT17 from rfl,
        rowCheck_singleton]
    exact rowCheckBody_of_chunks (rowCheckBody valT olT17 rowT17 17)
      (by rw [← rowCheck_eq_allL]; exact rw_ok17_0)
      (by rw [← rowCheck_eq_allL]; exact rw_ok17_1)
      (by rw [← rowCheck_eq_allL]; exact rw_ok17_2)
      (by rw [← rowCheck_eq_allL]; exact rw_ok17_3)
      t ht

end

end Work.PTCert
