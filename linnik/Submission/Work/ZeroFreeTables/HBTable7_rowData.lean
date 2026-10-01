/-
# ZeroFreeTables — HBTable7_rowData

The per-row data of Heath-Brown's Table 7: for each of the seventeen rows this file supplies

* the certificate of the **third method** (`CertRow`, from `table7_rows_cert`, read at `ε = 0`
  and upgraded to a positive slack by `CertRow.eps_pos`) together with the threshold `QEA` of the
  row core `HBTable7RowCoreA`;
* the certificate of the **five-term method** (`CertRow85`, from `HBTable7_cert85`, again at
  `ε = 0` and upgraded by `CertRow85.eps_pos`) together with the threshold `QEB` of the row core
  `HBTable7RowCoreB`;
* the `L52Hyp` supplies at the two levels `1/6` and `1/8` at *one* window radius, from
  `L52HypBoth`.

`HBTable7_of_count` (in `HBTable7_of_count.lean`) consumes it as its `hrowdata` hypothesis.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.ZeroFreeTables.table7_rows_cert
import Submission.Work.ZeroFreeTables.HBTable7_cert85
import Submission.Work.ZeroFreeTables.tfF_eq_laplace_pi4
import Submission.Work.ZeroFreeTables.L52HypBoth
import Submission.Work.ZeroFreeTables.L52Hyp_eighth_le4
import Submission.Work.ZeroFreeTables.HBTable7RowCoreAThr
import Submission.Work.ZeroFreeTables.HBTable7RowCoreBThr

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables

/-- The certificates of the third method for the seventeen rows of Table 7, read at `ε = 0`
(the form from which `CertRow.eps_pos` produces the positive slack required by the engine). -/
theorem table7_rows_cert_zero : ∀ p ∈ tableR hbTable7, ∃ (k lam : ℝ), CertRow p.1 p.2 k lam 0 := by
  intro p hp
  simp only [tableR, hbTable7, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨965/1000, 9758/10000, by convert T7Row01 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨962/1000, 9624/10000, by convert T7Row02 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨959/1000, 9497/10000, by convert T7Row03 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨956/1000, 9395/10000, by convert T7Row04 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨953/1000, 9281/10000, by convert T7Row05 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨950/1000, 9187/10000, by convert T7Row06 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨9425/10000, 8942/10000, by convert T7Row07 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨935/1000, 8725/10000, by convert T7Row08 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨9275/10000, 8514/10000, by convert T7Row09 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨92/100, 8331/10000, by convert T7Row10 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨9125/10000, 8164/10000, by convert T7Row11 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨905/1000, 7988/10000, by convert T7Row12 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨8975/10000, 7848/10000, by convert T7Row13 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨89/100, 7677/10000, by convert T7Row14 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨8825/10000, 7516/10000, by convert T7Row15 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨875/1000, 7371/10000, by convert T7Row16 using 1 <;> norm_num⟩
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    exact ⟨8682/10000, 726/1000, by convert T7Row17 using 1 <;> norm_num⟩

/-- **The per-row data of Table 7**: every row of `tableR hbTable7` carries the two certificates,
the `L52Hyp` supplies at `1/6` and `1/8` (with a common window radius) and the two engine
thresholds `QEA`, `QEB`. -/
theorem HBTable7_rowData (p : ℝ × ℝ) (hp : p ∈ tableR hbTable7) : ∃ D : RowData p.1 p.2, True := by
  obtain ⟨k, lamA, hcertA0⟩ := table7_rows_cert_zero p hp
  obtain ⟨lamB, hcertB0⟩ := HBTable7_cert85 p hp
  obtain ⟨εA, hεA, hcertA⟩ := CertRow.eps_pos hcertA0 hcertA0.1 hcertA0.2.1
  obtain ⟨εB, hεB, hcertB⟩ := CertRow85.eps_pos hcertB0 hcertB0.1
  obtain ⟨δA, hδA0, hδA1, qA, hLA⟩ := L52HypBoth εA hεA
  obtain ⟨δB, hδB0, hδB1, qB, hLB⟩ := L52Hyp_eighth_le4 εB hεB
  obtain ⟨qEA, _, hEA⟩ := HBTable7RowCoreAThr p.1 p.2 k lamA εA δA (max qA qB) hcertA0.2.1
    hcertA0.1 hεA hδA0 hδA1 hcertA
    (fun q hq => fun [NeZero q] χ [NeZero χ.conductor] hχ hsq =>
      (hLA q (le_trans (le_max_left _ _) hq) χ hχ).2 (by rw [pow_two]; exact hsq))
    (fun q hq => fun [NeZero q] χ [NeZero χ.conductor] hχ =>
      (hLA q (le_trans (le_max_left _ _) hq) χ hχ).1)
    (fun z => tfF_eq_laplace_pi4 lamA z hcertA0.1)
  obtain ⟨qEB, _, hEB⟩ := HBTable7RowCoreBThr p.1 p.2 lamB εB δB (max qA qB) hcertB0.1 hεB hδB0 hδB1
    hcertB
    (fun q hq => fun [NeZero q] χ [NeZero χ.conductor] hχ hχ4 =>
      hLB q (le_trans (le_max_right _ _) hq) χ hχ hχ4)
    (fun z => tfF_eq_laplace_pi4 lamB z hcertB0.1)
  have hL6A : ∀ q : ℕ, max qA qB ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      [NeZero χ.conductor], χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1 / 6) εA δA :=
    fun q hq => fun [NeZero q] χ [NeZero χ.conductor] hχ =>
      (hLA q (le_trans (le_max_left _ _) hq) χ hχ).1
  have hL8Av : ∀ q : ℕ, max qA qB ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      [NeZero χ.conductor], χ ≠ 1 → χ ^ 2 = 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ (1 / 8) εA δA :=
    fun q hq => fun [NeZero q] χ [NeZero χ.conductor] hχ hsq =>
      (hLA q (le_trans (le_max_left _ _) hq) χ hχ).2 hsq
  have hL8Bv : ∀ q : ℕ, max qA qB ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      [NeZero χ.conductor], χ ≠ 1 → χ ^ 4 = 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ (1 / 8) εB δB :=
    fun q hq => fun [NeZero q] χ [NeZero χ.conductor] hχ hχ4 =>
      hLB q (le_trans (le_max_right _ _) hq) χ hχ hχ4
  exact ⟨{ k := k, lamA := lamA, εA := εA, δA := δA, lamB := lamB, εB := εB, δB := δB, hεA := hεA, hδA0 := hδA0, hδA1 := hδA1, hcertA := hcertA, hεB := hεB, hδB0 := hδB0, hδB1 := hδB1, hcertB := hcertB, Qsup := max qA qB, hL6 := hL6A, hL8A := hL8Av, hL8B := hL8Bv, QEA := qEA, hcoreA := hEA, QEB := qEB, hcoreB := hEB }, trivial⟩

end Work.ZeroFreeTables
