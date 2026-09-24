import Mathlib
import Submission.Work.GM.S3.gen_defs

/-!
# The vocabulary of the cell decomposition `Work.GM.S3.Gen.S3_le_cellSum`

The target `S3_le_cellSum` bounds the truncated triple sum
`Σ_{0 < |m_i| ≤ Klev N δ} ‖Iterm N W (m₁,m₂,m₃)‖` by `C N^δ · cellSum + …`.
The decomposition used by the proof is the family of cells

`csCell N δ i j k = idx1 (Mdy N δ i) × idxM (Mdy N δ j) × idxM (Mdy N δ k)`,

the level `csLev N δ x` of `x > 0` being the unique `i` with `Mdy i < x ≤ 2 Mdy i`
(i.e. `i = ⌊log₂ (Klev/x)⌋ + 1`), and `csGcell` the resulting cell index of a triple.
-/

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators

noncomputable section

/-- The cell of dyadic levels `(i,j,k)`. -/
def csCell (N : ℕ) (δ : ℝ) (i j k : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (idx1 (Mdy N δ i)).product ((idxM (Mdy N δ j)).product (idxM (Mdy N δ k)))

/-- The dyadic level of `x > 0` relative to `Klev N δ`: the unique `i` with
`Mdy N δ i < x ≤ 2 * Mdy N δ i`. -/
def csLev (N : ℕ) (δ : ℝ) (x : ℝ) : ℕ := Nat.floor (Real.logb 2 (Klev N δ / x)) + 1

/-- The cell index of a triple, from the levels of the absolute values of its coordinates. -/
def csGcell (N : ℕ) (δ : ℝ) (u : ℤ × ℤ × ℤ) : ℕ × ℕ × ℕ :=
  (csLev N δ |(u.1 : ℝ)|, (csLev N δ |(u.2.1 : ℝ)|, csLev N δ |(u.2.2 : ℝ)|))

/-- The truncated cube of triples all of whose coordinates are nonzero. -/
def csNzBox (K : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)).product
    (((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)).product
      ((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)))

/-- The part of the truncated cube whose second coordinate has the largest modulus. -/
def csMaxBox (K : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  (csNzBox K).filter (fun u : ℤ × ℤ × ℤ =>
    |(u.1 : ℝ)| ≤ |(u.2.1 : ℝ)| ∧ |(u.2.2 : ℝ)| ≤ |(u.2.1 : ℝ)|)

/-- The left hand side of `S3_le_cellSum`. -/
def csLHS (N : ℕ) (δ : ℝ) (W : Finset ℝ) : ℝ :=
  ∑ m₁ ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋,
    ∑ m₂ ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋,
        if (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0

/-- `Klev N δ > 0` for `N ≥ 1`. -/
theorem csKlev_pos {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) : 0 < Klev N δ := by
  have hM : (0 : ℝ) < Submission.LargeValues.M N := by
    have := Submission.LargeValues.M_ge_one hN
    linarith
  have h1 : (0 : ℝ) < (Submission.LargeValues.M N) ^ (1 + δ) := Real.rpow_pos_of_pos hM _
  simpa only [Klev] using div_pos h1 (by positivity : (0 : ℝ) < (N : ℝ))

/-- `Mdy N δ j > 0` for `N ≥ 1`. -/
theorem csMdy_pos {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (j : ℕ) : 0 < Mdy N δ j := by
  have hK := csKlev_pos hN δ
  have : (0 : ℝ) < 2 ^ j := by positivity
  simpa only [Mdy] using div_pos hK this

/-- Membership in a cell, unfolded. -/
theorem mem_csCell {N : ℕ} {δ : ℝ} {i j k : ℕ} {u : ℤ × ℤ × ℤ} :
    u ∈ csCell N δ i j k ↔
      u.1 ∈ idx1 (Mdy N δ i) ∧ u.2.1 ∈ idxM (Mdy N δ j) ∧ u.2.2 ∈ idxM (Mdy N δ k) := by
  simp [csCell, Finset.mem_product, and_assoc]

/-- Membership in the truncated nonzero cube, unfolded. -/
theorem mem_csNzBox {K : ℝ} {u : ℤ × ℤ × ℤ} :
    u ∈ csNzBox K ↔
      (u.1 ∈ Finset.Icc (-⌊K⌋) ⌊K⌋ ∧ u.1 ≠ 0) ∧
        (u.2.1 ∈ Finset.Icc (-⌊K⌋) ⌊K⌋ ∧ u.2.1 ≠ 0) ∧
          (u.2.2 ∈ Finset.Icc (-⌊K⌋) ⌊K⌋ ∧ u.2.2 ≠ 0) := by
  simp [csNzBox, Finset.mem_product, and_assoc]

end

end Work.GM.S3.Gen
