import Mathlib
import Submission.Work.LT.good_base_defs

/-!
# Kalachev--Panteleev Lemma 1, forward direction

Product expansion of `(CA, CB)` implies agreement testability of the tensor code
`CA ⊗ CB` (in the normalisations of `Defs.lean`).

The proof is the standard one.  Given `w₁` with all rows in `CB` and `w₂` with all
columns in `CA`, the matrix `x = w₁ + w₂` lies in `CA ⊞ CB`, so product expansion
splits it as `x = a + b` with `a` column-wise in `CA`, `b` row-wise in `CB`, and few
non-zero columns/rows.  Then `w := w₁ + b = w₂ + a` is the required tensor codeword:
it differs from `w₁` exactly on the non-zero rows of `b` and from `w₂` exactly on the
non-zero columns of `a`, while `w₁` and `w₂` disagree exactly on the support of `x`.
-/

namespace Work.LT

namespace GB

/-- In `𝔽₂`, `a + b = 0` iff `a = b`. -/
lemma add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- In `𝔽₂`, `a ≠ a + b` iff `b ≠ 0`. -/
lemma ne_add_iff_ne_zero (a b : ZMod 2) : a ≠ a + b ↔ b ≠ 0 := by
  constructor
  · intro h hb; exact h (by rw [hb, add_zero])
  · intro h hh; exact h (add_left_cancel (by rw [add_zero]; exact hh.symm))

/-- In `𝔽₂`, `x + x = 0`. -/
lemma add_self_eq_zero (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 from CharP.cast_eq_zero _ 2, zero_mul]

end GB

/-- Kalachev--Panteleev Lemma 1, forward direction: product-expansion implies agreement testability, in the normalisations of the workspace (`agreementTestable` from `Defs.lean`). -/
theorem gb_agreement_of_prodExp {D : ℕ} (κ : ℝ) (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2))
    (h : GB.ProductExpanding κ CA CB) : agreementTestable κ CA CB := by
  intro w1 w2 hw1 hw2
  have hw1' : w1 ∈ GB.rowCode CB := (GB.mem_rowCode w1).mpr hw1
  have hw2' : w2 ∈ GB.colCode CA := (GB.mem_colCode w2).mpr hw2
  have hx : w1 + w2 ∈ GB.prodSum CA CB := by
    rw [GB.prodSum]
    exact Submodule.mem_sup.mpr ⟨w2, hw2', w1, hw1', by abel⟩
  obtain ⟨a, ha, b, hb, hab, hbound⟩ := h (w1 + w2) hx
  -- `w := w1 + b` agrees with `w2 + a`
  have hweq : w1 + b = w2 + a := by
    funext p
    have hp : w1 p + w2 p = a p + b p := congrFun hab p
    have h2 : (w1 p + b p) + (w2 p + a p) = 0 := by
      have h3 : (w1 p + b p) + (w2 p + a p) = (w1 p + w2 p) + (a p + b p) := by abel
      rw [h3, hp, GB.add_self_eq_zero]
    exact (GB.add_eq_zero_iff_eq (w1 p + b p) (w2 p + a p)).mp h2
  have hrow : GB.IsRowwise CB (w1 + b) := by
    intro i
    rw [show GB.row (w1 + b) i = GB.row w1 i + GB.row b i from by funext j; rfl]
    exact CB.add_mem ((GB.mem_rowCode w1).mp hw1' i) ((GB.mem_rowCode b).mp hb i)
  have hcol : GB.IsColwise CA (w1 + b) := by
    rw [hweq]
    intro j
    rw [show GB.col (w2 + a) j = GB.col w2 j + GB.col a j from by funext i; rfl]
    exact CA.add_mem ((GB.mem_colCode w2).mp hw2' j) ((GB.mem_colCode a).mp ha j)
  refine ⟨w1 + b, (GB.mem_tensorCode (w1 + b)).mpr ⟨hcol, hrow⟩, ?_⟩
  -- the bad rows of `w1` are the non-zero rows of `b`
  have heq1 : Finset.univ.filter (fun i => ∃ j, w1 (i, j) ≠ (w1 + b) (i, j))
      = Finset.univ.filter (fun i => ∃ j, b (i, j) ≠ 0) := by
    apply Finset.filter_congr
    intro i _
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (GB.ne_add_iff_ne_zero _ _).mp hj⟩,
      fun ⟨j, hj⟩ => ⟨j, (GB.ne_add_iff_ne_zero _ _).mpr hj⟩⟩
  have hrows : (Finset.univ.filter (fun i => ∃ j, w1 (i, j) ≠ (w1 + b) (i, j))).card
      = GB.nzRows b := by
    unfold GB.nzRows; rw [heq1]
  -- the bad columns of `w2` are the non-zero columns of `a`
  have heq2 : Finset.univ.filter (fun j => ∃ i, w2 (i, j) ≠ (w1 + b) (i, j))
      = Finset.univ.filter (fun j => ∃ i, a (i, j) ≠ 0) := by
    rw [hweq]
    apply Finset.filter_congr
    intro j _
    exact ⟨fun ⟨i, hi⟩ => ⟨i, (GB.ne_add_iff_ne_zero _ _).mp hi⟩,
      fun ⟨i, hi⟩ => ⟨i, (GB.ne_add_iff_ne_zero _ _).mpr hi⟩⟩
  have hcols : (Finset.univ.filter (fun j => ∃ i, w2 (i, j) ≠ (w1 + b) (i, j))).card
      = GB.nzCols a := by
    unfold GB.nzCols; rw [heq2]
  -- the disagreement of `w1` and `w2` is the weight of `w1 + w2`
  have heq3 : Finset.univ.filter (fun p => w1 p ≠ w2 p)
      = Finset.univ.filter (fun p => (w1 + w2) p ≠ 0) := by
    apply Finset.filter_congr
    intro p _
    constructor
    · intro h h0; exact h ((GB.add_eq_zero_iff_eq (w1 p) (w2 p)).mp h0)
    · intro h hh; exact h ((GB.add_eq_zero_iff_eq (w1 p) (w2 p)).mpr hh)
  have hpair : (Finset.univ.filter (fun p => w1 p ≠ w2 p)).card = GB.wt (w1 + w2) := by
    rw [heq3]; rfl
  have hcomm : (GB.nzRows b : ℝ) + (GB.nzCols a : ℝ)
      = (GB.nzCols a : ℝ) + (GB.nzRows b : ℝ) := by ring
  rw [hrows, hcols, hpair, hcomm]
  exact hbound

end Work.LT
