import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.KernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Max-norm shells of the integer lattice `ℤ³`

Vocabulary and elementary counting facts used by
`Work.BoseRowsFS.sum_exp_div_norm_sq_le`:

* `maxNat j` — the max-norm `max_i |j_i|` of an integer vector, as a natural number;
* `boxZ k` — the `k`-box `{j : ℤ³ | ∀ i, |j_i| ≤ k}`;
* membership/cardinality lemmas for `boxZ`, and `(maxNat j : ℝ) ≤ ‖vecZ j‖`.

The `k`-th shell `boxZ k \ boxZ (k-1)` is the set of vectors of max-norm exactly `k`
(for `k ≥ 1`); its cardinality is `(2k+1)³ - (2k-1)³ = 24k² + 2`, which is `O(k²)`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false

/-- The max-norm `max_i |j_i|` of an integer vector `j : ℤ³`, as a natural number. -/
def maxNat (j : Fin 3 → ℤ) : ℕ :=
  (Finset.univ.image (fun i : Fin 3 => (j i).natAbs)).max' (by simp)

/-- The `k`-box of integer vectors all of whose coordinates are bounded by `k`. -/
def boxZ (k : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))

/-- `natAbs` is bounded by `k` exactly when the integer lies in `[-k, k]`. -/
lemma natAbs_le_iff_int {z : ℤ} {k : ℕ} : z.natAbs ≤ k ↔ -(k : ℤ) ≤ z ∧ z ≤ (k : ℤ) := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]

/-- Membership in the `k`-box. -/
lemma mem_boxZ {k : ℕ} {j : Fin 3 → ℤ} : j ∈ boxZ k ↔ ∀ i, (j i).natAbs ≤ k := by
  rw [boxZ, Fintype.mem_piFinset]
  constructor
  · intro h i
    exact natAbs_le_iff_int.mpr (Finset.mem_Icc.mp (h i))
  · intro h i
    rw [Finset.mem_Icc]
    exact natAbs_le_iff_int.mp (h i)

/-- Each coordinate of `j` is bounded by the max-norm. -/
lemma le_maxNat (j : Fin 3 → ℤ) (i : Fin 3) : (j i).natAbs ≤ maxNat j := by
  rw [maxNat]
  exact Finset.le_max' (Finset.univ.image (fun i : Fin 3 => (j i).natAbs)) ((j i).natAbs)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The max-norm is bounded by `k` exactly when every coordinate is. -/
lemma maxNat_le_iff {k : ℕ} {j : Fin 3 → ℤ} : maxNat j ≤ k ↔ ∀ i, (j i).natAbs ≤ k := by
  rw [maxNat]
  constructor
  · intro h i
    exact (Finset.le_max' (Finset.univ.image (fun i : Fin 3 => (j i).natAbs)) ((j i).natAbs)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).trans h
  · intro h
    exact Finset.max'_le _ _ _ (fun y hy => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact h i)

/-- The max-norm of a nonzero integer vector is at least `1`. -/
lemma maxNat_pos {j : Fin 3 → ℤ} (hj : j ≠ 0) : 1 ≤ maxNat j := by
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ 0 := by
    by_contra h; push Not at h; exact hj (funext h)
  exact (Int.natAbs_pos.mpr hi).trans_le (le_maxNat j i)

/-- `j` lies in the `k`-box exactly when its max-norm is at most `k`. -/
lemma mem_boxZ_iff_maxNat_le {k : ℕ} {j : Fin 3 → ℤ} : j ∈ boxZ k ↔ maxNat j ≤ k := by
  rw [mem_boxZ, maxNat_le_iff]

/-- The `k`-box has `(2k+1)³` elements. -/
lemma card_boxZ (k : ℕ) : (boxZ k).card = (2 * k + 1) ^ 3 := by
  rw [boxZ, Fintype.card_piFinset]
  have h : ∀ i : Fin 3, (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
    intro i
    rw [Int.card_Icc]
    have : (k : ℤ) + 1 - (-(k : ℤ)) = (2 * k + 1 : ℕ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The `(k-1)`-box is contained in the `k`-box. -/
lemma boxZ_subset (k : ℕ) : boxZ (k - 1) ⊆ boxZ k := by
  intro j hj
  rw [mem_boxZ_iff_maxNat_le] at hj ⊢
  omega

/-- The max-norm of `j` is at most the Euclidean norm of `vecZ j`. -/
lemma norm_vecZ_ge_maxNat (j : Fin 3 → ℤ) : (maxNat j : ℝ) ≤ ‖vecZ j‖ := by
  have hmem : maxNat j ∈ Finset.univ.image (fun i : Fin 3 => (j i).natAbs) := by
    rw [maxNat]; exact Finset.max'_mem _ _
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  have h1 : (maxNat j : ℝ) = |(((j i : ℤ)) : ℝ)| := by
    rw [← hi]
    have h : ((((j i).natAbs : ℕ) : ℤ) : ℝ) = ((|(j i)| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
    simpa [Int.cast_abs] using h
  have h2 : ((((j i : ℤ)) : ℝ)) ^ 2 ≤ ‖vecZ j‖ ^ 2 := by
    rw [norm_vecZ_sq]
    exact Finset.single_le_sum (f := fun i' : Fin 3 => (((j i' : ℤ)) : ℝ) ^ 2)
      (fun i' _ => sq_nonneg _) (Finset.mem_univ i)
  calc (maxNat j : ℝ) = |(((j i : ℤ)) : ℝ)| := h1
    _ = Real.sqrt (((((j i : ℤ)) : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖vecZ j‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖vecZ j‖ := Real.sqrt_sq (norm_nonneg _)

end Work.BoseRowsFS
