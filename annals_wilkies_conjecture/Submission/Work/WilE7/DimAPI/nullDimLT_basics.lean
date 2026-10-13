/-
  E7_prop_main: elementary API for the induction measure `NullDimLT` of the design
  (`sources/wilkiesE7main/wilkies_e7_main_design.md`).

  `NullDimLT X K` is "`dim X < K`", with `K = 0` meaning `X = ∅` and `K+1` meaning `NullDimLE X K`.
  The bookkeeping of `CoreLT_succ` needs:

  * monotonicity in `X` and in `K` (`NullDimLT.mono`, `NullDimLT.mono_K`);
  * closure under finite unions (`NullDimLT.union`), used every time a Σ-set is assembled from
    finitely many pieces;
  * the "closure goes through `X ∪ ∂X`" step (`closure_nullDimLE`), since Lebesgue-nullity does not
    pass to closures (`ℚ`);
  * the embedding into `ℝ^{n+1}` of a level-`n` set (`NullDimLT.congr`/`nullDimLT_of_le`).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.nullDimLE_mono_dim

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.MainDesign
open WilkiesDesign WilkiesDesign.E

/-- `NullDimLT · 0` is emptiness, by definition. -/
theorem nullDimLT_zero_iff {N : ℕ} {X : Set (Fin N → ℝ)} : NullDimLT X 0 ↔ X = ∅ := Iff.rfl

/-- The empty set has `NullDimLT · K` for every `K`. -/
@[simp]
theorem nullDimLT_empty {N : ℕ} {K : ℕ} : NullDimLT (∅ : Set (Fin N → ℝ)) K := by
  cases K with
  | zero => rfl
  | succ K => simp [NullDimLT, NullDimLE]

/-- The successor case, unfolded. -/
theorem nullDimLT_succ_iff {N K : ℕ} {X : Set (Fin N → ℝ)} :
    NullDimLT X (K + 1) ↔ NullDimLE X K := Iff.rfl

/-- `NullDimLT` is monotone in the set. -/
theorem NullDimLT.mono {N K : ℕ} {X Y : Set (Fin N → ℝ)} (h : NullDimLT Y K) (hXY : X ⊆ Y) :
    NullDimLT X K := by
  cases K with
  | zero => rw [nullDimLT_zero_iff] at h ⊢; exact Set.eq_empty_of_subset_empty (h ▸ hXY)
  | succ K => exact NullDimLE.mono h hXY

/-- `NullDimLT` is monotone in the index. -/
theorem NullDimLT.mono_K {N K : ℕ} {X : Set (Fin N → ℝ)} (h : NullDimLT X K) :
    NullDimLT X (K + 1) := by
  cases K with
  | zero => rw [nullDimLT_zero_iff] at h; subst h; simp
  | succ K => exact Work.WilE7.DimAPI.nullDimLE_mono_dim h (Nat.le_succ K)

/-- Unions of two sets of dimension `< K` have dimension `< K`. -/
theorem NullDimLT.union {N K : ℕ} {X Y : Set (Fin N → ℝ)} (hX : NullDimLT X K)
    (hY : NullDimLT Y K) : NullDimLT (X ∪ Y) K := by
  cases K with
  | zero =>
      rw [nullDimLT_zero_iff] at hX hY ⊢
      rw [hX, hY]; simp
  | succ K => exact NullDimLE.union hX hY

/-- Finite unions of sets of dimension `< K` have dimension `< K`. -/
theorem NullDimLT.iUnion {N K : ℕ} {ι : Type*} [Finite ι] {f : ι → Set (Fin N → ℝ)}
    (hf : ∀ i, NullDimLT (f i) K) : NullDimLT (⋃ i, f i) K := by
  cases K with
  | zero =>
      simp only [nullDimLT_zero_iff] at hf ⊢
      exact Set.iUnion_eq_empty.mpr hf
  | succ K => exact NullDimLE.iUnion hf

/-- **Nullity passes to a closure through its frontier.**  `closure X = X ∪ (closure X \ X)`, and
`NullDimLE` is closed under finite unions (A2).  Both hypotheses are needed: `ℚ` has
`NullDimLE · 0` while `closure ℚ = ℝ` does not. -/
theorem closure_nullDimLE {N μ : ℕ} {X : Set (Fin N → ℝ)} (hX : NullDimLE X μ)
    (hbd : NullDimLE (closure X \ X) μ) : NullDimLE (closure X) μ := by
  have h : closure X = X ∪ (closure X \ X) := (Set.union_sdiff_cancel subset_closure).symm
  rw [h]
  exact NullDimLE.union hX hbd

/-- Coordinate projections do not raise the measure (`NullDimLT` form). -/
theorem NullDimLT.projFirst {n m K : ℕ} {X : Set (Fin (n + m) → ℝ)}
    (h : NullDimLT X K) : NullDimLT (projFirst n m '' X) K := by
  cases K with
  | zero => rw [nullDimLT_zero_iff] at h ⊢; rw [h]; simp
  | succ K => exact NullDimLE.projFirst h

end Work.WilE7.MainDesign
