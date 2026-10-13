/-
  The distinctness atom `lf3DistAtom` of the non-strict level-fibre construction,

    `lf3DistAtom = ∏_{l<l'} Σ_c (X_{z_l c} - X_{z_{l'} c})²`,

  is strictly positive at a point `U` exactly when the `k` blocks of `U` are pairwise distinct
  (as vectors `Fin (p+q) → ℝ`).

  This file proves that characterisation, together with the three elementary facts it rests on:
  * `lf3DistAtom_eval`     — evaluation of the atom as a product of sums of squares,
  * `lf3_sum_sq_pos_iff`   — a sum of squares is positive iff the two vectors differ,
  * `lf3_prod_pos_iff`     — a product of non-negative reals is positive iff all factors are.
-/
import Mathlib
import Submission.Work.WilE7.SheetData.NonstrictLevelFibre

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilE7.SheetData

/-! ## §1. Elementary ordering facts -/

/-- A non-negative real is positive exactly when it is non-zero. -/
theorem lf3_lt_zero_iff_ne_zero_of_nonneg {x : ℝ} (h : 0 ≤ x) : (0 < x ↔ x ≠ 0) :=
  ⟨ne_of_gt, fun hx => lt_of_le_of_ne h hx.symm⟩

/-- A sum of squares `Σ_c (a c - b c)²` is positive exactly when the two vectors `a` and `b`
differ. -/
theorem lf3_sum_sq_pos_iff {n : ℕ} (a b : Fin n → ℝ) :
    0 < (∑ c : Fin n, (a c - b c) ^ 2) ↔ a ≠ b := by
  rw [lf3_lt_zero_iff_ne_zero_of_nonneg (Finset.sum_nonneg (fun c _ => sq_nonneg _))]
  constructor
  · intro hsum hab
    apply hsum
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg _)]
    intro c _
    rw [hab]
    simp
  · intro hab hsum
    apply hab
    funext c
    have hc : (a c - b c) ^ 2 = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg _)] at hsum
      exact hsum c (Finset.mem_univ c)
    have h0 : a c - b c = 0 := sq_eq_zero_iff.mp hc
    linarith

/-- A product of non-negative reals is positive exactly when all its factors are. -/
theorem lf3_prod_pos_iff {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ f i) : 0 < ∏ i ∈ s, f i ↔ ∀ i ∈ s, 0 < f i := by
  constructor
  · intro hp i hi
    rw [lf3_lt_zero_iff_ne_zero_of_nonneg (h i hi)]
    intro hi0
    have hz : ∏ j ∈ s, f j = 0 := by
      rw [Finset.prod_eq_zero_iff]
      exact ⟨i, hi, hi0⟩
    linarith
  · intro hpos
    exact Finset.prod_pos hpos

/-! ## §2. Evaluating the distinctness atom -/

/-- The distinctness atom evaluates to the product of the pairwise sums of squares. -/
theorem lf3DistAtom_eval {p q M k : ℕ} (U : Fin (Work.WilE7.LevelFibre.lfD p (q + 1) M k) → ℝ) :
    MvPolynomial.eval U
        (Work.WilE7.SheetData.lf3DistAtom (p := p) (q := q) (M := M) (k := k)) =
      ∏ ll ∈ (Finset.univ.filter (fun ll : Fin k × Fin k => ll.1 < ll.2)),
        ∑ c : Fin (p + q),
          (U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) ll.1 c) -
            U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) ll.2 c)) ^ 2 := by
  rw [Work.WilE7.SheetData.lf3DistAtom, MvPolynomial.eval_prod]
  refine Finset.prod_congr rfl fun ll _ => ?_
  rw [MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X]

/-! ## §3. The characterisation -/

theorem lf3DistAtom_eval_pos {p q M k : ℕ} (U : Fin (Work.WilE7.LevelFibre.lfD p (q + 1) M k) → ℝ) :
    0 < MvPolynomial.eval U
        (Work.WilE7.SheetData.lf3DistAtom (p := p) (q := q) (M := M) (k := k)) ↔
      ∀ l l' : Fin k, l ≠ l' →
        (fun c : Fin (p + q) => U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) l c)) ≠
          (fun c : Fin (p + q) =>
            U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) l' c)) := by
  rw [lf3DistAtom_eval]
  have hnn : ∀ ll : Fin k × Fin k,
      0 ≤ ∑ c : Fin (p + q),
        (U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) ll.1 c) -
          U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) ll.2 c)) ^ 2 :=
    fun ll => Finset.sum_nonneg (fun c _ => sq_nonneg _)
  rw [lf3_prod_pos_iff _ _ (fun ll _ => hnn ll)]
  constructor
  · intro h l l' hne
    have hpair : ∀ a b : Fin k, a < b →
        0 < (∑ c : Fin (p + q),
          (U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) a c) -
            U (Work.WilE7.SheetData.lf3XpIdx (p := p) (q := q) (M := M) b c)) ^ 2) :=
      fun a b hab => h (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (lf3_sum_sq_pos_iff _ _).mp (hpair l l' hlt)
    · exact fun heq => (lf3_sum_sq_pos_iff _ _).mp (hpair l' l hlt) heq.symm
  · intro h ll hlt
    exact (lf3_sum_sq_pos_iff _ _).mpr (h ll.1 ll.2 (ne_of_lt (Finset.mem_filter.mp hlt).2))

end Work.WilE7.SheetData
