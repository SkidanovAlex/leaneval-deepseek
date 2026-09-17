import Mathlib
import Submission.ContactSharp
import Submission.Commons.GeometryOfNumbers.Counting.sum_int_points_annulus_le_radial

/-!
# The lattice weight of the contact estimate

For a nonzero integer vector `x ∈ ℤ^d` with `Q(x) = ‖x‖²` put

    wt K a₀ R x  :=  ∑_{k ∈ Icc 1 K} tailG ((a₀ - R²/Q(x)) · d² / √k)   if R² < Q(x) ≤ 4R²,
                  := 0                                                  otherwise.

This is exactly the weight `w` of `PLAN_V11 §2`: it is the sum, over the times `k`, of the
per-time contact probability of `PLAN_V10`(★) with `‖y‖ = ‖x‖/R`, `y = x/R ∈ Λ_A`, and it is
concentrated on the annulus `R < ‖x‖ ≤ 2R` because a lattice vector of `Λ_A = (1/R)·ker a` with
`‖y‖ ≤ 2` corresponds to an integer vector `x` with `Q(x) ≤ 4R²`.

The file also records the elementary properties needed to apply
`Commons.GeometryOfNumbers.Counting.sum_int_points_annulus_le_radial`.
-/

namespace Submission.Weight

open MeasureTheory
open Submission.ContactSharp
open Commons.GeometryOfNumbers.Counting

noncomputable section

variable {d : ℕ}

/-- `Q(x) = ‖x‖²` for an integer vector. -/
def intQ (x : Fin d → ℤ) : ℝ := ‖intVec x‖ ^ 2

lemma intQ_nonneg (x : Fin d → ℤ) : 0 ≤ intQ x := sq_nonneg _

lemma intQ_eq_sum (x : Fin d → ℤ) : intQ x = ∑ i, (x i : ℝ) ^ 2 := norm_intVec_sq x

lemma intQ_eq_zero_iff {x : Fin d → ℤ} : intQ x = 0 ↔ x = 0 := by
  rw [intQ_eq_sum, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro h
    funext i
    have := h i (Finset.mem_univ i)
    simpa using this
  · intro h
    subst h
    simp

lemma intQ_pos_of_ne_zero {x : Fin d → ℤ} (hx : x ≠ 0) : 0 < intQ x := by
  rcases lt_or_eq_of_le (intQ_nonneg x) with h | h
  · exact h
  · exact absurd (intQ_eq_zero_iff.mp h.symm) hx

/-- The finite set of integer points of the closed ball of radius `R`. -/
def intPoints (R : ℝ) : Finset (Fin d → ℤ) := (finite_int_points_ball R).toFinset

lemma mem_intPoints {R : ℝ} {x : Fin d → ℤ} : x ∈ intPoints (d := d) R ↔ intQ x ≤ R ^ 2 := by
  simp [intPoints, intQ_eq_sum]

/-- The lattice weight. -/
def wt (K : ℕ) (a₀ R : ℝ) (x : Fin d → ℤ) : ℝ :=
  if R ^ 2 < intQ x ∧ intQ x ≤ 4 * R ^ 2 then
    ∑ k ∈ Finset.Icc 1 K,
      tailG ((a₀ - R ^ 2 / intQ x) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ))
  else 0

lemma wt_nonneg (K : ℕ) (a₀ R : ℝ) (x : Fin d → ℤ) : 0 ≤ wt K a₀ R x := by
  rw [wt]
  split
  · exact Finset.sum_nonneg fun _k _ => tailG_nonneg _
  · exact le_rfl

lemma wt_of_mem_annulus (K : ℕ) (a₀ R : ℝ) {x : Fin d → ℤ}
    (h1 : R ^ 2 < intQ x) (h2 : intQ x ≤ 4 * R ^ 2) :
    wt K a₀ R x
      = ∑ k ∈ Finset.Icc 1 K,
          tailG ((a₀ - R ^ 2 / intQ x) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ)) := by
  rw [wt, if_pos ⟨h1, h2⟩]

lemma wt_eq_zero_of_not_annulus (K : ℕ) (a₀ R : ℝ) {x : Fin d → ℤ}
    (h : ¬ (R ^ 2 < intQ x ∧ intQ x ≤ 4 * R ^ 2)) : wt K a₀ R x = 0 := by
  rw [wt, if_neg h]

/-- The radial profile of the weight: for `‖x‖ = v` in the annulus it is
`∑_k tailG ((a₀ - R²/v²) d²/√k)`. -/
def prof (K : ℕ) (a₀ R : ℝ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, tailG ((a₀ - R ^ 2 / max v R ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ))

/-- On the annulus the weight is the radial profile evaluated at `‖x‖`. -/
lemma wt_eq_prof (K : ℕ) (a₀ R : ℝ) (hR : 0 ≤ R) {x : Fin d → ℤ}
    (h1 : R ^ 2 < intQ x) (h2 : intQ x ≤ 4 * R ^ 2) :
    wt (d := d) K a₀ R x = prof (d := d) K a₀ R ‖intVec x‖ := by
  rw [wt_of_mem_annulus K a₀ R h1 h2, prof]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hRlt : R < ‖intVec x‖ := by
    have h' := sq_lt_sq.mp (show R ^ 2 < ‖intVec x‖ ^ 2 from by rwa [intQ] at h1)
    rw [abs_of_nonneg hR, abs_of_nonneg (norm_nonneg _)] at h'
    exact h'
  have hmax : max ‖intVec x‖ R = ‖intVec x‖ := max_eq_left (le_of_lt hRlt)
  rw [hmax]
  norm_num [intQ]

lemma prof_nonneg (K : ℕ) (a₀ R : ℝ) (v : ℝ) : 0 ≤ prof (d := d) K a₀ R v :=
  Finset.sum_nonneg fun _k _ => tailG_nonneg _

/-- `v ↦ prof K a₀ R v` is non-increasing on `[0,∞)`. -/
lemma prof_antitone (K : ℕ) (a₀ R : ℝ) (hR : 0 < R) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → prof (d := d) K a₀ R b ≤ prof (d := d) K a₀ R a := by
  intro a b _ hab
  refine Finset.sum_le_sum fun k hk => tailG_mono ?_
  have ha : 0 < max a R := lt_of_lt_of_le hR (le_max_right _ _)
  have hmax : max a R ≤ max b R := max_le_max hab le_rfl
  have hsq : max a R ^ 2 ≤ max b R ^ 2 := pow_le_pow_left₀ (le_of_lt ha) hmax 2
  have h1 : R ^ 2 / max b R ^ 2 ≤ R ^ 2 / max a R ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg R) (pow_pos ha 2) hsq
  have h2 : a₀ - R ^ 2 / max a R ^ 2 ≤ a₀ - R ^ 2 / max b R ^ 2 := by linarith
  have h3 : (a₀ - R ^ 2 / max a R ^ 2) * (d : ℝ) ^ 2
      ≤ (a₀ - R ^ 2 / max b R ^ 2) * (d : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hkpos : (0 : ℝ) < Real.sqrt (k : ℝ) := by
    have hk1 : (1 : ℕ) ≤ k := (Finset.mem_Icc.mp hk).1
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
    exact Real.sqrt_pos.mpr this
  exact div_le_div_of_nonneg_right h3 (le_of_lt hkpos)

end

end Submission.Weight
