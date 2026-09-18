/-
# The Cantor construction of the mass transference principle: definitions

This file fixes the constants and the data structures used in the inductive
construction of the Beresnevich–Velani proof of the mass transference principle
in `ℝ` (`k = 1`, `f(r) = r ^ d`, `0 < d < 1`).

* `Rabs d` is an absolute upper bound for the radii of the balls in the
  construction: any radius `ρ ≤ Rabs d` satisfies `3 ρ ≤ ρ ^ d` (so that the
  threefold dilation `3 B(c,ρ)` of a small ball is contained in its enlarged
  version `B(c, ρ ^ d)`) and `(ρ) ^ (d - 1) ≥ 2 ^ 40` (the "smallness"
  hypothesis used to count sub-levels).
* `thrC d R L` is the threshold for the radii of the children of a ball of
  radius `R` whose local level consists of `L` sub-levels: any child radius
  `ρ ≤ thrC d R L` satisfies `ρ ^ (1 - d) ≤ R ^ (1 - d) / (2 ^ 40 * L)`, the
  estimate needed for the free space argument.
* `nsub d R` is the number of sub-levels of the local level of a ball of radius
  `R`: `⌊16 R ^ (d-1)⌋ + 1`, so that `16 R ^ (d-1) ≤ nsub` (mass conservation)
  and `nsub ≤ 32 R ^ (d-1)` when `R ≤ Rabs d` (the counting bound of case (ii)).
* `Good d c ρ i` says the `i`-th ball of the family is admissible as a node.
* `IsLoc d c ρ B R F sub L` is the package of properties (P1)–(P5) satisfied by a
  local level: the children `F` of a ball of centre `B` and radius `R`, with `L`
  sub-levels indexed by `sub`.
-/
import Submission.Work.MassTransferenceAlt.Basic

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Work.MassTransferenceAlt

/-- The absolute radius bound `Rabs d = (2 ^ (-40)) ^ (1 / (1 - d))`. -/
noncomputable def Rabs (d : ℝ) : ℝ := (((2:ℝ)^40)⁻¹) ^ (1 / (1 - d))

lemma Rabs_pos (d : ℝ) : 0 < Rabs d := Real.rpow_pos_of_pos (by positivity) _

lemma Rabs_rpow {d : ℝ} (hd1 : d < 1) : (Rabs d) ^ (1 - d) = ((2:ℝ)^40)⁻¹ := by
  rw [Rabs, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((2:ℝ)^40)⁻¹),
    one_div_mul_cancel (by linarith : (1:ℝ) - d ≠ 0), Real.rpow_one]

lemma Rabs_inv_rpow {d : ℝ} (hd1 : d < 1) : (Rabs d) ^ (d - 1) = (2:ℝ)^40 := by
  rw [show d - 1 = -(1 - d) by ring, Real.rpow_neg (Rabs_pos d).le, Rabs_rpow (d := d) hd1,
    inv_inv]

lemma Rabs_le_one {d : ℝ} (hd1 : d < 1) : Rabs d ≤ 1 := by
  refine Real.rpow_le_one (by positivity) ?_ (by positivity)
  rw [inv_le_one₀ (by positivity)]
  norm_num

/-- The threshold for the radii of the children of a ball of radius `R` whose local
level has `L` sub-levels. -/
noncomputable def thrC (d : ℝ) (R : ℝ) (L : ℕ) : ℝ :=
  min (Rabs d) ((R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ))) ^ (1 / (1 - d)))

lemma thrC_le_Rabs (d : ℝ) (R : ℝ) (L : ℕ) : thrC d R L ≤ Rabs d := min_le_left _ _

lemma thrC_pos {d R : ℝ} (hR : 0 < R) (hd1 : d < 1) {L : ℕ} (hL : 1 ≤ L) :
    0 < thrC d R L := by
  rw [thrC, lt_min_iff]
  refine ⟨Rabs_pos d, Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hR _) ?_) _⟩
  exact mul_pos (by positivity) (by exact_mod_cast hL)

lemma thrC_rpow {d R : ℝ} (hR : 0 < R) (hd1 : d < 1) {L : ℕ} (hL : 1 ≤ L) :
    (thrC d R L) ^ (1 - d) ≤ R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ)) := by
  have h1 : thrC d R L ≤ ((R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ))) ^ (1 / (1 - d))) :=
    min_le_right _ _
  have hbase : (0:ℝ) ≤ R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ)) := by positivity
  calc (thrC d R L) ^ (1 - d)
      ≤ ((R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ))) ^ (1 / (1 - d))) ^ (1 - d) :=
        Real.rpow_le_rpow (thrC_pos hR hd1 hL).le h1 (by linarith)
    _ = R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ)) := by
        rw [← Real.rpow_mul hbase, one_div_mul_cancel (by linarith : (1:ℝ) - d ≠ 0),
          Real.rpow_one]

lemma thrC_le_R {d R : ℝ} (hR : 0 < R) (hd1 : d < 1) {L : ℕ} (hL : 1 ≤ L) :
    thrC d R L ≤ R := by
  have h := thrC_rpow hR hd1 hL
  have hb : R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ)) ≤ R ^ (1 - d) := by
    refine div_le_self (by positivity) ?_
    have : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    nlinarith [show (1:ℝ) ≤ (2:ℝ)^40 by norm_num]
  exact (Real.rpow_le_rpow_iff (thrC_pos hR hd1 hL).le hR.le (by linarith)).mp (le_trans h hb)

/-- The number of sub-levels of the local level of a ball of radius `R`. -/
noncomputable def nsub (d : ℝ) (R : ℝ) : ℕ := Nat.floor (16 * R ^ (d - 1)) + 1

lemma nsub_pos (d : ℝ) (R : ℝ) : 1 ≤ nsub d R := Nat.le_add_left 1 _

lemma lt_nsub {d R : ℝ} (hR : 0 < R) (hd1 : d < 1) : 16 * R ^ (d - 1) < (nsub d R : ℝ) := by
  rw [nsub]; push_cast; exact Nat.lt_floor_add_one _

lemma nsub_le {d R : ℝ} (hR : 0 < R) (hd1 : d < 1) (hRabs : R ≤ Rabs d) :
    (nsub d R : ℝ) ≤ 32 * R ^ (d - 1) := by
  have h1 : (nsub d R : ℝ) ≤ 16 * R ^ (d - 1) + 1 := by
    rw [nsub]; push_cast
    linarith [Nat.floor_le (show (0:ℝ) ≤ 16 * R ^ (d - 1) by positivity)]
  have h2 : (1:ℝ) ≤ 16 * R ^ (d - 1) := by
    have h4 : R ^ (1 - d) ≤ ((2:ℝ)^40)⁻¹ := by
      calc R ^ (1 - d) ≤ (Rabs d) ^ (1 - d) := Real.rpow_le_rpow hR.le hRabs (by linarith)
        _ = ((2:ℝ)^40)⁻¹ := Rabs_rpow (d := d) hd1
    have h5 : R ^ (d - 1) = (R ^ (1 - d))⁻¹ := by
      rw [show d - 1 = -(1 - d) by ring, Real.rpow_neg hR.le]
    rw [h5]
    have hpos : (0:ℝ) < R ^ (1 - d) := Real.rpow_pos_of_pos hR _
    have : (2:ℝ)^40 ≤ (R ^ (1 - d))⁻¹ := by
      rw [show (2:ℝ)^40 = (((2:ℝ)^40)⁻¹)⁻¹ by rw [inv_inv]]
      exact (inv_le_inv₀ (by positivity) hpos).mpr h4
    nlinarith
  linarith


/-- For a radius below `Rabs d`, the quantity `ρ ^ (1 - d)` is at most `2 ^ (-40)`. -/
lemma rpow_one_sub_le {d ρ : ℝ} (hd1 : d < 1) (hρ0 : 0 < ρ) (hρ : ρ ≤ Rabs d) :
    ρ ^ (1 - d) ≤ ((2:ℝ)^40)⁻¹ := by
  calc ρ ^ (1 - d) ≤ (Rabs d) ^ (1 - d) := Real.rpow_le_rpow hρ0.le hρ (by linarith)
    _ = ((2:ℝ)^40)⁻¹ := Rabs_rpow (d := d) hd1

/-- For a radius `ρ ≤ Rabs d`, `3 ρ ≤ ρ ^ d`: the threefold dilation of a ball of the
construction is contained in its enlarged version. -/
lemma three_mul_le_rpow {d ρ : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ Rabs d) : 3 * ρ ≤ ρ ^ d := by
  have h : ρ ^ (1 - d) ≤ 1 / 3 := le_trans (rpow_one_sub_le hd1 hρ0 hρ) (by norm_num)
  have h1 : ρ ^ d = ρ / (ρ ^ (1 - d)) := by
    have h2 : ρ ^ d = ρ ^ (1:ℝ) * ρ ^ (d - 1) := by
      rw [← Real.rpow_add hρ0]; norm_num
    rw [h2, Real.rpow_one, show d - 1 = -(1 - d) by ring, Real.rpow_neg hρ0.le, div_eq_mul_inv]
  rw [h1, le_div_iff₀ (Real.rpow_pos_of_pos hρ0 _)]
  nlinarith [mul_le_mul_of_nonneg_left h hρ0.le]

lemma self_le_rpow {d ρ : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ Rabs d) : ρ ≤ ρ ^ d :=
  le_trans (by linarith) (three_mul_le_rpow hd0 hd1 hρ0 hρ)

/-- A ball of the family is admissible as a node of the construction. -/
def Good (d : ℝ) (c ρ : ℕ → ℝ) (i : ℕ) : Prop :=
  0 < ρ i ∧ ρ i ≤ Rabs d ∧ 0 ≤ c i - ρ i ∧ c i + ρ i ≤ 1

/-- **The local-level properties (P1)–(P5).**  `F` is the set of children of the ball
`Iv B R`, `sub` assigns to each child its sub-level index, and there are `L` sub-levels.
-/
def IsLoc (d : ℝ) (c ρ : ℕ → ℝ) (B R : ℝ) (F : Finset ℕ) (sub : ℕ → ℕ) (L : ℕ) : Prop :=
    (∀ i ∈ F, 0 < ρ i)
  ∧ (∀ i ∈ F, ρ i ≤ thrC d R L)
  ∧ (∀ i ∈ F, Fenl d c ρ i ⊆ Iv B R)
  ∧ (∀ i ∈ F, ∀ j ∈ F, i ≠ j → sub i = sub j →
      Disjoint (Fenl d c ρ i) (Fenl d c ρ j))
  ∧ (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (Iv (c i) (3 * ρ i)) (Iv (c j) (3 * ρ j)))
  ∧ (∀ i ∈ F, sub i < L)
  ∧ (∀ k, k < L → ∃ i ∈ F, sub i = k)
  ∧ (∀ k, k < L → R / 16 ≤ ∑ i ∈ F.filter (fun i => sub i = k), (ρ i) ^ d)
  ∧ (∀ i ∈ F, ∀ j ∈ F, sub i < sub j →
      (ρ j) ^ d ≤ ((1:ℝ)/2) ^ (sub j - sub i) * (ρ i) ^ d)

end Work.MassTransferenceAlt
