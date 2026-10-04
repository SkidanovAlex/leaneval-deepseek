import Mathlib
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A lattice sum of a function supported in a small ball collapses to one term

Let `φ : (Fin n → ℝ) → ℂ` be supported in the open ball of radius `r < 1/2` about the origin and
let `z : Fin n → ℝ`.  Then in the lattice sum `∑' m : Fin n → ℤ, φ (z + m)` at most one term can be
nonzero: `φ (z + m) ≠ 0` forces `‖z + m‖ < r < 1/2`, hence `|z i + m i| < 1/2` for every `i`, and an
open interval of length `1` contains at most one integer.  The unique surviving multi-index is
`m i = ⌊-(z i) + 1/2⌋`, the "round to nearest integer" of `-z i`.

The two elementary facts used are:
* `int_eq_floor_of_abs_add_lt_half` : `|x + k| < 1/2` for `x : ℝ`, `k : ℤ` forces
  `k = ⌊-x + 1/2⌋`;
* `lt_abs_add_int_of_ne_floor` : if `k ≠ ⌊-x + 1/2⌋` then `|x + k| ≥ 1/2` (indeed `> r` for
  every `r < 1/2`).
-/

namespace Work.Diff.STE.GalToolbox

/-- If `|x + k| < 1/2` for a real number `x` and an integer `k`, then `k` is the integer nearest
to `-x`, namely `k = ⌊-x + 1/2⌋`.  (Two integers in the open interval `(-x-1/2, -x+1/2)` of length
`1` have to coincide.) -/
lemma int_eq_floor_of_abs_add_lt_half {x : ℝ} {k : ℤ} (h : |x + (k : ℝ)| < 1 / 2) :
    k = ⌊-x + 1 / 2⌋ := by
  have h1 : x + (k : ℝ) < 1 / 2 := (abs_lt.mp h).2
  have h2 : -(1 / 2 : ℝ) < x + (k : ℝ) := (abs_lt.mp h).1
  have hle : k ≤ ⌊-x + 1 / 2⌋ := by
    have ht : (-x + 1 / 2 : ℝ) = 1 / 2 - x := by ring
    rw [ht]
    exact Int.le_floor.mpr (by linarith)
  have hge : ⌊-x + 1 / 2⌋ ≤ k := by
    have ht : (-x + 1 / 2 : ℝ) = 1 / 2 - x := by ring
    rw [ht]
    by_contra hc
    push Not at hc
    have hk : k + 1 ≤ ⌊1 / 2 - x⌋ := Int.add_one_le_iff.mpr hc
    have h3 := Int.le_floor.mp hk
    push_cast at h3
    linarith
  exact le_antisymm hle hge

/-- Quantitative companion of `int_eq_floor_of_abs_add_lt_half`: for an integer `k` different from
the nearest integer to `-x`, the quantity `|x + k|` is at least `1/2`; in particular it exceeds
every `r < 1/2`. -/
lemma lt_abs_add_int_of_ne_floor {x r : ℝ} (hr : r < 1 / 2) {k : ℤ} (hk : k ≠ ⌊-x + 1 / 2⌋) :
    r < |x + (k : ℝ)| := by
  have h0ub : x + ((⌊-x + 1 / 2⌋ : ℤ) : ℝ) ≤ 1 / 2 := by
    have := Int.floor_le (-x + 1 / 2 : ℝ); linarith
  have h0lb : -(1 / 2 : ℝ) < x + ((⌊-x + 1 / 2⌋ : ℤ) : ℝ) := by
    have := Int.sub_one_lt_floor (-x + 1 / 2 : ℝ); linarith
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · have hk1 : k + 1 ≤ ⌊-x + 1 / 2⌋ := Int.add_one_le_iff.mpr hlt
    have hcast : (k : ℝ) ≤ ((⌊-x + 1 / 2⌋ : ℤ) : ℝ) - 1 := by
      have h' : ((k + 1 : ℤ) : ℝ) ≤ ((⌊-x + 1 / 2⌋ : ℤ) : ℝ) := by exact_mod_cast hk1
      push_cast at h'
      linarith
    have hy : x + (k : ℝ) ≤ -(1 / 2) := by linarith
    rw [abs_of_neg (by linarith : x + (k : ℝ) < 0)]
    linarith
  · have hk1 : ⌊-x + 1 / 2⌋ + 1 ≤ k := Int.add_one_le_iff.mpr hgt
    have hcast : ((⌊-x + 1 / 2⌋ : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by
      have h' : ((((⌊-x + 1 / 2⌋ : ℤ) + 1 : ℤ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      push_cast at h'
      linarith
    have hy : (1 / 2 : ℝ) < x + (k : ℝ) := by linarith
    rw [abs_of_pos (by linarith : 0 < x + (k : ℝ))]
    linarith

theorem tsum_iVec_eq_single {n : ℕ} {r : ℝ} (hr : r < 1 / 2)
    {φ : (Fin n → ℝ) → ℂ}
    (hsupp : Function.support φ ⊆ Metric.ball (0 : Fin n → ℝ) r) (z : Fin n → ℝ) :
    (∑' m : Fin n → ℤ, φ (z + Work.Diff.STE.iVec m))
      = φ (z + Work.Diff.STE.iVec (fun i => ⌊-(z i) + 1 / 2⌋)) := by
  classical
  refine tsum_eq_single (fun i => ⌊-(z i) + 1 / 2⌋) ?_
  intro m hm
  by_contra hne
  have hmem : z + Work.Diff.STE.iVec m ∈ Function.support φ := hne
  have hb := hsupp hmem
  rw [Metric.mem_ball, dist_zero_right] at hb
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
  have hcoord : r < |z i + (m i : ℝ)| := lt_abs_add_int_of_ne_floor hr hi
  have hle : |z i + (m i : ℝ)| ≤ ‖z + Work.Diff.STE.iVec m‖ := by
    have h1 := dist_le_pi_dist (z + Work.Diff.STE.iVec m) (0 : Fin n → ℝ) i
    simp only [Pi.add_apply, Pi.zero_apply, Work.Diff.STE.iVec_apply] at h1
    rwa [Real.dist_eq, sub_zero, dist_zero_right] at h1
  linarith

end Work.Diff.STE.GalToolbox
