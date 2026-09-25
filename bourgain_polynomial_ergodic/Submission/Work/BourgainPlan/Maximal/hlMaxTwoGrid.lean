import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The centred Hardy--Littlewood maximal function is dominated by two dyadic maximal functions

Classical fact: the centred maximal function over *all* intervals is bounded by a fixed number of
dyadic maximal functions (with *shifted* dyadic grids).  Here we use two grids — the standard one
`dyCell n k = [k·2^n, (k+1)·2^n)` and the one shifted by half a cell — and prove

`hlMax φ x ≤ 4 · (dyMax φ x + dyMaxShift (1/2) φ x)`.

This is the bridge that makes any bound proved for the dyadic maximal function available for the
corpus's centred maximal function `Commons.Analysis.Maximal.hlMax` (and hence, via the domination
statements `dilation_hl.purePower_sup_le_hlMax` / `poly_dilation_lp`, for the `1 < p < 2` frontier;
see `WINDOW_WEAK_TYPE_STATUS_S9.md`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax)

/-- Dyadic cells shifted by `α` times their length: `[(k+α)·2^n, ((k+α)+1)·2^n)`. -/
def dyCellShift (α : ℝ) (n k : ℤ) : Set ℝ :=
  Set.Ico (((k : ℝ) + α) * (2 : ℝ) ^ n) ((((k : ℝ) + α) + 1) * (2 : ℝ) ^ n)

/-- The dyadic maximal function of the grid shifted by `α` cell lengths. -/
noncomputable def dyMaxShift (α : ℝ) (φ : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (n : ℤ) (k : ℤ) (_ : x ∈ dyCellShift α n k),
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) * ∫⁻ y in dyCellShift α n k, φ y

lemma dyCellShift_measurable (α : ℝ) (n k : ℤ) : MeasurableSet (dyCellShift α n k) :=
  measurableSet_Ico

lemma dyCellShift_zero_eq_dyCell (n k : ℤ) : dyCellShift 0 n k = dyCell n k := by
  unfold dyCellShift dyCell
  norm_num

lemma dyMaxShift_zero (φ : ℝ → ℝ≥0∞) (x : ℝ) : dyMaxShift 0 φ x = dyMax φ x := by
  unfold dyMaxShift dyMax dyCell dyCellShift
  norm_num

/-- The elementary weight identity `L⁻¹ = (2^N/L)·(2^N)⁻¹` in `ℝ≥0∞`. -/
lemma ofReal_inv_eq_mul {L : ℝ} (hL : 0 < L) (N : ℤ) :
    ENNReal.ofReal L⁻¹
      = ENNReal.ofReal ((2 : ℝ) ^ N / L) * ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

lemma natCast_le_two_pow (m : ℕ) : (m : ℝ) ≤ (2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      calc ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        _ ≤ 2 * (2 : ℝ) ^ k := by linarith
        _ = (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- **The dyadic level adapted to an interval length.**  For `L > 0` there is `N` with
`2^N ≤ 4L < 2^(N+1)`. -/
lemma exists_level (L : ℝ) (hL : 0 < L) :
    ∃ N : ℤ, (2 : ℝ) ^ N ≤ 4 * L ∧ 4 * L < (2 : ℝ) ^ (N + 1) := by
  have h4L : (0 : ℝ) < 4 * L := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (max (4 * L) ((4 * L)⁻¹))
  have hm2 : max (4 * L) ((4 * L)⁻¹) < (2 : ℝ) ^ m :=
    lt_of_lt_of_le hm (natCast_le_two_pow m)
  have hbig : 4 * L < (2 : ℝ) ^ (m : ℤ) := by
    rw [zpow_natCast]; exact lt_of_le_of_lt (le_max_left _ _) hm2
  have hsmall : (4 * L)⁻¹ < (2 : ℝ) ^ (m : ℤ) := by
    rw [zpow_natCast]; exact lt_of_le_of_lt (le_max_right _ _) hm2
  have hlow : (2 : ℝ) ^ (-(m : ℤ)) ≤ 4 * L := by
    have h2M : (0 : ℝ) < (2 : ℝ) ^ (m : ℤ) := zpow_two_pos (m : ℤ)
    rw [zpow_neg, inv_le_comm₀ h2M h4L]
    exact le_of_lt hsmall
  classical
  set S : Finset ℤ := (Finset.Icc (-(m : ℤ)) (m : ℤ)).filter
    (fun j => (2 : ℝ) ^ j ≤ 4 * L) with hS
  have hmem : S.Nonempty := ⟨-(m : ℤ), by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, by omega⟩, hlow⟩⟩
  have hmaxmem : S.max' hmem ∈ S := S.max'_mem hmem
  have hNle : S.max' hmem ≤ (m : ℤ) :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hmaxmem).1).2
  have hNlt : S.max' hmem < (m : ℤ) := by
    by_contra hc
    push Not at hc
    have hle : (2 : ℝ) ^ (m : ℤ) ≤ (2 : ℝ) ^ (S.max' hmem) :=
      zpow_le_zpow_right₀ (by norm_num) hc
    have := (Finset.mem_filter.mp hmaxmem).2
    linarith [hbig, hle, this]
  refine ⟨S.max' hmem, (Finset.mem_filter.mp hmaxmem).2, ?_⟩
  by_cases hP : (2 : ℝ) ^ (S.max' hmem + 1) ≤ 4 * L
  · have hIcc : S.max' hmem + 1 ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      rw [Finset.mem_Icc]
      exact ⟨by linarith [(Finset.mem_Icc.mp (Finset.mem_filter.mp hmaxmem).1).1], by omega⟩
    have hmem' : S.max' hmem + 1 ∈ S := Finset.mem_filter.mpr ⟨hIcc, hP⟩
    have := Finset.le_max' S _ hmem'
    omega
  · exact lt_of_not_ge hP



end Work.BourgainPlan.Maximal
