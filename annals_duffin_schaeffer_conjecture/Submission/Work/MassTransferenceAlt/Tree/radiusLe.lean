import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-- **The threshold `thrC` is at most half the radius.**  For `0 < d < 1`, a ball of
radius `R > 0` and a local level with `L ≥ 1` sub-levels, every child radius allowed
by `thrC d R L` is at most `R / 2`.

Indeed `thrC d R L ≤ (R ^ (1 - d) / (2 ^ 40 * L)) ^ (1 / (1 - d))`, and taking
`(1 - d)`-th powers this is `R / 2` exactly when `2 ^ (1 - d) = 2`, which holds for
`d = 0`; for `0 < d < 1` we have `2 ^ (1 - d) ≤ 2 ≤ 2 ^ 40 ≤ 2 ^ 40 * L`. -/
private lemma thrC_le_half (d R : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (hR : 0 < R) {L : ℕ}
    (hL : 1 ≤ L) : thrC d R L ≤ R / 2 := by
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hd : (0 : ℝ) < 1 - d := by linarith
  have hL0 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  -- the key numerical inequality: `2 ^ (1 - d) ≤ 2 ^ 40 * L`
  have hpow : (2 : ℝ) ^ (1 - d) ≤ (2 : ℝ) ^ 40 * (L : ℝ) := by
    have h1 : (2 : ℝ) ^ (1 - d) ≤ (2 : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    rw [Real.rpow_one] at h1
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ 40 * (L : ℝ) := by
      have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
      nlinarith
    linarith
  have hbase : R ^ (1 - d) / ((2 : ℝ) ^ 40 * (L : ℝ)) ≤ (R / 2) ^ (1 - d) := by
    rw [Real.div_rpow hR0 (by norm_num : (0 : ℝ) ≤ 2)]
    refine div_le_div_of_nonneg_left (by positivity) ?_ hpow
    exact Real.rpow_pos_of_pos (by norm_num) _
  calc thrC d R L
      ≤ (R ^ (1 - d) / ((2 : ℝ) ^ 40 * (L : ℝ))) ^ (1 / (1 - d)) := min_le_right _ _
    _ ≤ ((R / 2) ^ (1 - d)) ^ (1 / (1 - d)) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = R / 2 := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ R / 2),
          mul_one_div_cancel (ne_of_gt hd), Real.rpow_one]

/-- **Geometric decay of the radii along the tree.**  Every ball of level `n` has radius
at most `Rabs d / 2 ^ n`. -/
lemma radiusLe (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) (n : ℕ) {i : ℕ} (hi : i ∈ T.lev n) :
    ρ i ≤ Work.MassTransferenceAlt.Rabs d / 2 ^ n := by
  -- induction along the tree: the parent's radius bounds twice the child's radius
  have key : ∀ n, ∀ i ∈ T.lev n, ρ i ≤ Rabs d / 2 ^ n := by
    intro n
    induction n with
    | zero =>
        -- balls of level `0` are admissible, hence have radius at most `Rabs d`
        intro i hi
        simpa using (T.good 0 i hi).2.1
    | succ n ih =>
        intro i hi
        obtain ⟨B, hB, hpar⟩ := T.par_mem n i hi
        have hloc := T.loc n B hB
        have hF : i ∈ (T.lev (n + 1)).filter (fun j => T.par (n + 1) j = some B) :=
          Finset.mem_filter.mpr ⟨hi, hpar⟩
        -- the local level bounds the child radius by `thrC d (ρ B) (nsub d (ρ B))`
        have hle1 : ρ i ≤ thrC d (ρ B) (nsub d (ρ B)) := hloc.2.1 i hF
        have hBpos : 0 < ρ B := (T.good n B hB).1
        have hle2 : thrC d (ρ B) (nsub d (ρ B)) ≤ ρ B / 2 :=
          thrC_le_half d (ρ B) hd0 hd1 hBpos (nsub_pos d (ρ B))
        have hIH : ρ B ≤ Rabs d / 2 ^ n := ih B hB
        calc ρ i ≤ ρ B / 2 := le_trans hle1 hle2
          _ ≤ (Rabs d / 2 ^ n) / 2 := by linarith
          _ = Rabs d / 2 ^ (n + 1) := by rw [div_div, pow_succ]
  exact key n i hi

end Work.MassTransferenceAlt.Tree
