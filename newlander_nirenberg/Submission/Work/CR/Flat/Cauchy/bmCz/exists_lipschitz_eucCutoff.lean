import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

noncomputable section

open scoped NNReal

namespace Work.CR.Flat.Cauchy.bmCz

open Work.CR.Flat.Cauchy

/-- `eucNorm` is the norm of `x` viewed as an element of the `L²` space `WithLp 2 (Fin n → ℂ)`. -/
private lemma eucNorm_eq_norm_withLp {n : ℕ} (x : Fin n → ℂ) :
    eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [eucNorm]

/-- Reverse triangle inequality for the Euclidean norm on `ℂⁿ`. -/
private lemma abs_eucNorm_sub_le' {n : ℕ} (x y : Fin n → ℂ) :
    |eucNorm x - eucNorm y| ≤ eucNorm (x - y) := by
  rw [eucNorm_eq_norm_withLp x, eucNorm_eq_norm_withLp y, eucNorm_eq_norm_withLp (x - y)]
  have hsub : (WithLp.equiv 2 (Fin n → ℂ)).symm (x - y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x - (WithLp.equiv 2 (Fin n → ℂ)).symm y := by
    simp [WithLp.equiv_symm_apply]
  rw [hsub]
  exact abs_norm_sub_norm_le _ _

/-- The cutoff profile `cutProfile` is Lipschitz on the interval `[1/2, 1]`. -/
private lemma cutProfile_lipschitzOn_Icc :
    ∃ K : NNReal, LipschitzOnWith K cutProfile (Set.Icc (1/2 : ℝ) 1) :=
  (contDiff_cutProfile.contDiffOn).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc

/-- The cutoff profile is globally Lipschitz: the constant valid on `[1/2, 1]` works everywhere,
because `cutProfile` is constantly `1` on `(-∞, 1/2]` and constantly `0` on `[1, ∞)`. -/
private lemma cutProfile_lipschitz {K : NNReal}
    (hK : LipschitzOnWith K cutProfile (Set.Icc (1/2 : ℝ) 1)) :
    ∀ a b : ℝ, |cutProfile a - cutProfile b| ≤ (K : ℝ) * |a - b| := by
  have key : ∀ a b : ℝ, a ≤ b →
      |cutProfile a - cutProfile b| ≤ (K : ℝ) * (b - a) := by
    intro a b hab
    by_cases hb : b ≤ 1/2
    · rw [cutProfile_of_two_mul_le_one (by linarith), cutProfile_of_two_mul_le_one (by linarith)]
      simp only [sub_self, abs_zero]
      exact mul_nonneg K.coe_nonneg (by linarith)
    by_cases ha : 1 ≤ a
    · rw [cutProfile_of_one_le (le_trans ha hab), cutProfile_of_one_le ha]
      simp only [sub_self, abs_zero]
      exact mul_nonneg K.coe_nonneg (by linarith)
    rw [not_le] at hb ha
    set a' : ℝ := max a (1/2) with ha'
    set b' : ℝ := min b 1 with hb'
    have ha'mem : a' ∈ Set.Icc (1/2:ℝ) 1 :=
      ⟨le_max_right _ _, max_le (le_of_lt ha) (by norm_num)⟩
    have hb'mem : b' ∈ Set.Icc (1/2:ℝ) 1 :=
      ⟨le_min (le_of_lt hb) (by norm_num), min_le_right _ _⟩
    have hcut_a : cutProfile a = cutProfile a' := by
      rcases le_or_gt a (1/2) with h | h
      · rw [ha', max_eq_right h, cutProfile_of_two_mul_le_one (by linarith),
            cutProfile_of_two_mul_le_one (by norm_num)]
      · rw [ha', max_eq_left (le_of_lt h)]
    have hcut_b : cutProfile b = cutProfile b' := by
      rcases le_or_gt 1 b with h | h
      · rw [hb', min_eq_right h, cutProfile_of_one_le (le_refl 1), cutProfile_of_one_le h]
      · rw [hb', min_eq_left (le_of_lt h)]
    have hlip := hK.dist_le_mul a' ha'mem b' hb'mem
    rw [Real.dist_eq, Real.dist_eq] at hlip
    have ha'b' : a' ≤ b' :=
      max_le (le_min hab (le_of_lt ha)) (le_min (le_of_lt hb) (by norm_num))
    have hle : |a' - b'| = b' - a' := by rw [abs_of_nonpos (sub_nonpos.mpr ha'b'), neg_sub]
    calc |cutProfile a - cutProfile b|
        = |cutProfile a' - cutProfile b'| := by rw [hcut_a, hcut_b]
      _ ≤ (K:ℝ) * |a' - b'| := hlip
      _ = (K:ℝ) * (b' - a') := by rw [hle]
      _ ≤ (K:ℝ) * (b - a) := by
          apply mul_le_mul_of_nonneg_left (sub_le_sub (min_le_left b 1) (le_max_left a (1/2))) K.coe_nonneg
  intro a b
  rcases le_total a b with hab | hab
  · have h := key a b hab
    have hh : (K:ℝ) * |a - b| = (K:ℝ) * (b - a) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    rw [hh]; exact h
  · have h := key b a hab
    have hh : (K:ℝ) * |a - b| = (K:ℝ) * (a - b) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    rw [abs_sub_comm (cutProfile a) (cutProfile b), hh]
    exact h

/-- The radial cutoff `ρ` is Lipschitz for the Euclidean norm on `ℂⁿ`. -/
theorem exists_lipschitz_eucCutoff {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : Fin n → ℂ,
      |Work.CR.Flat.Cauchy.eucCutoff R x - Work.CR.Flat.Cauchy.eucCutoff R y|
        ≤ L * Work.CR.Flat.Cauchy.eucNorm (x - y) := by
  obtain ⟨K, hK⟩ := cutProfile_lipschitzOn_Icc
  have hglob := cutProfile_lipschitz hK
  refine ⟨max ((K : ℝ) / R) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x y
  have hstep : (K : ℝ) * |eucNorm x / R - eucNorm y / R|
      = ((K : ℝ) / R) * |eucNorm x - eucNorm y| := by
    rw [← sub_div, abs_div, abs_of_pos hR]
    ring
  calc |eucCutoff R x - eucCutoff R y|
      = |cutProfile (eucNorm x / R) - cutProfile (eucNorm y / R)| := by simp only [eucCutoff]
    _ ≤ (K : ℝ) * |eucNorm x / R - eucNorm y / R| := hglob _ _
    _ = ((K : ℝ) / R) * |eucNorm x - eucNorm y| := hstep
    _ ≤ ((K : ℝ) / R) * eucNorm (x - y) :=
        mul_le_mul_of_nonneg_left (abs_eucNorm_sub_le' x y) (div_nonneg K.coe_nonneg (le_of_lt hR))
    _ ≤ max ((K : ℝ) / R) 1 * eucNorm (x - y) :=
        mul_le_mul_of_nonneg_right
          (le_max_left ((K : ℝ) / R) 1) (eucNorm_nonneg _)

end Work.CR.Flat.Cauchy.bmCz
