import Mathlib
import Submission.Work.Repel.counting

/-!
# REPEL: the level-0 box window

Shishikura §6, Step 3 (level-0 count).  The box

`box η n = {z | n + 1/6 < Re z < n + 1/3, η + log(1/2)/2π < Im z < η + log(3/2)/2π}`

is a small open rectangle of width `1/6` in `Re` and of height `< 1/8` in `Im`, centred at
height `η`.  We show that at least `η/5` of its integer translates `n` sit inside the
counting disc `Dflat η = closedBall (iη) (|η|/8)`.

This is the level-0 factor of the cell count of `Work.Repel.boxes`.
-/

namespace Work.Repel

open Complex Set Metric

/-- `log 2 / 2π ≤ 1/8`. -/
private lemma log_two_div_two_pi_le : Real.log 2 / (2 * Real.pi) ≤ 1 / 8 := by
  have h4 : 4 * Real.log 2 < Real.pi := by
    have h1 := Real.log_two_lt_d9
    have h2 := Real.pi_gt_d6
    linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  linarith

/-- `log (1/2) / 2π = -(log 2 / 2π)`. -/
private lemma log_half_div_eq : Real.log (1 / 2 : ℝ) / (2 * Real.pi)
    = -(Real.log 2 / (2 * Real.pi)) := by
  have h : Real.log (1 / 2 : ℝ) = -(Real.log 2) := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  rw [h]; ring

/-- `box η n` is a non-empty open rectangle (e.g. `(n + 1/4) + iη` lies in it). -/
lemma box_nonempty (η : ℝ) (n : ℤ) : (box η n).Nonempty := by
  refine ⟨⟨(n : ℝ) + 1 / 4, η⟩, ?_⟩
  simp only [box, Set.mem_ofPred_eq]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have h : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    have h2 : 0 < 2 * Real.pi := by positivity
    have := div_neg_of_neg_of_pos h h2
    linarith
  · have h : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
    have h2 : 0 < 2 * Real.pi := by positivity
    have := div_pos h h2
    linarith

/-- For `z ∈ box η n`, `|Re z| < |n| + 1/3`. -/
lemma box_re_abs_lt {η : ℝ} {n : ℤ} {z : ℂ} (hz : z ∈ box η n) :
    |z.re| < |(n : ℝ)| + 1 / 3 := by
  obtain ⟨h1, h2, -, -⟩ := hz
  have hsel : |z.re - (n : ℝ)| < 1 / 3 := by
    rw [abs_lt]; constructor <;> linarith
  calc |z.re| = |(z.re - (n : ℝ)) + (n : ℝ)| := by rw [sub_add_cancel]
    _ ≤ |z.re - (n : ℝ)| + |(n : ℝ)| := abs_add_le _ _
    _ < 1 / 3 + |(n : ℝ)| := by linarith
    _ = |(n : ℝ)| + 1 / 3 := by ring

/-- For `z ∈ box η n`, `|Im z - η| < log 2 / 2π`. -/
lemma box_im_abs_lt {η : ℝ} {n : ℤ} {z : ℂ} (hz : z ∈ box η n) :
    |z.im - η| < Real.log 2 / (2 * Real.pi) := by
  obtain ⟨-, -, h3, h4⟩ := hz
  have h32 : Real.log (3 / 2 : ℝ) / (2 * Real.pi) < Real.log 2 / (2 * Real.pi) :=
    div_lt_div_of_pos_right (Real.log_lt_log (by norm_num) (by norm_num)) (by positivity)
  rw [log_half_div_eq] at h3
  rw [abs_lt]
  constructor <;> linarith

theorem box_window_count (η : ℝ) (hη : 100 ≤ η) :
    ∃ T : Finset ℤ, η / 5 ≤ (T.card : ℝ) ∧
      ∀ n ∈ T, Work.Repel.box η n ⊆ Work.Repel.Dflat η ∧ (Work.Repel.box η n).Nonempty := by
  classical
  set c : ℝ := Real.log 2 / (2 * Real.pi) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hc_le : c ≤ 1 / 8 := by rw [hcdef]; exact log_two_div_two_pi_le
  have hc2 : c ^ 2 ≤ 1 / 64 := by nlinarith [hcpos, hc_le]
  -- the integer window `[-M, M]`
  set M : ℤ := ⌊η / 10⌋ + 1 with hMdef
  have hMge : η / 10 ≤ (M : ℝ) := by
    have h := Int.lt_floor_add_one (η / 10)
    rw [hMdef]; push_cast; linarith
  have hMle : (M : ℝ) ≤ η / 10 + 1 := by
    have h := Int.floor_le (η / 10)
    rw [hMdef]; push_cast; linarith
  have hMnneg : (0 : ℝ) ≤ (M : ℝ) := by linarith [hMge, hη]
  have hMint : (0 : ℤ) ≤ M := by exact_mod_cast hMnneg
  -- the key numeric inequality
  have hkey : ((M : ℝ) + 1 / 3) ^ 2 + c ^ 2 ≤ (η / 8) ^ 2 := by
    have h1 : ((M : ℝ) + 1 / 3) ^ 2 ≤ (η / 10 + 4 / 3) ^ 2 := by
      have hle : (M : ℝ) + 1 / 3 ≤ η / 10 + 4 / 3 := by linarith
      have hnn : (0 : ℝ) ≤ (M : ℝ) + 1 / 3 := by linarith
      nlinarith
    have h3 : (η / 10 + 4 / 3) ^ 2 + c ^ 2 ≤ (η / 8) ^ 2 := by nlinarith [hη, hc2]
    linarith
  refine ⟨Finset.Icc (-M) M, ?_, ?_⟩
  · have hcardZ : ((Finset.Icc (-M) M).card : ℤ) = 2 * M + 1 := by
      have h := Int.card_Icc_of_le (-M) M (by omega)
      calc (Finset.Icc (-M) M).card = M + 1 - (-M) := h
        _ = 2 * M + 1 := by ring
    have hcard : ((Finset.Icc (-M) M).card : ℝ) = 2 * (M : ℝ) + 1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
      push_cast at this
      exact this
    rw [hcard]
    linarith [hMge]
  · intro n hn
    have hn' : -M ≤ n ∧ n ≤ M := Finset.mem_Icc.mp hn
    have habs : |(n : ℝ)| ≤ (M : ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast hn'.1, by exact_mod_cast hn'.2⟩
    refine ⟨?_, box_nonempty η n⟩
    intro z hz
    rw [Dflat, Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ η)]
    have hre : |z.re| < (M : ℝ) + 1 / 3 :=
      lt_of_lt_of_le (box_re_abs_lt hz) (by linarith)
    have him : |z.im - η| < c := by rw [hcdef]; exact box_im_abs_lt hz
    have hnorm : ‖z - Complex.I * η‖ ^ 2 = z.re ^ 2 + (z.im - η) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im]
      ring
    have hgoal2 : ‖z - Complex.I * η‖ ^ 2 < (η / 8) ^ 2 := by
      rw [hnorm]
      have h1 : z.re ^ 2 < ((M : ℝ) + 1 / 3) ^ 2 := by
        have := pow_lt_pow_left₀ hre (abs_nonneg z.re) (by norm_num : (2 : ℕ) ≠ 0)
        rwa [sq_abs] at this
      have h2 : (z.im - η) ^ 2 < c ^ 2 := by
        have := pow_lt_pow_left₀ him (abs_nonneg (z.im - η)) (by norm_num : (2 : ℕ) ≠ 0)
        rwa [sq_abs] at this
      linarith [hkey]
    have hlt : ‖z - Complex.I * η‖ < η / 8 := by
      have hh := sq_lt_sq.mp hgoal2
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0 : ℝ) ≤ η / 8)] at hh
      exact hh
    exact le_of_lt hlt

end Work.Repel
