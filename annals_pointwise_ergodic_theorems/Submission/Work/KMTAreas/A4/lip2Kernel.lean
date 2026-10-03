/-
# The smoothing-window package of Proposition `lip-2` (`Work.KMTAreas.A4.lip2Kernel`)

This module collects the elementary properties of the normalized reproducing window

  `win M γ m = M⁻¹ ψ(m/M) e(m γ)`     (`ψ = lipSchPsi = 𝓕⁻ lipSchChi`)

and of its `ℤ`-Fourier transform

  `winFT M s t = ∑_n lipSchChi (M (t - s + n))`

which the inverse Weyl estimate `Work.KMTAreas.A4.lip2Weyl` (and the alternate inverse theorem
`lip-2` of Krause–Mirek–Tao §5.2) use:

* `win M γ ∈ ℓ¹(ℤ)` for `M ≥ 1`, with a bound uniform in `M` and `γ`
  (`win_summable`, `win_tsum_le`); both are immediate from the Schwartz decay
  `‖ψ t‖ ≤ 2 ^ 12 (S + 1) ⟨t⟩^{-12}` and the uniform lattice-sum bound
  `ε ∑_{m ∈ ℤ} ⟨ε m⟩^{-12} ≤ 2 ^ 61` of `ε_tsum_jbDecay_twelve_int_le` (for `0 < ε ≤ 1`);
* the Poisson-summation identity `𝓕_ℤ (win M γ) (t) = winFT M s t` for `γ = (s mod 1)`
  (`winZFourier`, a child lemma — it is Mathlib's Poisson summation applied to the modulated
  dilated Schwartz function `x ↦ e^{-2πi(t-s)x} ψ(x/M)`, via
  `Work.KMTAreas.A4.lipPoissonMultiplier`);
* `winFT` is real-valued and non-negative, equals `1` on the central arc `|M(t - s)| ≤ 1/2`, and
  is bounded by `1` when `M ≥ 2` (`winFT_re_nonneg`, `winFT_eq_one`, `winFT_norm_le_one`).

The last three facts rest on the observation that for `M ≠ 0` the summands
`n ↦ lipSchChi (M (t - s + n))` are supported in the interval `|t - s + n| < 1/|M|`, and that for
`M ≥ 2` at most one of them is nonzero (`winFT_subsingleton`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.winZFourier

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Pointwise properties of the cut-off `lipSchChi` -/

theorem lipSchChi_re (z : ℝ) : (lipSchChi z).re = lipSchBump z := by
  rw [lipSchChi_apply, lipSchBumpFun]; simp

theorem lipSchChi_nonneg (z : ℝ) : 0 ≤ (lipSchChi z).re := by
  rw [lipSchChi_re]; exact ContDiffBump.nonneg lipSchBump

theorem lipSchChi_norm_le_one (z : ℝ) : ‖lipSchChi z‖ ≤ 1 := by
  rw [lipSchChi_apply, lipSchBumpFun]
  rw [show ‖(((lipSchBump z : ℝ)) : ℂ)‖ = |lipSchBump z| by simp]
  rw [abs_of_nonneg (ContDiffBump.nonneg lipSchBump)]
  exact ContDiffBump.le_one lipSchBump

theorem lipSchChi_eq_one {z : ℝ} (hz : |z| ≤ 1 / 2) : lipSchChi z = 1 := by
  rw [lipSchChi_apply, lipSchBumpFun]
  have hmem : z ∈ Metric.closedBall (0 : ℝ) lipSchBump.rIn := by
    rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, sub_zero, lipSchBump_rIn]
    exact hz
  rw [ContDiffBump.one_of_mem_closedBall lipSchBump hmem]
  norm_num

/-! ## Norm and summability of the window -/

theorem norm_win (M : ℝ) (hM : 0 < M) (γ : FreqCircle) (m : ℤ) :
    ‖win M γ m‖ = M⁻¹ * ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖ := by
  have hf : ‖(fourier m γ : ℂ)‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
  rw [win, norm_mul, norm_mul, hf, mul_one]
  rw [norm_inv, show ‖((M : ℝ) : ℂ)‖ = |M| by simp, abs_of_pos hM]

theorem win_summable (M : ℝ) (hM : 1 ≤ M) (γ : FreqCircle) :
    Summable (fun m : ℤ => ‖win M γ m‖) := by
  have hMpos : 0 < M := by linarith
  have hε0 : 0 < M⁻¹ := inv_pos.mpr hMpos
  have hdec : ∀ m : ℤ,
      ‖(lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖
        ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) * jbDecay 12 (M⁻¹ * (m : ℝ)) :=
    fun m => schwartz_decay lipSchPsi _
  have hbase : Summable (fun m : ℤ => jbDecay 12 (M⁻¹ * (m : ℝ))) :=
    (summable_jbDecay_twelve_shift hε0 (0 : ℤ)).congr (fun m => by simp)
  have hmaj : Summable (fun m : ℤ =>
      M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)
        * jbDecay 12 (M⁻¹ * (m : ℝ)))) :=
    (hbase.mul_left ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1))).mul_left M⁻¹
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
  rw [norm_win M hMpos γ m, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hdec m) hε0.le

theorem win_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (γ : FreqCircle), 1 ≤ M →
      (∑' m : ℤ, ‖win M γ m‖) ≤ C := by
  have hCpos : 0 < (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) := by
    have := schwartzSeminormSum_nonneg lipSchPsi; positivity
  refine ⟨(2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) * (2 : ℝ) ^ 61,
    by positivity, fun M γ hM => ?_⟩
  have hMpos : 0 < M := by linarith
  have hε0 : 0 < M⁻¹ := inv_pos.mpr hMpos
  have hε1 : M⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hMpos]; exact hM
  have hdec : ∀ m : ℤ,
      ‖(lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖
        ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) * jbDecay 12 (M⁻¹ * (m : ℝ)) :=
    fun m => schwartz_decay lipSchPsi _
  have hbase : Summable (fun m : ℤ => jbDecay 12 (M⁻¹ * (m : ℝ))) :=
    (summable_jbDecay_twelve_shift hε0 (0 : ℤ)).congr (fun m => by simp)
  have hmaj : Summable (fun m : ℤ =>
      M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)
        * jbDecay 12 (M⁻¹ * (m : ℝ)))) :=
    (hbase.mul_left ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1))).mul_left M⁻¹
  have hsum1 : Summable (fun m : ℤ => M⁻¹ * ‖(lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg hε0.le (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (hdec m) hε0.le) hmaj
  calc ∑' m : ℤ, ‖win M γ m‖
      = ∑' m : ℤ, M⁻¹ * ‖(lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖ := by
        refine tsum_congr fun m => ?_
        rw [norm_win M hMpos γ m, div_eq_inv_mul]
    _ ≤ ∑' m : ℤ, M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)
          * jbDecay 12 (M⁻¹ * (m : ℝ))) :=
        Summable.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left (hdec m) hε0.le) hsum1 hmaj
    _ = ∑' m : ℤ, (M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)))
          * jbDecay 12 (M⁻¹ * (m : ℝ)) := by
        refine tsum_congr fun m => ?_
        ring
    _ = (M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)))
          * ∑' m : ℤ, jbDecay 12 (M⁻¹ * (m : ℝ)) := tsum_mul_left
    _ = ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1))
          * (M⁻¹ * ∑' m : ℤ, jbDecay 12 (M⁻¹ * (m : ℝ))) := by ring
    _ ≤ ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)) * (2 : ℝ) ^ 61 :=
        mul_le_mul_of_nonneg_left (eps_tsum_jbDecay_twelve_int_le hε0 hε1) hCpos.le

/-! ## The support of `winFT` and its pointwise properties -/

/-- A term of `winFT` vanishes unless `|t - s + n| < 1/|M|`. -/
theorem winFT_term_eq_zero {M s t : ℝ} (hM : M ≠ 0) {n : ℤ}
    (hn : 1 / |M| ≤ |t - s + (n : ℝ)|) : lipSchChi (M * (t - s + n)) = 0 := by
  apply lipSchChi_eq_zero
  have hMpos : 0 < |M| := abs_pos.mpr hM
  have h3 : |M| * (1 / |M|) ≤ |M| * |t - s + (n : ℝ)| :=
    mul_le_mul_of_nonneg_left hn hMpos.le
  have h4 : |M| * (1 / |M|) = 1 := by
    rw [mul_one_div, div_self (ne_of_gt hMpos)]
  rw [abs_mul]
  rw [← h4]
  exact h3

/-- Conversely, a nonzero term of `winFT` forces `|t - s + n| < 1/|M|`. -/
theorem winFT_term_nonzero {M s t : ℝ} (hM : M ≠ 0) {n : ℤ}
    (hn : lipSchChi (M * (t - s + n)) ≠ 0) : |t - s + (n : ℝ)| < 1 / |M| := by
  by_contra h
  push Not at h
  exact hn (winFT_term_eq_zero hM h)

/-- `winFT` is a finite sum over the integers `n` with `|n| ≤ ⌈|t - s| + 1/|M|⌉` (for `M ≠ 0`). -/
theorem winFT_eq_sum_Icc {M s t : ℝ} (hM : M ≠ 0) :
    winFT M s t
      = ∑ n ∈ Finset.Icc (-(⌈|t - s| + 1 / |M|⌉ : ℤ)) (⌈|t - s| + 1 / |M|⌉ : ℤ),
          lipSchChi (M * (t - s + n)) := by
  show (∑' n : ℤ, lipSchChi (M * (t - s + (n : ℝ))))
      = ∑ n ∈ Finset.Icc (-(⌈|t - s| + 1 / |M|⌉ : ℤ)) (⌈|t - s| + 1 / |M|⌉ : ℤ),
          lipSchChi (M * (t - s + n))
  refine tsum_eq_sum fun n hn => ?_
  apply winFT_term_eq_zero hM
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  have hle : |t - s| + 1 / |M| ≤ ((⌈|t - s| + 1 / |M|⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hgt : ((⌈|t - s| + 1 / |M|⌉ : ℤ) : ℝ) < |(n : ℝ)| := by
    rcases hn with h | h
    · have h' : (n : ℝ) < -(((⌈|t - s| + 1 / |M|⌉ : ℤ)) : ℝ) := by exact_mod_cast h
      have : (((⌈|t - s| + 1 / |M|⌉ : ℤ)) : ℝ) < ((-n : ℤ) : ℝ) := by
        push_cast
        linarith
      calc ((⌈|t - s| + 1 / |M|⌉ : ℤ) : ℝ) < ((-n : ℤ) : ℝ) := this
        _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast neg_le_abs n
        _ = |(n : ℝ)| := Int.cast_abs
    · have h' : (((⌈|t - s| + 1 / |M|⌉ : ℤ)) : ℝ) < (n : ℝ) := by exact_mod_cast h
      calc ((⌈|t - s| + 1 / |M|⌉ : ℤ) : ℝ) < (n : ℝ) := h'
        _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast le_abs_self n
        _ = |(n : ℝ)| := Int.cast_abs
  have hgoal : 1 / |M| ≤ |t - s + (n : ℝ)| := by
    have h1 : |(n : ℝ)| - |t - s| ≤ |t - s + (n : ℝ)| := by
      have h := abs_add_le (t - s + (n : ℝ)) (-(t - s))
      rw [abs_neg] at h
      have hh : t - s + (n : ℝ) + -(t - s) = (n : ℝ) := by ring
      rw [hh] at h
      linarith
    linarith
  exact hgoal

/-- `winFT` takes values in `[0, ∞)`. -/
theorem winFT_re_nonneg (M s t : ℝ) : 0 ≤ (winFT M s t).re := by
  rcases eq_or_ne M 0 with hM | hM
  · subst hM
    rw [show winFT 0 s t = ∑' n : ℤ, (1 : ℂ) from by
      show (∑' n : ℤ, lipSchChi (0 * (t - s + (n : ℝ)))) = _
      simp only [zero_mul, lipSchChi_zero]]
    rw [tsum_eq_zero_of_not_summable (f := fun _ : ℤ => (1 : ℂ))]
    · simp
    · intro h
      exact one_ne_zero ((summable_const_iff (1 : ℂ)).mp h)
  · rw [winFT_eq_sum_Icc hM, Complex.re_sum]
    exact Finset.sum_nonneg fun n _ => lipSchChi_nonneg _

/-- On the central arc, `winFT` is exactly `1` (the reproducing property). -/
theorem winFT_eq_one {M s t : ℝ} (hM : 2 ≤ M) (hts : |M * (t - s)| ≤ 1 / 2) :
    winFT M s t = 1 := by
  have hMpos : 0 < M := by linarith
  have hcentral : lipSchChi (M * (t - s + (0 : ℤ))) = 1 := by
    apply lipSchChi_eq_one
    simpa using hts
  show (∑' n : ℤ, lipSchChi (M * (t - s + (n : ℝ)))) = 1
  rw [tsum_eq_single 0 (fun n hn => ?_), hcentral]
  apply winFT_term_eq_zero (ne_of_gt hMpos)
  have hts' : |t - s| ≤ 1 / (2 * M) := by
    have h : M * |t - s| ≤ 1 / 2 := by
      have h2 : |M * (t - s)| = M * |t - s| := by rw [abs_mul, abs_of_pos hMpos]
      rw [h2] at hts; exact hts
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have h : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast h
  have hb : |t - s| + 1 / M ≤ 3 / 4 := by
    have h1 : 3 / (2 * M) ≤ 3 / 4 := by
      rw [div_le_div_iff_of_pos_left (by norm_num : (0:ℝ) < 3) (by positivity) (by norm_num)]
      linarith
    have h2 : |t - s| + 1 / M ≤ 1 / (2 * M) + 1 / M := by linarith
    have h3 : 1 / (2 * M) + 1 / M = 3 / (2 * M) := by field_simp; ring
    linarith
  have h1 : |(n : ℝ)| - |t - s| ≤ |t - s + (n : ℝ)| := by
    have h := abs_add_le (t - s + (n : ℝ)) (-(t - s))
    rw [abs_neg] at h
    have hh : t - s + (n : ℝ) + -(t - s) = (n : ℝ) := by ring
    rw [hh] at h
    linarith
  have : 1 / |M| ≤ |t - s + (n : ℝ)| := by
    rw [abs_of_pos hMpos]
    linarith
  exact this

/-- For `M ≥ 2` at most one summand of `winFT` is nonzero. -/
theorem winFT_subsingleton {M s t : ℝ} (hM : 2 ≤ M) :
    ∀ n n' : ℤ, lipSchChi (M * (t - s + n)) ≠ 0 →
      lipSchChi (M * (t - s + n')) ≠ 0 → n = n' := by
  intro n n' hn hn'
  have hMpos : 0 < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have h1 := winFT_term_nonzero hMne hn
  have h2 := winFT_term_nonzero hMne hn'
  have hcast : ((n - n' : ℤ) : ℝ) = (n : ℝ) - (n' : ℝ) := by push_cast; ring
  have habs : |(n : ℝ) - (n' : ℝ)| < 1 := by
    have h3 : (n : ℝ) - (n' : ℝ) = (t - s + (n : ℝ)) - (t - s + (n' : ℝ)) := by ring
    rw [h3]
    have h4 : |(t - s + (n : ℝ)) - (t - s + (n' : ℝ))|
        ≤ |t - s + (n : ℝ)| + |t - s + (n' : ℝ)| := by
      have h := abs_add_le (t - s + (n : ℝ)) (-(t - s + (n' : ℝ)))
      rw [abs_neg] at h
      have hh : t - s + (n : ℝ) + -(t - s + (n' : ℝ))
          = (t - s + (n : ℝ)) - (t - s + (n' : ℝ)) := by ring
      rwa [hh] at h
    have h5 : |t - s + (n : ℝ)| < 1 / M := by rwa [abs_of_pos hMpos] at h1
    have h6 : |t - s + (n' : ℝ)| < 1 / M := by rwa [abs_of_pos hMpos] at h2
    have h7 : 1 / M ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hM
    linarith
  have h5 : (((|n - n'| : ℤ)) : ℝ) < 1 := by
    rw [Int.cast_abs, hcast]
    exact habs
  have : |n - n'| < 1 := by exact_mod_cast h5
  have : n - n' = 0 := Int.abs_lt_one_iff.mp this
  exact sub_eq_zero.mp this

/-- `winFT` is bounded by `1` for `M ≥ 2`. -/
theorem winFT_norm_le_one {M s t : ℝ} (hM : 2 ≤ M) : ‖winFT M s t‖ ≤ 1 := by
  show ‖(∑' n : ℤ, lipSchChi (M * (t - s + (n : ℝ))))‖ ≤ 1
  by_cases h : ∃ n : ℤ, lipSchChi (M * (t - s + n)) ≠ 0
  · obtain ⟨n₀, hn₀⟩ := h
    rw [tsum_eq_single n₀ (fun n hn => ?_)]
    · exact lipSchChi_norm_le_one _
    · by_contra hne
      exact hn (winFT_subsingleton hM n₀ n hn₀ hne).symm
  · push Not at h
    rw [tsum_congr (fun n => h n), tsum_zero, norm_zero]
    norm_num

/-! ## The window package -/

theorem lip2Kernel :
    (∀ (M : ℝ) (γ : Work.Analysis.InverseTheory.FreqCircle), 1 ≤ M →
      Summable (fun m : ℤ => ‖Work.KMTAreas.A4.win M γ m‖)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (γ : Work.Analysis.InverseTheory.FreqCircle), 1 ≤ M →
      (∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖) ≤ C) ∧
    (∀ (M s : ℝ) (γ : Work.Analysis.InverseTheory.FreqCircle),
      ((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle) = γ → 0 < M → ∀ t : ℝ,
      Work.Analysis.InverseTheory.ZFourier (Work.KMTAreas.A4.win M γ)
        ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle)
        = Work.KMTAreas.A4.winFT M s t) ∧
    (∀ (M s t : ℝ), 0 ≤ (Work.KMTAreas.A4.winFT M s t).re) ∧
    (∀ (M s t : ℝ), 2 ≤ M → |M * (t - s)| ≤ 1 / 2 → Work.KMTAreas.A4.winFT M s t = 1) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (M s t : ℝ), 2 ≤ M → ‖Work.KMTAreas.A4.winFT M s t‖ ≤ C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun M γ hM => win_summable M hM γ
  · exact win_tsum_le
  · intro M s γ hγ hM t
    rw [← hγ]
    exact winZFourier M s t hM
  · exact winFT_re_nonneg
  · exact fun M s t hM hts => winFT_eq_one hM hts
  · exact ⟨1, one_pos, fun M s t hM => winFT_norm_le_one hM⟩

end Work.KMTAreas.A4
