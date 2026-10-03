import Mathlib

namespace Work.FIArea6Hecke.R

/-! ### The comparison function

Throughout, `cPU z = (z + 1/2)^2 + 16 i` and
`cWU B₁ B₂ z = 2M · exp((3/2 - z)·log 2) · cPU z`, `M = B₁/2 + B₂/4`.  This is the comparison
function of `Work.FIArea6Hecke.R.strip_bound_of_two_lines` with the modulus-dependent factor
`(4d)^2` replaced by `log 2`, which is what makes the resulting constant absolute.
-/

/-- The quadratic factor `(z + 1/2)^2 + 16 i` of the comparison function. -/
private noncomputable def cPU (z : ℂ) : ℂ := (z + (1 / 2 : ℂ)) ^ 2 + 16 * Complex.I

/-- The comparison function of the uniform Phragmén–Lindelöf bound. -/
private noncomputable def cWU (B₁ B₂ : ℝ) (z : ℂ) : ℂ :=
  ((2 * (B₁ / 2 + B₂ / 4) : ℝ) : ℂ)
    * Complex.exp ((((3 / 2 : ℝ) : ℂ) - z) * (Real.log 2 : ℂ)) * cPU z

private lemma cWU_arg_re (z : ℂ) :
    ((((3 / 2 : ℝ) : ℂ) - z) * (Real.log 2 : ℂ)).re = (3 / 2 - z.re) * Real.log 2 := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

private lemma exp_two_log_two : Real.exp (2 * Real.log 2) = 4 := by
  rw [two_mul, Real.exp_add, Real.exp_log (by norm_num)]
  norm_num

/-- Norm formula for the comparison function (with `0 ≤ B₁`, `0 ≤ B₂`). -/
private lemma cWU_norm (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (z : ℂ) :
    ‖cWU B₁ B₂ z‖
      = 2 * (B₁ / 2 + B₂ / 4) * Real.exp ((3 / 2 - z.re) * Real.log 2) * ‖cPU z‖ := by
  have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
  rw [cWU, norm_mul, norm_mul, Complex.norm_of_nonneg h2M, Complex.norm_exp, cWU_arg_re]

/-! ### Elementary estimates for the quadratic factor -/

/-- Auxiliary computation: the complex number `(t·i)^2 + 16 i` has real part `-t²`,
imaginary part `16`, hence squared norm `t⁴ + 256`. -/
private lemma one_add_abs_sq_le_two_norm' (t : ℝ) :
    (1 + |t|) ^ 2 ≤ 2 * ‖((t : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
  set z : ℂ := ((t : ℂ) * Complex.I) ^ 2 + 16 * Complex.I with hz
  have hre : z.re = -(t ^ 2) := by
    rw [hz]
    norm_num [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have him : z.im = 16 := by
    rw [hz]
    norm_num [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have hns : Complex.normSq z = t ^ 4 + 256 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hnorm2 : ‖z‖ ^ 2 = t ^ 4 + 256 := by
    rw [← Complex.normSq_eq_norm_sq, hns]
  have hzn : ‖z‖ = Real.sqrt (t ^ 4 + 256) := by
    have h2' : ‖z‖ ^ 2 = (Real.sqrt (t ^ 4 + 256)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]; exact hnorm2
    have habs : |‖z‖| = |Real.sqrt (t ^ 4 + 256)| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h2'
    rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  rw [hzn]
  by_cases h : |t| ≤ 4
  · have h1 : (1 + |t|) ^ 2 ≤ 25 := by nlinarith [abs_nonneg t, h]
    have h16 : (16 : ℝ) ≤ Real.sqrt (t ^ 4 + 256) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [sq_nonneg t]
    linarith
  · have hu : (4 : ℝ) ≤ |t| := by
      have : (4 : ℝ) < |t| := not_le.mp h; linarith
    have h1 : (1 + |t|) ^ 2 ≤ 2 * |t| ^ 2 := by nlinarith [abs_nonneg t, hu]
    have hle : |t| ^ 2 ≤ Real.sqrt (t ^ 4 + 256) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have hs : (|t| ^ 2) ^ 2 = t ^ 4 := by rw [sq_abs]; ring
      rw [hs]; linarith [sq_nonneg t]
    linarith

/-- `|(z + 1/2)^2 + 16 i| ≥ 1` on the closed strip `-1/2 ≤ re z ≤ 3/2`. -/
private lemma cPU_ge_one (z : ℂ) (h1 : -1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 2) :
    1 ≤ ‖cPU z‖ := by
  rw [cPU]
  let w : ℂ := z + (1 / 2 : ℂ)
  have hwre : w.re = z.re + 1 / 2 := by simp [w]
  have ha0 : 0 ≤ w.re := by rw [hwre]; linarith
  have ha2 : w.re ≤ 2 := by rw [hwre]; linarith
  have hre : (w ^ 2 + 16 * Complex.I).re = w.re ^ 2 - w.im ^ 2 := by
    have h16 : (16 : ℂ).im = 0 := by norm_num
    have h16' : (16 : ℂ).re = 16 := by norm_num
    simp only [Complex.add_re, sq, Complex.mul_re, h16, h16', Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
  have him : (w ^ 2 + 16 * Complex.I).im = 2 * w.re * w.im + 16 := by
    have h16 : (16 : ℂ).im = 0 := by norm_num
    have h16' : (16 : ℂ).re = 16 := by norm_num
    simp only [Complex.add_im, sq, Complex.mul_im, h16, h16', Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero]
    ring
  have hns : Complex.normSq (w ^ 2 + 16 * Complex.I)
      = (w.re ^ 2 - w.im ^ 2) ^ 2 + (2 * w.re * w.im + 16) ^ 2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hkey : 1 ≤ Complex.normSq (w ^ 2 + 16 * Complex.I) := by
    rw [hns]
    rcases lt_or_ge w.im 3 with hb3 | hb3
    · rcases lt_or_ge w.im (-3) with hb3' | hb3'
      · have hb2 : 9 ≤ w.im ^ 2 := by nlinarith [sq_nonneg (w.im + 3)]
        have ha2sq : w.re ^ 2 ≤ 4 := by
          nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ 2 - w.re by linarith)]
        nlinarith [sq_nonneg (w.re ^ 2 - w.im ^ 2 + 5), sq_nonneg (2 * w.re * w.im + 16)]
      · have hab : -6 ≤ w.re * w.im := by
          nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ w.im + 3 by linarith)]
        nlinarith [sq_nonneg (w.re ^ 2 - w.im ^ 2), sq_nonneg (2 * w.re * w.im + 16 - 4)]
    · have hb2 : 9 ≤ w.im ^ 2 := by nlinarith [sq_nonneg (w.im - 3)]
      have ha2sq : w.re ^ 2 ≤ 4 := by
        nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ 2 - w.re by linarith)]
      nlinarith [sq_nonneg (w.re ^ 2 - w.im ^ 2 + 5), sq_nonneg (2 * w.re * w.im + 16)]
  have hsq : 1 ≤ ‖w ^ 2 + 16 * Complex.I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact hkey
  have hfin : 1 ≤ ‖w ^ 2 + 16 * Complex.I‖ := by
    rw [one_le_sq_iff_one_le_abs] at hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using hsq
  simpa [w] using hfin

private lemma shiftPU_re (σ t : ℝ) :
    (((σ : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ)).re = σ + 1 / 2 := by
  simp

private lemma shiftPU_im (σ t : ℝ) :
    (((σ : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ)).im = t := by
  simp

private lemma shiftPU_normSq (σ t : ℝ) :
    ‖(((σ : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ))‖ ^ 2
      = (σ + 1 / 2) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, shiftPU_re, shiftPU_im]
  ring

/-- `|(z + 1/2)^2 + 16 i| ≤ 20 (1 + |t|)^2` on the target strip `1/2 ≤ σ ≤ 1`, `z = σ + t i`. -/
private lemma cPU_le_target (σ t : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    ‖cPU ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 20 * (1 + |t|) ^ 2 := by
  rw [cPU]
  set s : ℂ := ((σ : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ)
  have hssq : ‖s‖ ^ 2 ≤ (3 / 2) ^ 2 + t ^ 2 := by
    rw [show ‖s‖ ^ 2 = (σ + 1 / 2) ^ 2 + t ^ 2 from by
      rw [show s = ((σ : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ) from rfl,
        shiftPU_normSq]]
    have hle' : σ + 1 / 2 ≤ 3 / 2 := by linarith
    have h0 : (0 : ℝ) ≤ σ + 1 / 2 := by linarith
    have hpow := pow_le_pow_left₀ h0 hle' 2
    linarith
  have htri : ‖s ^ 2 + 16 * Complex.I‖ ≤ ‖s ^ 2‖ + ‖(16 : ℂ) * Complex.I‖ := norm_add_le _ _
  have hp : ‖s ^ 2‖ = ‖s‖ ^ 2 := by rw [norm_pow]
  have h16 : ‖(16 : ℂ) * Complex.I‖ = 16 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hfinal : (3 / 2) ^ 2 + t ^ 2 + 16 ≤ 20 * (1 + |t|) ^ 2 := by
    nlinarith [sq_nonneg t, abs_nonneg t, sq_abs t]
  calc ‖s ^ 2 + 16 * Complex.I‖ ≤ ‖s ^ 2‖ + ‖(16 : ℂ) * Complex.I‖ := htri
    _ = ‖s‖ ^ 2 + 16 := by rw [hp, h16]
    _ ≤ (3 / 2) ^ 2 + t ^ 2 + 16 := by linarith [hssq]
    _ ≤ 20 * (1 + |t|) ^ 2 := hfinal

/-! ### The uniform two-lines Phragmén–Lindelöf bound -/

/-- **A two-lines Phragmén–Lindelöf bound, uniform in all parameters (`d`-free constant).**
There is an absolute constant `C > 0` such that for every entire `f` with `‖f(3/2+it)‖ ≤ B₁` and
`‖f(-1/2+it)‖ ≤ B₂·(1+|t|)²` on the two vertical lines and linear exponential growth inside the
strip, one has `‖f(σ+it)‖ ≤ C·(B₁+B₂)·(1+|t|)^10` for `1/2 ≤ σ ≤ 1`.  The point (as opposed to
`Work.FIArea6Hecke.R.strip_bound_of_two_lines`, which is stated with the specific factor `(4d)²` on
the left boundary, and to any per-`f` existential) is that `C` is a single absolute constant: it is
what makes the final strip bound uniform in the modulus `d`. -/
theorem strip_bound_of_two_lines_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ), AnalyticOn ℂ f Set.univ →
      ∀ (B₁ B₂ : ℝ), 0 < B₁ → 0 < B₂ →
      (∀ t : ℝ, ‖f (((3 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B₁) →
      (∀ t : ℝ, ‖f (((-1 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B₂ * (1 + |t|) ^ (2 : ℕ)) →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
        ‖f z‖ ≤ Real.exp (K * (1 + |z.im|))) →
      ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (B₁ + B₂) * (1 + |t|) ^ (10 : ℕ) := by
  refine ⟨80, by norm_num, ?_⟩
  intro f hf B₁ B₂ hB₁ hB₂ h1 h2 hg
  obtain ⟨K, hK0, hK⟩ := hg
  have hB₁' : (0 : ℝ) ≤ B₁ := le_of_lt hB₁
  have hB₂' : (0 : ℝ) ≤ B₂ := le_of_lt hB₂
  have hMpos : (0 : ℝ) < 2 * (B₁ / 2 + B₂ / 4) := by linarith
  have hW_diff : Differentiable ℂ (cWU B₁ B₂) := by
    unfold cWU cPU
    fun_prop
  have hW_an : AnalyticOn ℂ (cWU B₁ B₂) Set.univ :=
    hW_diff.differentiableOn.analyticOn isOpen_univ
  have hPge : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → (1 : ℝ) ≤ ‖cPU z‖ :=
    fun z hz1 hz2 => cPU_ge_one z hz1 hz2
  have hWne : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → cWU B₁ B₂ z ≠ 0 := by
    intro z hz1 hz2
    have hP : (1 : ℝ) ≤ ‖cPU z‖ := hPge z hz1 hz2
    have hPne : cPU z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hP
      linarith
    rw [cWU]
    exact mul_ne_zero (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hMpos)) (Complex.exp_ne_zero _)) hPne
  set U : Set ℂ := {z : ℂ | cWU B₁ B₂ z ≠ 0} with hUdef
  have hF_an : AnalyticOn ℂ (fun z => f z / cWU B₁ B₂ z) U := by
    refine AnalyticOn.div (hf.mono (Set.subset_univ U)) (hW_an.mono (Set.subset_univ U)) ?_
    intro z hz
    exact hz
  have hclo_sub : closure (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2)) ⊆ U := by
    refine fun z hz => ?_
    have hz' : z ∈ Complex.re ⁻¹' Set.Icc (-1 / 2) (3 / 2) :=
      closure_minimal
        (fun w hw => show w ∈ Complex.re ⁻¹' Set.Icc (-1 / 2) (3 / 2) from
          ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
        (IsClosed.preimage Complex.continuous_re isClosed_Icc) hz
    exact hWne z hz'.1 hz'.2
  have hF_dcl : DiffContOnCl ℂ (fun z => f z / cWU B₁ B₂ z)
      (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2)) := by
    refine ⟨hF_an.differentiableOn.mono ?_, hF_an.continuousOn.mono hclo_sub⟩
    intro z hz
    exact hWne z (le_of_lt hz.1) (le_of_lt hz.2)
  -- boundary, left line: `re z = -1/2`
  have hbd_a : ∀ z : ℂ, z.re = -1 / 2 → ‖f z / cWU B₁ B₂ z‖ ≤ 1 := by
    intro z hzr
    have hzdec : z = ((-1 : ℝ) / 2 : ℂ) + (z.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hzr]
      norm_num
    have hfz : ‖f z‖ ≤ B₂ * (1 + |z.im|) ^ 2 := by
      conv_lhs => rw [hzdec]
      exact h2 z.im
    have hPval : ‖cPU z‖ = ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
      have hzz : ((-1 : ℝ) / 2 : ℂ) + (z.im : ℂ) * Complex.I + 1 / 2 = (z.im : ℂ) * Complex.I := by
        norm_num
      conv_lhs => rw [cPU, hzdec, hzz]
    have hWval : ‖cWU B₁ B₂ z‖
        = 2 * (B₁ / 2 + B₂ / 4) * 4 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
      rw [cWU_norm B₁ B₂ hB₁' hB₂' z, hzr,
        show (3 / 2 : ℝ) - (-1 / 2) = 2 by norm_num, hPval, exp_two_log_two]
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [hWval]
    have hq := one_add_abs_sq_le_two_norm' z.im
    have hQnn : (0 : ℝ) ≤ ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := norm_nonneg _
    have hstep1 : B₂ * (1 + |z.im|) ^ 2 ≤ B₂ * (2 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖) :=
      mul_le_mul_of_nonneg_left hq hB₂'
    have hstep2 : B₂ * (2 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖)
        ≤ (2 * (B₁ / 2 + B₂ / 4) * 4) * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
      rw [show B₂ * (2 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖)
          = (B₂ * 2) * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ by ring]
      apply mul_le_mul_of_nonneg_right _ hQnn
      linarith
    exact le_trans hfz (le_trans hstep1 hstep2)
  -- boundary, right line: `re z = 3/2`
  have hbd_b : ∀ z : ℂ, z.re = 3 / 2 → ‖f z / cWU B₁ B₂ z‖ ≤ 1 := by
    intro z hzr
    have hzdec : z = (3 / 2 : ℂ) + (z.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hzr]
      norm_num
    have hfz : ‖f z‖ ≤ B₁ := by
      conv_lhs => rw [hzdec]
      exact h1 z.im
    have hPval : (1 : ℝ) ≤ ‖cPU z‖ := cPU_ge_one z (by rw [hzr]; norm_num) (by rw [hzr])
    have hWval : ‖cWU B₁ B₂ z‖ = 2 * (B₁ / 2 + B₂ / 4) * ‖cPU z‖ := by
      rw [cWU_norm B₁ B₂ hB₁' hB₂' z, hzr,
        show (3 / 2 : ℝ) - 3 / 2 = 0 by norm_num, zero_mul, Real.exp_zero]
      ring
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [hWval]
    have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
    calc ‖f z‖ ≤ B₁ := hfz
      _ ≤ 2 * (B₁ / 2 + B₂ / 4) * 1 := by linarith
      _ ≤ 2 * (B₁ / 2 + B₂ / 4) * ‖cPU z‖ := by
            exact mul_le_mul_of_nonneg_left hPval h2M
  -- growth condition
  have hgrowth : ∃ c < Real.pi / ((3 / 2 : ℝ) - (-1 / 2)), ∃ B' : ℝ,
      (fun z => f z / cWU B₁ B₂ z) =O[Filter.comap (abs ∘ Complex.im) Filter.atTop
        ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2))]
        fun z => Real.exp (B' * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, K, ?_⟩
    · rw [show (3 / 2 : ℝ) - (-1 / 2) = 2 by norm_num]
      linarith [Real.pi_gt_three]
    · rw [Asymptotics.isBigO_iff]
      refine ⟨1 / (2 * (B₁ / 2 + B₂ / 4)), ?_⟩
      refine Filter.Eventually.filter_mono inf_le_right ?_
      rw [Filter.eventually_principal]
      intro z hz
      have hzr1 : -1 / 2 ≤ z.re := le_of_lt hz.1
      have hzr2 : z.re ≤ 3 / 2 := le_of_lt hz.2
      have hfz : ‖f z‖ ≤ Real.exp (K * (1 + |z.im|)) := hK z hzr1 hzr2
      have hP1 : (1 : ℝ) ≤ ‖cPU z‖ := cPU_ge_one z hzr1 hzr2
      have hexp1 : (1 : ℝ) ≤ Real.exp ((3 / 2 - z.re) * Real.log 2) :=
        Real.one_le_exp (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
      have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
      have hWval := cWU_norm B₁ B₂ hB₁' hB₂' z
      have hWlb : 2 * (B₁ / 2 + B₂ / 4) ≤ ‖cWU B₁ B₂ z‖ := by
        rw [hWval]
        have hstep : (2 * (B₁ / 2 + B₂ / 4) * 1) * 1
            ≤ (2 * (B₁ / 2 + B₂ / 4) * Real.exp ((3 / 2 - z.re) * Real.log 2)) * ‖cPU z‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp1 h2M) hP1 zero_le_one (by positivity)
        simpa using hstep
      rw [norm_div, Real.norm_of_nonneg (Real.exp_nonneg _)]
      calc ‖f z‖ / ‖cWU B₁ B₂ z‖ ≤ Real.exp (K * (1 + |z.im|)) / (2 * (B₁ / 2 + B₂ / 4)) :=
            div_le_div₀ (Real.exp_nonneg _) hfz hMpos hWlb
        _ = (1 / (2 * (B₁ / 2 + B₂ / 4))) * Real.exp (K * (1 + |z.im|)) := by ring
        _ ≤ (1 / (2 * (B₁ / 2 + B₂ / 4))) * Real.exp (K * Real.exp (1 * |z.im|)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp.mpr
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hK0
  intro σ t hσ1 hσ2
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : z.re = σ := by rw [hz]; simp
  have hzim : z.im = t := by rw [hz]; simp
  have hza : -1 / 2 ≤ z.re := by rw [hzre]; linarith
  have hzb : z.re ≤ 3 / 2 := by rw [hzre]; linarith
  have hF1 : ‖f z / cWU B₁ B₂ z‖ ≤ 1 :=
    PhragmenLindelof.vertical_strip (f := fun w => f w / cWU B₁ B₂ w)
      (a := (-1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) hF_dcl hgrowth hbd_a hbd_b hza hzb
  have hWpos : 0 < ‖cWU B₁ B₂ z‖ := norm_pos_iff.mpr (hWne z hza hzb)
  have hfW : ‖f z‖ ≤ ‖cWU B₁ B₂ z‖ := by
    rw [norm_div] at hF1
    have := (div_le_iff₀ hWpos).mp hF1
    simpa using this
  have hPle : ‖cPU z‖ ≤ 20 * (1 + |t|) ^ 2 := by
    rw [show z = (σ : ℂ) + (t : ℂ) * Complex.I from hz]
    exact cPU_le_target σ t hσ1 hσ2
  have hexp_le : Real.exp ((3 / 2 - z.re) * Real.log 2) ≤ 2 := by
    rw [hzre]
    calc Real.exp ((3 / 2 - σ) * Real.log 2) ≤ Real.exp (1 * Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          nlinarith
      _ = 2 := by rw [one_mul, Real.exp_log (by norm_num)]
  have hWup2 : ‖cWU B₁ B₂ z‖ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ 2 := by
    rw [cWU_norm B₁ B₂ hB₁' hB₂' z]
    have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
    calc 2 * (B₁ / 2 + B₂ / 4) * Real.exp ((3 / 2 - z.re) * Real.log 2) * ‖cPU z‖
        ≤ (2 * (B₁ / 2 + B₂ / 4) * 2) * (20 * (1 + |t|) ^ 2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hexp_le h2M) hPle (norm_nonneg _)
            (by positivity)
      _ = 80 * (B₁ / 2 + B₂ / 4) * (1 + |t|) ^ 2 := by ring
      _ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  have hWup : ‖cWU B₁ B₂ z‖ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ (10 : ℕ) := by
    refine le_trans hWup2 ?_
    have hpow : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ (10 : ℕ) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
    exact mul_le_mul_of_nonneg_left hpow (by linarith)
  calc ‖f z‖ ≤ ‖cWU B₁ B₂ z‖ := hfW
    _ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ (10 : ℕ) := hWup

end Work.FIArea6Hecke.R
