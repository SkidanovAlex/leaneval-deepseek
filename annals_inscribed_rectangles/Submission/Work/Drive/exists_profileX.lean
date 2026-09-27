import Mathlib

/-!
# A smooth radial unit profile on `ℂ`

We construct a smooth function `x : ℂ → ℂ` which is bounded by `1`, equals the
normalisation `z / ‖z‖` as soon as `‖z‖ ≥ 1/8`, and stays bounded below by `1/8`
once `‖z‖ ≥ 1/16`.

The construction is a *radial* one: `x z = h (‖z‖²) * z` where `h : ℝ → ℝ` is a
smooth function which vanishes near `0` (so that the flat factor kills the
singularity of `z ↦ z/‖z‖` at the origin, giving smoothness) and which equals
`t^{-1/2}` for `t` large.  Concretely we take

`h t = smoothTransition (1024 * t - 1) * (√t)⁻¹`,

so that `h t = (√t)⁻¹` for `t ≥ 1/512` and `h t = 0` for `t ≤ 1/1024`.
-/

namespace Work.Drive

noncomputable section

/-- The radial profile: a smooth function of `t = ‖z‖²` with the flat factor
`Real.smoothTransition (1024 * t - 1)` (which is `0` on `(-∞, 1/1024]` and `1` on
`[1/512, ∞)`) glued to `(√t)⁻¹`. -/
private def profH (t : ℝ) : ℝ :=
  Real.smoothTransition (1024 * t - 1) * (Real.sqrt t)⁻¹

private lemma profH_eq_zero_of_le (t : ℝ) (ht : t ≤ 1/1024) : profH t = 0 := by
  have h : Real.smoothTransition (1024 * t - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [profH, h]

private lemma profH_of_one_le (t : ℝ) (ht : 1/512 ≤ t) : profH t = (Real.sqrt t)⁻¹ := by
  have h : Real.smoothTransition (1024 * t - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp [profH, h]

private lemma abs_profH_le (t : ℝ) : |profH t| ≤ (Real.sqrt t)⁻¹ := by
  have hσ : |Real.smoothTransition (1024 * t - 1)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  calc |profH t| = |Real.smoothTransition (1024 * t - 1)| * (Real.sqrt t)⁻¹ := by
        rw [profH, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg t)]
    _ ≤ 1 * (Real.sqrt t)⁻¹ :=
        mul_le_mul_of_nonneg_right hσ (inv_nonneg.mpr (Real.sqrt_nonneg t))
    _ = (Real.sqrt t)⁻¹ := one_mul _

private lemma abs_profH_mul_sqrt_le_one (t : ℝ) : |profH t| * Real.sqrt t ≤ 1 := by
  calc |profH t| * Real.sqrt t ≤ (Real.sqrt t)⁻¹ * Real.sqrt t :=
        mul_le_mul_of_nonneg_right (abs_profH_le t) (Real.sqrt_nonneg t)
    _ ≤ 1 := by
        rcases eq_or_lt_of_le (Real.sqrt_nonneg t) with h | h
        · rw [← h, inv_zero, zero_mul]; norm_num
        · rw [inv_mul_cancel₀ (ne_of_gt h)]

private lemma contDiff_profH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) profH := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (1/1024) with ht | ht
  · refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with u hu
    have hu' : u < 1/1024 := hu
    have h : Real.smoothTransition (1024 * u - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    simp [profH, h]
  · have ht0 : 0 < t := by linarith
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => Real.smoothTransition (1024 * u - 1)) t :=
      Real.smoothTransition.contDiffAt.comp t (by fun_prop)
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (Real.sqrt u)⁻¹) t :=
      (Real.contDiffAt_sqrt (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (ne_of_gt ht0)).inv
        (by simp [ne_of_gt (Real.sqrt_pos.2 ht0)])
    exact h1.mul h2

/-- The candidate: `z ↦ h (‖z‖²) * z`. -/
private def profX (z : ℂ) : ℂ := ((profH (Complex.normSq z) : ℝ) : ℂ) * z

private lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg ((r : ℝ) : ℂ), abs_nonneg r, sq_abs r]

private lemma sqrt_normSq (z : ℂ) : Real.sqrt (Complex.normSq z) = ‖z‖ := by
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]

private lemma contDiff_profX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) profX := by
  have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.normSq := by
    have h : Complex.normSq = fun z : ℂ => z.re * z.re + z.im * z.im :=
      funext Complex.normSq_apply
    rw [h]
    have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.re) := Complex.reCLM.contDiff
    have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im) := Complex.imCLM.contDiff
    exact (hre.mul hre).add (him.mul him)
  have hcomp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => profH (Complex.normSq z)) := contDiff_profH.comp hns
  have hcoe : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => ((profH (Complex.normSq z) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hcomp
  exact hcoe.mul contDiff_id

private lemma profX_norm_le_one (z : ℂ) : ‖profX z‖ ≤ 1 := by
  rw [profX, norm_mul, norm_ofReal_complex, ← sqrt_normSq z]
  exact abs_profH_mul_sqrt_le_one (Complex.normSq z)

private lemma profX_of_ge (z : ℂ) (hz : 1/8 ≤ ‖z‖) : profX z = z / ((‖z‖ : ℝ) : ℂ) := by
  have ht : (1 : ℝ)/512 ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z, hz]
  calc profX z = ((profH (Complex.normSq z) : ℝ) : ℂ) * z := rfl
    _ = (((Real.sqrt (Complex.normSq z))⁻¹ : ℝ) : ℂ) * z := by rw [profH_of_one_le _ ht]
    _ = (((‖z‖)⁻¹ : ℝ) : ℂ) * z := by rw [sqrt_normSq]
    _ = z / ((‖z‖ : ℝ) : ℂ) := by rw [Complex.ofReal_inv]; ring

private lemma profX_norm_ge (z : ℂ) (hz : 1/16 ≤ ‖z‖) : 1/8 ≤ ‖profX z‖ := by
  have ht : (1 : ℝ)/512 ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z, hz]
  have hzpos : 0 < ‖z‖ := by linarith
  have hstep : ‖profX z‖ = (‖z‖)⁻¹ * ‖z‖ := by
    rw [profX, norm_mul, norm_ofReal_complex, profH_of_one_le _ ht, sqrt_normSq,
      abs_inv, abs_of_nonneg (le_of_lt hzpos)]
  rw [hstep, inv_mul_cancel₀ (ne_of_gt hzpos)]; norm_num

theorem exists_profileX :
    ∃ x : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x ∧
      (∀ z : ℂ, ‖x z‖ ≤ 1) ∧
      (∀ z : ℂ, 1 / 8 ≤ ‖z‖ → x z = z / ((‖z‖ : ℝ) : ℂ)) ∧
      (∀ z : ℂ, 1 / 16 ≤ ‖z‖ → 1 / 8 ≤ ‖x z‖) :=
  ⟨profX, contDiff_profX, profX_norm_le_one, profX_of_ge, profX_norm_ge⟩

end

end Work.Drive
