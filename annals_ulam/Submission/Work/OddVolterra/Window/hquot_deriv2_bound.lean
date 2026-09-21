import Mathlib
import Submission.Work.OddVolterra.Defs

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- Differentiation under the integral sign for a parametric integral of the shape
`x ↦ ∫_0^1 w τ * u (x + τ (σ - x)) dτ`, in the special case where `w` is bounded by `1`
on `[0,1]`.

The derivative of the integrand in `x` is `w τ * ((1 - τ) * u' (x + τ (σ-x)))`; the
hypothesis `hC` bounds `u'` on the compact interval spanned by `(x₀ - 1, x₀ + 1)` and `σ`,
which contains all points `x + τ (σ - x)` with `x` close to `x₀` and `τ ∈ [0,1]`. -/
private lemma hasDerivAt_param_int
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) {σ x₀ : ℝ}
    {C : ℝ} (hC : ∀ y ∈ Set.Icc (min (x₀ - 1) σ) (max (x₀ + 1) σ), ‖deriv u y‖ ≤ C)
    {w : ℝ → ℝ} (hwcont : Continuous w) (hw1 : ∀ τ ∈ Set.Icc (0:ℝ) 1, |w τ| ≤ 1) :
    HasDerivAt (fun x : ℝ => ∫ τ in (0:ℝ)..1, w τ * u (x + τ * (σ - x)))
      (∫ τ in (0:ℝ)..1, w τ * ((1 - τ) * deriv u (x₀ + τ * (σ - x₀)))) x₀ := by
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hdu_cont : Continuous (deriv u) := hdu.continuous
  set s : Set ℝ := Set.Ioo (x₀ - 1) (x₀ + 1) with hs
  have hs_mem : s ∈ 𝓝 x₀ := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  set F : ℝ → ℝ → ℝ := fun x τ => w τ * u (x + τ * (σ - x)) with hF
  set F' : ℝ → ℝ → ℝ := fun x τ => w τ * ((1 - τ) * deriv u (x + τ * (σ - x))) with hF'
  -- the moving point stays in the compact interval where `u'` is bounded
  have hmem : ∀ x ∈ s, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      x + τ * (σ - x) ∈ Set.Icc (min (x₀ - 1) σ) (max (x₀ + 1) σ) := by
    intro x hx τ hτ
    have hSC : StarConvex ℝ x (Set.Icc (min x σ) (max x σ)) :=
      convex_Icc _ _ ⟨min_le_left _ _, le_max_left _ _⟩
    have hσI : σ ∈ Set.Icc (min x σ) (max x σ) := ⟨min_le_right _ _, le_max_right _ _⟩
    have h1 : x + τ * (σ - x) ∈ Set.Icc (min x σ) (max x σ) := by
      have h := hSC.add_smul_sub_mem hσI hτ.1 hτ.2
      rwa [smul_eq_mul] at h
    exact ⟨le_trans (min_le_min (le_of_lt hx.1) le_rfl) h1.1,
      le_trans h1.2 (max_le_max (le_of_lt hx.2) le_rfl)⟩
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι (0:ℝ) 1)) :=
    Filter.Eventually.of_forall (fun x =>
      (hwcont.mul (hu.continuous.comp
        (by fun_prop : Continuous fun τ : ℝ => x + τ * (σ - x)))).aestronglyMeasurable)
  have hF_int : IntervalIntegrable (F x₀) volume (0:ℝ) 1 :=
    (hwcont.mul (hu.continuous.comp
      (by fun_prop : Continuous fun τ : ℝ => x₀ + τ * (σ - x₀)))).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι (0:ℝ) 1)) :=
    (hwcont.mul ((continuous_const.sub continuous_id).mul
      (hdu_cont.comp (by fun_prop : Continuous fun τ : ℝ => x₀ + τ * (σ - x₀))))).aestronglyMeasurable
  have h_bound : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ι (0:ℝ) 1 →
      ∀ x ∈ s, ‖F' x τ‖ ≤ (fun _ : ℝ => C) τ := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    have hwle : |w τ| ≤ 1 := hw1 τ hτIcc
    have hτ1 : |(1:ℝ) - τ| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hCy : |deriv u (x + τ * (σ - x))| ≤ C := by
      simpa [Real.norm_eq_abs] using hC _ (hmem x hx τ hτIcc)
    have hInner : |1 - τ| * |deriv u (x + τ * (σ - x))| ≤ 1 * C :=
      mul_le_mul hτ1 hCy (abs_nonneg _) (by norm_num)
    simp only [hF', Real.norm_eq_abs, abs_mul]
    calc |w τ| * (|1 - τ| * |deriv u (x + τ * (σ - x))|)
        ≤ 1 * (1 * C) :=
          mul_le_mul hwle hInner (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = C := by ring
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume (0:ℝ) 1 := intervalIntegrable_const
  have h_diff : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ι (0:ℝ) 1 → ∀ x ∈ s,
      HasDerivAt (fun x => F x τ) (F' x τ) x := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    have hinner : HasDerivAt (fun x : ℝ => x + τ * (σ - x)) (1 - τ) x := by
      have hfun : (fun x : ℝ => x + τ * (σ - x)) = fun x : ℝ => (1 - τ) * x + τ * σ := by
        funext y; ring
      rw [hfun]
      simpa using ((hasDerivAt_id x).const_mul (1 - τ)).add_const (τ * σ)
    have houter : HasDerivAt u (deriv u (x + τ * (σ - x))) (x + τ * (σ - x)) :=
      (hu.differentiable (by simp)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun x : ℝ => u (x + τ * (σ - x)))
        (deriv u (x + τ * (σ - x)) * (1 - τ)) x := houter.comp x hinner
    have hfull := hcomp.const_mul (w τ)
    refine hfull.congr_deriv ?_
    simp only [hF']
    ring
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume) (F := F) (F' := F') (x₀ := x₀)
    (s := s) (bound := fun _ : ℝ => C)
    hs_mem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact hmain.2

theorem hquot_deriv2_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ} (hδ : 0 ≤ δ)
    (h3 : ∀ s : ℝ, |iteratedDeriv 3 h s| ≤ δ) (σ a : ℝ) :
    |deriv (deriv (fun x : ℝ => Work.OddVolterra.hquot h x σ)) a| ≤ δ := by
  -- unfold `hquot` to its integral form
  change |deriv (deriv (fun x : ℝ => ∫ τ in (0:ℝ)..1, deriv h (x + τ * (σ - x)))) a| ≤ δ
  -- smoothness of the successive derivatives
  have h1 : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv h)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3' : ContDiff ℝ ∞ (deriv (deriv (deriv h))) := (contDiff_infty_iff_deriv.mp h2).2
  have hiter3 : iteratedDeriv 3 h = deriv (deriv (deriv h)) := by
    rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
    congr 1
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  set g : ℝ → ℝ := fun x => ∫ τ in (0:ℝ)..1, deriv h (x + τ * (σ - x)) with hg
  set G : ℝ → ℝ := fun x => ∫ τ in (0:ℝ)..1, (1 - τ) * deriv (deriv h) (x + τ * (σ - x))
    with hG
  set G2 : ℝ → ℝ := fun x => ∫ τ in (0:ℝ)..1,
    (1 - τ) * ((1 - τ) * deriv (deriv (deriv h)) (x + τ * (σ - x))) with hG2
  -- first derivative: differentiate under the integral sign
  have hstep1 : ∀ x : ℝ, HasDerivAt g (G x) x := by
    intro x
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := min (x - 1) σ) (b := max (x + 1) σ))
      |>.exists_bound_of_continuousOn (h2.continuous.continuousOn)
    have h := hasDerivAt_param_int (u := deriv h) h1 (σ := σ) (x₀ := x) (C := C) hC
      (w := fun _ : ℝ => (1:ℝ)) continuous_const (by intro τ hτ; simp)
    simpa only [one_mul, hg, hG] using h
  -- second derivative: differentiate under the integral sign again
  have hstep2 : ∀ x : ℝ, HasDerivAt G (G2 x) x := by
    intro x
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := min (x - 1) σ) (b := max (x + 1) σ))
      |>.exists_bound_of_continuousOn (h3'.continuous.continuousOn)
    have h := hasDerivAt_param_int (u := deriv (deriv h)) h2 (σ := σ) (x₀ := x) (C := C) hC
      (w := fun τ : ℝ => 1 - τ) (by fun_prop)
      (by intro τ hτ; rw [abs_le]; exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩)
    simpa only [hG, hG2] using h
  have hderivg : deriv g = G := funext (fun x => (hstep1 x).deriv)
  have hkey : deriv (deriv g) a = G2 a := by
    rw [hderivg]
    exact (hstep2 a).deriv
  rw [hkey]
  have hG2eq : G2 a = ∫ τ in (0:ℝ)..1,
      (1 - τ) * ((1 - τ) * deriv (deriv (deriv h)) (a + τ * (σ - a))) := by rw [hG2]
  rw [hG2eq]
  -- bound the resulting integral
  have hbdfun : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0:ℝ) 1 →
      ‖(1 - τ) * ((1 - τ) * deriv (deriv (deriv h)) (a + τ * (σ - a)))‖
        ≤ (1 - τ)^2 * δ := by
    refine Filter.Eventually.of_forall (fun τ hτ => ?_)
    have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
    have h3'' : |deriv (deriv (deriv h)) (a + τ * (σ - a))| ≤ δ := by
      rw [← hiter3]
      exact h3 _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1τ]
    calc (1 - τ) * ((1 - τ) * |deriv (deriv (deriv h)) (a + τ * (σ - a))|)
        = (1 - τ)^2 * |deriv (deriv (deriv h)) (a + τ * (σ - a))| := by ring
      _ ≤ (1 - τ)^2 * δ := mul_le_mul_of_nonneg_left h3'' (sq_nonneg _)
  have hint1 : IntervalIntegrable
      (fun τ : ℝ => (1 - τ) * ((1 - τ) * deriv (deriv (deriv h)) (a + τ * (σ - a))))
      volume (0:ℝ) 1 :=
    (((continuous_const.sub continuous_id).mul
      ((continuous_const.sub continuous_id).mul
        ((h3'.continuous.comp (by fun_prop)))))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun τ : ℝ => (1 - τ)^2 * δ) volume (0:ℝ) 1 :=
    (((continuous_const.sub continuous_id).pow 2).mul continuous_const).intervalIntegrable _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (a := (0:ℝ)) (b := 1)
    (by norm_num) hbdfun hint2
  rw [Real.norm_eq_abs] at hnorm
  have hmono : (∫ τ in (0:ℝ)..1, (1 - τ)^2 * δ) ≤ ∫ τ in (0:ℝ)..1, δ := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint2 intervalIntegrable_const ?_
    intro x hx
    have hx1 : (0:ℝ) ≤ 1 - x := by linarith [hx.2]
    have hx2 : (1 - x)^2 ≤ 1 := by
      have habs : |1 - x| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have h : |1 - x|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
      rwa [sq_abs] at h
    exact le_trans (mul_le_mul_of_nonneg_right hx2 hδ) (by simp)
  have hconst : (∫ τ in (0:ℝ)..1, δ) = δ := by
    rw [intervalIntegral.integral_const]; simp
  linarith [hnorm, hmono, hconst]

end Work.OddVolterra.Window
