import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

open MeasureTheory Filter

/-- The angular Dirichlet eigenfunctions `eFam m` of `Lzero` are continuous. -/
private lemma continuous_eFam (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  have h : (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = fun θ : ℝ =>
          Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- The cut-off family `χ δ` tends to `1` pointwise on the *open* angular interval, so
it is an approximation of the identity on `Iθ = [0, π/2]` up to a null set.  Consequently
the truncated integrals `∫_{Iθ} f · χ δ · (eFam m · cos)` converge to the untruncated one. -/
theorem bmcut_chi_tendsto (χ : ℝ → ℝ → ℝ) (A : ℝ) (hA : 0 < A) (m : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (hχc : ∀ δ : ℝ, 0 < δ → Continuous (χ δ))
    (hχ0 : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) → χ δ θ = 0)
    (hχ1 : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∈ Set.Icc δ (Real.pi / 2 - δ) → χ δ θ = 1)
    (hχnn : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, 0 ≤ χ δ θ)
    (hχle : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, χ δ θ ≤ 1)
    (hAe : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ A) :
    Filter.Tendsto
      (fun n : ℕ => ∫ θ in Work.Spaces.Iθ,
        f θ * χ (1 / ((n : ℝ) + 1)) θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Filter.atTop
      (nhds (∫ θ in Work.Spaces.Iθ,
        f θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)) := by
  -- `f` is bounded on the compact interval `Iθ`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC0 : 0 ≤ C := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
    have := hC 0 h0
    rw [Real.norm_eq_abs] at this
    exact le_trans (abs_nonneg (f 0)) this
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIθ_top : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- the dominating function `C * A` is integrable on `Iθ`
  have hbound_int : Integrable (fun _ : ℝ => C * A) (volume.restrict Work.Spaces.Iθ) := by
    refine integrableOn_const (s := Work.Spaces.Iθ) hIθ_top ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_ne_top
  -- measurability of every member of the sequence
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => f θ * χ (1 / ((n : ℝ) + 1)) θ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) := by
    intro n
    have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact (((hf.aestronglyMeasurable (show MeasurableSet Work.Spaces.Iθ from
              measurableSet_Icc)).mul
            ((hχc _ hδ).aestronglyMeasurable)).mul
          ((continuous_eFam m).aestronglyMeasurable)).mul
      Real.continuous_cos.aestronglyMeasurable
  -- the dominating bound, using `0 ≤ χ ≤ 1` and the two given bounds
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖f θ * χ (1 / ((n : ℝ) + 1)) θ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ‖ ≤ C * A := by
    intro n
    rw [ae_restrict_iff' (s := Work.Spaces.Iθ) (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)]
    refine Eventually.of_forall fun θ hθ => ?_
    have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hχabs : |χ (1 / ((n : ℝ) + 1)) θ| ≤ 1 := by
      rw [abs_of_nonneg (hχnn _ hδ θ)]
      exact hχle _ hδ θ
    have hfC : |f θ| ≤ C := by
      have h := hC θ (by simpa [Work.Spaces.Iθ] using hθ)
      rwa [Real.norm_eq_abs] at h
    have heA : |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ A := hAe θ hθ
    have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ| ≤ A := by
      rw [← abs_mul]
      exact heA
    have h1 : |f θ| * |χ (1 / ((n : ℝ) + 1)) θ| ≤ C := by
      calc |f θ| * |χ (1 / ((n : ℝ) + 1)) θ| ≤ C * 1 :=
            mul_le_mul hfC hχabs (abs_nonneg _) hC0
        _ = C := mul_one C
    calc ‖f θ * χ (1 / ((n : ℝ) + 1)) θ *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ‖
        = |f θ| * |χ (1 / ((n : ℝ) + 1)) θ| *
            |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      _ = (|f θ| * |χ (1 / ((n : ℝ) + 1)) θ|) *
            (|Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ|) := by ring
      _ ≤ C * A := mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC0
  -- pointwise convergence on a conull subset of `Iθ`: on `(0, π/2)` the cut-off is
  -- eventually identically `1`
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n : ℕ => f θ * χ (1 / ((n : ℝ) + 1)) θ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) atTop
        (nhds (f θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)) := by
    have hcount : ({0, Real.pi / 2} : Set ℝ).Countable :=
      ((Set.finite_singleton (Real.pi / 2)).insert 0).countable
    have hae1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) :=
      hcount.ae_notMem volume
    refine ((ae_restrict_mem hIθ_meas).and (ae_restrict_of_ae hae1)).mono ?_
    rintro θ ⟨hθI, hne⟩
    have hθI' : θ ∈ Set.Icc 0 (Real.pi / 2) := hθI
    have hθ0 : 0 < θ :=
      lt_of_le_of_ne hθI'.1 (fun h => hne (by simp [h]))
    have hθlt : θ < Real.pi / 2 :=
      lt_of_le_of_ne hθI'.2 (fun h => hne (by simp [h]))
    have hmin : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ0 (by linarith)
    have hsmall : ∀ᶠ n : ℕ in atTop,
        1 / ((n : ℝ) + 1) < min θ (Real.pi / 2 - θ) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (eventually_lt_nhds hmin)
    refine (tendsto_const_nhds (x := f θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Real.cos θ)).congr' ?_
    filter_upwards [hsmall] with n hn
    have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle1 : 1 / ((n : ℝ) + 1) ≤ θ :=
      le_of_lt (lt_of_lt_of_le hn (min_le_left _ _))
    have hle2 : θ ≤ Real.pi / 2 - 1 / ((n : ℝ) + 1) :=
      le_of_lt (by linarith [lt_of_lt_of_le hn (min_le_right θ (Real.pi / 2 - θ))])
    have hχ1' : χ (1 / ((n : ℝ) + 1)) θ = 1 :=
      hχ1 _ hδ θ (Set.mem_Icc.mpr ⟨hle1, hle2⟩)
    simp only [hχ1', mul_one]
  exact tendsto_integral_of_dominated_convergence (fun _ : ℝ => C * A)
    hmeas hbound_int hbound hlim

end Work.FTS.PhiStar.Series
