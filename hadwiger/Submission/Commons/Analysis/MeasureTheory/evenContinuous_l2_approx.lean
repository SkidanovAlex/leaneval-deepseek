import Mathlib
import Submission.Commons.Analysis.MeasureTheory.integral_sq_add_le_two_mul
import Submission.Commons.Analysis.MeasureTheory.integral_even_mul_odd
import Submission.Commons.Analysis.MeasureTheory.reflSphere_measurePreserving

noncomputable section
set_option linter.unusedVariables false
open Set Function MeasureTheory Metric
open scoped Classical ENNReal Topology BoundedContinuousFunction

namespace Commons.Analysis.MeasureTheory

/-- The antipodal map on the unit sphere is an involution. -/
private lemma antipodalSphere_invol (V : Type*) [NormedAddCommGroup V]
    (θ : Metric.sphere (0 : V) 1) :
    antipodalSphere V (antipodalSphere V θ) = θ := by
  apply Subtype.ext
  simp [antipodalSphere]

theorem evenContinuous_l2_approx
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    {f : Metric.sphere (0 : V) 1 → ℝ}
    (hfmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume.toSphere)
    (hfin : MeasureTheory.MemLp f 2 MeasureTheory.volume.toSphere)
    (hfeven : ∀ θ : Metric.sphere (0 : V) 1,
      f (Commons.Analysis.MeasureTheory.antipodalSphere V θ) = f θ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : BoundedContinuousFunction (Metric.sphere (0 : V) 1) ℝ,
      (∀ θ : Metric.sphere (0 : V) 1,
        g (Commons.Analysis.MeasureTheory.antipodalSphere V θ) = g θ) ∧
      MeasureTheory.MemLp (fun θ : Metric.sphere (0 : V) 1 =>
        (g : Metric.sphere (0 : V) 1 → ℝ) θ)
        2 MeasureTheory.volume.toSphere ∧
      (∫ θ : Metric.sphere (0 : V) 1,
          (f θ - (g : Metric.sphere (0 : V) 1 → ℝ) θ)^2 ∂MeasureTheory.volume.toSphere) ≤ ε := by
  let S := Metric.sphere (0 : V) 1
  let μ : Measure S := MeasureTheory.volume.toSphere
  let ant : S ≃ₜ S := Commons.Analysis.MeasureTheory.antipodalSphere V
  -- approximation of f by bounded continuous g₀
  have hfin2 : MemLp f (ENNReal.ofReal 2) μ := by
    dsimp [μ]
    simpa using hfin
  rcases hfin2.exists_boundedContinuous_integral_rpow_sub_le (p := (2:ℝ)) (by norm_num : 0 < (2:ℝ)) hε with ⟨g₀, hAg₀, hg₀m⟩
  let g0fun : S → ℝ := (g₀ : S → ℝ)
  have hg0mem2 : MemLp g0fun 2 μ := by
    dsimp [g0fun]
    simpa using hg₀m
  -- hAg₀ : ∫ ‖f - g₀‖^(2:ℝ) ≤ ε ; convert to square
  have hAg₀sq : (∫ θ : S, (f θ - g0fun θ)^2 ∂μ) ≤ ε := by
    have heqfun : (fun θ : S => ‖f θ - (g₀ : S → ℝ) θ‖ ^ (2:ℝ)) =
        fun θ : S => (f θ - (g₀ : S → ℝ) θ)^2 := by
      funext θ
      rw [Real.norm_eq_abs]
      norm_num [Real.rpow_natCast]
    rw [heqfun] at hAg₀
    simpa [g0fun] using hAg₀
  -- symmetrized function
  let gfun : S → ℝ := fun θ : S => (g0fun θ + g0fun (ant θ)) / 2
  have hcont : Continuous gfun := by
    dsimp [gfun, g0fun, ant]
    fun_prop
  have hgbd : ∀ θ : S, ‖gfun θ‖ ≤ ‖g₀‖ := by
    intro θ
    have hsum : |(g₀ θ + g₀ (ant θ)) / 2| ≤ (|g₀ θ| + |g₀ (ant θ)|) / 2 := by
      have hsum' : |g₀ θ + g₀ (ant θ)| ≤ |g₀ θ| + |g₀ (ant θ)| := abs_add_le _ _
      have hd : |(g₀ θ + g₀ (ant θ)) / 2| = |(g₀ θ + g₀ (ant θ))| / 2 := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      rw [hd]
      exact div_le_div_of_nonneg_right hsum' (by norm_num : 0 ≤ (2:ℝ))
    have hn1 : |g₀ θ| ≤ ‖g₀‖ := by
      simpa [Real.norm_eq_abs] using (BoundedContinuousFunction.norm_coe_le_norm g₀ θ)
    have hn2 : |g₀ (ant θ)| ≤ ‖g₀‖ := by
      simpa [Real.norm_eq_abs] using (BoundedContinuousFunction.norm_coe_le_norm g₀ (ant θ))
    have hle1 : |(g₀ θ + g₀ (ant θ)) / 2| ≤ ‖g₀‖ := by linarith
    calc
      ‖gfun θ‖ = |gfun θ| := Real.norm_eq_abs _
      _ = |(g₀ θ + g₀ (ant θ)) / 2| := by simp [gfun, g0fun]
      _ ≤ ‖g₀‖ := hle1
  let g : S →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup gfun hcont ‖g₀‖ hgbd
  have hgfun_eq : (g : S → ℝ) = gfun := by
    dsimp [g]
  -- evenness of g
  have hinvo : ∀ θ : S, ant (ant θ) = θ := by
    intro θ
    dsimp [ant]
    exact antipodalSphere_invol V θ
  have heven : ∀ θ : S, (g : S → ℝ) (ant θ) = (g : S → ℝ) θ := by
    intro θ
    rw [hgfun_eq]
    dsimp [gfun, g0fun]
    rw [hinvo θ]
    ring
  -- MemLp g
  have hmeas_g : AEStronglyMeasurable (g : S → ℝ) μ := by
    dsimp [g]
    exact hcont.aestronglyMeasurable
  have hgm2 : MemLp (g : S → ℝ) 2 μ := by
    apply MemLp.of_bound hmeas_g ‖g₀‖
    filter_upwards with θ
    rw [hgfun_eq]
    exact hgbd θ
  -- MemLp g0 ∘ ant
  have hmeas_g0ant : AEStronglyMeasurable (fun θ : S => g0fun (ant θ)) μ := by
    have hc : Continuous (fun θ : S => g0fun (ant θ)) := by
      dsimp [g0fun, ant]
      fun_prop
    exact hc.aestronglyMeasurable
  have hg0ant_mem : MemLp (fun θ : S => g0fun (ant θ)) 2 μ := by
    apply MemLp.of_bound hmeas_g0ant ‖g₀‖
    filter_upwards with θ
    simpa [g0fun, Real.norm_eq_abs] using (BoundedContinuousFunction.norm_coe_le_norm g₀ (ant θ))
  -- measure preservation of ant
  have hantMP : MeasurePreserving (ant : S → S) μ μ := by
    dsimp [S, μ, ant]
    simpa [Commons.Analysis.MeasureTheory.antipodalSphere] using
      (Commons.Analysis.MeasureTheory.reflSphere_measurePreserving (V := V))
  have hantME : MeasurableEmbedding (ant : S → S) := by
    dsimp [ant]
    simpa using (Commons.Analysis.MeasureTheory.antipodalSphere V).measurableEmbedding
  -- evenness for ant-form of f
  have hfeven_ant : ∀ θ : S, f (ant θ) = f θ := by
    intro θ
    dsimp [ant]
    exact hfeven θ
  -- the main integral estimate
  let A : S → ℝ := fun θ : S => f θ - g0fun θ
  let B : S → ℝ := fun θ : S => f θ - g0fun (ant θ)
  let c : S → ℝ := fun θ : S => f θ - gfun θ
  -- A,B ∈ L²
  have hA_mem : MemLp A 2 μ := by
    dsimp [A]
    exact hfin.sub hg0mem2
  have hB_mem : MemLp B 2 μ := by
    dsimp [B]
    exact hfin.sub hg0ant_mem
  -- ∫ B² = ∫ A²
  have hB2_eq_A2 : (∫ θ : S, (B θ)^2 ∂μ) = (∫ θ : S, (A θ)^2 ∂μ) := by
    dsimp [A, B]
    calc
      (∫ θ : S, (f θ - g0fun (ant θ))^2 ∂μ)
          = (∫ θ : S, (f (ant θ) - g0fun (ant (ant θ)))^2 ∂μ) := by
              symm
              exact MeasurePreserving.integral_comp hantMP hantME (fun φ : S => (f φ - g0fun (ant φ))^2)
      _ = (∫ θ : S, (f (ant θ) - g0fun θ)^2 ∂μ) := by
          apply integral_congr_ae
          filter_upwards with θ
          rw [hinvo θ]
      _ = (∫ θ : S, (f θ - g0fun θ)^2 ∂μ) := by
          apply integral_congr_ae
          filter_upwards with θ
          rw [hfeven_ant θ]
  -- c = (A + B)/2 pointwise
  have hmid : ∀ θ : S, c θ = (A θ + B θ) / 2 := by
    intro θ
    dsimp [c, A, B, gfun]
    ring
  -- integral estimate for c²
  have hineq : (∫ θ : S, (c θ)^2 ∂μ) ≤
      (1/2) * ((∫ θ : S, (A θ)^2 ∂μ) + (∫ θ : S, (B θ)^2 ∂μ)) := by
    have hCS := Commons.Analysis.MeasureTheory.integral_sq_add_le_two_mul (a := A) (b := B) hA_mem hB_mem
    have hsq1 : (fun θ : S => (c θ)^2) = fun θ : S => (((A θ + B θ) / 2)^2) := by
      funext θ
      rw [hmid θ]
    have hsq2 : (fun θ : S => (((A θ + B θ) / 2)^2)) = fun θ : S => (1/4 : ℝ) * (A θ + B θ)^2 := by
      funext θ
      ring
    calc
      (∫ θ : S, (c θ)^2 ∂μ) = (∫ θ : S, (((A θ + B θ) / 2)^2) ∂μ) := by rw [hsq1]
      _ = (∫ θ : S, (1/4 : ℝ) * (A θ + B θ)^2 ∂μ) := by rw [hsq2]
      _ = (1/4 : ℝ) * (∫ θ : S, (A θ + B θ)^2 ∂μ) := by rw [integral_const_mul]
      _ ≤ (1/4 : ℝ) * (2 * (∫ θ : S, (A θ)^2 ∂μ) + 2 * (∫ θ : S, (B θ)^2 ∂μ)) := by
          exact mul_le_mul_of_nonneg_left hCS (by norm_num : (0:ℝ) ≤ (1/4))
      _ = (1/2) * ((∫ θ : S, (A θ)^2 ∂μ) + (∫ θ : S, (B θ)^2 ∂μ)) := by ring
  have hmainA : (∫ θ : S, (A θ)^2 ∂μ) ≤ ε := by
    simpa [A] using hAg₀sq
  have hsqc : (fun θ : S => (f θ - (g : S → ℝ) θ)^2) = fun θ : S => (c θ)^2 := by
    funext θ
    dsimp [c]
    rw [hgfun_eq]
  have hmain : (∫ θ : S, (f θ - (g : S → ℝ) θ)^2 ∂μ) ≤ ε := by
    calc
      (∫ θ : S, (f θ - (g : S → ℝ) θ)^2 ∂μ) = (∫ θ : S, (c θ)^2 ∂μ) := by rw [hsqc]
      _ ≤ (1/2) * ((∫ θ : S, (A θ)^2 ∂μ) + (∫ θ : S, (B θ)^2 ∂μ)) := hineq
      _ = (1/2) * ((∫ θ : S, (A θ)^2 ∂μ) + (∫ θ : S, (A θ)^2 ∂μ)) := by rw [hB2_eq_A2]
      _ = (∫ θ : S, (A θ)^2 ∂μ) := by ring
      _ ≤ ε := hmainA
  refine ⟨g, ?_, ?_, ?_⟩
  · intro θ
    simpa [ant] using heven θ
  · simpa [S, μ] using hgm2
  · simpa [S, μ] using hmain

end Commons.Analysis.MeasureTheory
