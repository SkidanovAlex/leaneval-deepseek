import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.RingTheory.Finiteness.Prod

open Filter MeasureTheory
open scoped Topology

namespace Commons.Analysis.Calculus

/-- A `C¹` compactly supported function has uniformly bounded Fréchet derivative. -/
theorem exists_bound_fderiv_of_contDiff_one_hasCompactSupport {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [ProperSpace E] {f : E → G} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E, ‖fderiv ℝ f x‖ ≤ B := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨B₀, hB₀⟩ := hc.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  have hzero : ∀ x : E, x ∉ tsupport f → fderiv ℝ f x = 0 := by
    intro x hx
    have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    have hev : f =ᶠ[𝓝 x] fun _ => (0 : G) := by
      filter_upwards [hmem] with y hy using image_eq_zero_of_notMem_tsupport hy
    rw [Filter.EventuallyEq.fderiv_eq hev]
    simp
  exact ⟨max B₀ 0, le_max_right _ _, fun x => by
    by_cases hx : x ∈ tsupport f
    · exact (hB₀ x hx).trans (le_max_left _ _)
    · rw [hzero x hx, norm_zero]; exact le_max_right _ _⟩

/-- The linear map `q ↦ q.1 + t • q.2` on `ℝᵈ × ℝᵈ`. -/
noncomputable def poissonLinearMap (d : ℕ) (t : ℝ) :
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.fst ℝ _ _ + t • ContinuousLinearMap.snd ℝ _ _

lemma poissonLinearMap_apply {d : ℕ} (t : ℝ)
    (q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    poissonLinearMap d t q = q.1 + t • q.2 := by
  simp [poissonLinearMap]

lemma norm_poissonLinearMap_le {d : ℕ} (t : ℝ) : ‖poissonLinearMap d t‖ ≤ 1 + |t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  rw [poissonLinearMap_apply]
  calc ‖q.1 + t • q.2‖ ≤ ‖q.1‖ + ‖t • q.2‖ := norm_add_le _ _
    _ = ‖q.1‖ + |t| * ‖q.2‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖q‖ + |t| * ‖q‖ :=
      add_le_add (norm_fst_le q) (mul_le_mul_of_nonneg_left (norm_snd_le q) (abs_nonneg t))
    _ = (1 + |t|) * ‖q‖ := by ring

lemma continuous_poissonLinearMap {d : ℕ} : Continuous fun t : ℝ => poissonLinearMap d t := by
  rw [show (fun t : ℝ => poissonLinearMap d t) = fun t : ℝ =>
      ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) +
        t • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))
      from rfl]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- The Poisson integrand `(q, t) ↦ f (q.1 + t • q.2) / (1 + t²)`. -/
noncomputable def poissonIntegrand (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
  f (q.1 + t • q.2) * (1 + t ^ 2)⁻¹

/-- The Fréchet derivative of the Poisson integrand in `q` at `p`, as a function of `t`. -/
noncomputable def poissonDerivAt (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ :=
  (1 + t ^ 2)⁻¹ • ((fderiv ℝ f (p.1 + t • p.2)).comp (poissonLinearMap d t))

/-- An integrable dominating function: `B * (1 + min |t| T) / (1 + t²)`.  On `|t| ≤ T` it is
the Lipschitz bound `B * (1 + |t|) / (1 + t²)` for the Poisson integrand, while globally it is
dominated by `B * (1 + T) / (1 + t²)`, which is integrable. -/
noncomputable def poissonBound (B T : ℝ) (t : ℝ) : ℝ :=
  B * (1 + min |t| T) * (1 + t ^ 2)⁻¹

lemma poissonBound_nonneg {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ poissonBound B T t := by
  have h1 : 0 ≤ min |t| T := le_min (abs_nonneg t) hT
  simp only [poissonBound]
  positivity

lemma poissonIntegrand_continuous {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    Continuous (poissonIntegrand d f q) := by
  have h1 : Continuous fun t : ℝ => f (q.1 + t • q.2) :=
    hf.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h2 : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ := by
    have h : Continuous fun t : ℝ => 1 + t ^ 2 := continuous_const.add (continuous_id.pow 2)
    exact h.inv₀ fun t => by positivity
  refine (h1.mul h2).congr fun t => ?_
  simp only [Pi.mul_apply, poissonIntegrand]

lemma hasFDerivAt_poissonIntegrand {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 1 f) (t : ℝ)
    (q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        f (y.1 + t • y.2) * (1 + t ^ 2)⁻¹)
      ((1 + t ^ 2)⁻¹ • ((fderiv ℝ f (q.1 + t • q.2)).comp (poissonLinearMap d t))) q := by
  have hinner : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => y.1 + t • y.2)
      (poissonLinearMap d t) q :=
    (poissonLinearMap d t).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => poissonLinearMap_apply t y)
  have hcomp : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => f (y.1 + t • y.2))
      ((fderiv ℝ f (q.1 + t • q.2)).comp (poissonLinearMap d t)) q :=
    ((hf.differentiable_one (q.1 + t • q.2)).hasFDerivAt).comp q hinner
  exact hcomp.mul_const ((1 + t ^ 2)⁻¹)

theorem differentiableAt_poisson_extension_of_second_ne {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (hp : p.2 ≠ 0) :
    DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      MeasureTheory.integral MeasureTheory.volume fun t : ℝ =>
        f (q.1 + t • q.2) * (1 + t ^ 2)⁻¹) p := by
  obtain ⟨Bf, hBf⟩ := hfs.exists_bound_of_continuous hf.continuous
  obtain ⟨B, hB0, hB⟩ := exists_bound_fderiv_of_contDiff_one_hasCompactSupport hf hfs
  obtain ⟨R₀, hR₀⟩ := hfs.isCompact.exists_bound_of_continuousOn
    (continuousOn_id : ContinuousOn (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (tsupport f))
  set R : ℝ := max R₀ 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ z ∈ tsupport f, ‖z‖ ≤ R := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  have hp2 : 0 < ‖p.2‖ := norm_pos_iff.mpr hp
  set δ : ℝ := min 1 (‖p.2‖ / 2) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ‖p.2‖ / 2 := min_le_right _ _
  set T : ℝ := 2 * (R + ‖p.1‖ + 1) / ‖p.2‖ with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact div_nonneg (by linarith [hR0, norm_nonneg p.1]) (norm_nonneg _)
  have hTm : T * (‖p.2‖ / 2) = R + ‖p.1‖ + 1 := by
    rw [hT]
    field_simp
  -- Vanishing of the integrand far out, uniformly on a neighbourhood of `p`
  have hvanish : ∀ q ∈ Metric.ball p δ, ∀ t : ℝ, T < |t| → f (q.1 + t • q.2) = 0 := by
    intro q hq t ht
    by_contra hne
    have hzt : q.1 + t • q.2 ∈ tsupport f := subset_tsupport f hne
    have hzR : ‖q.1 + t • q.2‖ ≤ R := hR _ hzt
    have hq2 : ‖p.2‖ / 2 ≤ ‖q.2‖ := by
      have h1 : ‖p.2‖ ≤ ‖q.2‖ + ‖p.2 - q.2‖ := by
        have he : q.2 + (p.2 - q.2) = p.2 := by abel
        calc ‖p.2‖ = ‖q.2 + (p.2 - q.2)‖ := by rw [he]
          _ ≤ ‖q.2‖ + ‖p.2 - q.2‖ := norm_add_le _ _
      have h2 : ‖p.2 - q.2‖ < δ := by
        calc ‖p.2 - q.2‖ = ‖(p - q).2‖ := by simp
          _ ≤ ‖p - q‖ := norm_snd_le _
          _ = dist q p := by rw [dist_eq_norm, norm_sub_rev]
          _ < δ := hq
      linarith
    have hq1 : ‖q.1‖ ≤ ‖p.1‖ + 1 := by
      have h2 : ‖q.1 - p.1‖ < δ := by
        calc ‖q.1 - p.1‖ = ‖(q - p).1‖ := by simp
          _ ≤ ‖q - p‖ := norm_fst_le _
          _ = dist q p := by rw [dist_eq_norm]
          _ < δ := hq
      have h3 : ‖q.1‖ ≤ ‖q.1 - p.1‖ + ‖p.1‖ := by
        have he : (q.1 - p.1) + p.1 = q.1 := by abel
        have h4 := norm_add_le (q.1 - p.1) p.1
        rwa [he] at h4
      linarith
    have hlow : R + ‖p.1‖ + 1 < |t| * ‖q.2‖ := by
      have h1 : T * (‖p.2‖ / 2) < |t| * (‖p.2‖ / 2) :=
        mul_lt_mul_of_pos_right (lt_of_not_ge (not_le.mpr ht)) (by positivity)
      have h2 : |t| * (‖p.2‖ / 2) ≤ |t| * ‖q.2‖ :=
        mul_le_mul_of_nonneg_left hq2 (abs_nonneg t)
      linarith [hTm]
    have hhigh : |t| * ‖q.2‖ ≤ R + ‖p.1‖ + 1 := by
      have h1 : ‖t • q.2‖ = |t| * ‖q.2‖ := by rw [norm_smul, Real.norm_eq_abs]
      have h3 : ‖t • q.2‖ ≤ ‖q.1 + t • q.2‖ + ‖q.1‖ := by
        have h4 := norm_sub_le (q.1 + t • q.2) q.1
        have he : (q.1 + t • q.2) - q.1 = t • q.2 := by abel
        rwa [he] at h4
      linarith
    exact absurd hhigh (not_le.mpr hlow)
  -- Continuity of the `t`-dependent derivative
  have hw_cont : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ := by
    have h : Continuous fun t : ℝ => 1 + t ^ 2 := continuous_const.add (continuous_id.pow 2)
    exact h.inv₀ fun t => by positivity
  have hF'_cont : Continuous (poissonDerivAt d f p) := by
    have h1 : Continuous fun t : ℝ => fderiv ℝ f (p.1 + t • p.2) :=
      (hf.continuous_fderiv one_ne_zero).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    have h2 : Continuous fun t : ℝ =>
        (fderiv ℝ f (p.1 + t • p.2)).comp (poissonLinearMap d t) :=
      h1.clm_comp continuous_poissonLinearMap
    have h3 : Continuous fun t : ℝ =>
        (1 + t ^ 2)⁻¹ • (fderiv ℝ f (p.1 + t • p.2)).comp (poissonLinearMap d t) :=
      hw_cont.smul h2
    exact h3
  -- Integrability of the dominating function
  have h_bound_int : Integrable (poissonBound B T) volume := by
    have hcont : Continuous (poissonBound B T) := by
      have h1 : Continuous fun t : ℝ => 1 + min |t| T :=
        continuous_const.add (continuous_abs.min continuous_const)
      have h2 : Continuous fun t : ℝ => B * (1 + min |t| T) := h1.const_mul B
      have h3 : Continuous fun t : ℝ => B * (1 + min |t| T) * (1 + t ^ 2)⁻¹ :=
        h2.mul hw_cont
      exact Continuous.congr h3 fun t => by simp only [poissonBound]
    refine (integrable_inv_one_add_sq.const_mul (B * (1 + T))).mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards with t
    have hw : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    have hmin : min |t| T ≤ T := min_le_right _ _
    have hpos : 0 ≤ poissonBound B T t := poissonBound_nonneg hB0 hT0 t
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    simp only [poissonBound]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hB0) hw
  -- The Lipschitz estimate
  have hflip : ∀ a b : EuclideanSpace ℝ (Fin d), ‖f b - f a‖ ≤ B * ‖b - a‖ := fun a b =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun x _ => hf.differentiable_one x)
      (fun x _ => hB x) convex_univ (Set.mem_univ a) (Set.mem_univ b)
  have h_lip : ∀ᵐ t ∂volume, LipschitzOnWith (Real.nnabs (poissonBound B T t))
      (fun q => poissonIntegrand d f q t) (Metric.ball p δ) := by
    filter_upwards with t
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro q₁ hq₁ q₂ hq₂
    rw [Real.coe_nnabs]
    have hw : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    by_cases ht : |t| ≤ T
    · have hmin : min |t| T = |t| := min_eq_left ht
      have hbnd : |poissonBound B T t| = B * (1 + |t|) * (1 + t ^ 2)⁻¹ := by
        simp only [poissonBound, hmin]
        exact abs_of_nonneg (by positivity)
      rw [hbnd]
      have hA : (q₁.1 + t • q₁.2) - (q₂.1 + t • q₂.2) = poissonLinearMap d t (q₁ - q₂) := by
        rw [poissonLinearMap_apply, Prod.fst_sub, Prod.snd_sub, smul_sub]
        abel
      have hAle : ‖(q₁.1 + t • q₁.2) - (q₂.1 + t • q₂.2)‖ ≤ (1 + |t|) * ‖q₁ - q₂‖ := by
        rw [hA]
        calc ‖poissonLinearMap d t (q₁ - q₂)‖ ≤ ‖poissonLinearMap d t‖ * ‖q₁ - q₂‖ :=
              (poissonLinearMap d t).le_opNorm _
          _ ≤ (1 + |t|) * ‖q₁ - q₂‖ :=
              mul_le_mul_of_nonneg_right (norm_poissonLinearMap_le t) (norm_nonneg _)
      have hstep : poissonIntegrand d f q₁ t - poissonIntegrand d f q₂ t
          = (f (q₁.1 + t • q₁.2) - f (q₂.1 + t • q₂.2)) * (1 + t ^ 2)⁻¹ := by
        simp only [poissonIntegrand]; ring
      simp only [hstep, norm_mul, Real.norm_eq_abs, abs_of_nonneg hw]
      calc |f (q₁.1 + t • q₁.2) - f (q₂.1 + t • q₂.2)| * (1 + t ^ 2)⁻¹
          ≤ (B * ‖(q₁.1 + t • q₁.2) - (q₂.1 + t • q₂.2)‖) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right
              (by simpa only [Real.norm_eq_abs] using hflip _ _) hw
        _ ≤ (B * ((1 + |t|) * ‖q₁ - q₂‖)) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAle hB0) hw
        _ = B * (1 + |t|) * (1 + t ^ 2)⁻¹ * ‖q₁ - q₂‖ := by ring
    · have hbnd : |poissonBound B T t| = poissonBound B T t :=
        abs_of_nonneg (poissonBound_nonneg hB0 hT0 t)
      have hzero₁ : poissonIntegrand d f q₁ t = 0 := by
        simp only [poissonIntegrand]
        rw [hvanish q₁ hq₁ t (lt_of_not_ge ht), zero_mul]
      have hzero₂ : poissonIntegrand d f q₂ t = 0 := by
        simp only [poissonIntegrand]
        rw [hvanish q₂ hq₂ t (lt_of_not_ge ht), zero_mul]
      rw [hzero₁, hzero₂, sub_zero, norm_zero]
      exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
  -- Measurability and integrability of the integrand
  have hF_meas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (poissonIntegrand d f q) volume := by
    filter_upwards with q
    exact (poissonIntegrand_continuous hf.continuous q).aestronglyMeasurable
  have hF_int : Integrable (poissonIntegrand d f p) volume := by
    refine (integrable_inv_one_add_sq.const_mul Bf).mono'
      (poissonIntegrand_continuous hf.continuous p).aestronglyMeasurable ?_
    filter_upwards with t
    have hw : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    simp only [poissonIntegrand, norm_mul, Real.norm_eq_abs, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hBf _) hw
  have hF'_meas : AEStronglyMeasurable (poissonDerivAt d f p) volume :=
    hF'_cont.aestronglyMeasurable
  have h_diff : ∀ᵐ t ∂volume,
      HasFDerivAt (fun q => poissonIntegrand d f q t) (poissonDerivAt d f p t) p := by
    filter_upwards with t
    have h := hasFDerivAt_poissonIntegrand hf t p
    simpa only [poissonIntegrand, poissonDerivAt] using h
  obtain ⟨-, hmain⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip (𝕜 := ℝ) (μ := volume)
    (F := poissonIntegrand d f) (x₀ := p) (bound := poissonBound B T) (s := Metric.ball p δ)
    (F' := poissonDerivAt d f p) (Metric.ball_mem_nhds p hδ0) hF_meas hF_int hF'_meas h_lip
    h_bound_int h_diff
  have hfun : (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ∫ t : ℝ, poissonIntegrand d f q t) =
      (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ∫ t : ℝ, f (q.1 + t • q.2) * (1 + t ^ 2)⁻¹) := by
    funext q
    simp only [poissonIntegrand]
  rw [hfun] at hmain
  exact hmain.differentiableAt

end Commons.Analysis.Calculus