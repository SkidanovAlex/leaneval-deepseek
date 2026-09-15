import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.differentiableAt_poisson_extension_of_second_ne
import Submission.Commons.MeasureTheory.Integral.intervalIntegral_eq_integral_of_tsupport_subset

open MeasureTheory Filter Set
open scoped Topology Interval

namespace Commons.Analysis.Calculus

/-- The product space `ℝᵈ × ℝᵈ`. -/
abbrev PoissonDiag (d : ℕ) := EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)

/-- Post-composition by a fixed continuous linear map, as a continuous linear map. -/
noncomputable def poissonPostcomp (d : ℕ) :
    (PoissonDiag d →L[ℝ] EuclideanSpace ℝ (Fin d)) →L[ℝ]
      ((EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (PoissonDiag d →L[ℝ] ℝ)) :=
  (ContinuousLinearMap.compL ℝ (PoissonDiag d) (EuclideanSpace ℝ (Fin d)) ℝ).flip

lemma postcomp_apply (d : ℕ) (L : PoissonDiag d →L[ℝ] EuclideanSpace ℝ (Fin d))
    (C : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    poissonPostcomp d L C = C.comp L := by
  simp [poissonPostcomp, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

lemma norm_postcomp_le (d : ℕ) (L : PoissonDiag d →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ‖poissonPostcomp d L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro C
  rw [postcomp_apply]
  calc ‖C.comp L‖ ≤ ‖C‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le C L
    _ = ‖L‖ * ‖C‖ := mul_comm _ _

/-- The derivative of `x ↦ (Df (x.₁ + s • x.₂)) ∘ (x ↦ x.₁ + s • x.₂)`. -/
lemma hasFDerivAt_fderiv_poisson (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ContDiff ℝ 2 F) (s : ℝ) (q : PoissonDiag d) :
    HasFDerivAt (fun x : PoissonDiag d => (fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s))
      ((poissonPostcomp d (poissonLinearMap d s)).comp
        ((fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)).comp (poissonLinearMap d s))) q := by
  have hh : HasFDerivAt (fun x : PoissonDiag d => x.1 + s • x.2) (poissonLinearMap d s) q := by
    have h1 : HasFDerivAt (poissonLinearMap d s) (poissonLinearMap d s) q :=
      (poissonLinearMap d s).hasFDerivAt
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun x => (poissonLinearMap_apply s x).symm)
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ F) := by
    have h := hF.fderiv_right (m := (1 : ℕ∞)) (by norm_num)
    simpa using h
  have hfd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)) (q.1 + s • q.2) :=
    ((hfd1.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hcomp : HasFDerivAt (fun x : PoissonDiag d => fderiv ℝ F (x.1 + s • x.2))
      ((fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)).comp (poissonLinearMap d s)) q := by
    have h := hfd.comp q hh
    simpa [Function.comp_def] using h
  have hpc : HasFDerivAt (fun C : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => C.comp (poissonLinearMap d s))
      (poissonPostcomp d (poissonLinearMap d s)) (fderiv ℝ F (q.1 + s • q.2)) := by
    have h1 : HasFDerivAt (poissonPostcomp d (poissonLinearMap d s)) (poissonPostcomp d (poissonLinearMap d s))
        (fderiv ℝ F (q.1 + s • q.2)) := (poissonPostcomp d (poissonLinearMap d s)).hasFDerivAt
    exact h1.congr_of_eventuallyEq
      (Eventually.of_forall fun C => (postcomp_apply d (poissonLinearMap d s) C).symm)
  have hmain := hpc.comp q hcomp
  simpa [Function.comp_def, ContinuousLinearMap.comp_assoc] using hmain

/-- **The shifted interval integral of a `C²` function is `C²`.**
For `F : ℝᵈ → ℝ` of class `C²` with bounded first and second derivative,
`q ↦ ∫ s in a..b, F (q.₁ + s • q.₂) * (1 + s²)⁻¹` is `C²`. -/
theorem contDiff_two_intervalIntegral_shift (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ContDiff ℝ 2 F) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B2)
    (a b : ℝ) :
    ContDiff ℝ 2 (fun q : PoissonDiag d => ∫ s in a..b, F (q.1 + s • q.2) * (1 + s ^ 2)⁻¹) := by
  have hψcont : Continuous (fun s : ℝ => (1 + s ^ 2)⁻¹) := by
    have : Continuous (fun s : ℝ => 1 + s ^ 2) := by fun_prop
    exact this.inv₀ (fun s => by positivity)
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hB1nn : 0 ≤ B1 := le_trans (norm_nonneg (fderiv ℝ F 0)) (hB1 0)
  have hB2nn : 0 ≤ B2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)) (hB2 0)
  have hfdc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ F) := by
    have h := hF.fderiv_right (m := (1 : ℕ∞)) (by norm_num); simpa using h
  have hfd2c : Continuous (fderiv ℝ (fderiv ℝ F)) := hfd1.continuous_fderiv (by norm_num)
  -- Step 1
  have hstep1 : ∀ q : PoissonDiag d,
      HasFDerivAt (fun x : PoissonDiag d => ∫ s in a..b, F (x.1 + s • x.2) * (1 + s ^ 2)⁻¹)
        (∫ s in a..b, (1 + s ^ 2)⁻¹ • ((fderiv ℝ F (q.1 + s • q.2)).comp (poissonLinearMap d s))) q := by
    intro q
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (s := Set.univ) (a := a) (b := b)
      (F := fun x : PoissonDiag d => fun s : ℝ => F (x.1 + s • x.2) * (1 + s ^ 2)⁻¹)
      (F' := fun x : PoissonDiag d => fun s : ℝ =>
        (1 + s ^ 2)⁻¹ • ((fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s)))
      (x₀ := q) (bound := fun s : ℝ => B1 * (1 + |s|))
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun x => rfl)
    · filter_upwards with x
      exact ((hF.continuous.comp (by fun_prop)).mul hψcont).aestronglyMeasurable
    · exact ((hF.continuous.comp (by fun_prop)).mul hψcont).intervalIntegrable a b
    · exact (hψcont.smul (hfdc.comp (by fun_prop) |>.clm_comp continuous_poissonLinearMap)).aestronglyMeasurable
    · filter_upwards with s hs x hx
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (1 + s ^ 2)⁻¹ * ‖(fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s)‖
          ≤ (1 + s ^ 2)⁻¹ * (B1 * (1 + |s|)) := by
            gcongr
            calc ‖(fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s)‖
                  ≤ ‖fderiv ℝ F (x.1 + s • x.2)‖ * ‖poissonLinearMap d s‖ :=
                    ContinuousLinearMap.opNorm_comp_le _ _
                _ ≤ B1 * (1 + |s|) :=
                    mul_le_mul (hB1 _) (norm_poissonLinearMap_le s)
                      (norm_nonneg (poissonLinearMap d s)) hB1nn
        _ ≤ 1 * (B1 * (1 + |s|)) := by
            gcongr
            exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg s] : (1 : ℝ) ≤ 1 + s ^ 2)
        _ = B1 * (1 + |s|) := one_mul _
    · exact (continuous_const.mul (continuous_const.add continuous_abs)).intervalIntegrable a b
    · filter_upwards with s hs x hx
      exact hasFDerivAt_poissonIntegrand hF1 s x
  -- Step 2
  have hstep2 : ∀ q : PoissonDiag d,
      HasFDerivAt (fun x : PoissonDiag d => ∫ s in a..b,
          (1 + s ^ 2)⁻¹ • ((fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s)))
        (∫ s in a..b,
          (1 + s ^ 2)⁻¹ • ((poissonPostcomp d (poissonLinearMap d s)).comp
            ((fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)).comp (poissonLinearMap d s)))) q := by
    intro q
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (s := Set.univ) (a := a) (b := b)
      (F := fun x : PoissonDiag d => fun s : ℝ =>
        (1 + s ^ 2)⁻¹ • ((fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s)))
      (F' := fun x : PoissonDiag d => fun s : ℝ =>
        (1 + s ^ 2)⁻¹ • ((poissonPostcomp d (poissonLinearMap d s)).comp
          ((fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2)).comp (poissonLinearMap d s))))
      (x₀ := q) (bound := fun s : ℝ => B2 * (1 + |s|) ^ 2)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun x => rfl)
    · filter_upwards with x
      exact (hψcont.smul (hfdc.comp (by fun_prop) |>.clm_comp continuous_poissonLinearMap)).aestronglyMeasurable
    · exact (hψcont.smul (hfdc.comp (by fun_prop) |>.clm_comp continuous_poissonLinearMap)).intervalIntegrable a b
    · exact (hψcont.smul (((ContinuousLinearMap.continuous (poissonPostcomp d)).comp continuous_poissonLinearMap).clm_comp
        (hfd2c.comp (by fun_prop) |>.clm_comp continuous_poissonLinearMap))).aestronglyMeasurable
    · filter_upwards with s hs x hx
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (1 + s ^ 2)⁻¹ * ‖(poissonPostcomp d (poissonLinearMap d s)).comp
            ((fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2)).comp (poissonLinearMap d s))‖
          ≤ (1 + s ^ 2)⁻¹ * (B2 * (1 + |s|) ^ 2) := by
            gcongr
            calc ‖(poissonPostcomp d (poissonLinearMap d s)).comp
                  ((fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2)).comp (poissonLinearMap d s))‖
                ≤ ‖poissonPostcomp d (poissonLinearMap d s)‖ *
                  ‖(fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2)).comp (poissonLinearMap d s)‖ :=
                  ContinuousLinearMap.opNorm_comp_le _ _
              _ ≤ (1 + |s|) * (B2 * (1 + |s|)) := by
                  apply mul_le_mul
                  · exact (norm_postcomp_le d _).trans (norm_poissonLinearMap_le s)
                  · calc ‖(fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2)).comp (poissonLinearMap d s)‖
                        ≤ ‖fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2)‖ * ‖poissonLinearMap d s‖ :=
                          ContinuousLinearMap.opNorm_comp_le _ _
                      _ ≤ B2 * (1 + |s|) :=
                          mul_le_mul (hB2 _) (norm_poissonLinearMap_le s)
                            (norm_nonneg (poissonLinearMap d s)) hB2nn
                  · exact norm_nonneg (fderiv ℝ (fderiv ℝ F) (x.1 + s • x.2) ∘SL poissonLinearMap d s)
                  · positivity
              _ = B2 * (1 + |s|) ^ 2 := by ring
        _ ≤ 1 * (B2 * (1 + |s|) ^ 2) := by
            gcongr
            exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg s] : (1 : ℝ) ≤ 1 + s ^ 2)
        _ = B2 * (1 + |s|) ^ 2 := one_mul _
    · exact (continuous_const.mul ((continuous_const.add continuous_abs).pow 2)).intervalIntegrable a b
    · filter_upwards with s hs x hx
      exact (hasFDerivAt_fderiv_poisson d F hF s x).const_smul ((1 + s ^ 2)⁻¹)
  -- Step 3 : continuity of the second derivative candidate
  have huncurry : Continuous (Function.uncurry (fun q : PoissonDiag d => fun s : ℝ =>
      (1 + s ^ 2)⁻¹ • ((poissonPostcomp d (poissonLinearMap d s)).comp
        ((fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)).comp (poissonLinearMap d s))))) := by
    have hz : Continuous (fun p : PoissonDiag d × ℝ => p.1.1 + p.2 • p.1.2) := by fun_prop
    have hL : Continuous (fun p : PoissonDiag d × ℝ => poissonLinearMap d p.2) :=
      continuous_poissonLinearMap.comp continuous_snd
    have hD2 : Continuous (fun p : PoissonDiag d × ℝ => fderiv ℝ (fderiv ℝ F) (p.1.1 + p.2 • p.1.2)) :=
      hfd2c.comp hz
    have hB : Continuous (fun p : PoissonDiag d × ℝ =>
        (fderiv ℝ (fderiv ℝ F) (p.1.1 + p.2 • p.1.2)).comp (poissonLinearMap d p.2)) :=
      hD2.clm_comp hL
    have hpc : Continuous (fun p : PoissonDiag d × ℝ => poissonPostcomp d (poissonLinearMap d p.2)) :=
      (ContinuousLinearMap.continuous (poissonPostcomp d)).comp hL
    have hcomp : Continuous (fun p : PoissonDiag d × ℝ =>
        (poissonPostcomp d (poissonLinearMap d p.2)).comp
          ((fderiv ℝ (fderiv ℝ F) (p.1.1 + p.2 • p.1.2)).comp (poissonLinearMap d p.2))) :=
      hpc.clm_comp hB
    have hψp : Continuous (fun p : PoissonDiag d × ℝ => (1 + p.2 ^ 2)⁻¹) := hψcont.comp continuous_snd
    have hjoint : Continuous (fun p : PoissonDiag d × ℝ => (1 + p.2 ^ 2)⁻¹ •
        ((poissonPostcomp d (poissonLinearMap d p.2)).comp
          ((fderiv ℝ (fderiv ℝ F) (p.1.1 + p.2 • p.1.2)).comp (poissonLinearMap d p.2)))) :=
      hψp.smul hcomp
    rw [show Function.uncurry (fun q : PoissonDiag d => fun s : ℝ =>
        (1 + s ^ 2)⁻¹ • ((poissonPostcomp d (poissonLinearMap d s)).comp
          ((fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)).comp (poissonLinearMap d s))))
        = (fun p : PoissonDiag d × ℝ => (1 + p.2 ^ 2)⁻¹ • ((poissonPostcomp d (poissonLinearMap d p.2)).comp
          ((fderiv ℝ (fderiv ℝ F) (p.1.1 + p.2 • p.1.2)).comp (poissonLinearMap d p.2)))) from rfl]
    exact hjoint
  have hcont2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun q : PoissonDiag d => fun s : ℝ =>
      (1 + s ^ 2)⁻¹ • ((poissonPostcomp d (poissonLinearMap d s)).comp
        ((fderiv ℝ (fderiv ℝ F) (q.1 + s • q.2)).comp (poissonLinearMap d s)))) huncurry a b
  have hD1 : ContDiff ℝ 1 (fun x : PoissonDiag d => ∫ s in a..b,
      (1 + s ^ 2)⁻¹ • ((fderiv ℝ F (x.1 + s • x.2)).comp (poissonLinearMap d s))) := by
    rw [contDiff_one_iff_hasFDerivAt]
    exact ⟨_, hcont2, hstep2⟩
  exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)).mpr ⟨_, hD1, hstep1⟩

theorem contDiffOn_two_Eomega_diag {d : ℕ} {ω : EuclideanSpace ℝ (Fin d) → ℝ}
    (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) :
    ContDiffOn ℝ 2 (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫ u : ℝ, ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹) {p | p.2 ≠ 0} := by
  -- Bounds on the first and second derivatives of `ω`
  obtain ⟨B1, hB1nn, hB1⟩ :=
    exists_bound_fderiv_of_contDiff_one_hasCompactSupport (hω.of_le (by norm_num)) hc
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ ω) := by
    have h := hω.fderiv_right (m := (1 : ℕ∞)) (by norm_num); simpa using h
  obtain ⟨B2, hB2nn, hB2⟩ :=
    exists_bound_fderiv_of_contDiff_one_hasCompactSupport hfd1 (hc.fderiv ℝ)
  -- The set `{p | p.2 ≠ 0}` is open
  have hUo : IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
    have h1 : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0}
        = (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2) ⁻¹' ({0}ᶜ) := rfl
    rw [h1]
    exact isOpen_compl_singleton.preimage continuous_snd
  rw [hUo.contDiffOn_iff]
  -- Bound `R` for the support of `ω`
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.exists_bound_of_continuousOn
    (continuousOn_id : ContinuousOn (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (tsupport ω))
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ z ∈ tsupport ω, ‖z‖ ≤ R := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  intro q₀ hq₀
  have hq₂ : 0 < ‖q₀.2‖ := norm_pos_iff.mpr hq₀
  set δ : ℝ := min 1 (‖q₀.2‖ / 2) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ‖q₀.2‖ / 2 := min_le_right _ _
  set T : ℝ := 2 * (R + ‖q₀.1‖ + 1) / ‖q₀.2‖ with hTdef
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact div_nonneg (by linarith [hR0, norm_nonneg q₀.1]) (norm_nonneg _)
  have hTm : T * (‖q₀.2‖ / 2) = R + ‖q₀.1‖ + 1 := by
    rw [hTdef]; field_simp
  -- the integrand vanishes for `|t| > T` on the whole ball
  have hvanish : ∀ q ∈ Metric.ball q₀ δ, ∀ t : ℝ, T < |t| → ω (q.1 + t • q.2) = 0 := by
    intro q hq t ht
    by_contra hne
    have hzt : q.1 + t • q.2 ∈ tsupport ω := subset_tsupport ω hne
    have hzR : ‖q.1 + t • q.2‖ ≤ R := hR _ hzt
    have hq2 : ‖q₀.2‖ / 2 ≤ ‖q.2‖ := by
      have h1 : ‖q₀.2‖ ≤ ‖q.2‖ + ‖q₀.2 - q.2‖ := by
        have he : q.2 + (q₀.2 - q.2) = q₀.2 := by abel
        calc ‖q₀.2‖ = ‖q.2 + (q₀.2 - q.2)‖ := by rw [he]
          _ ≤ ‖q.2‖ + ‖q₀.2 - q.2‖ := norm_add_le _ _
      have h2 : ‖q₀.2 - q.2‖ < δ := by
        calc ‖q₀.2 - q.2‖ = ‖(q₀ - q).2‖ := by simp
          _ ≤ ‖q₀ - q‖ := norm_snd_le _
          _ = dist q q₀ := by rw [dist_eq_norm, norm_sub_rev]
          _ < δ := hq
      linarith
    have hq1 : ‖q.1‖ ≤ ‖q₀.1‖ + 1 := by
      have h2 : ‖q.1 - q₀.1‖ < δ := by
        calc ‖q.1 - q₀.1‖ = ‖(q - q₀).1‖ := by simp
          _ ≤ ‖q - q₀‖ := norm_fst_le _
          _ = dist q q₀ := by rw [dist_eq_norm]
          _ < δ := hq
      have h3 : ‖q.1‖ ≤ ‖q.1 - q₀.1‖ + ‖q₀.1‖ := by
        have he : (q.1 - q₀.1) + q₀.1 = q.1 := by abel
        have h4 := norm_add_le (q.1 - q₀.1) q₀.1
        rwa [he] at h4
      linarith
    have hlow : R + ‖q₀.1‖ + 1 < |t| * ‖q.2‖ := by
      have h1 : T * (‖q₀.2‖ / 2) < |t| * (‖q₀.2‖ / 2) :=
        mul_lt_mul_of_pos_right (lt_of_not_ge (not_le.mpr ht)) (by positivity)
      have h2 : |t| * (‖q₀.2‖ / 2) ≤ |t| * ‖q.2‖ :=
        mul_le_mul_of_nonneg_left hq2 (abs_nonneg t)
      linarith [hTm]
    have hhigh : |t| * ‖q.2‖ ≤ R + ‖q₀.1‖ + 1 := by
      have h1 : ‖t • q.2‖ = |t| * ‖q.2‖ := by rw [norm_smul, Real.norm_eq_abs]
      have h3 : ‖t • q.2‖ ≤ ‖q.1 + t • q.2‖ + ‖q.1‖ := by
        have h4 := norm_sub_le (q.1 + t • q.2) q.1
        have he : (q.1 + t • q.2) - q.1 = t • q.2 := by abel
        rwa [he] at h4
      linarith
    exact absurd hhigh (not_le.mpr hlow)
  -- the whole-line integral agrees with an interval integral near `q₀`
  have hlocal : ∀ q ∈ Metric.ball q₀ δ,
      (∫ u : ℝ, ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹)
        = ∫ u in (-(T + 1))..(T + 1), ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹ := by
    intro q hq
    have hH : tsupport (fun u : ℝ => ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹)
        ⊆ Set.Ioo (-(T + 1)) (T + 1) := by
      have hzero : ∀ u : ℝ, T < |u| →
          (fun u : ℝ => ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹) u = 0 := by
        intro u hu
        simp only
        rw [hvanish q hq u hu, zero_mul]
      have hsupp : Function.support (fun u : ℝ => ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹)
          ⊆ {u : ℝ | |u| ≤ T} := by
        intro u hu
        by_contra hc
        exact hu (hzero u (not_le.mp (show ¬ |u| ≤ T from hc)))
      have hclosed : IsClosed {u : ℝ | |u| ≤ T} :=
        isClosed_le continuous_abs continuous_const
      have h1 : tsupport (fun u : ℝ => ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹)
          ⊆ {u : ℝ | |u| ≤ T} := by
        rw [tsupport]
        exact closure_minimal hsupp hclosed
      refine h1.trans ?_
      intro u hu
      have hu' := abs_le.mp (show |u| ≤ T from hu)
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    have h := Commons.MeasureTheory.Integral.intervalIntegral_eq_integral_of_tsupport_subset
      (H := fun u : ℝ => ω (q.1 + u • q.2) * (1 + u ^ 2)⁻¹)
      (a := -(T + 1)) (b := T + 1) (by linarith) hH
    exact h.symm
  have hev : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ∫ u : ℝ, ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹)
      =ᶠ[𝓝 q₀] (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ∫ u in (-(T + 1))..(T + 1), ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹) := by
    filter_upwards [Metric.ball_mem_nhds q₀ hδ0] with q hq
    exact hlocal q hq
  have hcd : ContDiff ℝ 2 (fun p : PoissonDiag d =>
      ∫ u in (-(T + 1))..(T + 1), ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹) :=
    contDiff_two_intervalIntegral_shift d ω hω hB1 hB2 _ _
  exact (hcd.contDiffAt (x := q₀)).congr_of_eventuallyEq hev

end Commons.Analysis.Calculus