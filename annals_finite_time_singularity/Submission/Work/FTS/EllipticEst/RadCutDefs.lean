import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.RadialEnergyDefs
import Submission.Work.FTS.EllipticEst.cutoff_facts
import Submission.Work.FTS.EllipticEst.Phi_derivs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The truncated radial energy functional: interface

This module collects the vocabulary used by `Work.FTS.EllipticEst.radial_energy_of_truncated`:

* the angular `θ`-integrals `thRadSq Φ`, `thDthSq Φ`, `thDivCosSq Φ`, `thGPair G Φ` of the four
  quadratic quantities appearing in the radial energy inequality and of the source pairing;
* the truncated functionals `tS, tB, tC, tP, tL` obtained from those by integrating against the
  truncated weight `cutW R = chi (·/R) · w²` of `RadialEnergyDefs`, and the truncation error
  `tErr Φ R = ∫_{z > R} w z² · ∫_θ Φ(z,θ)²`;
* the elementary facts about `cutW` (positivity, domination by `w²`, measurability, the values on
  `[0,R]` and off `[0,2R]`, pointwise convergence to `w²`);
* the dominated-convergence tool `tendsto_integral_chi_mul`;
* the identification `w z² · ∫_θ h(z,θ)² = ∫_θ (h(z,θ) · w z)²`, which turns the `L2Mem`
  hypotheses of the caller into integrability of the untruncated integrands;
* almost-everywhere strong measurability of the `θ`-integrals above (from continuity of the
  integrand on the open quadrant).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RadCut

/-! ## The truncated functionals -/

/-- The angular integral `z ↦ ∫_θ (z ∂_zΦ(z,θ))²`. -/
def thRadSq (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz Φ z θ) ^ 2

/-- The angular integral `z ↦ ∫_θ (∂_θΦ(z,θ))²`. -/
def thDthSq (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Φ z θ) ^ 2

/-- The angular integral `z ↦ ∫_θ (Φ(z,θ)/cos θ)²`. -/
def thDivCosSq (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Φ z θ / Real.cos θ) ^ 2

/-- The angular pairing `z ↦ ∫_θ G(z,θ)·Φ(z,θ)` of the source with the solution. -/
def thGPair (G Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, G z θ * Φ z θ

/-- The truncated radial term `α² ∫ cutW R · ∫_θ (∂_zΦ)²` of the identity (written exactly as it
occurs in `TruncIdentity`). -/
def tS (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, z ^ 2 * Work.FTS.EllipticEst.cutW R z
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Φ z θ) ^ 2)

/-- The truncated angular term `∫ cutW R · ∫_θ (∂_θΦ)²`. -/
def tB (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cutW R z * thDthSq Φ z

/-- The truncated angular term `∫ cutW R · ∫_θ (Φ/cos θ)²`. -/
def tC (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cutW R z * thDivCosSq Φ z

/-- The truncated `L²`-mass `∫ cutW R · ∫_θ Φ²`. -/
def tP (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cutW R z * Work.FTS.EllipticEst.thSq Φ z

/-- The truncated source pairing `∫ cutW R · ∫_θ G·Φ`. -/
def tL (G Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cutW R z * thGPair G Φ z

/-- The truncation error `∫_{z > R} w z² · ∫_θ Φ(z,θ)²`. -/
def tErr (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Set.Ioi R, (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thSq Φ z

/-! ## Elementary facts about the truncated weight -/

theorem cutW_nonneg (R z : ℝ) : 0 ≤ Work.FTS.EllipticEst.cutW R z :=
  mul_nonneg (Work.Stability.chi_nonneg _) (sq_nonneg _)

theorem cutW_le_wSq (R z : ℝ) : Work.FTS.EllipticEst.cutW R z ≤ (Work.Spaces.w z) ^ 2 :=
  mul_le_of_le_one_left (sq_nonneg _) (Work.Stability.chi_le_one _)

theorem measurable_cutW (R : ℝ) : Measurable (Work.FTS.EllipticEst.cutW R) := by
  have h1 : Measurable (fun z : ℝ => Work.Stability.chi (z / R)) :=
    Work.Stability.chi_continuous.measurable.comp (measurable_id.div_const R)
  have h2 : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
    rw [h]
    exact (Measurable.div ((measurable_const.add measurable_id).pow_const 2)
      (measurable_id.pow_const 2)).pow_const 2
  exact h1.mul h2

theorem cutW_eq_wSq {R z : ℝ} (hR : 1 ≤ R) (hz0 : 0 ≤ z) (hz : z ≤ R) :
    Work.FTS.EllipticEst.cutW R z = (Work.Spaces.w z) ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have habs : |z / R| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hz0 hR0.le), div_le_one hR0]
    exact hz
  rw [Work.FTS.EllipticEst.cutW, Work.Stability.chi_eq_one habs, one_mul]

theorem cutW_eq_zero {R z : ℝ} (hR : 1 ≤ R) (hz : 2 * R ≤ z) :
    Work.FTS.EllipticEst.cutW R z = 0 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have habs : 2 ≤ |z / R| := by
    rw [abs_of_nonneg (div_nonneg (by linarith) hR0.le), le_div_iff₀ hR0]
    linarith
  rw [Work.FTS.EllipticEst.cutW, Work.Stability.chi_eq_zero habs, zero_mul]

theorem chi_tendsto_one {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun R : ℝ => Work.Stability.chi (z / R)) atTop (𝓝 1) := by
  rw [tendsto_congr' (Filter.eventually_atTop.2 ⟨max 1 z, fun R hR => ?_⟩)]
  · exact tendsto_const_nhds
  · have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hzle : z ≤ R := le_trans (le_max_right _ _) hR
    have habs : |z / R| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hz hR0.le), div_le_one hR0]; exact hzle
    exact Work.Stability.chi_eq_one habs

theorem cutW_tendsto_wSq {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun R : ℝ => Work.FTS.EllipticEst.cutW R z) atTop (𝓝 ((Work.Spaces.w z) ^ 2)) := by
  simpa [Work.FTS.EllipticEst.cutW] using
    (chi_tendsto_one hz).mul_const ((Work.Spaces.w z) ^ 2)

/-! ## Dominated convergence with the rescaled cut-off -/

/-- For every function `g` integrable on `Iz = [0,∞)`, `∫_z chi (z/R)·g z → ∫_z g z`. -/
theorem tendsto_integral_chi_mul (g : ℝ → ℝ) (hg : MeasureTheory.IntegrableOn g Work.Spaces.Iz) :
    Tendsto (fun R : ℝ => ∫ z in Work.Spaces.Iz, Work.Stability.chi (z / R) * g z)
      atTop (𝓝 (∫ z in Work.Spaces.Iz, g z)) := by
  have hI : (Filter.atTop : Filter ℝ).IsCountablyGenerated := inferInstance
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (F := fun R z => Work.Stability.chi (z / R) * g z) (f := g)
    (bound := fun z => ‖g z‖) (l := atTop) (μ := volume.restrict Work.Spaces.Iz) ?_ ?_ ?_ ?_
  · filter_upwards with R
    exact ((Work.Stability.chi_continuous.measurable.comp
      (measurable_id.div_const R)).aestronglyMeasurable).mul hg.aestronglyMeasurable
  · filter_upwards with R
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Work.Stability.chi_le_one _)
  · exact hg.norm
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have h1 : Tendsto (fun R : ℝ => Work.Stability.chi (z / R)) atTop (𝓝 1) := chi_tendsto_one hz
    simpa using h1.mul_const (g z)

/-- If `f ≥ 0` is almost everywhere strongly measurable and `w²·f` is integrable, then so is
`cutW R · f`: the truncated weight is dominated by `w²`. -/
theorem integrableOn_cutW_mul {f : ℝ → ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable f (volume.restrict Work.Spaces.Iz))
    (hpos : ∀ z, 0 ≤ f z)
    (hf : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * f z) Work.Spaces.Iz)
    (R : ℝ) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cutW R z * f z) Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' hf ?_ ?_
  · exact (measurable_cutW R).aestronglyMeasurable.mul hmeas
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutW_nonneg R z), abs_of_nonneg (hpos z)]
    exact mul_le_mul_of_nonneg_right (cutW_le_wSq R z) (hpos z)

/-! ## From the `L2Mem` hypotheses to integrability of the untruncated integrands -/

/-- `w z² · ∫_θ h(z,θ)² = ∫_θ (h(z,θ)·w z)²`. -/
theorem wSq_mul_integral_sq (h : ℝ → ℝ → ℝ) (z : ℝ) :
    (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (h z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (h z θ * Work.Spaces.w z) ^ 2 := by
  have hfun : (fun θ : ℝ => (h z θ * Work.Spaces.w z) ^ 2)
      = fun θ : ℝ => (h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    funext θ; ring
  rw [hfun, MeasureTheory.integral_mul_const]
  ring

/-- An `L2Mem` hypothesis for `h·w` gives integrability of `w²·∫_θ h²`. -/
theorem integrableOn_wSq_mul_thetaSq {h : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.L2Mem (fun z θ => h z θ * Work.Spaces.w z)) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (h z θ) ^ 2))
      Work.Spaces.Iz := by
  refine hmem.2.congr_fun (fun z _ => ?_) measurableSet_Ici
  exact (wSq_mul_integral_sq h z).symm

/-- **The weighted `L²`-square as an iterated integral of the unweighted slice square**:
`L2Sq (h·w) = ∫_z w z² · ∫_θ h(z,θ)²`. -/
theorem L2Sq_mul_w_eq (h : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => h z θ * Work.Spaces.w z)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (h z θ) ^ 2) := by
  rw [Work.Spaces.L2Sq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici
    fun z _ => (wSq_mul_integral_sq h z).symm

/-- **The radial term of the energy inequality**: `L2Sq (z ∂_zΦ · w)` written as the integral of
the truncated radial integrand's limit. -/
theorem L2Sq_radSq (Φ : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz Φ z θ * Work.Spaces.w z)
      = ∫ z in Work.Spaces.Iz, z ^ 2 * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Φ z θ) ^ 2) := by
  rw [L2Sq_mul_w_eq (fun z θ => z * Work.Spaces.pz Φ z θ)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  have h1 : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz Φ z θ) ^ 2)
      = z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Φ z θ) ^ 2) := by
    rw [show (fun θ : ℝ => (z * Work.Spaces.pz Φ z θ) ^ 2)
        = fun θ : ℝ => z ^ 2 * (Work.Spaces.pz Φ z θ) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  rw [h1]
  ring

/-! ## Almost everywhere strong measurability of the angular integrals -/

/-- The open quadrant `(0,∞) × (0,π/2)` is contained in the smoothness neighbourhood of
`SmoothNbhd`. -/
theorem quad_subset_nbhU :
    Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ⊆ Work.Spaces.nbhU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  rw [Work.Spaces.nbhU]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Set.mem_Ioi] at hz ⊢; linarith
  · simp only [Set.mem_Ioo] at hθ ⊢; linarith [hθ.1]
  · simp only [Set.mem_Ioo] at hθ ⊢; linarith [hθ.2, Real.pi_pos]

/-- A function smooth on a neighbourhood of the closed quadrant is continuous on the open
quadrant. -/
theorem continuousOn_quad_of_smoothNbhd {F : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  h.continuousOn.mono quad_subset_nbhU

/-- The `θ`-integral of a function continuous on the open quadrant is almost everywhere strongly
measurable as a function of `z` (Fubini, together with the fact that the product of the
restrictions of Lebesgue measure to `Iz` and `Iθ` is the planar measure of the quadrant). -/
theorem aesm_integral_theta {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, F z θ)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => F p.1 p.2) hcont).integral_prod_right'

theorem aesm_thSq (Φ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Φ) :
    MeasureTheory.AEStronglyMeasurable (Work.FTS.EllipticEst.thSq Φ)
      (volume.restrict Work.Spaces.Iz) :=
  aesm_integral_theta (F := fun z θ => (Φ z θ) ^ 2)
    ((continuousOn_quad_of_smoothNbhd hsm).pow 2)

theorem aesm_thDthSq (Φ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Φ) :
    MeasureTheory.AEStronglyMeasurable (thDthSq Φ) (volume.restrict Work.Spaces.Iz) :=
  aesm_integral_theta (F := fun z θ => (Work.Spaces.pth Φ z θ) ^ 2)
    ((continuousOn_quad_of_smoothNbhd
      (Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_nbhU hsm)).pow 2)

theorem aesm_thDivCosSq (Φ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Φ) :
    MeasureTheory.AEStronglyMeasurable (thDivCosSq Φ) (volume.restrict Work.Spaces.Iz) := by
  refine aesm_integral_theta (F := fun z θ => (Φ z θ / Real.cos θ) ^ 2) ?_
  refine ((continuousOn_quad_of_smoothNbhd hsm).div ?_ ?_).pow 2
  · exact (Real.continuous_cos.comp continuous_snd).continuousOn
  · intro p hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)

theorem aesm_thRadSq (Φ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Φ) :
    MeasureTheory.AEStronglyMeasurable (thRadSq Φ) (volume.restrict Work.Spaces.Iz) :=
  aesm_integral_theta (F := fun z θ => (z * Work.Spaces.pz Φ z θ) ^ 2)
    ((continuousOn_fst.mul (continuousOn_quad_of_smoothNbhd
      (Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_nbhU hsm))).pow 2)

end Work.FTS.EllipticEst.RadCut
