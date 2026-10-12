import ChallengeDeps
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.NewtonRep
import Submission.ShellCapChild
import Submission.ShellOneDimChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Downstream assembly for the shell formula

This module derives, from the projection measure (`shell_proj_measure`) and
the one-dimensional integral identity (`shell_integral_sqrt_one`), the
*spherical mean* of the Newton kernel over a shell, and assembles the polar
decomposition of `∫_y g(y)‖x−y‖⁻¹ dy` into its one-dimensional form.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real ENNReal NNReal BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

-- ============ interface to the child-proved lemmas ============
-- `shell_proj_measure` is proved in `Submission.ShellCapChild`,
-- `shell_integral_sqrt_one` in `Submission.ShellOneDimChild`.  We keep the
-- (now alias) names below to avoid changing all internal references.

lemma shell_proj_measure_dev :
    (volume.toSphere : Measure ShellS2).map (fun u : ShellS2 => (u : ℝ³) 0) =
      ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ) :=
  shell_proj_measure

/-- Squared distance from `r•shellE0` to `s•u` (u on the unit sphere). -/
lemma shell_sq_norm_sub_e0 (r s : ℝ) (u : ShellS2) :
    ‖r • shellE0 - s • (u : ℝ³)‖ ^ 2 =
      r ^ 2 + s ^ 2 - 2 * r * s * (u : ℝ³) 0 := by
  have hnorm : (u : ℝ³) 0 ^ 2 + (u : ℝ³) 1 ^ 2 + (u : ℝ³) 2 ^ 2 = 1 := by
    have hu : ‖(u : ℝ³)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm, dist_zero_right] using u.2
    have h1 : ‖(u : ℝ³)‖ ^ 2 = 1 := by rw [hu]; norm_num
    have hs : (∑ i : Fin 3, (u : ℝ³) i ^ 2) = 1 := by
      rw [← shell_sq_norm3 (u : ℝ³)]
      exact h1
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
    simp at hs
    nlinarith [hs]
  rw [shell_sq_norm3]
  simp [shellE0_coord]
  rw [show (∑ x : Fin 3, ((if x = (0 : Fin 3) then r else 0) - s * (u : ℝ³) x) ^ 2) =
      (r - s * (u : ℝ³) 0) ^ 2 + (s * (u : ℝ³) 1) ^ 2 + (s * (u : ℝ³) 2) ^ 2 by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp
    ring]
  nlinarith [hnorm]

/-- `√(‖z‖²) = ‖z‖`. -/
lemma shell_sqrt_sq_norm (z : ℝ³) : Real.sqrt (‖z‖ ^ 2) = ‖z‖ := by
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (norm_nonneg z)

/-- Distance `‖r•shellE0 − s•u‖` equals the square root expression. -/
lemma shell_kernel_eq_sqrt (r s : ℝ) (u : ShellS2) :
    ‖r • shellE0 - s • (u : ℝ³)‖ = Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * (u : ℝ³) 0) := by
  have hsq := shell_sq_norm_sub_e0 r s u
  calc
    ‖r • shellE0 - s • (u : ℝ³)‖ = Real.sqrt (‖r • shellE0 - s • (u : ℝ³)‖ ^ 2) := by
      rw [shell_sqrt_sq_norm]
    _ = Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * (u : ℝ³) 0) := by rw [hsq]



section AxisReduction

/-- A whole-space integral is invariant under replacing the "centre" `x` by
any vector of the same norm, for radial `g`: with an isometry moving `x` to
`‖x‖•shellE0`. -/
lemma shell_axis_reduce {g : ℝ³ → ℝ} (hgrad : IsRadial g) {x : ℝ³} (hx : x ≠ 0) :
    (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹) =
      (∫ y : ℝ³, g y * (‖(‖x‖ • shellE0) - y‖ : ℝ)⁻¹) := by
  let r : ℝ := ‖x‖
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr hx
  have hnorm : ‖r • shellE0‖ = ‖x‖ := by
    dsimp [r]
    calc
      ‖‖x‖ • shellE0‖ = ‖‖x‖‖ * ‖shellE0‖ := by rw [norm_smul]
      _ = ‖x‖ := by rw [shellE0_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rcases exists_linearIsometry_of_norm_eq (x := r • shellE0) (y := x) hnorm with ⟨U, hU⟩
  -- ∫_y g y ‖x − y‖⁻¹ = ∫_y g y ‖r e0 − y‖⁻¹
  -- rewrite x = U (r e0); substitute y ↦ U z
  have hUx : x = U (r • shellE0) := hU.symm
  have hmp : MeasurePreserving U := by
    exact LinearIsometryEquiv.measurePreserving U
  have hemb : MeasurableEmbedding U :=
    (LinearIsometryEquiv.toHomeomorph U).measurableEmbedding
  have hsub := MeasurePreserving.integral_comp (μ := volume) (ν := volume) hmp hemb
      (fun y : ℝ³ => g y * (‖x - y‖ : ℝ)⁻¹)
  -- hsub : ∫ z, g (U z) * ‖x - U z‖⁻¹ = ∫ y, g y * ‖x-y‖⁻¹
  -- we want to rewrite the LHS integrand
  have hpt : (fun z : ℝ³ => g (U z) * (‖x - U z‖ : ℝ)⁻¹) =
      (fun z : ℝ³ => g z * (‖r • shellE0 - z‖ : ℝ)⁻¹) := by
    funext z
    have hk : ‖x - U z‖ = ‖r • shellE0 - z‖ := by
      rw [hUx, ← U.map_sub, U.norm_map]
    rw [hgrad (U z) z (U.norm_map z), hk]
  calc
    (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹) = ∫ z : ℝ³, g (U z) * (‖x - U z‖ : ℝ)⁻¹ := hsub.symm
    _ = ∫ z : ℝ³, g z * (‖r • shellE0 - z‖ : ℝ)⁻¹ := by rw [hpt]

end AxisReduction



section SphereMean

/-- The first-coordinate projection is measurable. -/
lemma shell_coord0_measurable : Measurable (fun u : ShellS2 => (u : ℝ³) 0) := by
  have hc : Continuous (fun x : ℝ³ => (x : ℝ³) 0) := by fun_prop
  exact hc.measurable.comp measurable_subtype_coe

/-- Integration of `h` against the first coordinate of the sphere equals
`2π`-times the one-dimensional integral of `h` over `[−1,1]`. -/
lemma shell_coord0_integral {h : ℝ → ℝ} (hm : Measurable h) :
    (∫ u : ShellS2, h ((u : ℝ³) 0) ∂(volume.toSphere)) =
      2 * π * (∫ t in Set.Icc (-1) 1, h t) := by
  let q : ShellS2 → ℝ := fun u => (u : ℝ³) 0
  have hq_meas : Measurable q := by simpa [q] using shell_coord0_measurable
  have hq_ae : AEMeasurable q (volume.toSphere) := hq_meas.aemeasurable
  have hh_ae : AEStronglyMeasurable h ((volume.toSphere).map q) := hm.aestronglyMeasurable
  have h1 := MeasureTheory.integral_map (μ := (volume.toSphere)) (φ := q) (f := h) hq_ae hh_ae
  calc
    (∫ u : ShellS2, h ((u : ℝ³) 0) ∂(volume.toSphere))
        = ∫ t : ℝ, h t ∂((volume.toSphere).map q) := h1.symm
    _ = ∫ t : ℝ, h t ∂(ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ)) := by
          have hpr := shell_proj_measure_dev
          dsimp [q] at hpr
          rw [hpr]
    _ = (ENNReal.ofReal (2 * π)).toReal * (∫ t : ℝ, h t ∂(volume.restrict (Set.Icc (-1) 1))) := by
          rw [MeasureTheory.integral_smul_measure]
          simp
    _ = 2 * π * (∫ t in Set.Icc (-1) 1, h t) := by
          congr 1
          rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * π)]

/-- The kernel height function `t ↦ (√(r²+s²−2rs t))⁻¹` is measurable. -/
lemma shell_kernel_h_meas (r s : ℝ) :
    Measurable (fun t : ℝ => (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹) := by
  refine Measurable.inv ?_
  refine Measurable.sqrt ?_
  fun_prop

/-- The spherical mean of the Newton kernel on the axis direction:
`∫_u 1/‖r•shellE0 − s•u‖ dσ(u) = 4π/max r s`. -/
lemma shell_mean_e0 {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ u : ShellS2, (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹ ∂(volume.toSphere)) =
      4 * π / max r s := by
  let h : ℝ → ℝ := fun t => (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹
  have hm : Measurable h := by
    dsimp [h]
    exact shell_kernel_h_meas r s
  have hpt : (fun u : ShellS2 => (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹) =
      (fun u : ShellS2 => h ((u : ℝ³) 0)) := by
    funext u
    dsimp [h]
    congr 1
    exact shell_kernel_eq_sqrt r s u
  have hmax : max r s ≠ 0 := by
    have hpos : 0 < max r s := lt_of_lt_of_le hr (le_max_left r s)
    exact ne_of_gt hpos
  calc
    (∫ u : ShellS2, (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹ ∂(volume.toSphere))
        = ∫ u : ShellS2, h ((u : ℝ³) 0) ∂(volume.toSphere) := by rw [hpt]
    _ = 2 * π * (∫ t in Set.Icc (-1) 1, h t) := shell_coord0_integral hm
    _ = 2 * π * (2 / max r s) := by
          congr 1
          dsimp [h]
          exact shell_integral_sqrt_one hr hs
    _ = 4 * π / max r s := by
          field_simp [hmax]
          ring

end SphereMean



section NonnegTools

/-- For a nonnegative real measurable function with a finite nonzero Bochner
integral, the extended integral of its `ofReal` is `ofReal` of the value. -/
lemma shell_lintegral_ofReal_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {c : ℝ} {f : X → ℝ} (hm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hval : (∫ x, f x ∂μ) = c) (hc : c ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ENNReal.ofReal c := by
  have hnonneg_ae : 0 ≤ᵐ[μ] f := ae_of_all μ hf0
  have hmain := MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := μ) (f := f) hnonneg_ae
    hm.aestronglyMeasurable
  have hne : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ := by
    intro htop
    have hz : (∫ x, f x ∂μ) = 0 := by
      rw [hmain, htop]
      simp
    rw [hval] at hz
    exact hc hz
  have hmain' : (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal = c := by
    rw [← hmain]
    exact hval
  have hnorm : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal) :=
      (ENNReal.ofReal_toReal hne).symm
  rw [hnorm, hmain']

/-- A nonnegative real measurable function with a finite nonzero Bochner integral
is integrable. -/
lemma shell_integrable_of_nonneg_value {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {c : ℝ} {f : X → ℝ} (hm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hval : (∫ x, f x ∂μ) = c) (hc : c ≠ 0) : Integrable f μ := by
  have hL : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ := by
    have h := shell_lintegral_ofReal_eq (μ := μ) (f := f) hm hf0 hval hc
    rw [h]
    exact ENNReal.ofReal_ne_top
  have hfin : HasFiniteIntegral f μ := by
    rw [hasFiniteIntegral_iff_enorm]
    rw [show (∫⁻ x, ‖f x‖ₑ ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ by
      apply MeasureTheory.lintegral_congr
      intro x
      rw [enorm_real]
      congr 1
      rw [abs_of_nonneg (hf0 x)]]
    rw [lt_top_iff_ne_top]
    exact hL
  exact ⟨hm.aestronglyMeasurable, hfin⟩

lemma shell_integrableOn_of_nonneg_value {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {c : ℝ} {s : Set X} {f : X → ℝ} (hm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hval : (∫ x in s, f x ∂μ) = c) (hc : c ≠ 0) : IntegrableOn f s μ := by
  simpa [IntegrableOn] using
    (shell_integrable_of_nonneg_value (μ := μ.restrict s) (f := f) hm hf0 hval hc)

end NonnegTools



section PolarG

/-- On a shell of positive radius the radial function equals its profile: for
`ρ > 0`, `g(ρ•u) = radialProfile g ρ`. -/
lemma shell_radial_at_polar {g : ℝ³ → ℝ} (hg : IsRadial g) (ρ : ℝ) (hρ : 0 < ρ)
    (u : ℝ³) (hu : ‖u‖ = 1) : g (ρ • u) = radialProfile g ρ := by
  unfold radialProfile
  apply hg
  -- norms: ‖ρ u‖ = ρ (hu) ; ‖ρ radU0‖ = ρ
  have h1 : ‖ρ • u‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hρ), hu, mul_one]
  have h2 : ‖ρ • radU0‖ = ρ := by
    rw [norm_smul_radU0, abs_of_nonneg (le_of_lt hρ)]
  rw [h1, h2]

/-- The profile vanishes outside the support radius. -/
lemma shell_gprof_zero_of_ge {g : ℝ³ → ℝ} {R s : ℝ} (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    (hR : 0 ≤ R) (hs : R ≤ s) : radialProfile g s = 0 := by
  unfold radialProfile
  apply hgsupp
  rw [norm_smul_radU0]
  exact le_trans hs (le_abs_self s)

/-- Absolute value version of `shell_radial_at_polar`. -/
lemma shell_abs_radial_at_polar {g : ℝ³ → ℝ} (hg : IsRadial g) (ρ : ℝ) (hρ : 0 < ρ)
    (u : ℝ³) (hu : ‖u‖ = 1) : |g (ρ • u)| = |radialProfile g ρ| := by
  rw [shell_radial_at_polar hg ρ hρ u hu]

/-- Profile at a positive radius on the axis equals the value on any sphere point. -/
lemma shell_gprof_at_polar {g : ℝ³ → ℝ} (hg : IsRadial g) (ρ : ShellRpos) (u : ShellS2) :
    g ((ρ : ℝ) • (u : ℝ³)) = radialProfile g (ρ : ℝ) :=
  shell_radial_at_polar hg (ρ : ℝ) ρ.2 (u : ℝ³) (by simpa [Metric.mem_sphere, dist_eq_norm, dist_zero_right] using u.2)

/-- The kernel (inverse distance) is nonnegative. -/
lemma shell_kernel_nonneg (a b : ℝ³) : 0 ≤ (‖a - b‖ : ℝ)⁻¹ := by
  exact inv_nonneg.mpr (norm_nonneg _)

/-- The kernel in the axis direction is nonnegative as a function on the sphere. -/
lemma shell_kernel_nonneg_sphere (r s : ℝ) (u : ShellS2) :
    0 ≤ (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹ := shell_kernel_nonneg _ _

/-- The axis kernel is measurable on the sphere. -/
lemma shell_kernel_meas_sphere (r s : ℝ) :
    Measurable (fun u : ShellS2 => (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹) := by
  have hc : Continuous (fun u : ShellS2 => (r • shellE0 - s • (u : ℝ³) : ℝ³)) := by
    fun_prop
  exact Measurable.inv (continuous_norm.comp hc).measurable

/-- The axis kernel is σ-integrable for `s > 0` (`r > 0`). -/
lemma shell_kernel_integrable_sphere {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun u : ShellS2 => (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹)
      (volume.toSphere) := by
  have hval := shell_mean_e0 hr hs
  have hc : 4 * π / max r s ≠ 0 := by
    have hpos : 0 < 4 * π / max r s := by
      positivity
    exact ne_of_gt hpos
  exact shell_integrable_of_nonneg_value (μ := (volume.toSphere))
    (f := fun u : ShellS2 => (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹)
    (shell_kernel_meas_sphere r s) (shell_kernel_nonneg_sphere r s) hval hc

end PolarG




section Assembly

/-- The radial profile is integrable against `s² ds` (from `g ∈ L¹`). -/
lemma shell_profile_integrable {g : ℝ³ → ℝ} (hg : Integrable g) (hgrad : IsRadial g) :
    IntegrableOn (fun s : ℝ => s ^ 2 * |radialProfile g s|) (Set.Ioi (0 : ℝ)) volume := by
  have hpt : (fun y : ℝ³ => |g y|) = fun y : ℝ³ => |radialProfile g ‖y‖| := by
    funext y
    congr 1
    exact radial_eq_profile hgrad y
  have hL : Integrable (fun y : ℝ³ => |radialProfile g ‖y‖|) := by
    rw [← hpt]
    exact hg.norm
  have hiff := integrable_radial_r3 (f := fun s : ℝ => |radialProfile g s|)
  exact hiff.mp hL

/-- `∫⁻` over the radius measure `ρ²dρ` reduces to a set lintegral over `(0,∞)`. -/
lemma shell_lintegral_volumeIoiPow {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ρ : ShellRpos, F (ρ : ℝ) ∂(Measure.volumeIoiPow 2)) =
      ∫⁻ s in Set.Ioi (0 : ℝ), F s * ENNReal.ofReal (s ^ 2) := by
  let μc : Measure ShellRpos := Measure.comap (Subtype.val : ShellRpos → ℝ) volume
  have hwd : (∫⁻ ρ : ShellRpos, F (ρ : ℝ) ∂μc.withDensity
        (fun ρ : ShellRpos => ENNReal.ofReal ((ρ : ℝ) ^ 2))) =
      ∫⁻ ρ : ShellRpos, ENNReal.ofReal ((ρ : ℝ) ^ 2) * F (ρ : ℝ) ∂μc := by
    exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul μc
      (f := fun ρ : ShellRpos => ENNReal.ofReal ((ρ : ℝ) ^ 2))
      (ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const 2))
      (g := fun ρ : ShellRpos => F (ρ : ℝ))
      (hF.comp measurable_subtype_coe)
  have hsub : (∫⁻ ρ : ShellRpos, ENNReal.ofReal ((ρ : ℝ) ^ 2) * F (ρ : ℝ) ∂μc) =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ 2) * F s := by
    simpa [μc, mul_comm] using
      (MeasureTheory.lintegral_subtype_comap
        (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
        (fun s : ℝ => ENNReal.ofReal (s ^ 2) * F s))
  calc
    (∫⁻ ρ : ShellRpos, F (ρ : ℝ) ∂(Measure.volumeIoiPow 2))
        = ∫⁻ ρ : ShellRpos, F (ρ : ℝ) ∂μc.withDensity
            (fun ρ : ShellRpos => ENNReal.ofReal ((ρ : ℝ) ^ 2)) := by
          simp [Measure.volumeIoiPow, μc]
    _ = ∫⁻ ρ : ShellRpos, ENNReal.ofReal ((ρ : ℝ) ^ 2) * F (ρ : ℝ) ∂μc := hwd
    _ = ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ 2) * F s := hsub
    _ = ∫⁻ s in Set.Ioi (0 : ℝ), F s * ENNReal.ofReal (s ^ 2) := by
          refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi ?_
          intro s hs
          simp [mul_comm]

/-- `∫⁻` over `σ` of a function of the first coordinate reduces to a 1D set lintegral. -/
lemma shell_proj_lintegral {h : ℝ → ℝ} (hm : Measurable h) :
    (∫⁻ u : ShellS2, ENNReal.ofReal (h ((u : ℝ³) 0)) ∂(volume.toSphere)) =
      ENNReal.ofReal (2 * π) * (∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal (h t)) := by
  let q : ShellS2 → ℝ := fun u => (u : ℝ³) 0
  have hq_meas : Measurable q := by simpa [q] using shell_coord0_measurable
  have hF : Measurable (fun t : ℝ => ENNReal.ofReal (h t)) := ENNReal.measurable_ofReal.comp hm
  have hmap := MeasureTheory.lintegral_map (μ := (volume.toSphere)) (g := q) hF hq_meas
  calc
    (∫⁻ u : ShellS2, ENNReal.ofReal (h ((u : ℝ³) 0)) ∂(volume.toSphere))
        = ∫⁻ t : ℝ, ENNReal.ofReal (h t) ∂((volume.toSphere).map q) := hmap.symm
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (h t)
          ∂(ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ)) := by
          have hpr := shell_proj_measure_dev
          dsimp [q] at hpr
          rw [hpr]
    _ = ENNReal.ofReal (2 * π) * (∫⁻ t : ℝ, ENNReal.ofReal (h t)
          ∂(volume.restrict (Set.Icc (-1) 1))) := by
          rw [MeasureTheory.lintegral_smul_measure]
          simp
    _ = ENNReal.ofReal (2 * π) * (∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal (h t)) := by rfl

/-- The `σ`-lintegral of the axis kernel on a shell of radius `s`: value `4π/max r s`. -/
lemma shell_kernel_lintegral_axis {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫⁻ u : ShellS2, ENNReal.ofReal ((‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹)
        ∂(volume.toSphere)) = ENNReal.ofReal (4 * π / max r s) := by
  let h : ℝ → ℝ := fun t => (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹
  have hm : Measurable h := by
    dsimp [h]
    exact shell_kernel_h_meas r s
  have hh0 : ∀ t, 0 ≤ h t := by
    intro t
    dsimp [h]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hpt : (fun u : ShellS2 => ENNReal.ofReal ((‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹)) =
      (fun u : ShellS2 => ENNReal.ofReal (h ((u : ℝ³) 0))) := by
    funext u
    congr 1
    dsimp [h]
    congr 1
    exact shell_kernel_eq_sqrt r s u
  have hval : (∫ t in Set.Icc (-1 : ℝ) 1, h t) = 2 / max r s := by
    dsimp [h]
    exact shell_integral_sqrt_one hr hs
  have hc : 2 / max r s ≠ 0 := by
    have hpos : 0 < 2 / max r s := by positivity
    exact ne_of_gt hpos
  have hlin : (∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal (h t)) = ENNReal.ofReal (2 / max r s) := by
    have hval' : (∫ t : ℝ, h t ∂(volume.restrict (Set.Icc (-1) 1))) = 2 / max r s := by
      simpa using hval
    exact shell_lintegral_ofReal_eq (μ := volume.restrict (Set.Icc (-1) 1)) (f := h) hm hh0 hval' hc
  have hmax : max r s ≠ 0 := ne_of_gt (lt_of_lt_of_le hr (le_max_left r s))
  calc
    (∫⁻ u : ShellS2, ENNReal.ofReal ((‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹) ∂(volume.toSphere))
        = ∫⁻ u : ShellS2, ENNReal.ofReal (h ((u : ℝ³) 0)) ∂(volume.toSphere) := by rw [hpt]
    _ = ENNReal.ofReal (2 * π) * (∫⁻ t in Set.Icc (-1) 1, ENNReal.ofReal (h t)) :=
          shell_proj_lintegral hm
    _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 / max r s) := by rw [hlin]
    _ = ENNReal.ofReal (4 * π / max r s) := by
          have h2π : 0 ≤ 2 * π := by positivity
          rw [← ENNReal.ofReal_mul h2π]
          congr 1
          field_simp [hmax]
          ring

/-- Pointwise `g(ρ•u) = radialProfile g ρ`-based identity in the product integrand (abs). -/
lemma shell_prod_pointwise_abs {g : ℝ³ → ℝ} (hgrad : IsRadial g) (z : ShellS2 × ShellRpos) :
    |g ((z.2 : ℝ) • (z.1 : ℝ³))| = |radialProfile g (z.2 : ℝ)| := by
  exact shell_abs_radial_at_polar hgrad (z.2 : ℝ) z.2.2 (z.1 : ℝ³)
    (by simpa [Metric.mem_sphere, dist_eq_norm, dist_zero_right] using z.1.2)

/-- The `σ`-lintegral of the absolute kernel is bounded by `ofReal (4π/r)` for
every radius (used to keep the product integral finite). -/
lemma shell_kernel_lintegral_axis_bound {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫⁻ u : ShellS2, ENNReal.ofReal ((‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹)
        ∂(volume.toSphere)) ≤ ENNReal.ofReal (4 * π / r) := by
  have hval := shell_kernel_lintegral_axis hr hs
  rw [hval]
  exact ENNReal.ofReal_le_ofReal (by
    have hmax : 0 < max r s := lt_of_lt_of_le hr (le_max_left r s)
    have : (4 * π) * r ≤ (4 * π) * max r s := by
      have h4 : 0 ≤ 4 * π := by positivity
      gcongr
      exact le_max_left r s
    rw [div_le_div_iff₀ hmax hr]
    exact this)


end Assembly











section ProfileMeas

/-- The radial profile is strongly measurable on `(0,∞)` (from `g ∈ L¹`,
`g` radial): it is the quotient of the measurable `s ↦ s²·gprof s` by the
(nonzero on `(0,∞)`) factor `s²`. -/
lemma shell_gprof_ae_strong {g : ℝ³ → ℝ} (hg : Integrable g) (hgrad : IsRadial g) :
    AEStronglyMeasurable (fun s : ℝ => radialProfile g s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hpt : (fun y : ℝ³ => g y) = fun y : ℝ³ => radialProfile g ‖y‖ := by
    funext y
    exact radial_eq_profile hgrad y
  have hL : Integrable (fun y : ℝ³ => radialProfile g ‖y‖) := by
    rw [← hpt]
    exact hg
  have hiff := integrable_radial_r3 (f := fun s : ℝ => radialProfile g s)
  have hOn : IntegrableOn (fun s : ℝ => s ^ 2 * radialProfile g s) (Set.Ioi (0 : ℝ)) volume :=
    hiff.mp hL
  have hsm : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * radialProfile g s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := hOn.1
  let h : ℝ → ℝ := fun s => (s ^ 2 * radialProfile g s) / s ^ 2
  have hh_sm : AEStronglyMeasurable h (volume.restrict (Set.Ioi (0 : ℝ))) := by
    dsimp [h]
    change AEStronglyMeasurable (fun s : ℝ => (s ^ 2 * radialProfile g s) * (s ^ 2)⁻¹)
        (volume.restrict (Set.Ioi (0 : ℝ)))
    have hinv : AEStronglyMeasurable (fun s : ℝ => (s ^ 2)⁻¹)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (Measurable.inv (by fun_prop : Measurable (fun s : ℝ => s ^ 2))).aestronglyMeasurable
    exact hsm.mul hinv
  have hdiv : (fun s : ℝ => radialProfile g s) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : s ≠ 0 := ne_of_gt (by simpa using hs)
    dsimp [h]
    field_simp [hs0]
  exact hh_sm.congr hdiv.symm

end ProfileMeas


end Submission.BoseGases
