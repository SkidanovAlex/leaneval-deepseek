import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.ShellMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Task: prove the one-dimensional (axis) shell formula

GOAL (`shell_potential_axis`): for radial `g : ℝ³ → ℝ` with `g y = 0` when
`‖y‖ ≥ R > 0`, integrable, and `r > 0`:

    (∫ y : ℝ³, g y * (‖r • shellE0 - y‖ : ℝ)⁻¹)
        = 4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s)

(`shellE0` is the coordinate axis `(1,0,0)`, see `Submission.ShellGeom`.)

MATH: Newton's shell theorem for a radial mass distribution — integrate in
polar coordinates around the origin and use the spherical mean identity
`∫_u ‖r•e0 − ρ•u‖⁻¹ dσ(u) = 4π/max r ρ` (already proved:
`Submission.BoseGases.shell_mean_e0`).

SUGGESTED ROUTE (all the hard input lemmas exist and are listed below;
only the measure choreography remains).  Throughout,
`ShellS2 := Metric.sphere (0:ℝ³) 1`, `ShellRpos := Set.Ioi (0:ℝ)`,
`σ := (volume.toSphere : Measure ShellS2)`,
`ν₂ := (Measure.volumeIoiPow 2 : Measure ShellRpos)`.

Step 1 (polar decomposition, unconditional Bochner identity):
`shell_integral_polar` in `Submission.ShellGeom`:
`∫_y f y = ∫ over (σ × ν₂) of f ((z.2:ℝ) • (z.1:ℝ³))`.
Apply to `f := fun y => g y * (‖r • shellE0 − y‖:ℝ)⁻¹` and use
`shell_radial_at_polar` (g(ρu) = radialProfile g ρ) pointwise to get

    ∫_y g y ‖r e0 − y‖⁻¹ = ∫_{(u,ρ)} gprof((ρ:ℝ)) · K(u,ρ) d(σ×ν₂)

with `K(u,ρ) := (‖r • shellE0 − (ρ:ℝ)•(u:ℝ³)‖:ℝ)⁻¹`, `gprof := radialProfile g`.

Step 2 (integrability & Fubini).  Show `G := fun z => gprof((z.2:ℝ))·K z.1 z.2`
is integrable w.r.t. `σ×ν₂`, e.g. by proving first that `|G|` is integrable
using the tools in `Submission.ShellMean`:
`shell_kernel_integrable_sphere` (σ-integrability of `u ↦ K(u,s)` for each
`s>0`), `shell_kernel_lintegral_axis` (the σ-lintegral of K equals
`ofReal(4π/max r s)`) and its bound `shell_kernel_lintegral_axis_bound`
(`≤ ofReal (4π/r)`), `shell_lintegral_volumeIoiPow` (reduces `∫⁻` over ν₂
to a set-lintegral over `(0,∞)` with density `s²`), and the radial
integrability of the profile `shell_profile_integrable`
(`IntegrableOn (fun s => s^2 * |radialProfile g s|) (Ioi 0) volume`).
Since `radialProfile g s = 0` for `s ≥ R` (`shell_gprof_zero_of_ge`), all
radius integrals are effectively over `(0,R)`, where `max r s ≥ r` bounds
`4π/max r s ≤ 4π/r`.

Then apply `integral_prod`/`integral_prod_symm` (Fubini) to obtain

    ∫_{(u,ρ)} G d(σ×ν₂) = ∫_ρ (∫_u G(u,ρ) dσ) dν₂

(outer integral over `ρ : ShellRpos` w.r.t. ν₂).

Step 3 (inner integral).  For each `ρ` with `s := (ρ:ℝ) > 0`:

    ∫_u G(u,ρ) dσ = gprof s · (4π / max r s)

This follows from `shell_mean_e0 hr hs` (the mean) and linearity
(`MeasureTheory.integral_const_mul`, `Integrable.const_mul`).  Use the
σ-integrability `shell_kernel_integrable_sphere` to justify pulling the
scalar out.

Step 4 (outer integral): with the identity from Step 3 pointwise in `ρ`,
and `shell_volumeIoiPow_integral` from `Submission.ShellGeom`:

    ∫_ρ h ((ρ:ℝ)) dν₂ = ∫ s in Set.Ioi (0:ℝ), s^2 * h s      (real Bochner)

applied to `h := fun s => gprof s * (4π / max r s)`, conclude

    RHS = 4 * π * ∫ s in Set.Ioi (0:ℝ), (s^2 * gprof s) / max r s

(rearrange with `ring`/`field_simp`; note `max r s ≠ 0` since `r > 0`).

You may add any helper definitions/lemmas in this file.  Useful existing
lemmas (all in `Submission.BoseGases`, gap-free):
- `shell_mean_e0`, `shell_coord0_integral`, `shell_coord0_measurable`
- `shell_kernel_integrable_sphere`, `shell_kernel_meas_sphere`,
  `shell_kernel_nonneg_sphere`
- `shell_kernel_lintegral_axis`, `shell_kernel_lintegral_axis_bound`
- `shell_lintegral_volumeIoiPow`, `shell_proj_lintegral`
- `shell_integral_polar`, `shell_volumeIoiPow_integral`
- `shell_radial_at_polar`, `shell_abs_radial_at_polar`,
  `shell_gprof_zero_of_ge`, `shell_profile_integrable`
- generic: `shell_lintegral_ofReal_eq`, `shell_integrable_of_nonneg_value`,
  `shell_integrableOn_of_nonneg_value`
- `MeasureTheory.integral_prod`, `integral_prod_symm`,
  `integrable_prod_iff`, `MeasureTheory.lintegral_prod`,
  `lintegral_prod_symm`
- Newton's identity infra in `Submission.NewtonRep` if needed.

The exact statement to prove:
```
lemma shell_potential_axis {g : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hgrad : IsRadial g) (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    (hg : MeasureTheory.Integrable g) {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ³, g y * (‖r • shellE0 - y‖ : ℝ)⁻¹) =
      4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s)
```
Do NOT change the statement.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real ENNReal NNReal BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)



section ShellProductMeas

/-- The radial profile (pulled back to `ShellRpos`) is a.e.-measurable w.r.t. the
comap-Lebesgue measure on `(0,∞)`. -/
lemma shell_gprof_aemeasurable_comap {g : ℝ³ → ℝ} (hg : Integrable g) (hgrad : IsRadial g) :
    AEMeasurable (fun ρ : ShellRpos => radialProfile g (ρ : ℝ))
      (Measure.comap (Subtype.val : ShellRpos → ℝ) volume) := by
  have hsm := shell_gprof_ae_strong hg hgrad
  have ham : AEMeasurable (fun s : ℝ => radialProfile g s)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (aestronglyMeasurable_iff_aemeasurable).1 hsm
  have hiff := (aemeasurable_restrict_iff_comap_subtype
    (s := Set.Ioi (0 : ℝ)) (μ := (volume : Measure ℝ))
    (f := fun s : ℝ => radialProfile g s) measurableSet_Ioi)
  exact hiff.1 ham

/-- The radial profile is a.e.-measurable w.r.t. the shell-radius measure
`volumeIoiPow 2` (density `s ↦ s²` over the comap measure). -/
lemma shell_gprof_aemeasurable_volumeIoiPow {g : ℝ³ → ℝ} (hg : Integrable g) (hgrad : IsRadial g) :
    AEMeasurable (fun ρ : ShellRpos => radialProfile g (ρ : ℝ)) (Measure.volumeIoiPow 2) := by
  rw [Measure.volumeIoiPow]
  rcases shell_gprof_aemeasurable_comap hg hgrad with ⟨g₀, hgm, hg_eq⟩
  refine ⟨g₀, hgm, ?_⟩
  change (fun ρ : ShellRpos => radialProfile g (ρ : ℝ)) =ᵐ[_] g₀
  rw [EventuallyEq]
  rw [ae_withDensity_iff (μ := Measure.comap (Subtype.val : ShellRpos → ℝ) volume)
    (f := fun ρ : ShellRpos => ENNReal.ofReal ((ρ : ℝ) ^ 2)) ?hd]
  filter_upwards [hg_eq] with ρ hρ
  intro _
  exact hρ
  · exact ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const 2)

/-- The radial profile (as a function of the second coordinate of the product)
is a.e.-strongly-measurable on `S² × (0,∞)`. -/
lemma shell_gprof_prod_aestrong {g : ℝ³ → ℝ} (hg : Integrable g) (hgrad : IsRadial g) :
    AEStronglyMeasurable (fun z : ShellS2 × ShellRpos => radialProfile g (z.2 : ℝ))
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := by
  have h1 : AEStronglyMeasurable (fun ρ : ShellRpos => radialProfile g (ρ : ℝ))
      (Measure.volumeIoiPow 2) :=
    (aestronglyMeasurable_iff_aemeasurable).2 (shell_gprof_aemeasurable_volumeIoiPow hg hgrad)
  exact AEStronglyMeasurable.comp_snd h1





/-- The Newton kernel in polar product coordinates `(u,ρ) ↦ ‖r•e₀ − ρ•u‖⁻¹`. -/
noncomputable def shellKernel (r : ℝ) (z : ShellS2 × ShellRpos) : ℝ :=
  (‖r • shellE0 - (z.2 : ℝ) • (z.1 : ℝ³)‖ : ℝ)⁻¹

/-- The kernel is measurable on the product. -/
lemma shellKernel_measurable (r : ℝ) :
    Measurable (shellKernel r) := by
  have hc : Continuous (fun z : ShellS2 × ShellRpos =>
      (r • shellE0 - (z.2 : ℝ) • (z.1 : ℝ³) : ℝ³)) := by
    fun_prop
  change Measurable (fun z : ShellS2 × ShellRpos =>
      (‖r • shellE0 - (z.2 : ℝ) • (z.1 : ℝ³)‖ : ℝ)⁻¹)
  exact Measurable.inv (continuous_norm.comp hc).measurable

/-- Pointwise norm identity for the product integrand. -/
lemma shell_prod_norm_eq {g : ℝ³ → ℝ} (hgrad : IsRadial g) (r : ℝ) (z : ShellS2 × ShellRpos) :
    ‖g ((z.2 : ℝ) • (z.1 : ℝ³)) * shellKernel r z‖ =
      |radialProfile g (z.2 : ℝ)| * shellKernel r z := by
  rw [Real.norm_eq_abs, abs_mul]
  have hK : 0 ≤ shellKernel r z := shell_kernel_nonneg (r • shellE0) ((z.2 : ℝ) • (z.1 : ℝ³))
  rw [abs_of_nonneg hK]
  congr 1
  exact shell_abs_radial_at_polar hgrad (z.2 : ℝ) z.2.2 (z.1 : ℝ³)
    (by simpa [Metric.mem_sphere, dist_eq_norm, dist_zero_right] using z.1.2)

/-- The σ-lintegral of the kernel in the product is bounded independently of the radius. -/
lemma shell_kernel_lintegral_prod_axis_bound {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    (∫⁻ u : ShellS2, ENNReal.ofReal ((‖r • shellE0 - ρ • (u : ℝ³)‖ : ℝ)⁻¹)
        ∂(volume.toSphere)) ≤ ENNReal.ofReal (4 * π / r) := by
  exact shell_kernel_lintegral_axis_bound (r := r) (s := ρ) hr hρ

/-- Finiteness of the `ν₂`-lintegral of `|radialProfile|` (measurable-profile case). -/
lemma shell_absprofile_lintegral_finite_meas {g : ℝ³ → ℝ}
    (hprof : Measurable (fun s : ℝ => radialProfile g s)) (hg : Integrable g)
    (hgrad : IsRadial g) :
    (∫⁻ ρ : ShellRpos, ENNReal.ofReal |radialProfile g (ρ : ℝ)|
        ∂(Measure.volumeIoiPow 2)) < ⊤ := by
  have hF : Measurable (fun s : ℝ => ENNReal.ofReal |radialProfile g s|) :=
    ENNReal.measurable_ofReal.comp (measurable_abs.comp hprof)
  have hconv := shell_lintegral_volumeIoiPow (F := fun s : ℝ => ENNReal.ofReal |radialProfile g s|) hF
  -- hconv : ∫⁻ ρ, ofReal|p (ρ:ℝ)| dν = ∫⁻ s in Ioi 0, ofReal|p s| * ofReal (s^2)
  have hbound : (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal |radialProfile g s| * ENNReal.ofReal (s ^ 2))
      ≤ (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ 2 * |radialProfile g s|)) := by
    apply lintegral_mono
    intro s
    change ENNReal.ofReal |radialProfile g s| * ENNReal.ofReal (s ^ 2) ≤
        ENNReal.ofReal (s ^ 2 * |radialProfile g s|)
    rw [mul_comm]
    rw [← ENNReal.ofReal_mul (sq_nonneg s)]
  have hprof_int := shell_profile_integrable hg hgrad
  -- hprof_int : IntegrableOn (fun s => s ^ 2 * |radialProfile g s|) (Ioi 0) volume
  have hfin : (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ 2 * |radialProfile g s|)) < ⊤ := by
    have hh := hprof_int.2
    -- hh : HasFiniteIntegral (fun s => s ^ 2 * |radialProfile g s|) (volume.restrict (Set.Ioi 0))
    rw [hasFiniteIntegral_iff_norm] at hh
    simpa using hh
  rw [hconv]
  exact lt_of_le_of_lt hbound hfin

/-- The product integrand (with `g` along the shell point) is a.e.-strongly
measurable on `S² × (0,∞)`. -/
lemma shell_prod_g_aestrong {g : ℝ³ → ℝ} (hg : Integrable g) (hgrad : IsRadial g) (r : ℝ) :
    AEStronglyMeasurable (fun z : ShellS2 × ShellRpos =>
      g ((z.2 : ℝ) • (z.1 : ℝ³)) * shellKernel r z)
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := by
  have h1 : AEStronglyMeasurable (fun z : ShellS2 × ShellRpos => radialProfile g (z.2 : ℝ))
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) :=
    shell_gprof_prod_aestrong hg hgrad
  have h2 : AEStronglyMeasurable (fun z : ShellS2 × ShellRpos => shellKernel r z)
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) :=
    (aestronglyMeasurable_iff_aemeasurable).2 (shellKernel_measurable r).aemeasurable
  have hmul : AEStronglyMeasurable (fun z : ShellS2 × ShellRpos =>
      radialProfile g (z.2 : ℝ) * shellKernel r z)
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := h1.mul h2
  refine AEStronglyMeasurable.congr hmul ?_
  filter_upwards with z
  rw [shell_gprof_at_polar hgrad z.2 z.1]

end ShellProductMeas
section MeasurableProfile

/-- The profile pulled back to `ShellRpos` is measurable when the profile is. -/
lemma shell_meas_profile_rpos {g : ℝ³ → ℝ}
    (hprof : Measurable (fun s : ℝ => radialProfile g s)) :
    Measurable (fun ρ : ShellRpos => radialProfile g (ρ : ℝ)) := by
  exact hprof.comp measurable_subtype_coe

/-- In the measurable-profile case the product integrand is genuinely measurable. -/
lemma shell_prod_g_measurable {g : ℝ³ → ℝ} (hgrad : IsRadial g)
    (hprof : Measurable (fun s : ℝ => radialProfile g s)) (r : ℝ) :
    Measurable (fun z : ShellS2 × ShellRpos =>
      g ((z.2 : ℝ) • (z.1 : ℝ³)) * shellKernel r z) := by
  have h1 : Measurable (fun z : ShellS2 × ShellRpos => radialProfile g (z.2 : ℝ)) :=
    (shell_meas_profile_rpos hprof).comp measurable_snd
  have hmul : Measurable (fun z : ShellS2 × ShellRpos =>
      radialProfile g (z.2 : ℝ) * shellKernel r z) := h1.mul (shellKernel_measurable r)
  convert hmul using 1
  funext z
  rw [shell_gprof_at_polar hgrad z.2 z.1]

end MeasurableProfile


/-- Inner σ-lintegral bound: `∫_u ofReal(|p(ρ)|·K) ≤ ofReal|p(ρ)|·ofReal(4π/r)`. -/
lemma shell_inner_lintegral_bound_meas {g : ℝ³ → ℝ}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    (∫⁻ u : ShellS2, ENNReal.ofReal
        (|radialProfile g ρ| * ((‖r • shellE0 - ρ • (u : ℝ³)‖ : ℝ)⁻¹))
        ∂(volume.toSphere)) ≤ ENNReal.ofReal |radialProfile g ρ| * ENNReal.ofReal (4 * π / r) := by
  have hK : (∫⁻ u : ShellS2, ENNReal.ofReal ((‖r • shellE0 - ρ • (u : ℝ³)‖ : ℝ)⁻¹)
        ∂(volume.toSphere)) ≤ ENNReal.ofReal (4 * π / r) :=
    shell_kernel_lintegral_axis_bound (r := r) (s := ρ) hr hρ
  have hrew : (fun u : ShellS2 => ENNReal.ofReal
        (|radialProfile g ρ| * ((‖r • shellE0 - ρ • (u : ℝ³)‖ : ℝ)⁻¹)))
      = fun u : ShellS2 => ENNReal.ofReal |radialProfile g ρ| *
          ENNReal.ofReal ((‖r • shellE0 - ρ • (u : ℝ³)‖ : ℝ)⁻¹) := by
    funext u
    rw [ENNReal.ofReal_mul (abs_nonneg (radialProfile g ρ))]
  rw [hrew]
  rw [lintegral_const_mul]
  · rw [mul_comm (ENNReal.ofReal |radialProfile g ρ|), mul_comm (ENNReal.ofReal |radialProfile g ρ|)]
    exact mul_le_mul_left hK (ENNReal.ofReal |radialProfile g ρ|)
  · exact ENNReal.measurable_ofReal.comp (shell_kernel_meas_sphere r ρ)

/-- Finite integral over the product in the measurable-profile case. -/
lemma shell_prod_g_hasFiniteIntegral_meas {g : ℝ³ → ℝ} (hgrad : IsRadial g)
    (hprof : Measurable (fun s : ℝ => radialProfile g s)) (hg : Integrable g)
    {r : ℝ} (hr : 0 < r) :
    HasFiniteIntegral (fun z : ShellS2 × ShellRpos =>
      g ((z.2 : ℝ) • (z.1 : ℝ³)) * shellKernel r z)
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := by
  rw [hasFiniteIntegral_iff_norm]
  have hpt : (fun z : ShellS2 × ShellRpos => ENNReal.ofReal
        ‖g ((z.2 : ℝ) • (z.1 : ℝ³)) * shellKernel r z‖) =
      (fun z : ShellS2 × ShellRpos => ENNReal.ofReal
        (|radialProfile g (z.2 : ℝ)| * shellKernel r z)) := by
    funext z
    congr 1
    exact shell_prod_norm_eq hgrad r z
  rw [hpt]
  -- Tonelli
  have hTon : (∫⁻ z : ShellS2 × ShellRpos, ENNReal.ofReal
        (|radialProfile g (z.2 : ℝ)| * shellKernel r z)
        ∂((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)))
      = (∫⁻ ρ : ShellRpos, (∫⁻ u : ShellS2, ENNReal.ofReal
          (|radialProfile g (ρ : ℝ)| * shellKernel r (u, ρ))
          ∂(volume.toSphere)) ∂(Measure.volumeIoiPow 2)) := by
    -- lintegral_prod_symm: for product μ.prod ν with α=ShellS2, β=ShellRpos:
    -- ∫⁻ z f z ∂μ.prod ν = ∫⁻ y ∫⁻ x f (x,y) ∂μ ∂ν
    have hf : AEMeasurable (fun z : ShellS2 × ShellRpos => ENNReal.ofReal
        (|radialProfile g (z.2 : ℝ)| * shellKernel r z))
        ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := by
      have h1 : Measurable (fun z : ShellS2 × ShellRpos => |radialProfile g (z.2 : ℝ)|) :=
        (measurable_abs.comp (shell_meas_profile_rpos hprof)).comp measurable_snd
      exact (ENNReal.measurable_ofReal.comp (h1.mul (shellKernel_measurable r))).aemeasurable
    exact lintegral_prod_symm (μ := (volume.toSphere : Measure ShellS2))
      (ν := (Measure.volumeIoiPow 2)) _ hf
  rw [hTon]
  -- bound inner pointwise
  have hbd : (fun ρ : ShellRpos => (∫⁻ u : ShellS2, ENNReal.ofReal
        (|radialProfile g (ρ : ℝ)| * shellKernel r (u, ρ))
        ∂(volume.toSphere)))
      ≤ fun ρ : ShellRpos => ENNReal.ofReal |radialProfile g (ρ : ℝ)| * ENNReal.ofReal (4 * π / r) := by
    intro ρ
    calc
      (∫⁻ u : ShellS2, ENNReal.ofReal (|radialProfile g (ρ : ℝ)| * shellKernel r (u, ρ)) ∂(volume.toSphere))
          = ∫⁻ u : ShellS2, ENNReal.ofReal (|radialProfile g (ρ : ℝ)| * ((‖r • shellE0 - (ρ : ℝ) • (u : ℝ³)‖ : ℝ)⁻¹)) ∂(volume.toSphere) := by
            apply lintegral_congr
            intro u
            simp [shellKernel]
      _ ≤ ENNReal.ofReal |radialProfile g (ρ : ℝ)| * ENNReal.ofReal (4 * π / r) :=
            shell_inner_lintegral_bound_meas (g := g) hr ρ.2
  -- apply monotonicity of lintegral
  calc
    (∫⁻ ρ : ShellRpos, (∫⁻ u : ShellS2, ENNReal.ofReal
        (|radialProfile g (ρ : ℝ)| * shellKernel r (u, ρ))
        ∂(volume.toSphere)) ∂(Measure.volumeIoiPow 2))
        ≤ (∫⁻ ρ : ShellRpos, ENNReal.ofReal |radialProfile g (ρ : ℝ)| * ENNReal.ofReal (4 * π / r)
            ∂(Measure.volumeIoiPow 2)) := by
            exact lintegral_mono hbd
    _ = ENNReal.ofReal (4 * π / r) * (∫⁻ ρ : ShellRpos, ENNReal.ofReal |radialProfile g (ρ : ℝ)|
            ∂(Measure.volumeIoiPow 2)) := by
            rw [lintegral_mul_const'']
            · rw [mul_comm]
            · exact (ENNReal.measurable_ofReal.comp (measurable_abs.comp (shell_meas_profile_rpos hprof))).aemeasurable
    _ < ⊤ := by
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (shell_absprofile_lintegral_finite_meas hprof hg hgrad)


section RadialNullSet

/-- Bounded core: if `S ⊆ Iio a` is a measurable Lebesgue-null set of radii,
the shell set `{x | ‖x‖ ∈ S}` has zero volume in `ℝ³`. -/
lemma shell_volume_preimage_norm_bounded_null_r3 {a : ℝ} (ha : 0 ≤ a) {S : Set ℝ}
    (hSmeas : MeasurableSet S) (hSb : S ⊆ Set.Iio a)
    (hSvol : (volume : Measure ℝ) S = 0) :
    (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 := by
  let U : Set ℝ³ := {x : ℝ³ | ‖x‖ ∈ S}
  let g : ℝ → ℝ := S.indicator (fun _ : ℝ => (1 : ℝ))
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact hSmeas.preimage continuous_norm.measurable
  have hUfinite : (volume : Measure ℝ³) U ≠ ⊤ := by
    have hUsub : U ⊆ Metric.closedBall (0 : ℝ³) a := by
      intro x hx
      have hxa : ‖x‖ < a := hSb hx
      simpa [Metric.mem_closedBall, dist_zero_right, U] using le_of_lt hxa
    have hvolball : (volume : Measure ℝ³) (Metric.closedBall (0 : ℝ³) a) ≠ ⊤ := by
      rw [volume_ball_r3 a ha]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hvolball (measure_mono hUsub)
  have hpoint : (fun x : ℝ³ => U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) =
      fun x : ℝ³ => g ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ ∈ S
    · have hxU : x ∈ U := by simpa [U] using hx
      simp [hxU, hx, g]
    · have hxU : x ∉ U := by simpa [U] using hx
      simp [hxU, hx, g]
  have hg0 : g =ᵐ[(volume : Measure ℝ)] (fun _ : ℝ => (0 : ℝ)) := by
    change ∀ᵐ (r : ℝ) ∂(volume : Measure ℝ), S.indicator (fun _ : ℝ => (1 : ℝ)) r = 0
    rw [MeasureTheory.ae_iff]
    have hset : {r : ℝ | S.indicator (fun _ : ℝ => (1 : ℝ)) r ≠ 0} = S := by
      ext r
      by_cases hr : r ∈ S
      · simp [hr]
      · simp [hr]
    rw [hset]
    exact hSvol
  have hI0 : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) = 0 := by
    calc
      (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
          = ∫ r in Set.Ioi (0 : ℝ), (0 : ℝ) := by
            refine MeasureTheory.setIntegral_congr_ae (s := Set.Ioi (0 : ℝ))
              (f := fun r : ℝ => r ^ 2 * g r) (g := fun _ : ℝ => (0 : ℝ))
              (μ := (volume : Measure ℝ)) ?_ ?_
            · measurability
            · filter_upwards [hg0] with r hr
              intro _
              simp [hr]
      _ = 0 := by simp
  have hRHS : (∫ x : ℝ³, g ‖x‖) = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) :=
    integral_fun_norm_r3 (g := g)
  have hLHS : (∫ x : ℝ³, U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) =
      (volume : Measure ℝ³).real U := by
    rw [integral_indicator (s := U) (f := fun _ : ℝ³ => (1 : ℝ))
      (μ := (volume : Measure ℝ³)) hUmeas]
    rw [setIntegral_const (c := (1 : ℝ)) (s := U) (μ := (volume : Measure ℝ³))]
    simp
  have hMain : (∫ x : ℝ³, U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) = 0 := by
    calc
      (∫ x : ℝ³, U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) = ∫ x : ℝ³, g ‖x‖ := by
        rw [hpoint]
      _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := hRHS
      _ = 0 := by rw [hI0]; norm_num
  have htoReal0 : (volume : Measure ℝ³).real U = 0 := by
    rw [← hLHS]
    exact hMain
  rw [measureReal_def] at htoReal0
  rw [ENNReal.toReal_eq_zero_iff] at htoReal0
  exact htoReal0.resolve_right hUfinite

/-- Preimage of a *measurable* Lebesgue-null set of radii under the norm is null. -/
lemma shell_volume_preimage_norm_null_r3 {S : Set ℝ} (hSmeas : MeasurableSet S)
    (hSvol : (volume : Measure ℝ) S = 0) :
    (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 := by
  let piece : ℕ → Set ℝ³ := fun k => {x : ℝ³ | ‖x‖ ∈ S ∧ ‖x‖ < (k : ℝ)}
  have hcover : {x : ℝ³ | ‖x‖ ∈ S} ⊆ ⋃ k : ℕ, piece k := by
    intro x hx
    rcases exists_nat_gt ‖x‖ with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, ⟨hx, hk⟩⟩
  have hpiece_null : ∀ k : ℕ, (volume : Measure ℝ³) (piece k) = 0 := by
    intro k
    let Sₖ : Set ℝ := S ∩ Set.Iio (k : ℝ)
    have hSₖmeas : MeasurableSet Sₖ := hSmeas.inter measurableSet_Iio
    have hSₖvol : (volume : Measure ℝ) Sₖ = 0 :=
      measure_mono_null (Set.inter_subset_left) hSvol
    have hpiece_eq : piece k = {x : ℝ³ | ‖x‖ ∈ Sₖ} := by
      ext x
      simp [piece, Sₖ]
    rw [hpiece_eq]
    exact shell_volume_preimage_norm_bounded_null_r3 (a := (k : ℝ))
      (by exact_mod_cast Nat.zero_le k) hSₖmeas (Set.inter_subset_right) hSₖvol
  have hunion_null : (volume : Measure ℝ³) (⋃ k : ℕ, piece k) = 0 :=
    measure_iUnion_null hpiece_null
  exact measure_mono_null hcover hunion_null

end RadialNullSet
/-- Inner sphere integral: for each shell radius, `∫_u g(ρu)/‖r e0 - ρu‖ dσ
= gprof(ρ)·4π/max r ρ`. -/
lemma shell_inner_axis {g : ℝ³ → ℝ} (hgrad : IsRadial g) {r : ℝ} (hr : 0 < r)
    (ρ : ShellRpos) :
    (∫ u : ShellS2, g ((ρ : ℝ) • (u : ℝ³)) * (‖r • shellE0 - (ρ : ℝ) • (u : ℝ³)‖ : ℝ)⁻¹
        ∂(volume.toSphere)) =
      radialProfile g (ρ : ℝ) * (4 * π / max r (ρ : ℝ)) := by
  let s : ℝ := (ρ : ℝ)
  have hs : 0 < s := ρ.2
  let K : ShellS2 → ℝ := fun u => (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹
  have hpt : (fun u : ShellS2 => g (s • (u : ℝ³)) * (‖r • shellE0 - s • (u : ℝ³)‖ : ℝ)⁻¹)
      = fun u : ShellS2 => radialProfile g s * K u := by
    funext u
    dsimp [K]
    rw [shell_gprof_at_polar hgrad ρ u]
  calc
    (∫ u : ShellS2, g ((ρ : ℝ) • (u : ℝ³)) * (‖r • shellE0 - (ρ : ℝ) • (u : ℝ³)‖ : ℝ)⁻¹
        ∂(volume.toSphere))
        = ∫ u : ShellS2, radialProfile g s * K u ∂(volume.toSphere) := by
            simpa [s, K] using congrArg (fun h : ShellS2 → ℝ => ∫ u : ShellS2, h u ∂(volume.toSphere)) hpt
    _ = radialProfile g s * (∫ u : ShellS2, K u ∂(volume.toSphere)) := by
            rw [integral_const_mul]
    _ = radialProfile g (ρ : ℝ) * (4 * π / max r (ρ : ℝ)) := by
            dsimp [s]
            congr 1
            dsimp [K]
            exact shell_mean_e0 hr hs


/-- Integrability of the product function on `S² × (0,∞)` in the
measurable-profile case. -/
lemma shell_prod_g_integrable_meas {g : ℝ³ → ℝ} (hgrad : IsRadial g)
    (hprof : Measurable (fun s : ℝ => radialProfile g s)) (hg : Integrable g)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun z : ShellS2 × ShellRpos =>
      g ((z.2 : ℝ) • (z.1 : ℝ³)) * shellKernel r z)
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := by
  refine ⟨?_, ?_⟩
  · exact (shell_prod_g_measurable hgrad hprof r).aestronglyMeasurable
  · exact shell_prod_g_hasFiniteIntegral_meas hgrad hprof hg hr

/-- Measurable-profile version of the shell formula: when `radialProfile g` is
measurable no extra support or a.e.-profile arguments are needed. -/
lemma shell_potential_axis_meas {g : ℝ³ → ℝ} (hgrad : IsRadial g)
    (hprof : Measurable (fun s : ℝ => radialProfile g s)) (hg : Integrable g)
    {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ³, g y * (‖r • shellE0 - y‖ : ℝ)⁻¹) =
      4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s) := by
  let σ : Measure ShellS2 := volume.toSphere
  let ν : Measure ShellRpos := Measure.volumeIoiPow 2
  let G : ShellS2 × ShellRpos → ℝ :=
    fun z => g ((z.2 : ℝ) • (z.1 : ℝ³)) * (‖r • shellE0 - (z.2 : ℝ) • (z.1 : ℝ³)‖ : ℝ)⁻¹
  -- integrability of the product function G (Fubini input); measurable profile
  have hG : Integrable G (σ.prod ν) := by
    dsimp [G, σ, ν]
    simpa [shellKernel] using shell_prod_g_integrable_meas hgrad hprof hg hr
  calc
    (∫ y : ℝ³, g y * (‖r • shellE0 - y‖ : ℝ)⁻¹)
        = (∫ z : ShellS2 × ShellRpos, G z ∂(σ.prod ν)) := by
            dsimp [G]
            exact shell_integral_polar (f := fun y : ℝ³ => g y * (‖r • shellE0 - y‖ : ℝ)⁻¹)
    _ = (∫ ρ : ShellRpos, (∫ u : ShellS2, G (u, ρ) ∂σ) ∂ν) := by
            dsimp [σ, ν]
            exact MeasureTheory.integral_prod_symm G hG
    _ = (∫ ρ : ShellRpos, radialProfile g (ρ : ℝ) * (4 * π / max r (ρ : ℝ)) ∂ν) := by
            apply integral_congr_ae
            filter_upwards with ρ
            exact shell_inner_axis hgrad hr ρ
    _ = (∫ s in Set.Ioi (0 : ℝ), s ^ 2 * (radialProfile g s * (4 * π / max r s))) := by
            dsimp [ν]
            rw [shell_volumeIoiPow_integral (fun s : ℝ => radialProfile g s * (4 * π / max r s))]
    _ = 4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s) := by
            have hpt : (fun s : ℝ => s ^ 2 * (radialProfile g s * (4 * π / max r s))) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
                (fun s : ℝ => (4 * π) * ((s ^ 2 * radialProfile g s) / max r s)) := by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
              have hmax : max r s ≠ 0 := ne_of_gt (lt_of_lt_of_le hr (le_max_left r s))
              field_simp [hmax]
            rw [integral_congr_ae hpt]
            rw [integral_const_mul]



/-- If two radial profiles agree a.e. on `(0,∞)`, the induced radial functions
agree a.e. on `R^3`. -/
lemma shell_ae_eq_of_ae_profile {g : ℝ³ → ℝ} (hgrad : IsRadial g) (phat : ℝ → ℝ)
    (h : (fun s : ℝ => radialProfile g s) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] phat) :
    (fun y : ℝ³ => g y) =ᵐ[(volume : Measure ℝ³)] fun y : ℝ³ => phat ‖y‖ := by
  have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioi (0 : ℝ) → radialProfile g s = phat s := by
    exact ae_imp_of_ae_restrict h
  let E : Set ℝ := {s | s ∈ Set.Ioi (0 : ℝ) ∧ radialProfile g s ≠ phat s}
  have hE : (volume : Measure ℝ) E = 0 := by
    have hv := MeasureTheory.ae_iff.mp h1
    have hset : E = {s | ¬(s ∈ Set.Ioi (0 : ℝ) → radialProfile g s = phat s)} := by
      ext s
      by_cases hs : s ∈ Set.Ioi (0 : ℝ)
      · simp [E, hs]
      · simp [E, hs]
    rw [hset]
    exact hv
  let M : Set ℝ := MeasureTheory.toMeasurable (volume : Measure ℝ) E
  have hMmeas : MeasurableSet M := MeasureTheory.measurableSet_toMeasurable (volume : Measure ℝ) E
  have hMvol : (volume : Measure ℝ) M = 0 := by
    rw [MeasureTheory.measure_toMeasurable]
    exact hE
  have hMnull : (volume : Measure ℝ³) {y : ℝ³ | ‖y‖ ∈ M} = 0 :=
    shell_volume_preimage_norm_null_r3 hMmeas hMvol
  have h0null : (volume : Measure ℝ³) {y : ℝ³ | ‖y‖ = 0} = 0 := by
    have h01 : (volume : Measure ℝ) ({0} : Set ℝ) = 0 := by
      simpa using (Real.volume_singleton (a := (0 : ℝ)))
    exact shell_volume_preimage_norm_null_r3 (by measurability) h01
  let bad : Set ℝ³ := {y : ℝ³ | ¬(g y = phat ‖y‖)}
  have hbadsub : bad ⊆ {y : ℝ³ | ‖y‖ ∈ M} ∪ {y : ℝ³ | ‖y‖ = 0} := by
    intro y hy
    by_cases hy0 : ‖y‖ = 0
    · right; exact hy0
    · left
      have hyI : ‖y‖ ∈ Set.Ioi (0 : ℝ) := by
        simpa [Set.mem_Ioi] using lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
      have hEy : ‖y‖ ∈ E := by
        dsimp [E]
        refine ⟨hyI, ?_⟩
        intro heq
        apply hy
        rw [radial_eq_profile hgrad y]
        exact heq
      exact MeasureTheory.subset_toMeasurable (volume : Measure ℝ) E hEy
  have hunion : (volume : Measure ℝ³)
      ({y : ℝ³ | ‖y‖ ∈ M} ∪ {y : ℝ³ | ‖y‖ = 0}) = 0 :=
    measure_union_null hMnull h0null
  rw [EventuallyEq]
  rw [MeasureTheory.ae_iff]
  exact measure_mono_null hbadsub hunion

/-- Shell formula along the axis: for a radial integrable `g` with support
radius `R` and `r > 0`,
`∫_y g(y)/‖r•e₀−y‖ = 4π ∫₀^∞ s² gprof(s)/max r s`. -/
lemma shell_potential_axis {g : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hgrad : IsRadial g) (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    (hg : MeasureTheory.Integrable g) {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ³, g y * (‖r • shellE0 - y‖ : ℝ)⁻¹) =
      4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s) := by
  -- take a measurable representative phat of the radial profile on (0,∞)
  rcases (aestronglyMeasurable_iff_aemeasurable).1 (shell_gprof_ae_strong hg hgrad)
    with ⟨phat, hphatm, hphateq⟩
  -- hphateq : (fun s => radialProfile g s) =ᵐ[volume.restrict (Set.Ioi 0)] phat
  let ghat : ℝ³ → ℝ := fun y => phat ‖y‖
  have hghateq : ghat =ᵐ[(volume : Measure ℝ³)] g := by
    dsimp [ghat]
    exact (shell_ae_eq_of_ae_profile hgrad phat hphateq).symm
  have hghatint : Integrable ghat := by
    exact hg.congr hghateq.symm
  have hghatrad : IsRadial ghat := by
    intro x y hxy
    simp [ghat, hxy]
  have hghatprof : Measurable (fun s : ℝ => radialProfile ghat s) := by
    have hpt : (fun s : ℝ => radialProfile ghat s) = fun s : ℝ => phat |s| := by
      funext s
      change phat ‖s • radU0‖ = phat |s|
      rw [norm_smul_radU0]
    rw [hpt]
    exact hphatm.comp continuous_abs.measurable
  have hmain := shell_potential_axis_meas hghatrad hghatprof hghatint hr
  -- hmain : ∫ ghat·K = 4π∫ s²·(radialProfile ghat s)/max r s
  calc
    (∫ y : ℝ³, g y * (‖r • shellE0 - y‖ : ℝ)⁻¹)
        = (∫ y : ℝ³, ghat y * (‖r • shellE0 - y‖ : ℝ)⁻¹) := by
            apply integral_congr_ae
            filter_upwards [hghateq] with y hy
            rw [hy]
    _ = 4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile ghat s) / max r s) := hmain
    _ = 4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s) := by
            have hgt : ∀ s : ℝ, 0 < s → radialProfile ghat s = phat s := by
              intro s hs
              have hpt : radialProfile ghat s = phat |s| := by
                change phat ‖s • radU0‖ = phat |s|
                rw [norm_smul_radU0]
              rw [hpt, abs_of_pos hs]
            have hc : (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max r s)
                = (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile ghat s) / max r s) := by
              apply integral_congr_ae
              filter_upwards [hphateq, ae_restrict_mem measurableSet_Ioi] with s hs hsI
              rw [hs]
              rw [hgt s hsI]
            rw [hc]

end Submission.BoseGases
