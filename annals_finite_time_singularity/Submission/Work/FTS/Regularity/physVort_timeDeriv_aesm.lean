/-
# `Work.FTS.Regularity.physVort_timeDeriv_aesm` — the `τ`-derivative slices of the physical
vorticity are ae-strongly measurable

Node N7 of the audit needs, besides the boundedness of `∂_τ ω`, the **measurability** of the
`τ`-derivative slices: for every `τ` in the strip `[0,S]`, the field

  `y ↦ ∂_τ ω(y,τ) = timeDeriv (physVort α A B g) y τ`

must be ae-strongly measurable for Lebesgue measure on `ℝ³` (this is the clause
`TimeDerivStrip` of the bundle `Work.CoreResiduals.BSAdmissibleStripFull`).

The proof is a *difference-quotient* argument and never needs a formula for the derivative:

* `∂_τ ω(y,τ)` is the pointwise limit of the difference quotients
  `(t n)⁻¹ • (ω(y, τ + t n) - ω(y, τ))`, where `t n = c/(n+1)` is a sequence of *non-zero*
  shifts converging to `0` chosen so that **every** shifted time `τ + t n` stays inside the
  strip `[0,S]`: for `τ ≤ S/2` shift right by `S/2`, for `τ > S/2` shift left by `S/2`, so that
  `τ + c·s ∈ [0,S]` for all `s ∈ [0,1]` (both endpoints lie in the interval, which is convex).
  Staying inside the strip matters: `RegPkg` controls the profile only for `τ ∈ [0,S]`.
* each difference quotient is measurable as a function of `y` because the vorticity slices on the
  strip are measurable (`physVort_slice_measurable_of_holder`), and scalar multiplication and
  subtraction preserve measurability;
* a pointwise limit of measurable functions is measurable (`measurable_of_tendsto_metrizable`),
  and a measurable function into `ℝ³` is ae-strongly measurable
  (`Measurable.aestronglyMeasurable`).

The two analytic inputs are

* `physVort_slice_measurable_of_holder`: each vorticity slice on the strip is `α`-Hölder in `x`
  with a constant uniform on the strip (`physVort_holder_slice` of the sibling module), hence
  Borel measurable;
* `physVort_differentiableAt_time`: each slice `s ↦ ω(y,s)` is differentiable at every
  `τ ∈ [0,S]` — the chain rule along the rescaled curve `s ↦ (ρ(y)^{3α}/B(s), s)`.

The assembly of the two into the statement is `physVort_timeDeriv_aesm_of`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.physVort_bound
import Submission.Work.FTS.Regularity.physVort_holder_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## The profile, written with the sign of the angle and the absolute angle

The profile is extended oddly in `θ`; since `|θ(y)| ∈ Iθ` and `θ(y) ≤ π/2`, the slice of the
profile along the physical angle is a *fixed* sign times the profile at the absolute angle. -/

/-- **The slice of the profile through the physical angle.**  For every `τ`, `z` and `θ`,

  `profile (3α) (gSlice g τ) z θ = sgn(θ) · (F_*(z,|θ|) + g(z,|θ|,τ))`,

with `sgn(θ) = 1` for `θ ≥ 0` and `-1` otherwise. -/
theorem profile_gSlice_eq_sign (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ
      = (if 0 ≤ θ then (1 : ℝ) else -1) *
        (Work.Construction.Fstar (pExp α) z |θ| + g z |θ| τ) := by
  by_cases hθ : 0 ≤ θ
  · rw [if_pos hθ, Work.ConstructionInstance.profile_of_nonneg hθ, abs_of_nonneg hθ, one_mul,
      gSlice_apply]
  · rw [if_neg hθ, Work.ConstructionInstance.profile_of_neg hθ, abs_of_neg (not_le.mp hθ),
      gSlice_apply]
    ring

/-- **The vorticity as a scalar multiple of the frame `e_θ(y)`.**  Separating the `τ`-manifold
structure: for every `y` and `s`,

  `ω(y,s) = (A(s)⁻¹ · sgn(θ(y)) · (F_*(ρ(y)^{3α}/B(s),|θ(y)|) + g(ρ(y)^{3α}/B(s),|θ(y)|,s))) • e_θ(y)`. -/
theorem physVort_eq_scalar_smul (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (y : R3) (s : ℝ) :
    physVort α A B g y s
      = ((A s)⁻¹ * ((if 0 ≤ Work.Cyl.theta y then (1 : ℝ) else -1) *
          (Work.Construction.Fstar (pExp α) (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y|
            + g (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y| s))) • Work.Cyl.eTheta y := by
  rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, smul_smul,
    profile_gSlice_eq_sign]

/-! ## The two analytic inputs -/

/-- **The vorticity slices on the strip are Borel measurable.**  Each slice is `α`-Hölder
continuous in `x` with a constant uniform on the strip (`physVort_holder_slice`), hence
continuous, hence measurable; the continuity from the Hölder bound is proved by a squeeze
(`t ↦ C·t^α` is continuous at `0` as `α > 0`). -/
theorem physVort_slice_measurable_of_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∀ τ ∈ Set.Icc 0 S, Measurable (fun y : R3 => physVort α A B g y τ) := by
  obtain ⟨C, hC0, hC⟩ := physVort_holder_slice h
  have hα : 0 < α := h.hα
  intro τ hτ
  have hcont : Continuous (fun y : R3 => physVort α A B g y τ) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun x => norm_nonneg _) (fun x => hC τ hτ x x₀) ?_
    have hu : Tendsto (fun x : R3 => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
      have h1 : Tendsto (fun x : R3 => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) :=
        tendsto_id.sub tendsto_const_nhds
      have h2 := (continuous_norm.tendsto (x₀ - x₀)).comp h1
      simpa only [Function.comp_def, sub_self, norm_zero] using h2
    have hpow : ContinuousAt (fun t : ℝ => C * t ^ α) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
    have h3 := hpow.tendsto.comp hu
    simpa only [Function.comp_def, Real.zero_rpow (ne_of_gt hα), mul_zero] using h3
  exact hcont.measurable

/-- **The slices of the physical vorticity are differentiable in physical time on the strip.**
Along the rescaled curve `s ↦ (ρ(y)^{3α}/B(s), s)` the profile `(z,s) ↦ F(z,θ(y),s)` is
differentiable at `(ρ(y)^{3α}/B τ, τ)`: the scale `B` is differentiable with `B τ ≠ 0`, the leading
part `F_*` is smooth in `z` for `z ≥ 0` (`hasDerivAt_Fstar_z`), and the perturbation is `C¹` on an
open neighbourhood of the curve (`RegPkg.hcont`, through the chain rule with the Fréchet
derivative).  Multiplying by the differentiable amplitude `(A s)⁻¹` and by the constant frame
vector `e_θ(y)` gives the differentiability of the slice. -/
theorem physVort_differentiableAt_time {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∀ y : R3, ∀ τ ∈ Set.Icc 0 S,
      DifferentiableAt ℝ (fun s : ℝ => physVort α A B g y s) τ := by
  intro y τ hτ
  have hθ₀ : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := abs_theta_mem_Iθ y
  have hBτ : B τ ≠ 0 := ne_of_gt (h.hB τ hτ)
  have hAτ : A τ ≠ 0 := ne_of_gt (h.hA τ hτ)
  have hZnn : 0 ≤ Work.Cyl.rho y ^ pExp α / B τ :=
    div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _) (le_of_lt (h.hB τ hτ))
  -- the rescaled self-similar variable `s ↦ ρ(y)^{3α}/B(s)` is differentiable at `τ`
  have hZder : HasDerivAt (fun s : ℝ => Work.Cyl.rho y ^ pExp α / B s)
      ((0 * B τ - Work.Cyl.rho y ^ pExp α * deriv B τ) / (B τ) ^ 2) τ :=
    (hasDerivAt_const τ (Work.Cyl.rho y ^ pExp α)).div (h.hBdiff τ hτ) hBτ
  -- the leading profile `F_*` is differentiable in the self-similar variable (`Z τ ≥ 0 > -1`)
  have hF : HasDerivAt (fun z : ℝ => Work.Construction.Fstar (pExp α) z |Work.Cyl.theta y|)
      (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) (Work.Cyl.rho y ^ pExp α / B τ)
        |Work.Cyl.theta y|) (Work.Cyl.rho y ^ pExp α / B τ) :=
    Work.ConstructionInstance.hasDerivAt_Fstar_z _ _ (by linarith)
  have hFc := hF.comp τ hZder
  -- the perturbation, along the diagonal curve `s ↦ (ρ(y)^{3α}/B(s), s)`
  have hmem : (Work.Cyl.rho y ^ pExp α / B τ, τ) ∈
      Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (S + 1) := by
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith [hZnn], by linarith [hτ.1], by linarith [hτ.2, h.hS]⟩
  have hmem_nhds : (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝
      (Work.Cyl.rho y ^ pExp α / B τ, τ) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem
  have hGdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => g q.1 |Work.Cyl.theta y| q.2)
      (Work.Cyl.rho y ^ pExp α / B τ, τ) :=
    ((h.hcont |Work.Cyl.theta y| hθ₀).contDiffAt hmem_nhds).differentiableAt (by norm_num)
  have hpair : HasDerivAt
      (fun s : ℝ => (Work.Cyl.rho y ^ pExp α / B s, s))
      (((0 * B τ - Work.Cyl.rho y ^ pExp α * deriv B τ) / (B τ) ^ 2), (1 : ℝ)) τ :=
    hZder.prodMk (hasDerivAt_id τ)
  -- differentiability of the three factors
  have hFc : HasDerivAt (fun s : ℝ =>
      Work.Construction.Fstar (pExp α) (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y|)
      (Work.Spaces.pz (Work.Construction.Fstar (pExp α))
          (Work.Cyl.rho y ^ pExp α / B τ) |Work.Cyl.theta y| *
        ((0 * B τ - Work.Cyl.rho y ^ pExp α * deriv B τ) / (B τ) ^ 2)) τ := by
    have h0 := hF.comp τ hZder
    simpa only [Function.comp_def] using h0
  have hGc : HasDerivAt (fun s : ℝ =>
      g (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y| s)
      (fderiv ℝ (fun q : ℝ × ℝ => g q.1 |Work.Cyl.theta y| q.2)
        (Work.Cyl.rho y ^ pExp α / B τ, τ)
        (((0 * B τ - Work.Cyl.rho y ^ pExp α * deriv B τ) / (B τ) ^ 2), (1 : ℝ))) τ := by
    have h0 := HasFDerivAt.comp_hasDerivAt
      (f := fun s : ℝ => (Work.Cyl.rho y ^ pExp α / B s, s)) τ hGdiff.hasFDerivAt hpair
    simpa only [Function.comp_def] using h0
  obtain ⟨u', hu⟩ : ∃ u' : ℝ, HasDerivAt (fun s : ℝ =>
      (if 0 ≤ Work.Cyl.theta y then (1 : ℝ) else -1) *
        (Work.Construction.Fstar (pExp α) (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y|
          + g (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y| s)) u' τ :=
    ⟨_, (hFc.add hGc).const_mul (if 0 ≤ Work.Cyl.theta y then (1 : ℝ) else -1)⟩
  have hAinv : HasDerivAt (fun s : ℝ => (A s)⁻¹) (-(deriv A τ) / (A τ) ^ 2) τ :=
    (h.hAdiff τ hτ).inv hAτ
  obtain ⟨v', hfin⟩ : ∃ v' : R3, HasDerivAt (fun s : ℝ =>
      ((A s)⁻¹ * ((if 0 ≤ Work.Cyl.theta y then (1 : ℝ) else -1) *
          (Work.Construction.Fstar (pExp α) (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y|
            + g (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y| s))) •
        Work.Cyl.eTheta y) v' τ :=
    ⟨_, (hAinv.mul hu).smul_const (Work.Cyl.eTheta y)⟩
  have hgoal : (fun s : ℝ => physVort α A B g y s)
      = fun s : ℝ => ((A s)⁻¹ * ((if 0 ≤ Work.Cyl.theta y then (1 : ℝ) else -1) *
          (Work.Construction.Fstar (pExp α) (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y|
            + g (Work.Cyl.rho y ^ pExp α / B s) |Work.Cyl.theta y| s))) • Work.Cyl.eTheta y :=
    funext fun s => physVort_eq_scalar_smul α A B g y s
  rw [hgoal]
  exact hfin.differentiableAt

/-- **The `τ`-derivative of the vorticity slices**, in the form consumed by the assembly below:
`HasDerivAt` with the value `deriv`. -/
theorem physVort_hasDerivAt_time_deriv {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∀ y : R3, ∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (fun s : ℝ => physVort α A B g y s)
        (deriv (fun s : ℝ => physVort α A B g y s) τ) τ :=
  fun y τ hτ => (physVort_differentiableAt_time h y τ hτ).hasDerivAt

/-! ## The difference-quotient assembly -/

/-- **The difference-quotient assembly.**  If the vorticity slices are measurable on the strip and
the slices `s ↦ ω(y,s)` are `τ`-differentiable at every `τ ∈ [0,S]`, then the `τ`-derivative
slices are ae-strongly measurable on `[0,S]`.

This is the core of `physVort_timeDeriv_aesm`, stated with the two analytic inputs as hypotheses
so that it can be assembled from the sibling modules. -/
theorem physVort_timeDeriv_aesm_of {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hslice : ∀ τ ∈ Set.Icc 0 S,
      Measurable (fun y : R3 => physVort α A B g y τ))
    (hdiff : ∀ y : R3, ∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (fun s : ℝ => physVort α A B g y s)
        (deriv (fun s : ℝ => physVort α A B g y s) τ) τ)
    (hS : 0 < S) :
    ∀ τ ∈ Set.Icc 0 S, MeasureTheory.AEStronglyMeasurable
      (fun y : R3 => FiniteTimeSingularity.timeDeriv (physVort α A B g) y τ)
      MeasureTheory.volume := by
  intro τ hτ
  -- the direction and size of the shift: from `τ` we may reach `S/2` (up or down) inside `[0,S]`
  set c : ℝ := if τ ≤ S / 2 then S / 2 else -S / 2 with hcdef
  have hS2 : 0 < S / 2 := by linarith
  have hcne : c ≠ 0 := by
    rw [hcdef]
    split_ifs with hle
    · linarith
    · linarith
  have hc_cases : (c = S / 2 ∧ τ ≤ S / 2) ∨ (c = -S / 2 ∧ S / 2 < τ) := by
    rw [hcdef]
    split_ifs with hle
    · exact Or.inl ⟨rfl, hle⟩
    · exact Or.inr ⟨rfl, not_le.mp hle⟩
  -- the shifted times stay in the strip (both endpoints are in `[0,S]`, and `[0,S]` is convex)
  have hshift : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → τ + c * s ∈ Set.Icc 0 S := by
    intro s hs0 hs1
    rw [Set.mem_Icc]
    rcases hc_cases with ⟨hc1, hle⟩ | ⟨hc2, hgt⟩
    · rw [hc1]
      constructor
      · nlinarith [mul_nonneg hS2.le hs0, hτ.1]
      · nlinarith [mul_le_mul_of_nonneg_left hs1 hS2.le, hle]
    · rw [hc2]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hs1 hS2.le, hgt]
      · nlinarith [mul_nonneg hS2.le hs0, hτ.2]
  -- the shift sequence `t n = c/(n+1)`
  have ht_ne : ∀ n : ℕ, c / ((n : ℝ) + 1) ≠ 0 :=
    fun n => div_ne_zero hcne (by positivity)
  have ht_mem : ∀ n : ℕ, τ + c / ((n : ℝ) + 1) ∈ Set.Icc 0 S := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    have h1 : 0 ≤ (((n : ℝ) + 1))⁻¹ := inv_nonneg.mpr hpos.le
    have h2 : (((n : ℝ) + 1))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hpos]
      linarith
    have h3 := hshift (((n : ℝ) + 1))⁻¹ h1 h2
    rw [div_eq_mul_inv]
    exact h3
  have ht_tend : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.const_mul c
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using h2
  have ht_tend' : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht_tend, Filter.Eventually.of_forall fun n => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ht_ne n⟩
  -- each difference quotient is measurable in `y`
  have hmeas : ∀ n : ℕ, Measurable fun y : R3 =>
      (c / ((n : ℝ) + 1))⁻¹ •
        (physVort α A B g y (τ + c / ((n : ℝ) + 1)) - physVort α A B g y τ) := by
    intro n
    have h1 : Measurable (fun y : R3 => physVort α A B g y (τ + c / ((n : ℝ) + 1))) :=
      hslice _ (ht_mem n)
    have h2 : Measurable (fun y : R3 => physVort α A B g y τ) := hslice τ hτ
    exact (h1.sub h2).const_smul ((c / ((n : ℝ) + 1))⁻¹)
  -- and they converge pointwise to the `τ`-derivative
  have hlim : Tendsto (fun n : ℕ => fun y : R3 =>
      (c / ((n : ℝ) + 1))⁻¹ •
        (physVort α A B g y (τ + c / ((n : ℝ) + 1)) - physVort α A B g y τ))
      atTop (𝓝 (fun y : R3 => deriv (fun s : ℝ => physVort α A B g y s) τ)) := by
    rw [tendsto_pi_nhds]
    intro y
    show Tendsto (fun n : ℕ => (c / ((n : ℝ) + 1))⁻¹ •
        (physVort α A B g y (τ + c / ((n : ℝ) + 1)) - physVort α A B g y τ))
      atTop (𝓝 (deriv (fun s : ℝ => physVort α A B g y s) τ))
    have h2 := ((hdiff y τ hτ).tendsto_slope_zero).comp ht_tend'
    simpa only [Function.comp_def] using h2
  have hfin : Measurable (fun y : R3 => deriv (fun s : ℝ => physVort α A B g y s) τ) :=
    measurable_of_tendsto_metrizable hmeas hlim
  simpa only [physVort_timeDeriv] using hfin.aestronglyMeasurable

/-! ## The target -/

theorem physVort_timeDeriv_aesm {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∀ τ ∈ Set.Icc 0 S, MeasureTheory.AEStronglyMeasurable
      (fun y : Work.FTS.Regularity.R3 =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) y τ)
      MeasureTheory.volume :=
  physVort_timeDeriv_aesm_of (physVort_slice_measurable_of_holder h)
    (physVort_hasDerivAt_time_deriv h) h.hS

end Work.FTS.Regularity
