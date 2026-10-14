import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Defs
-- ===== merged: Submission.Work.ConstructionInstance.aestronglyMeasurable_of_continuousOn_core_of_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- A field `ω` that is continuous on the core region `coreRegion R'` and whose support lies in
the closed ball of radius `R ≤ R'` is almost everywhere strongly measurable for the Lebesgue
measure.  Indeed `ω` coincides with its restriction to the closed ball of radius `R` cut off
by zero, and the restriction is continuous there while the complement is the null-behaviour
part; the two are glued along a measurable set. -/
theorem aestronglyMeasurable_of_continuousOn_core_of_support
    {ω : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {R R' : ℝ} (hR : R ≤ R')
    (hcont : ContinuousOn ω (Work.StabilityFar.coreRegion R'))
    (hsupp : ∀ y : EuclideanSpace ℝ (Fin 3),
      ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume := by
  classical
  set s : Set (EuclideanSpace ℝ (Fin 3)) := Metric.closedBall 0 R with hs_def
  have hsub : s ⊆ Work.StabilityFar.coreRegion R' := by
    intro x hx
    rw [hs_def, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    rw [Work.StabilityFar.mem_coreRegion]
    exact le_trans hx hR
  have hcont_s : ContinuousOn ω s := hcont.mono hsub
  have hs_meas : MeasurableSet s := by
    rw [hs_def]; exact Metric.isClosed_closedBall.measurableSet
  have hAESM_restrict :
      MeasureTheory.AEStronglyMeasurable ω (MeasureTheory.volume.restrict s) :=
    hcont_s.aestronglyMeasurable hs_meas
  have h_ind :
      MeasureTheory.AEStronglyMeasurable (s.indicator ω) MeasureTheory.volume :=
    (aestronglyMeasurable_indicator_iff hs_meas).mpr hAESM_restrict
  have hfix : s.indicator ω =ᵐ[MeasureTheory.volume] ω := by
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · have hz : ω x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      simp [Set.indicator_of_notMem hx, hz]
  exact h_ind.congr hfix

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.DerivDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- `ℝ³` (definitionally `Work.LWP.R3`). -/
abbrev R3 : Type := Work.LWP.R3

/-- The un-normalised Biot–Savart field, as an integral of the kernel
`a ↦ ω a ×₃ kf (x - a)` over the fixed ball `B(0,ρ)`:
`4π • biotSavart ω x = bsField ω ρ x` as soon as `R + ‖x‖ ≤ ρ` (cf. `biotSavart_ball_integral`). -/
noncomputable def bsField (ω : R3 → R3) (ρ : ℝ) (x : R3) : R3 :=
  ∫ a in Metric.ball (0 : R3) ρ, crossL (ω a) (kf (x - a))

/-- The candidate Fréchet derivative of `bsField ω ρ` at `x`: the Bochner integral of the CLMs
`(crossL (ω a - ω x)).comp (kDerivCLM (x - a))` plus the *shape* term `(4π/3) • crossL (ω x)`.

The subtracted `ω x` makes the integrand absolutely integrable (`‖·‖ ≤ C‖x-a‖^{c-3}`), and the
shape term accounts for the derivative of the ball potential `z ↦ ∫_{B(0,ρ)} kf (z - a) da`
(`kf_ball_integral`). -/
noncomputable def bsDerivCLM (ω : R3 → R3) (ρ : ℝ) (x : R3) : R3 →L[ℝ] R3 :=
  (∫ a in Metric.ball (0 : R3) ρ, (crossL (ω a - ω x)).comp (kDerivCLM (x - a)))
    + (4 * Real.pi / 3) • crossL (ω x)

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integral_kf_sub_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Change of variables `b = y - a` for the far-field kernel `kf`.**  The map
`a ↦ y - a` is the isometry `subLeft y` of `ℝ³` (a reflection followed by a translation); it is
measure-preserving for Lebesgue measure and sends the ball `B(0,ρ)` onto the ball `B(y,ρ)`.
Hence the integral of the kernel over `B(0,ρ)` after the substitution equals the integral of the
kernel over `B(y,ρ)`. -/
theorem integral_kf_sub_left (ρ : ℝ) (y : Work.LWP.R3) :
    ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, Work.StabilityFar.Decay.kf (y - a)
      = ∫ b in Metric.ball y ρ, Work.StabilityFar.Decay.kf b := by
  -- `a ↦ y - a` preserves Lebesgue measure on `ℝ³`...
  have hmp := MeasureTheory.Measure.measurePreserving_sub_left (MeasureTheory.volume) y
  -- ... and is a measurable embedding, being a homeomorphism of `ℝ³`.
  have hemb : MeasurableEmbedding (fun a : Work.LWP.R3 => y - a) :=
    (MeasurableEquiv.subLeft y).measurableEmbedding
  -- ... and it maps `B(0,ρ)` onto `B(y,ρ)`.
  have hset : (fun a : Work.LWP.R3 => y - a) '' Metric.ball (0 : Work.LWP.R3) ρ
      = Metric.ball y ρ := by
    ext b
    simp only [Set.mem_image, Metric.mem_ball, dist_eq_norm]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hb
      refine ⟨y - b, ?_, by abel⟩
      simpa [norm_sub_rev] using hb
  rw [← hset]
  exact (hmp.setIntegral_image_emb hemb Work.StabilityFar.Decay.kf
    (Metric.ball (0 : Work.LWP.R3) ρ)).symm

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.ray_indicator_kDerivCLM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open Work.LWP

/-- **The value of the kernel `kDerivCLM` on a ray.**

For `s > 0` and a unit vector `ω`, the Fréchet derivative of the Newtonian kernel
`kf b = ‖b‖⁻³ • b` at the point `b = s • ω` is
`(s ^ 3)⁻¹ • (Id − 3 (innerSL ℝ ω).smulRight ω)`: the radial factor `‖b‖⁻³ = s⁻³` and the
angular factor `Id − 3 ω⊗ω` separate, because `‖ω‖ = 1`. -/
theorem kDerivCLM_smul_sphere (s : Set.Ioi (0 : ℝ))
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    Work.StabilityFar.Decay.kDerivCLM ((s : ℝ) • (ω : Work.LWP.R3))
      = (((s : ℝ)) ^ 3)⁻¹ •
          (ContinuousLinearMap.id ℝ Work.LWP.R3
            - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3)) := by
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hω : ‖(ω : Work.LWP.R3)‖ = 1 := by
    have h := ω.2
    simp only [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have hnorm : ‖(s : ℝ) • (ω : Work.LWP.R3)‖ = (s : ℝ) := by
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  ext v
  simp only [Work.StabilityFar.Decay.kDerivCLM, hnorm, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_sub]
  rw [real_inner_smul_left]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sub]
  simp only [Pi.sub_apply, Pi.smul_apply]
  field_simp
  ring_nf
  field_simp

theorem ray_indicator_kDerivCLM {r ρ : ℝ}
    (s : Set.Ioi (0 : ℝ)) (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r).indicator
        (fun b => Work.StabilityFar.Decay.kDerivCLM b) ((s : ℝ) • (ω : Work.LWP.R3))
      = (if r ≤ (s : ℝ) ∧ (s : ℝ) < ρ then (((s : ℝ)) ^ 3)⁻¹ else 0)
          • (ContinuousLinearMap.id ℝ Work.LWP.R3
              - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3)) := by
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hω : ‖(ω : Work.LWP.R3)‖ = 1 := by
    have h := ω.2
    simp only [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have hnorm : ‖(s : ℝ) • (ω : Work.LWP.R3)‖ = (s : ℝ) := by
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  have hkey := kDerivCLM_smul_sphere s ω
  by_cases h : r ≤ (s : ℝ) ∧ (s : ℝ) < ρ
  · have hmem : (s : ℝ) • (ω : Work.LWP.R3)
        ∈ Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r := by
      simp only [Set.mem_diff, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
      exact ⟨h.2, not_lt.mpr h.1⟩
    rw [Set.indicator_of_mem hmem, if_pos h, hkey]
  · have hnotmem : (s : ℝ) • (ω : Work.LWP.R3)
        ∉ Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r := by
      intro con
      have h' : (s : ℝ) < ρ ∧ ¬ (s : ℝ) < r := by
        simpa only [Set.mem_diff, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm] using con
      exact h ⟨not_lt.mp h'.2, h'.1⟩
    rw [Set.indicator_of_notMem hnotmem, if_neg h]
    exact (zero_smul ℝ (ContinuousLinearMap.id ℝ Work.LWP.R3
      - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3))).symm

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-! ## The `SmoothNbhd` toolkit -/



/-- The first coordinate is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_fst : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z _ : ℝ => z) Work.Spaces.nbhU
  have h : (Function.uncurry fun z _ : ℝ => z) = fun p : ℝ × ℝ => p.1 := rfl
  rw [h]
  exact contDiffOn_fst








/-- `SmoothNbhd` is closed under pointwise multiplication. -/
theorem smoothNbhd_mul' {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothNbhd (fun z θ => f z θ * g z θ) :=
  Work.Spaces.smoothNbhd_mul hf hg

/-! ## The smooth integrand -/



/-! ## The `tan`-derivative away from the pole, and its cancellation by the weight -/

/-- `∂_θ(tan θ · Ψ) = Ψ/cos²θ + tan θ · ∂_θΨ` for `cos θ ≠ 0`. -/
theorem pth_tan_mul (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (fun z θ : ℝ => Real.tan θ * Ψ z θ) z θ
      = (1 / Real.cos θ ^ 2) * Ψ z θ
        + Real.tan θ * Work.Spaces.pth Ψ z θ := by
  have h1 : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have h2 : HasDerivAt (fun θ' : ℝ => Ψ z θ') (Work.Spaces.pth Ψ z θ) θ := hd.hasDerivAt
  have h3 := h1.mul h2
  have hfun : (Real.tan * fun θ' : ℝ => Ψ z θ') = fun θ' : ℝ => Real.tan θ' * Ψ z θ' := by
    funext θ'; rw [Pi.mul_apply]
  rw [hfun] at h3
  simpa only [Work.Spaces.pth] using h3.deriv



end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gsing_ode_of_sol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

/-! ## Auxiliary facts

This module proves `Work.FTS.EllipticEst.Gsing_ode_of_sol`: for a smooth solution `Ψ` of the
axi-symmetric Biot–Savart law (PolarBSL) with source `F ∈ ℋ^k`, the angular moment `F_*` and
the singular term `Gsing α F` are smooth on `(0,∞)`, and `Gsing` solves the Euler-type ODE
`α²z²G'' + α(5+α)zG' = (15/4)F_*`.

The three analytic ingredients are

* `F_*` is smooth, because `Work.Elliptic.PsiStar_ode` exhibits it as
  `-(α²z²(Ψ_*)'' + α(5+α)z(Ψ_*)')` with `Ψ_*` smooth (`Fstar_contDiffOn`);
* `|F_*(z)| ≤ √(π/2)·(z²/(1+z)²)·√(∫_θ HkIntegrand α k F z θ)`, by Cauchy–Schwarz on the
  angular slice, using only the `D_z⁰`-summand of the `H^k`-integrand;
* consequently `F_*/z` is integrable on every tail and `z^{(5-α)/α}F_*` is integrable near
  `0`, so that the tail integral `L₁₂` and the primitive occurring in `Ḡ` are smooth.
-/










/-! ## The main theorem -/


end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.pth_zero_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The `k = 0` integrand -/

/-- At `k = 0` the `H^k`-integrand is the single square of `g · w/ sin(2θ)^{η/2}`, i.e. the
unweighted expression `g² w² sin(2θ)^{-η}`.  (The mixed sum of `HkIntegrand` is empty, because
its condition `1 ≤ i ∧ i + j ≤ 0` is unsatisfiable.) -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  rw [show Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 by
        simp [Work.Spaces.HkIntegrand]]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-! ## Extraction of the two honesty properties of the `k = 0` integrand -/

/-- **The two integrability properties hidden in `HkMem α 0 g`.**

`HkMem α 0 g` is the honesty of the iterated integral of the single square
`(g · w/ sin(2θ)^{η/2})²`; this lemma extracts the two consequences in the *unweighted*
angular form `g² sin(2θ)^{-η}` that the divergence argument consumes: every angular slice with
`z > 0` is integrable on `Iθ`, and the radial slice `z ↦ ∫_θ g² w² sin(2θ)^{-η}` is integrable
on `Iz`.

The only place where the positivity of `z` matters is the *division* by `w(z)²`, which vanishes
at `z = 0`; the `z`-integral itself becomes the unweighted expression by a pointwise rewriting
(`mul_w_sin_rpow_sq`) alone, so it holds on all of `Iz`. -/
theorem HkMem_zero_slices {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α 0 g) :
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        Work.Spaces.Iz := by
  have hL : Work.Spaces.L2Mem (fun z θ => g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :=
    Work.Coercivity.L2Mem_DzIter_Hwt α 0 g hsm hmem 0 (le_refl 0)
  constructor
  · -- angular slices: divide the weighted integrand by the nonzero constant `w(z)²`
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hwz : Work.Spaces.w z ≠ 0 := by
      simp only [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
    have hbase : MeasureTheory.IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := (hL.1 z hzIz).const_mul _
    refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    show ((Work.Spaces.w z) ^ 2)⁻¹
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
    have h := Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ
    rw [h]
    have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
    field_simp
  · -- the radial integral: a pointwise rewriting inside the integral suffices
    refine hL.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-! ## The main theorem -/


end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.StabilityFar.Decay.hasDerivAt_bsK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-!
# `Work.StabilityFar.Decay.hasDerivAt_bsK` — the time derivative of the Biot–Savart kernel

`bsK ω x a = (‖x - a‖³)⁻¹ • (ω a × (x - a))` (`Work.LWP.BiotSavart.bsK`) depends on the
vorticity `ω` *only through its value at the fixed point `a`*, and there only linearly: for fixed
`x, a` the map

  `v ↦ bsK (fun _ => v) x a = (‖x - a‖³)⁻¹ • (v × (x - a))`

is a fixed continuous linear map `bsKCLM x a`.  Consequently, if the field slice
`s ↦ ω a s` is differentiable at `t` with derivative `∂ₜω(a,t)`, then so is
`s ↦ bsK (ω · s) x a`, with derivative `bsK (· , t) x a` (the kernel of the `t`-derivative
slice), which is exactly the pointwise statement needed to differentiate the Biot–Savart
integral under the integral sign.
-/

/-- The pointwise Biot–Savart kernel `v ↦ (‖x - a‖³)⁻¹ • (v × (x - a))` as a continuous linear
map in `v`.  It is the fixed linear factor through which `bsK (ω · s) x a` depends on `ω a s`. -/
noncomputable def bsKCLM (x a : Work.StabilityFar.R3) :
    Work.StabilityFar.R3 →L[ℝ] Work.StabilityFar.R3 :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.comp
      (((‖x - a‖ ^ (3 : ℕ))⁻¹ • (LinearMap.flip crossProduct)
          ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) (x - a))).comp
        ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap)))

/-- The defining property of `bsKCLM`: `bsKCLM x a v = bsK (fun _ => v) x a`. -/
theorem bsKCLM_apply (x a v : Work.StabilityFar.R3) :
    bsKCLM x a v = Work.LWP.BiotSavart.bsK (fun _ => v) x a := by
  rw [Work.LWP.BiotSavart.bsK.eq_def]
  simp only [bsKCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.flip_apply, LinearEquiv.coe_toLinearMap,
    WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv, WithLp.ofLp_sub]

/-- `bsK ω x a` depends on the vorticity only through its value `ω a` at `a`. -/
theorem bsK_fun_congr {ω ω' : Work.StabilityFar.R3 → Work.StabilityFar.R3}
    {x a : Work.StabilityFar.R3} (h : ω a = ω' a) :
    Work.LWP.BiotSavart.bsK ω x a = Work.LWP.BiotSavart.bsK ω' x a := by
  rw [Work.LWP.BiotSavart.bsK.eq_def, Work.LWP.BiotSavart.bsK.eq_def, h]

/-- **The time-derivative of the Biot–Savart kernel.**  If the slice `s ↦ ω a s` has derivative
`∂ₜω(a,t)` at `t`, then `s ↦ bsK (ω · s) x a` is differentiable at `t` with derivative
`bsK (fun y => ∂ₜω(y,t)) x a`, since the kernel is the fixed linear map `bsKCLM x a` applied to
`s ↦ ω a s`. -/
theorem hasDerivAt_bsK {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {x a : Work.StabilityFar.R3} {t : ℝ}
    (h : HasDerivAt (fun s' => ω a s') (FiniteTimeSingularity.timeDeriv ω a t) t) :
    HasDerivAt (fun s => Work.LWP.BiotSavart.bsK (ω · s) x a)
      (Work.LWP.BiotSavart.bsK (fun y => FiniteTimeSingularity.timeDeriv ω y t) x a) t := by
  have hcomp : HasDerivAt (fun s => bsKCLM x a (ω a s))
      (bsKCLM x a (FiniteTimeSingularity.timeDeriv ω a t)) t :=
    (bsKCLM x a).hasFDerivAt.comp_hasDerivAt t h
  convert hcomp using 1
  · funext s
    rw [bsKCLM_apply]
    exact bsK_fun_congr rfl
  · rw [bsKCLM_apply]
    exact bsK_fun_congr rfl

end Work.StabilityFar.Decay
end
