import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.OmegaCutSupport
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.ConstructionInstance.div_cutDatum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The dictionary `(rho, theta)` on `ℝ³` vs `(rhoP, thetaP)` on the `(r,x₃)` half plane -/

private lemma rho_eq_rhoP' (y : R3) :
    Work.Cyl.rho y = Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) := by
  rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]

private lemma theta_eq_thetaP' (y : R3) :
    Work.Cyl.theta y = Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y) := rfl

/-! ## Swirl fields are divergence free -/

/-- The field `A(r,x₃) • angularVec = (A(r,x₃)/r) • (r e_θ)` (the `r`-multiple of a swirl field,
which is the smooth object off the axis). -/
private def swirlField (A : ℝ → ℝ → ℝ) : R3 → R3 :=
  fun y => A (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.angularVec y

private lemma differentiableAt_angularVec (x : R3) :
    DifferentiableAt ℝ Work.Cyl.angularVec x := by
  have hcoord : ∀ j : Fin 3, DifferentiableAt ℝ (fun y : R3 => y j) x := fun j =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x j).differentiableAt
  rw [show Work.Cyl.angularVec = fun y : R3 =>
      (-(y 1)) • Work.Cyl.e0 + (y 0) • Work.Cyl.e1 from by
    funext y
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
  exact (((hcoord 1).neg).smul_const Work.Cyl.e0).add ((hcoord 0).smul_const Work.Cyl.e1)

/-- **A swirl field `A(r,x₃)·e_θ` is divergence free** off the axis, for every profile `A` which
is differentiable at `(radial x, axial x)`. -/
private theorem div_swirlField {A : ℝ → ℝ → ℝ} (x : R3)
    (hA : Work.Cyl.DiffAt2 A (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (swirlField A) x = 0 := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hpair : DifferentiableAt ℝ (fun y : R3 => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    (Work.Cyl.differentiableAt_radial x hrne).prodMk (Work.Cyl.differentiableAt_axial x)
  have hdiffA : DifferentiableAt ℝ (fun y : R3 => A (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    have h := hA.comp x hpair
    convert h using 1
    funext y; rfl
  have hU : DifferentiableAt ℝ (swirlField A) x := by
    have h := hdiffA.smul (differentiableAt_angularVec x)
    convert h using 1
    funext y; rfl
  rw [Work.Cyl.div_eq_sum_partials _ x hU, Fin.sum_univ_three]
  simp only [Work.Cyl.basisVec_zero, Work.Cyl.basisVec_one, Work.Cyl.basisVec_two]
  have hd0 := Work.Cyl.hasDerivAt_comp_cyl_e0 A x hA hr
  have hd1 := Work.Cyl.hasDerivAt_comp_cyl_e1 A x hA hr
  have hline0 : (fun t : ℝ => (swirlField A (x + t • Work.Cyl.e0)) 0)
      = fun t : ℝ =>
          A (Work.Cyl.radial (x + t • Work.Cyl.e0)) (Work.Cyl.axial (x + t • Work.Cyl.e0))
            * (-(x 1)) := by
    funext t
    simp [swirlField, smul_eq_mul]
  have hline1 : (fun t : ℝ => (swirlField A (x + t • Work.Cyl.e1)) 1)
      = fun t : ℝ =>
          A (Work.Cyl.radial (x + t • Work.Cyl.e1)) (Work.Cyl.axial (x + t • Work.Cyl.e1))
            * (x 0) := by
    funext t
    simp [swirlField, smul_eq_mul]
  have hline2 : (fun t : ℝ => (swirlField A (x + t • Work.Cyl.eZ)) 2) = fun t : ℝ => 0 := by
    funext t
    simp [swirlField, smul_eq_mul]
  rw [hline0, hline1, hline2]
  rw [(hd0.mul_const (-(x 1))).deriv, (hd1.mul_const (x 0)).deriv]
  rw [deriv_const (0 : ℝ)]
  ring

/-- **The divergence of `φ(r,x₃) • e_θ` vanishes** off the axis, for every profile `φ` which is
differentiable at `(radial x, axial x)`.  This is the shape of `omegaS p g` and of `omega₀ p g L`
once their scalar factors are merged. -/
private theorem div_smul_eTheta_of_diffAt2 {φ : ℝ → ℝ → ℝ} (x : R3)
    (hφ : Work.Cyl.DiffAt2 φ (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div
      (fun y : R3 => φ (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.eTheta y) x = 0 := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  -- the reduced profile `(r,z) ↦ φ(r,z)/r` is differentiable at `(radial x, axial x)`
  have hnum : DifferentiableAt ℝ (fun q : ℝ × ℝ => φ q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hφ
  have hinv : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1)⁻¹)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    (by fun_prop : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1)
        (Work.Cyl.radial x, Work.Cyl.axial x)).inv (by simpa using hrne)
  have hred : Work.Cyl.DiffAt2 (fun r z : ℝ => φ r z / r) (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    have hmain : DifferentiableAt ℝ (fun q : ℝ × ℝ => φ q.1 q.2 * (q.1)⁻¹)
        (Work.Cyl.radial x, Work.Cyl.axial x) := hnum.mul hinv
    convert hmain using 1
    funext q
    simp [div_eq_mul_inv]
  have hfield : (fun y : R3 => φ (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.eTheta y)
      = swirlField (fun r z : ℝ => φ r z / r) := by
    funext y
    show φ (Work.Cyl.radial y) (Work.Cyl.axial y) • Work.Cyl.eTheta y
      = (φ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y) • Work.Cyl.angularVec y
    rw [Work.Cyl.eTheta, smul_smul]
    congr 1
    simp [div_eq_mul_inv]
  rw [hfield]
  exact div_swirlField x hred hr

/-! ## Differentiability of the cut-off profile `Φ(r,z) = χ(ρP/L)·F(ρP^p, θP)` -/

private theorem diffAt2_cutProfile {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} {x : R3}
    (hg : ContDiffAt ℝ 1 (Function.uncurry (profile p g)) ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x))
    (hr : 0 < Work.Cyl.radial x) :
    Work.Cyl.DiffAt2
      (fun r z : ℝ =>
        Work.Stability.chi (Work.Cyl.rhoP r z / L) *
          profile p g (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z))
      (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  have hρ0 : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have h : (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2)
        = fun q : ℝ × ℝ => Real.sqrt (q.1 ^ 2 + q.2 ^ 2) := by
      funext q; rw [Work.Cyl.rhoP]
    rw [h]
    apply DifferentiableAt.sqrt
    · fun_prop
    · exact ne_of_gt (by positivity)
  have hρ : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ p)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    hρ0.rpow_const (Or.inl (ne_of_gt (Work.Cyl.rhoP_pos hr (Work.Cyl.axial x))))
  have hθ : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have h : (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2)
        = fun q : ℝ × ℝ => Real.arctan (q.2 * (q.1)⁻¹) := by
      funext q; rw [Work.Cyl.thetaP, div_eq_mul_inv]
    rw [h]
    apply DifferentiableAt.arctan
    have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.2)
        (Work.Cyl.radial x, Work.Cyl.axial x) := by fun_prop
    have h2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1)⁻¹)
        (Work.Cyl.radial x, Work.Cyl.axial x) :=
      (by fun_prop : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1)
        (Work.Cyl.radial x, Work.Cyl.axial x)).inv (by simpa using ne_of_gt hr)
    exact h1.mul h2
  have hpair : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => (Work.Cyl.rhoP q.1 q.2 ^ p, Work.Cyl.thetaP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := hρ.prodMk hθ
  -- the profile is differentiable at the image point `(ρ(x)^p, θ(x))`
  have hprof : DifferentiableAt ℝ (Function.uncurry (profile p g))
      ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x) := hg.differentiableAt (by simp)
  rw [rho_eq_rhoP' x, theta_eq_thetaP' x] at hprof
  have hcomp := hprof.comp (Work.Cyl.radial x, Work.Cyl.axial x) hpair
  -- the smooth cut-off factor `χ(·/L)` costs nothing
  have hcut : DifferentiableAt ℝ
      ((fun s : ℝ => Work.Stability.chi (s / L)) ∘ (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have h1 : DifferentiableAt ℝ (fun s : ℝ => Work.Stability.chi (s / L))
        (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x)) :=
      ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt).comp _
        (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s / L)
          (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x)))
    exact h1.comp (Work.Cyl.radial x, Work.Cyl.axial x) hρ0
  have hprod := hcut.mul hcomp
  convert hprod using 1
  · funext q
    simp [Function.uncurry, Function.comp_def, Pi.mul_apply]

/-! ## The main theorem -/

theorem div_cutDatum {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} {x : Work.ConstructionInstance.R3}
    (hg : ContDiffAt ℝ 1 (Function.uncurry (Work.ConstructionInstance.profile p g))
      ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (Work.ConstructionInstance.omega₀ p g L) x = 0 := by
  -- the cut-off profile as a function of `(r, x₃)`
  have hΦ : Work.Cyl.DiffAt2
      (fun r z : ℝ =>
        Work.Stability.chi (Work.Cyl.rhoP r z / L) *
          profile p g (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z))
      (Work.Cyl.radial x) (Work.Cyl.axial x) := diffAt2_cutProfile hg hr
  -- `omega₀ p g L = Φ(radial, axial) • e_θ`
  have hfield : omega₀ p g L
      = fun y : R3 =>
          (Work.Stability.chi (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) / L) *
            profile p g (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) ^ p)
              (Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y))) • Work.Cyl.eTheta y := by
    funext y
    have h1 : Work.Stability.chi (Work.Cyl.rho y / L) * profile p g (Work.Cyl.rho y ^ p)
          (Work.Cyl.theta y)
        = Work.Stability.chi (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) / L) *
          profile p g (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) ^ p)
            (Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y)) := by
      rw [rho_eq_rhoP' y, theta_eq_thetaP' y]
    rw [omega₀_apply, omegaS_apply', smul_smul, h1]
  rw [hfield]
  exact div_smul_eTheta_of_diffAt2 x hΦ hr

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.EllipticEst.agmon_cutoff_estimate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology ContDiff
open Work.FTS.EllipticEst.Blocks

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### Elementary AM–GM and integral helpers -/

/-- **Weighted Young inequality**: for `r ≥ 0` and `c > 0`, `2 r |a| |b| ≤ c (r a²) + c⁻¹ (r b²)`.
(This is the completing-of-the-square identity `c x² - 2xy + c⁻¹ y² = c (x - c⁻¹ y)² ≥ 0`
with `x = |a|`, `y = |b|`, multiplied by `r`.) -/
theorem young_weighted (r c a b : ℝ) (hr : 0 ≤ r) (hc : 0 < c) :
    2 * r * |a| * |b| ≤ c * (r * a ^ 2) + c⁻¹ * (r * b ^ 2) := by
  have hexp : c * (|a| - c⁻¹ * |b|) ^ 2 = c * a ^ 2 - 2 * |a| * |b| + c⁻¹ * b ^ 2 := by
    rw [sub_sq, mul_pow, sq_abs a, sq_abs b]
    field_simp
  have hsq : 0 ≤ c * (|a| - c⁻¹ * |b|) ^ 2 := mul_nonneg (le_of_lt hc) (sq_nonneg _)
  rw [hexp] at hsq
  have hmul : 0 ≤ r * (c * a ^ 2 - 2 * |a| * |b| + c⁻¹ * b ^ 2) := mul_nonneg hr hsq
  have heq : r * (c * a ^ 2 - 2 * |a| * |b| + c⁻¹ * b ^ 2)
      = c * (r * a ^ 2) + c⁻¹ * (r * b ^ 2) - 2 * r * |a| * |b| := by ring
  linarith [hmul, heq ▸ hmul]

/-- The `1/8`-instance of Young's inequality: `2 r |a| |b| ≤ (1/8) (r a²) + 8 (r b²)`. -/
theorem young_eighth (r a b : ℝ) (hr : 0 ≤ r) :
    2 * r * |a| * |b| ≤ (1 / 8) * (r * a ^ 2) + 8 * (r * b ^ 2) := by
  have h := young_weighted r (1 / 8) a b hr (by norm_num)
  rw [show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num] at h
  linarith [h]

/-- Completing of the square in the form used for the `(zχ')`-pairing:
`(1/4) (r x |y|) ≤ (1/64) (r x²) + r y²` for `r ≥ 0` (from `(x/8 - |y|)² ≥ 0`). -/
theorem young_quarter (r x y : ℝ) (hr : 0 ≤ r) :
    (1 / 4) * (r * x * |y|) ≤ (1 / 64) * (r * x ^ 2) + r * y ^ 2 := by
  have hexp : (x / 8 - |y|) ^ 2 = x ^ 2 / 64 - x * |y| / 4 + |y| ^ 2 := by ring
  have hsq : 0 ≤ (x / 8 - |y|) ^ 2 := sq_nonneg _
  rw [hexp, sq_abs y] at hsq
  have hmul : 0 ≤ r * (x ^ 2 / 64 - x * |y| / 4 + y ^ 2) := mul_nonneg hr hsq
  have heq : r * (x ^ 2 / 64 - x * |y| / 4 + y ^ 2)
      = (1 / 64) * (r * x ^ 2) + r * y ^ 2 - (1 / 4) * (r * x * |y|) := by ring
  linarith [hmul, heq ▸ hmul]

/-- The integral of a four-term linear combination over `(0,∞)`. -/
theorem integral_lin4 {f₁ f₂ f₃ f₄ : ℝ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    (h₁ : IntegrableOn f₁ (Set.Ioi (0 : ℝ))) (h₂ : IntegrableOn f₂ (Set.Ioi (0 : ℝ)))
    (h₃ : IntegrableOn f₃ (Set.Ioi (0 : ℝ))) (h₄ : IntegrableOn f₄ (Set.Ioi (0 : ℝ))) :
    (∫ z in Set.Ioi (0 : ℝ), (c₁ * f₁ z + c₂ * f₂ z + c₃ * f₃ z + c₄ * f₄ z))
      = c₁ * (∫ z in Set.Ioi (0 : ℝ), f₁ z) + c₂ * (∫ z in Set.Ioi (0 : ℝ), f₂ z)
        + c₃ * (∫ z in Set.Ioi (0 : ℝ), f₃ z) + c₄ * (∫ z in Set.Ioi (0 : ℝ), f₄ z) := by
  have h12 : IntegrableOn (fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z) (Set.Ioi (0 : ℝ)) :=
    (h₁.const_mul c₁).add (h₂.const_mul c₂)
  have h123 : IntegrableOn (fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z + c₃ * f₃ z) (Set.Ioi (0 : ℝ)) :=
    h12.add (h₃.const_mul c₃)
  rw [integral_add (f := fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z + c₃ * f₃ z)
        (g := fun z : ℝ => c₄ * f₄ z) h123 (h₄.const_mul c₄),
      integral_add (f := fun z : ℝ => c₁ * f₁ z + c₂ * f₂ z) (g := fun z : ℝ => c₃ * f₃ z)
        h12 (h₃.const_mul c₃),
      integral_add (f := fun z : ℝ => c₁ * f₁ z) (g := fun z : ℝ => c₂ * f₂ z)
        (h₁.const_mul c₁) (h₂.const_mul c₂),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-! ### The pointwise core -/

/-- **The pointwise AM–GM core of the cut-off weighted Agmon estimate** (with `ρ = W2`).

For `z > 0`, `0 < α`, `0 ≤ δ`, `h, χ` of class `C^∞` on `(0,∞)`, `0 ≤ χ z ≤ 1`,
`|z χ'(z)| ≤ 1/8` and `|z² χ''(z)| ≤ δ`,

`-(d/dz)(ρ z² (hχ)')(z) · (hχ)(z) ≤ (9/64) ρ (zh')² χ² + (α²/4) ρ (z²h'')² χ²
   + (α⁻² + 8) ρ h² χ² + (5/4 + δ) ρ h²`   (all values at `z`).

Route: `|(d/dz)(ρz²g')| ≤ 2ρz|g'| + ρz²|g''|` with `g = hχ`, `|g'| ≤ |h'|χ + |h||χ'|`,
`|g''| ≤ |h''|χ + 2|h'||χ'| + |h||χ''|`, then the AM–GM pairings
`2ρz|h'||h|χ² ≤ (1/8)ρ(zh')²χ² + 8ρh²χ²`, `2ρz|h|²|χ'|χ ≤ (1/4)ρh²`,
`ρz²|h''||h|χ² ≤ (α²/4)ρ(z²h'')²χ² + α⁻²ρh²χ²`,
`2ρz²|h'||χ'||h|χ ≤ (1/64)ρ(zh')²χ² + ρh²`, `ρz²|h|²|χ''|χ ≤ δρh²`. -/
theorem agmon_pointwise {χ : ℝ → ℝ} {α δ : ℝ} {h : ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (hα : 0 < α) (hδ0 : 0 ≤ δ)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)))
    (hχcd : ContDiffOn ℝ Work.Stability.smoothOrder χ (Set.Ioi (0 : ℝ)))
    (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1)
    (hχder1 : |z * deriv χ z| ≤ 1 / 8)
    (hχder2 : |z ^ 2 * deriv (deriv χ) z| ≤ δ) :
    -(deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z * (h z * χ z))
      ≤ (9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
        + (5 / 4 + δ) * (W2 z * h z ^ 2) := by
  have hne : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  have hder : Work.Stability.smoothOrder + 1 ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hρ : 0 ≤ W2 z := W2_nonneg z
  have hA : 0 ≤ W2 z * h z ^ 2 := mul_nonneg hρ (sq_nonneg _)
  -- differentiability of the data at `z`
  have hh_at : DifferentiableAt ℝ h z :=
    (hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hχ_at : DifferentiableAt ℝ χ z :=
    (hχcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdh_cd : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi (0 : ℝ)) :=
    hcd.deriv_of_isOpen isOpen_Ioi hder
  have hdχ_cd : ContDiffOn ℝ Work.Stability.smoothOrder (deriv χ) (Set.Ioi (0 : ℝ)) :=
    hχcd.deriv_of_isOpen isOpen_Ioi hder
  have hdh_at : DifferentiableAt ℝ (deriv h) z :=
    (hdh_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdχ_at : DifferentiableAt ℝ (deriv χ) z :=
    (hdχ_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hgcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => h y * χ y) (Set.Ioi (0 : ℝ)) :=
    hcd.mul hχcd
  have hdg_cd : ContDiffOn ℝ Work.Stability.smoothOrder
      (deriv (fun y : ℝ => h y * χ y)) (Set.Ioi (0 : ℝ)) :=
    hgcd.deriv_of_isOpen isOpen_Ioi hder
  have hdg_at : DifferentiableAt ℝ (deriv (fun y : ℝ => h y * χ y)) z :=
    (hdg_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hW2sq_cd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun y : ℝ => W2 y * y ^ 2) (Set.Ioi (0 : ℝ)) :=
    (W2_contDiffOn.of_le le_top).mul (contDiffOn_id.pow 2)
  have hW2sq_at : DifferentiableAt ℝ (fun y : ℝ => W2 y * y ^ 2) z :=
    (hW2sq_cd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- first and second derivatives of `g = h χ`
  have hg1 : deriv (fun y : ℝ => h y * χ y) z = deriv h z * χ z + h z * deriv χ z := by
    rw [show (fun y : ℝ => h y * χ y) = h * χ from rfl, deriv_mul hh_at hχ_at]
  have hg2 : deriv (deriv (fun y : ℝ => h y * χ y)) z
      = deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z + h z * deriv (deriv χ) z := by
    have heq : deriv (h * χ) =ᶠ[𝓝 z] fun y => deriv h y * χ y + h y * deriv χ y := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      rw [deriv_mul]
      · exact (hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hy)
      · exact (hχcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hy)
    have h1 : (fun y : ℝ => h y * χ y) = h * χ := rfl
    rw [h1, heq.deriv_eq]
    rw [show (fun y : ℝ => deriv h y * χ y + h y * deriv χ y) = deriv h * χ + h * deriv χ from rfl,
      deriv_add (hdh_at.mul hχ_at) (hh_at.mul hdχ_at),
      deriv_mul hdh_at hχ_at, deriv_mul hh_at hdχ_at]
    ring
  -- bounds on `|g'|` and `|g''|`
  have hG1 : |deriv (fun y : ℝ => h y * χ y) z| ≤ |deriv h z| * χ z + |h z| * |deriv χ z| := by
    rw [hg1]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hχ0]
  have hG2 : |deriv (deriv (fun y : ℝ => h y * χ y)) z|
      ≤ |deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z| + |h z| * |deriv (deriv χ) z| := by
    rw [hg2]
    have h1 : |deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z|
        ≤ |deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : |h z * deriv (deriv χ) z| = |h z| * |deriv (deriv χ) z| := abs_mul _ _
    calc |deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z + h z * deriv (deriv χ) z|
        ≤ |deriv (deriv h) z * χ z + 2 * deriv h z * deriv χ z| + |h z * deriv (deriv χ) z| :=
          abs_add_le _ _
      _ ≤ (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|)
            + |h z| * |deriv (deriv χ) z| := by
          rw [h2]; linarith [h1]
  -- the derivative of `ρ z² g'`
  have hD_id : deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
      = deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
        + (W2 z * z ^ 2) * deriv (deriv (fun y : ℝ => h y * χ y)) z := by
    have hsplit : deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
        = deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
          + (fun y : ℝ => W2 y * y ^ 2) z * deriv (deriv (fun y : ℝ => h y * χ y)) z := by
      rw [show (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y)
          = (fun y : ℝ => W2 y * y ^ 2) * deriv (fun y : ℝ => h y * χ y) from rfl,
        deriv_mul hW2sq_at hdg_at]
    have hbeta : (fun y : ℝ => W2 y * y ^ 2) z = W2 z * z ^ 2 := rfl
    rw [hsplit, hbeta]
  have hD_abs : |deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z|
      ≤ 2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
        + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
    rw [hD_id]
    have h1 := abs_deriv_W2_mul_sq_le (z := z) hz
    have h2 : |deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
          + (W2 z * z ^ 2) * deriv (deriv (fun y : ℝ => h y * χ y)) z|
        ≤ |deriv (fun y : ℝ => W2 y * y ^ 2) z| * |deriv (fun y : ℝ => h y * χ y) z|
          + (W2 z * z ^ 2) * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hρ (sq_nonneg z))]
    have h3 : 2 / z * (W2 z * z ^ 2) = 2 * W2 z * z := by
      field_simp
    calc |deriv (fun y : ℝ => W2 y * y ^ 2) z * deriv (fun y : ℝ => h y * χ y) z
            + (W2 z * z ^ 2) * deriv (deriv (fun y : ℝ => h y * χ y)) z|
        ≤ |deriv (fun y : ℝ => W2 y * y ^ 2) z| * |deriv (fun y : ℝ => h y * χ y) z|
            + (W2 z * z ^ 2) * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := h2
      _ ≤ (2 / z * (W2 z * z ^ 2)) * |deriv (fun y : ℝ => h y * χ y) z|
            + (W2 z * z ^ 2) * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
          have h4 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (deriv (fun y : ℝ => h y * χ y) z))
          linarith [h4]
      _ = 2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
            + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z| := by
          rw [h3]
  -- the five AM–GM pairings
  have hb1 : 2 * W2 z * z * |deriv h z| * |h z| * χ z ^ 2
      ≤ (1 / 8) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + 8 * (W2 z * h z ^ 2 * χ z ^ 2) := by
    have h := young_eighth (W2 z * χ z ^ 2) (z * deriv h z) (h z)
      (mul_nonneg hρ (sq_nonneg _))
    rw [abs_mul, abs_of_pos hz] at h
    linarith [h]
  have hb2 : 2 * W2 z * z * |h z| * |deriv χ z| * |h z| * χ z ≤ (1 / 4) * (W2 z * h z ^ 2) := by
    have habs : |z * deriv χ z| = z * |deriv χ z| := by rw [abs_mul, abs_of_pos hz]
    have hsq : |h z| * |h z| = h z ^ 2 := by rw [← sq_abs (h z)]; ring
    have hstep : 2 * z * |deriv χ z| ≤ 1 / 4 := by linarith [hχder1, habs]
    have hpos : 0 ≤ W2 z * (|h z| * |h z|) * χ z :=
      mul_nonneg (mul_nonneg hρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))) hχ0
    calc 2 * W2 z * z * |h z| * |deriv χ z| * |h z| * χ z
        = (2 * z * |deriv χ z|) * (W2 z * (|h z| * |h z|) * χ z) := by ring
      _ ≤ (1 / 4) * (W2 z * (|h z| * |h z|) * χ z) := mul_le_mul_of_nonneg_right hstep hpos
      _ ≤ (1 / 4) * (W2 z * h z ^ 2) := by
          have hle : W2 z * (|h z| * |h z|) * χ z ≤ W2 z * h z ^ 2 := by
            rw [hsq]
            nlinarith [hA, hχ0, hχ1]
          linarith [hle]
  have hb3 : W2 z * z ^ 2 * |deriv (deriv h) z| * |h z| * χ z ^ 2
      ≤ (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + (α ^ 2)⁻¹ * (W2 z * h z ^ 2 * χ z ^ 2) := by
    have h := young_weighted (W2 z * χ z ^ 2) (α ^ 2 / 2) (z ^ 2 * deriv (deriv h) z) (h z)
      (mul_nonneg hρ (sq_nonneg _)) (by positivity)
    rw [abs_mul, abs_of_nonneg (sq_nonneg z),
      show ((α ^ 2 / 2))⁻¹ = 2 * (α ^ 2)⁻¹ by field_simp] at h
    linarith [h]
  have hb4 : 2 * W2 z * z ^ 2 * |deriv h z| * |deriv χ z| * |h z| * χ z
      ≤ (1 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2) + W2 z * h z ^ 2 := by
    have he : 2 * W2 z * z ^ 2 * |deriv h z| * |deriv χ z| * |h z| * χ z
        = 2 * |z * deriv χ z| * (W2 z * (z * |deriv h z| * χ z) * |h z|) := by
      rw [abs_mul, abs_of_pos hz]; ring
    rw [he]
    have hstep : 2 * |z * deriv χ z| ≤ 1 / 4 := by linarith [hχder1]
    have hq := young_quarter (W2 z) (z * |deriv h z| * χ z) (h z) hρ
    rw [show (z * |deriv h z| * χ z) ^ 2 = (z * deriv h z) ^ 2 * χ z ^ 2 by
      rw [mul_pow, mul_pow, sq_abs]; ring] at hq
    have hpos : 0 ≤ W2 z * (z * |deriv h z| * χ z) * |h z| :=
      mul_nonneg (mul_nonneg hρ (mul_nonneg (mul_nonneg hz.le (abs_nonneg _)) hχ0))
        (abs_nonneg _)
    have hstep2 : 2 * |z * deriv χ z| * (W2 z * (z * |deriv h z| * χ z) * |h z|)
        ≤ (1 / 4) * (W2 z * (z * |deriv h z| * χ z) * |h z|) :=
      mul_le_mul_of_nonneg_right hstep hpos
    linarith [hstep2, hq]
  have hb5 : W2 z * z ^ 2 * |h z| * |deriv (deriv χ) z| * |h z| * χ z
      ≤ δ * (W2 z * h z ^ 2) := by
    have habs : |z ^ 2 * deriv (deriv χ) z| = z ^ 2 * |deriv (deriv χ) z| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
    have hsq : |h z| * |h z| = h z ^ 2 := by rw [← sq_abs (h z)]; ring
    have hstep : z ^ 2 * |deriv (deriv χ) z| ≤ δ := by linarith [hχder2, habs]
    have hpos : 0 ≤ W2 z * (|h z| * |h z|) * χ z :=
      mul_nonneg (mul_nonneg hρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))) hχ0
    calc W2 z * z ^ 2 * |h z| * |deriv (deriv χ) z| * |h z| * χ z
        = (z ^ 2 * |deriv (deriv χ) z|) * (W2 z * (|h z| * |h z|) * χ z) := by ring
      _ ≤ δ * (W2 z * (|h z| * |h z|) * χ z) := mul_le_mul_of_nonneg_right hstep hpos
      _ ≤ δ * (W2 z * h z ^ 2) := by
          have hle : W2 z * (|h z| * |h z|) * χ z ≤ W2 z * h z ^ 2 := by
            rw [hsq]
            nlinarith [hA, hχ0, hχ1]
          exact mul_le_mul_of_nonneg_left hle hδ0
  -- assemble
  have hstep1 : -(deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
        * (h z * χ z))
      ≤ |deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z|
        * (|h z| * χ z) := by
    refine (neg_le_abs _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hχ0]
  have hstep2 : |deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z|
        * (|h z| * χ z)
      ≤ (2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
          + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z|) * (|h z| * χ z) :=
    mul_le_mul_of_nonneg_right hD_abs (mul_nonneg (abs_nonneg _) hχ0)
  have hstep3 : (2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
          + W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z|) * (|h z| * χ z)
      ≤ (2 * W2 z * z * (|deriv h z| * χ z + |h z| * |deriv χ z|)
          + W2 z * z ^ 2 * (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|
              + |h z| * |deriv (deriv χ) z|)) * (|h z| * χ z) := by
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) hχ0)
    have hA1 : 2 * W2 z * z * |deriv (fun y : ℝ => h y * χ y) z|
        ≤ 2 * W2 z * z * (|deriv h z| * χ z + |h z| * |deriv χ z|) :=
      mul_le_mul_of_nonneg_left hG1 (by positivity)
    have hA2 : W2 z * z ^ 2 * |deriv (deriv (fun y : ℝ => h y * χ y)) z|
        ≤ W2 z * z ^ 2 * (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|
            + |h z| * |deriv (deriv χ) z|) :=
      mul_le_mul_of_nonneg_left hG2 (by positivity)
    linarith [hA1, hA2]
  have hstep4 : (2 * W2 z * z * (|deriv h z| * χ z + |h z| * |deriv χ z|)
          + W2 z * z ^ 2 * (|deriv (deriv h) z| * χ z + 2 * |deriv h z| * |deriv χ z|
              + |h z| * |deriv (deriv χ) z|)) * (|h z| * χ z)
      = 2 * W2 z * z * |deriv h z| * |h z| * χ z ^ 2
        + 2 * W2 z * z * |h z| * |deriv χ z| * |h z| * χ z
        + (W2 z * z ^ 2 * |deriv (deriv h) z| * |h z| * χ z ^ 2
          + 2 * W2 z * z ^ 2 * |deriv h z| * |deriv χ z| * |h z| * χ z
          + W2 z * z ^ 2 * |h z| * |deriv (deriv χ) z| * |h z| * χ z) := by
    ring
  linarith [hstep1, hstep2, hstep3, hstep4, hb1, hb2, hb3, hb4, hb5]

/-! ### The arithmetic core -/

/-- **Pure arithmetic core of the cut-off Agmon estimate.**  If `0 < α ≤ 1`, `δ ≤ 1`, all of
`Ag, X, p, q` are nonnegative and
`X ≤ 2 Ag + p/32`,  `Ag ≤ (9/64) X + (α²/4) q + (α⁻² + 12 + δ) p`,
then `α² X ≤ 100 (p + α⁴ q)`.  (Substituting the first inequality into the second gives
`(23/32) Ag ≤ (9/2048 + α⁻² + 12 + δ) p + (α²/4) q`, whence
`α² X ≤ (16/23) α⁴ q + (32/23)(2 + 27α²) p ≤ 39 (p + α⁴ q)`.) -/
theorem agmon_arith {α δ Ag X p q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ1 : δ ≤ 1)
    (hAg : 0 ≤ Ag) (hX : 0 ≤ X) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : X ≤ 2 * Ag + p / 32)
    (h2 : Ag ≤ (9 / 64) * X + (α ^ 2 / 4) * q + ((α ^ 2)⁻¹ + 12 + δ) * p) :
    α ^ 2 * X ≤ 100 * (p + α ^ 4 * q) := by
  have hα2pos : 0 < α ^ 2 := pow_pos hα 2
  have hα2le : α ^ 2 ≤ 1 := by nlinarith
  have hα2ne : α ^ 2 ≠ 0 := ne_of_gt hα2pos
  have hα4nn : 0 ≤ α ^ 4 := by positivity
  -- multiply `h2` by `α²`
  have h2α : α ^ 2 * Ag ≤ (9 / 64) * (α ^ 2 * X) + (α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p := by
    have h := mul_le_mul_of_nonneg_left h2 (le_of_lt hα2pos)
    have he : α ^ 2 * ((9 / 64) * X + (α ^ 2 / 4) * q + ((α ^ 2)⁻¹ + 12 + δ) * p)
        = (9 / 64) * (α ^ 2 * X) + (α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p := by
      field_simp
      ring
    rw [he] at h
    exact h
  -- multiply `h1` by `α²`
  have h1α : α ^ 2 * X ≤ 2 * (α ^ 2 * Ag) + (α ^ 2 * p) / 32 := by
    have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hα2pos)
    have he : α ^ 2 * (2 * Ag + p / 32) = 2 * (α ^ 2 * Ag) + (α ^ 2 * p) / 32 := by ring
    rw [he] at h
    exact h
  have hstep : (1 - 2 * (9 / 64)) * (α ^ 2 * X)
      ≤ 2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32 := by
    nlinarith [h1α, h2α]
  have hstep2 : α ^ 2 * X
      ≤ (32 / 23) * (2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32) := by
    have hpos : (0 : ℝ) < 1 - 2 * (9 / 64) := by norm_num
    have h2' : α ^ 2 * X * (1 - 2 * (9 / 64))
        ≤ 2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32 := by
      rw [mul_comm]
      exact hstep
    have h := (le_div_iff₀ hpos).mpr h2'
    have he : (32 / 23 : ℝ) = (1 - 2 * (9 / 64))⁻¹ := by norm_num
    rw [he]
    rw [div_eq_inv_mul] at h
    exact h
  have hb : 2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32
      ≤ (23 / 32) * (100 * (p + α ^ 4 * q)) := by
    nlinarith [hα1, hδ1, hp, hq, hα2le, hα4nn, mul_nonneg hα4nn hq, mul_nonneg (sq_nonneg α) hp,
      mul_nonneg (sq_nonneg α) (mul_nonneg (le_of_lt hα) hp)]
  calc α ^ 2 * X
      ≤ (32 / 23) * (2 * ((α ^ 4 / 4) * q + (1 + (12 + δ) * α ^ 2) * p) + (α ^ 2 * p) / 32) := hstep2
    _ ≤ (32 / 23) * ((23 / 32) * (100 * (p + α ^ 4 * q))) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 100 * (p + α ^ 4 * q) := by ring

/-! ### The cut-off weighted Agmon estimate -/

/-- **The cut-off form of the weighted Agmon estimate**: for a smooth cut-off `χ` with `0 ≤ χ ≤ 1`,
`|z χ'| ≤ 1/8`, `|z² χ''| ≤ δ ≤ 1` and compact support in `(0,∞)`, and for `C^∞` data `h` on
`(0,∞)` with `∫ ρ h² < ∞` and `∫ ρ (z²h'')² < ∞` (`ρ = W2 z = (w z)^2`),

`α² ∫ ρ (zh')² χ² ≤ 100 (∫ ρ h² + α⁴ ∫ ρ (z²h'')²)`,  for `0 < α ≤ 1`.

This is Piece 2 of `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`; read that file for the
derivation (integration by parts for the compactly supported `h·χ`, then the pointwise AM–GM
pairings — the `zχ'` terms are paired with `h·χ`, never with a second `zh'`).  All integrals are
honest Bochner integrals over `(0,∞)`. -/
theorem agmon_cutoff_estimate (χ : ℝ → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hχcd : ContDiffOn ℝ Work.Stability.smoothOrder χ (Set.Ioi (0 : ℝ)))
    (hχ0 : ∀ z : ℝ, 0 ≤ χ z) (hχ1 : ∀ z : ℝ, χ z ≤ 1)
    (hχder1 : ∀ z : ℝ, 0 < z → |z * deriv χ z| ≤ 1 / 8)
    (hχder2 : ∀ z : ℝ, 0 < z → |z ^ 2 * deriv (deriv χ) z| ≤ δ)
    (hsupp : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → χ z = 0)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)))
    (hp : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.EllipticEst.Blocks.W2 z * h z ^ 2) (Set.Ioi (0 : ℝ)))
    (hq : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.EllipticEst.Blocks.W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)
      (Set.Ioi (0 : ℝ))) :
    α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.EllipticEst.Blocks.W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      ≤ 100 * ((∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.Blocks.W2 z * h z ^ 2)
          + α ^ 4 * (∫ z in Set.Ioi (0 : ℝ),
              Work.FTS.EllipticEst.Blocks.W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)) := by
  obtain ⟨a, b, ha, hab, hsuppχ⟩ := hsupp
  have hne : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  have hder : Work.Stability.smoothOrder + 1 ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => by
    simp only [Set.mem_Ioi]; linarith [hz.1, ha]
  -- the compactly supported function `g = h χ`
  have hgsupp : ∀ z : ℝ, z ∉ Set.Icc a b → (fun y : ℝ => h y * χ y) z = 0 := by
    intro z hz; simp [hsuppχ z hz]
  have hgcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => h y * χ y) (Set.Ioi (0 : ℝ)) :=
    hcd.mul hχcd
  -- integration by parts
  have hibp : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
      = -∫ z in Set.Ioi (0 : ℝ),
          deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z
            * (h z * χ z) :=
    AgmonIBP (h := fun y : ℝ => h y * χ y) (a := a) (b := b) ha hgsupp hgcd
  -- off the support, `g` is locally zero, so is its derivative
  have hderivg_zero : ∀ z : ℝ, z ∉ Set.Icc a b → deriv (fun y : ℝ => h y * χ y) z = 0 := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · have hev : (fun y : ℝ => h y * χ y) =ᶠ[𝓝 z] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        simp [hsuppχ y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)]
      rw [hev.deriv_eq]; simp
    · have hev : (fun y : ℝ => h y * χ y) =ᶠ[𝓝 z] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        simp [hsuppχ y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)]
      rw [hev.deriv_eq]; simp
  -- continuity facts on `[a,b]`
  have hcontW2 : ContinuousOn W2 (Set.Icc a b) := W2_contDiffOn.continuousOn.mono hsub
  have hcont_h : ContinuousOn h (Set.Icc a b) := hcd.continuousOn.mono hsub
  have hcont_chi : ContinuousOn χ (Set.Icc a b) := hχcd.continuousOn.mono hsub
  have hcont_dh : ContinuousOn (deriv h) (Set.Icc a b) :=
    (hcd.deriv_of_isOpen isOpen_Ioi hder).continuousOn.mono hsub
  have hcont_ddh : ContinuousOn (deriv (deriv h)) (Set.Icc a b) :=
    ((hcd.deriv_of_isOpen isOpen_Ioi hder).deriv_of_isOpen isOpen_Ioi hder).continuousOn.mono hsub
  have hcont_g : ContinuousOn (fun y : ℝ => h y * χ y) (Set.Icc a b) :=
    hcont_h.mul hcont_chi
  have hcont_dg : ContinuousOn (deriv (fun y : ℝ => h y * χ y)) (Set.Icc a b) :=
    (hgcd.deriv_of_isOpen isOpen_Ioi hder).continuousOn.mono hsub
  have hU_cd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) (Set.Ioi (0 : ℝ)) :=
    ((W2_contDiffOn.of_le le_top).mul (contDiffOn_id.pow 2)).mul
      (hgcd.deriv_of_isOpen isOpen_Ioi hder)
  have hcont_dU : ContinuousOn
      (deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y)) (Set.Icc a b) :=
    ((hU_cd.of_le (by simp [Work.Stability.smoothOrder])).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).mono hsub
  -- integrability of the pieces
  have hInt_Ag : IntegrableOn
      (fun z : ℝ => W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact hcontW2.mul ((continuousOn_id.mul hcont_dg).pow 2)
    · intro z hz
      rw [hderivg_zero z hz]; ring
  have hInt_X : IntegrableOn (fun z : ℝ => W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact (hcontW2.mul ((continuousOn_id.mul hcont_dh).pow 2)).mul (hcont_chi.pow 2)
    · intro z hz
      rw [hsuppχ z hz]; ring
  have hInt_Q : IntegrableOn
      (fun z : ℝ => W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact (hcontW2.mul (((continuousOn_id.pow 2).mul hcont_ddh).pow 2)).mul (hcont_chi.pow 2)
    · intro z hz
      rw [hsuppχ z hz]; ring
  have hInt_P : IntegrableOn (fun z : ℝ => W2 z * h z ^ 2 * χ z ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact (hcontW2.mul (hcont_h.pow 2)).mul (hcont_chi.pow 2)
    · intro z hz
      rw [hsuppχ z hz]; ring
  have hInt_DU : IntegrableOn (fun z : ℝ =>
      deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z * (h z * χ z))
      (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact hcont_dU.mul hcont_g
    · intro z hz
      rw [hsuppχ z hz]; ring
  -- pointwise bound at every `z > 0`
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      -(deriv (fun y : ℝ => W2 y * y ^ 2 * deriv (fun y : ℝ => h y * χ y) y) z * (h z * χ z))
        ≤ (9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
          + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
          + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
          + (5 / 4 + δ) * (W2 z * h z ^ 2) :=
    fun z hz => agmon_pointwise hz hα hδ0 hcd hχcd (hχ0 z) (hχ1 z) (hχder1 z hz) (hχder2 z hz)
  -- integrability of the pointwise upper bound
  have hInt_rhs : IntegrableOn (fun z : ℝ =>
      (9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
        + (5 / 4 + δ) * (W2 z * h z ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (((hInt_X.const_mul (9 / 64)).add (hInt_Q.const_mul (α ^ 2 / 4))).add
      (hInt_P.const_mul ((α ^ 2)⁻¹ + 8))).add (hp.const_mul (5 / 4 + δ))
  -- the Agmon integral is bounded by the integral of the pointwise bound
  have hAg_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ),
          ((9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
            + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
            + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
            + (5 / 4 + δ) * (W2 z * h z ^ 2)) := by
    rw [hibp, ← integral_neg]
    exact integral_mono_ae hInt_DU.neg hInt_rhs (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz)
  -- split the integral of the pointwise bound
  have hsplit : (∫ z in Set.Ioi (0 : ℝ),
        ((9 / 64) * (W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
          + (α ^ 2 / 4) * (W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
          + ((α ^ 2)⁻¹ + 8) * (W2 z * h z ^ 2 * χ z ^ 2)
          + (5 / 4 + δ) * (W2 z * h z ^ 2)))
      = (9 / 64) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        + ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 * χ z ^ 2)
        + (5 / 4 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) :=
    integral_lin4 hInt_X hInt_Q hInt_P hp
  -- `X ≤ 2 Ag + p/32`
  have hptX : ∀ z ∈ Set.Ioi (0 : ℝ),
      W2 z * (z * deriv h z) ^ 2 * χ z ^ 2
        ≤ 2 * (W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
          + (1 / 32) * (W2 z * h z ^ 2) := by
    intro z hz
    have hρ : 0 ≤ W2 z := W2_nonneg z
    have hz2 : 2 * (z * deriv χ z) ^ 2 ≤ 1 / 32 := by
      have h1 : (z * deriv χ z) ^ 2 ≤ 1 / 64 := by
        calc (z * deriv χ z) ^ 2 = |z * deriv χ z| ^ 2 := (sq_abs _).symm
          _ ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hχder1 z hz) 2
          _ = 1 / 64 := by norm_num
      linarith
    have hdiff : deriv (fun y : ℝ => h y * χ y) z - deriv h z * χ z = h z * deriv χ z := by
      have hh_at : DifferentiableAt ℝ h z :=
        (hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hχ_at : DifferentiableAt ℝ χ z :=
        (hχcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)
      rw [show (fun y : ℝ => h y * χ y) = h * χ from rfl, deriv_mul hh_at hχ_at]
      ring
    have heq : z * deriv h z * χ z
        = z * deriv (fun y : ℝ => h y * χ y) z - z * h z * deriv χ z := by
      have h2 := congrArg (fun t : ℝ => z * t) hdiff
      rw [mul_sub] at h2
      linarith [h2]
    have hkey : (z * deriv h z * χ z) ^ 2
        ≤ 2 * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2 + 2 * (z * h z * deriv χ z) ^ 2 := by
      have hsq : 0 ≤ (z * deriv (fun y : ℝ => h y * χ y) z + z * h z * deriv χ z) ^ 2 :=
        sq_nonneg _
      rw [heq]
      nlinarith [hsq]
    have h1 : W2 z * (z * deriv h z) ^ 2 * χ z ^ 2
        = W2 z * (z * deriv h z * χ z) ^ 2 := by ring
    rw [h1]
    have h2 : W2 z * (z * deriv h z * χ z) ^ 2
        ≤ W2 z * (2 * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2
            + 2 * (z * h z * deriv χ z) ^ 2) := mul_le_mul_of_nonneg_left hkey hρ
    have h3 : W2 z * (2 * (z * h z * deriv χ z) ^ 2)
        = (2 * (z * deriv χ z) ^ 2) * (W2 z * h z ^ 2) := by ring
    have h4 : 0 ≤ W2 z * h z ^ 2 := mul_nonneg hρ (sq_nonneg _)
    have h5 : (2 * (z * deriv χ z) ^ 2) * (W2 z * h z ^ 2) ≤ (1 / 32) * (W2 z * h z ^ 2) :=
      mul_le_mul_of_nonneg_right hz2 h4
    linarith [h2, h3, h5]
  have hX_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      ≤ 2 * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
        + (1 / 32) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) := by
    have hInt_rhs2 : IntegrableOn (fun z : ℝ =>
        2 * (W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
          + (1 / 32) * (W2 z * h z ^ 2)) (Set.Ioi (0 : ℝ)) :=
      (hInt_Ag.const_mul 2).add (hp.const_mul (1 / 32))
    have hmono := integral_mono_ae hInt_X hInt_rhs2 (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hptX z hz)
    rw [integral_add (f := fun z : ℝ => 2 * (W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2))
        (g := fun z : ℝ => (1 / 32) * (W2 z * h z ^ 2)) (hInt_Ag.const_mul 2) (hp.const_mul (1 / 32)),
      integral_const_mul, integral_const_mul] at hmono
    exact hmono
  -- `P ≤ p`, `Q ≤ q`
  have hP_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 * χ z ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 := by
    refine integral_mono_ae hInt_P hp ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hc : χ z ^ 2 ≤ 1 := by nlinarith [hχ0 z, hχ1 z]
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg (W2_nonneg z) (sq_nonneg (h z)))
    linarith [this]
  have hQ_le : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 := by
    refine integral_mono_ae hInt_Q hq ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hc : χ z ^ 2 ≤ 1 := by nlinarith [hχ0 z, hχ1 z]
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg (W2_nonneg z) (sq_nonneg (z ^ 2 * deriv (deriv h) z)))
    linarith [this]
  -- nonnegativity
  have hX_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2 :=
    integral_nonneg fun z => mul_nonneg (mul_nonneg (W2_nonneg z) (sq_nonneg _)) (sq_nonneg _)
  have hAg_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (W2_nonneg z) (sq_nonneg _)
  have hp_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 :=
    integral_nonneg fun z => mul_nonneg (W2_nonneg z) (sq_nonneg _)
  have hq_nn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (W2_nonneg z) (sq_nonneg _)
  -- final arithmetic
  have hmain : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
      ≤ (9 / 64) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
        + (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)
        + ((α ^ 2)⁻¹ + 12 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) := by
    rw [hsplit] at hAg_le
    have hQ' : (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2 * χ z ^ 2)
        ≤ (α ^ 2 / 4) * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2) :=
      mul_le_mul_of_nonneg_left hQ_le (by positivity)
    have hP' : ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2 * χ z ^ 2)
        ≤ ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) :=
      mul_le_mul_of_nonneg_left hP_le (by positivity)
    have hb : ((α ^ 2)⁻¹ + 8) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2)
          + (5 / 4 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2)
        ≤ ((α ^ 2)⁻¹ + 12 + δ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) := by
      have h := hp_nn
      nlinarith [hp_nn]
    linarith [hAg_le, hQ', hP', hb]
  have hX_le' : (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv h z) ^ 2 * χ z ^ 2)
      ≤ 2 * (∫ z in Set.Ioi (0 : ℝ), W2 z * (z * deriv (fun y : ℝ => h y * χ y) z) ^ 2)
        + (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) / 32 := by
    have h32 : (1 / 32 : ℝ) * (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2)
        = (∫ z in Set.Ioi (0 : ℝ), W2 z * h z ^ 2) / 32 := by ring
    rw [h32] at hX_le
    exact hX_le
  exact agmon_arith hα hα1 hδ1 hAg_nn hX_nn hp_nn hq_nn hX_le' hmain

end

end Work.EllipticEst
end
-- ===== merged: Submission.Work.FTS.LocDataExt.DthIter_Gam_abs_le5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `|D_θ^i Γ| ≤ 100000 · Γ` on `Iθ`, for `i ≤ 5`

This extends `Work.FTS.LocData.DthIter_Gam_abs_le` (the case `i ≤ 4`) by one order.

The `i ≤ 4` file reduces the statement, through
`Spaces.dthU_iter_Gam_abs_bound`, to the coefficient bound `|Tfun j α θ| ≤ 100000`
for `j ≤ 3`.  Recall `Tfun j α θ = (Qp j α).eval (cos 2θ)`, where the coefficient
polynomials satisfy

`Qp 0 α = X - 1/3`,   `Qp (j+1) α = -2(1-X²)·(Qp j α)' + α·(X-1/3)·(Qp j α)`.

Hence for `i ≤ 5` it remains to bound `Tfun 4 α`, i.e. `Qp 4 α` on `[-1,1]`.  Since

`(Qp 4 α).eval v = -2(1-v²)·(Qp 3 α)'.eval v + α(v-1/3)·(Qp 3 α).eval v`

and `|(Qp 3 α).eval v| ≤ 10300/81` is already known, we need a bound on the derivative
`(Qp 3 α)'.eval v`.  Differentiating the recursion gives

`Qp (j+1)' = 4v·Qp j' - 2(1-v²)·Qp j'' + α·Qp j + α(v-1/3)·Qp j'`,

so `(Qp 3 α)'.eval v` is controlled by `(Qp 2 α)`, `(Qp 2 α)'` (both already bounded) and
the second derivative `(Qp 2 α)''`.  The latter is computed explicitly and bounded by `96`.
Carrying the numbers through gives

`|(Qp 3 α)'.eval v| ≤ 13072/27`  and  `|(Qp 4 α).eval v| ≤ 276496/243 ≤ 100000`,

which is all that is needed.
-/

namespace Work.FTS.LocDataExt

open Work.FTS.LocData

set_option autoImplicit false

/-! ## Derivative recursions for the coefficient polynomials -/

/-- The derivative recursion for the coefficient polynomials, obtained by
differentiating `Q_{j+1} = -2(1-X²)Q_j' + α(X-1/3)Q_j`. -/
theorem Qp_deriv_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.eval v
      = 4 * v * (Qp j α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp j α).derivative.derivative.eval v
        + α * (Qp j α).eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.eval v := by
  simp [Qp]; ring

/-- Explicit second derivative of `Qp 2`, evaluated. -/
theorem Qp2_deriv2_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.eval v
      = 4 * (4 * v + 2 * α * (v - 1 / 3)) + 8 * v * (4 + 2 * α)
        + 2 * α * (4 * v + 2 * α * (v - 1 / 3)) + α * (v - 1 / 3) * (4 + 2 * α) := by
  simp [Qp]; ring

/-- **Bound on `(Qp 2 α)''`.** -/
theorem Qp2_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 2 α).derivative.derivative.eval v| ≤ 96 := by
  rw [Qp2_deriv2_eval]
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hR : |4 * v + 2 * α * (v - 1 / 3)| ≤ 20 / 3 := by
    rw [← Qp1_deriv_eval]; exact Qp1_deriv_bound hα0 hα1 hv
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hA : |4 * (4 * v + 2 * α * (v - 1 / 3))| ≤ 4 * (20 / 3) :=
    abs_mul_le_of (A := 4) (B := 20 / 3) (by norm_num) hR (by norm_num)
  have hB : |8 * v * (4 + 2 * α)| ≤ 8 * 1 * 6 := by
    rw [show 8 * v * (4 + 2 * α) = (8 * v) * (4 + 2 * α) by ring]
    exact abs_mul_le_of (A := 8 * 1) (B := 6)
      (by rw [abs_mul]; norm_num; exact hv) h4 (by norm_num)
  have hC : |2 * α * (4 * v + 2 * α * (v - 1 / 3))| ≤ 2 * 1 * (20 / 3) := by
    rw [show 2 * α * (4 * v + 2 * α * (v - 1 / 3))
        = (2 * α) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 20 / 3)
      (by simpa using abs_two_mul_le_two hα0 hα1) hR (by norm_num)
  have hD : |α * (v - 1 / 3) * (4 + 2 * α)| ≤ 1 * (4 / 3) * 6 := by
    rw [show α * (v - 1 / 3) * (4 + 2 * α) = (α * (v - 1 / 3)) * (4 + 2 * α) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 6)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      h4 (by norm_num)
  have hsp1 := abs_add_le (4 * (4 * v + 2 * α * (v - 1 / 3)) + 8 * v * (4 + 2 * α)
      + 2 * α * (4 * v + 2 * α * (v - 1 / 3))) (α * (v - 1 / 3) * (4 + 2 * α))
  have hsp2 := abs_add_le (4 * (4 * v + 2 * α * (v - 1 / 3)) + 8 * v * (4 + 2 * α))
      (2 * α * (4 * v + 2 * α * (v - 1 / 3)))
  have hsp3 := abs_add_le (4 * (4 * v + 2 * α * (v - 1 / 3))) (8 * v * (4 + 2 * α))
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-- The derivative recursion at `j = 2`, i.e. for `Qp 3`. -/
theorem Qp3_deriv_eval (α v : ℝ) :
    (Qp 3 α).derivative.eval v
      = 4 * v * (Qp 2 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v
        + α * (Qp 2 α).eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.eval v :=
  Qp_deriv_succ_eval 2 α v

/-- **Bound on `(Qp 3 α)'`.** -/
theorem Qp3_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 := by
  rw [Qp3_deriv_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS2 : |(Qp 2 α).derivative.eval v| ≤ 154 / 3 := Qp2_deriv_bound hα0 hα1 hv
  have hU2 : |(Qp 2 α).derivative.derivative.eval v| ≤ 96 := Qp2_deriv2_bound hα0 hα1 hv
  have hQ2 : |(Qp 2 α).eval v| ≤ 496 / 27 := Qp2_eval_bound hα0 hα1 hv
  have hA : |4 * v * (Qp 2 α).derivative.eval v| ≤ 4 * 1 * (154 / 3) := by
    rw [show 4 * v * (Qp 2 α).derivative.eval v
        = (4 * v) * (Qp 2 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 * 1) (B := 154 / 3)
      (by rw [abs_mul]; norm_num; exact hv) hS2 (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v| ≤ 2 * 1 * 96 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 96)
      (by rw [abs_mul]; norm_num; exact h1) hU2 (by norm_num)
  have hC : |α * (Qp 2 α).eval v| ≤ 1 * (496 / 27) :=
    abs_mul_le_of (A := 1) (B := 496 / 27) (by rwa [abs_of_nonneg hα0]) hQ2 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 2 α).derivative.eval v| ≤ 1 * (4 / 3) * (154 / 3) := by
    rw [show α * (v - 1 / 3) * (Qp 2 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 2 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 154 / 3)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hS2 (by norm_num)
  have hsp1 := abs_add_le (4 * v * (Qp 2 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v
      + α * (Qp 2 α).eval v) (α * (v - 1 / 3) * (Qp 2 α).derivative.eval v)
  have hsp2 := abs_add_le (4 * v * (Qp 2 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v)
      (α * (Qp 2 α).eval v)
  have hsp3 := abs_add_le (4 * v * (Qp 2 α).derivative.eval v)
      ((-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v)
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-- The recursion at `j = 3`, i.e. for `Qp 4`. -/
theorem Qp4_eval (α v : ℝ) :
    (Qp 4 α).eval v = (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
      + α * (v - 1 / 3) * (Qp 3 α).eval v := by
  have h := Qp_succ_eval 3 α v
  simpa using h

/-- **Bound on `Qp 4 α` on `[-1,1]`.** -/
theorem Qp4_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).eval v| ≤ 100000 := by
  rw [Qp4_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 := Qp3_deriv_bound hα0 hα1 hv
  have hQ : |(Qp 3 α).eval v| ≤ 10300 / 81 := Qp3_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v| ≤ 2 * 1 * (13072 / 27) := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 13072 / 27)
      (by rw [abs_mul]; norm_num; exact h1) hS (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 3 α).eval v| ≤ 1 * (4 / 3) * (10300 / 81) := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 10300 / 81)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ (by norm_num)
  calc |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 3 α).eval v|
      ≤ |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v|
        + |α * (v - 1 / 3) * (Qp 3 α).eval v| := abs_add_le _ _
    _ ≤ 2 * 1 * (13072 / 27) + 1 * (4 / 3) * (10300 / 81) := add_le_add hA hB
    _ = 276496 / 243 := by norm_num
    _ ≤ 100000 := by norm_num

/-- **The coefficient bound `|Tfun j α θ| ≤ 100000` for `j ≤ 4`**, extending
`Work.FTS.LocData.Tfun_abs_le` by one order. -/
theorem Tfun_abs_le4 (j : ℕ) (hj : j ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 100000 := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact Tfun_abs_le j (by omega) α hα hα1 θ
  · subst heq
    have hq : |(Qp 4 α).eval (Real.cos (2 * θ))| ≤ 100000 :=
      Qp4_eval_bound (le_of_lt hα) hα1
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    rw [Tfun_eq_Qp 4 α]
    simpa using hq

/-- The angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` on `Iθ`, extended by one order (to `i ≤ 5`).
The proved `i ≤ 4` version `Work.FTS.LocData.DthIter_Gam_abs_le` reduces the statement to a
bound `|Tfun (i-1) α θ| ≤ 100000`, so it suffices to bound `Qp 4 α` on `|v| ≤ 1`, `α ∈ [0,1]`
through the recursion `Qp (j+1) = -2(1-X²)·Qp j' + α·(X-1/3)·Qp j` and a bound on
`(Qp 3 α).derivative.eval v` obtained from the explicit `Qp3_eval`, and then to re-run the
final assembly of that file (`Work.Spaces.dthU_iter_Gam_abs_bound`). -/
theorem DthIter_Gam_abs_le5 (i : ℕ) (hi : i ≤ 5) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    linarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Tfun_abs_le4 (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 100000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS.LocDataExt
end
-- ===== merged: Submission.Work.SolutionDelivery.DatumCut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The cut-off datum is supported in the ball of radius `2L`.** -/
theorem cutDatum_support {L : ℝ} (hL : 0 < L) {ω : R3 → R3} :
    ∀ x : R3, cutDatum L ω x ≠ 0 → x ∈ Metric.closedBall 0 (2 * L) := by
  intro x hx
  have h1 : Work.Stability.chi (Work.Cyl.rho x / L) ≠ 0 := by
    intro h0
    exact hx (by simp [cutDatum, Work.Stability.omegaCut, h0])
  exact Work.Stability.cutFactor_support_subset (L := L) hL
    (by simpa [Function.mem_support] using h1)

/-- **The cut-off datum is bounded by the bound of `ω`.** -/
theorem cutDatum_bdd {L M : ℝ} {ω : R3 → R3} (h : ∀ x, ‖ω x‖ ≤ M) :
    ∀ x : R3, ‖cutDatum L ω x‖ ≤ M := by
  intro x
  have h1 : |Work.Stability.chi (Work.Cyl.rho x / L)| ≤ 1 := by
    rw [abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have h2 := h x
  rw [cutDatum, Work.Stability.omegaCut, norm_smul, Real.norm_eq_abs]
  calc |Work.Stability.chi (Work.Cyl.rho x / L)| * ‖ω x‖ ≤ 1 * M :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = M := one_mul M

/-- The cut-off datum of a measurable field is measurable (the cut-off factor is continuous). -/
theorem cutDatum_measurable {L : ℝ} {ω : R3 → R3} (h : AEStronglyMeasurable ω volume) :
    AEStronglyMeasurable (cutDatum L ω) volume := by
  have hscalar : AEStronglyMeasurable (fun x : R3 => Work.Stability.chi (Work.Cyl.rho x / L))
      volume := by
    have hc : Continuous fun x : R3 => Work.Stability.chi (‖x‖ / L) :=
      Work.Stability.chi_continuous.comp (continuous_norm.div_const L)
    have heq : (fun x : R3 => Work.Stability.chi (Work.Cyl.rho x / L))
        = fun x : R3 => Work.Stability.chi (‖x‖ / L) := by
      funext x
      rw [Work.Cyl.rho_eq_norm x]
    rw [heq]
    exact hc.aestronglyMeasurable
  exact hscalar.smul h

/-- **The cut-off datum is integrable** when `ω` is measurable and bounded. -/
theorem cutDatum_integrable {L M : ℝ} (hL : 0 < L) {ω : R3 → R3}
    (hmeas : AEStronglyMeasurable ω volume) (hbdd : ∀ x, ‖ω x‖ ≤ M) :
    Integrable (cutDatum L ω) volume :=
  Integrable.integrable_of_support_subset_closedBall (R := 2 * L) (M := M)
    (cutDatum_measurable hmeas) (cutDatum_support hL) (cutDatum_bdd hbdd)

end Work.SolutionDelivery
end
end
-- ===== merged: Submission.Work.SolutionDelivery.Slices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}

namespace ConstructedSolution

variable (C : ConstructedSolution α)

/-- **The slices of `ω` are measurable.** -/
theorem slicesMeasurable :
    Work.StabilityFar.SlicesMeasurable C.ω C.T :=
  Measurable.slicesMeasurable_of_core (ρ := C.R + 1) (R := C.R) (T := C.T)
    (le_of_lt (lt_add_one C.R)) C.hωcore.1 C.hSupp


/-- **The vorticity slices are integrable**: they are measurable, bounded by `M` and supported in
the ball of radius `R`. -/
theorem slices_integrable :
    ∀ t ∈ Work.StabilityFar.window C.T, Integrable (fun y : R3 => C.ω y t) :=
  fun t ht => Integrable.integrable_of_support_subset_closedBall (R := C.R) (M := C.M)
    ((C.slicesMeasurable t ht)) (fun y hy => C.hSupp_window t ht y hy)
    (fun y => C.hBdd_window t ht y)

/-- **The vorticity slices are bounded as a function** (the form consumed by the Biot–Savart
law). -/
theorem slices_isBoundedFun :
    ∀ t ∈ Work.StabilityFar.window C.T, IsBoundedFun (fun y : R3 => C.ω y t) :=
  fun t ht => Work.LWP.isBoundedFun_of_norm_le (C.hBdd_window t ht)

/-- **The Biot–Savart dictionary**: the vorticity of the constructed velocity is the field `ω`
that the construction uses to build it. -/
theorem vorticity_eq :
    ∀ t ∈ Work.StabilityFar.window C.T,
      ∀ x : R3, vorticity (fun y => C.u y t) x = C.ω x t :=
  Vorticity.vorticity_eq_of_bsSlice C.lwp.law C.bsSlice C.slices_integrable
    C.slices_isBoundedFun
    (fun t ht => C.hDivω t (C.window_subset ht))

/-- The vorticity slices are supported in `B(0,R)`. -/
theorem vorticity_supported :
    ∀ t ∈ Work.StabilityFar.window C.T,
      ∀ x : R3, vorticity (fun y => C.u y t) x ≠ 0 → x ∈ Metric.closedBall 0 C.R :=
  fun t ht x hx => C.hSupp_window t ht x (by rwa [C.vorticity_eq t ht x] at hx)

/-- The vorticity slices are bounded by `M`. -/
theorem vorticity_bounded :
    ∀ t ∈ Work.StabilityFar.window C.T, ∀ x : R3, ‖vorticity (fun y => C.u y t) x‖ ≤ C.M :=
  fun t ht x => by rw [C.vorticity_eq t ht x]; exact C.hBdd_window t ht x

/-- The vorticity sup-norm is honest (`BddAbove`) at every time of `[0,T)`. -/
theorem bddAbove_vorticity {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    BddAbove (Set.range (fun x : R3 => ‖vorticity (fun y => C.u y t) x‖)) :=
  ⟨C.M, by
    rintro _ ⟨x, rfl⟩
    exact C.vorticity_bounded t (Work.StabilityFar.Ico_subset_window C.hT.le ht) x⟩

end ConstructedSolution

end Work.SolutionDelivery
end
end
