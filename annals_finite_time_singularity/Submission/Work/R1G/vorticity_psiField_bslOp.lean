import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.Defs
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.DynGEquation
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.R1G.L12densFstar_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- For `α > 0`, `F_*(s)/s = 2 (1+s)^{-2}` — the elementary form of the model density. -/
private theorem Fstar_div_self_eq (s : ℝ) (hs : 0 < s) :
    Work.FM.Fstar s / s = 2 * (s + 1) ^ (-2 : ℝ) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have h2 : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
    simp only [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat, one_div]
  rw [h2]
  unfold Work.FM.Fstar
  field_simp
  ring


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.L12densFtot_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# Additivity of the angular density `L₁₂dens` over `F = F_* + g`

`Work.Construction.L12dens f r` is the *angular* density of the operator `L₁₂`, i.e. the integral

  `L₁₂dens f r = ∫_0^{π/2} K(θ)·f(r,θ)/r dθ`   (`K(θ) = 3 sinθ cos²θ`),

`Work.FM.L12dens Work.Spaces.K f r`.  Additivity in `f` is therefore additivity of the angular
integral, and it requires only that the two θ-slices be integrable on the compact interval
`Iθ = [0,π/2]`: for the reference profile this is `Work.Stability.integrableOn_slice_Fstar`
(`K` bounded, `Γ` continuous), and for the perturbation it follows from the smoothness
`ProfileData.hsmooth` of `g` on a neighbourhood of the closed quadrant.  The hypothesis `0 < r`
of the statement is then not needed for the algebra (only, through `g`'s slice continuity, the
weaker `-1 < r` entering `SmoothNbhd`).

This is the `hL`-splitting of the derivation bundle `GDerivData`/`GDerivDataQd`, read at a fixed
value of `z` (`z = r > 0`, where the `L₁₂`-operator is regular).
-/

variable {α : NNReal}




end Work.R1G
end
-- ===== merged: Submission.Work.R1G.L12densFtot_continuousAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G




end Work.R1G
end
-- ===== merged: Submission.Work.R1G.L12dens_g_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.cutDeficit_eq_zero_of_rho_lt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G



end Work.R1G
end
-- ===== merged: Submission.Work.R1G.cutDeficit_eq_zero_of_two_mul_lt_rho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set
open scoped Topology

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.exists_chiRad_ne_zero_of_annulus =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# The cut-off's radial logarithmic derivative is nonzero inside the annulus `(L, 2L)`

`Work.Stability.chi` is the `ContDiffBump 0` with `rIn = 1`, `rOut = 2`: `chi = 1` on `[-1,1]`
and `chi = 0` for `|x| ≥ 2`.  Hence `chi 1 = 1 ≠ 0 = chi 2`, and by the mean value theorem the
derivative of `chi` does not vanish identically on `(1,2)`.  Scaling back, the radial logarithmic
derivative `chiRad P r z = deriv chi (ρ(r,z)/L)/L` of the cut-off `χ(ρ/L)` is nonzero somewhere in
the annulus `L < ρ < 2L` — i.e. the cut-off deficit `cutDeficit` is a genuinely non-trivial object
on that annulus.
-/




end Work.R1G
end
-- ===== merged: Submission.Work.R1G.exists_cutDeficit_ne_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

open Set


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.exists_profileData_g_ne_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.R1G

/-! ## Scalar homogeneity of the weighted `H^k` operators

These elementary normalisations of `Work.Spaces.HkIntegrand` under `f ↦ c·f` are used to transfer
the estimates for `gA` to the amplitude-scaled perturbation `λ·gA`. -/

theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field c

theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  rw [Work.Spaces.pth, Work.Spaces.pth]
  exact deriv_const_mul_field c

theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  rw [Work.Spaces.Dz, Work.Spaces.Dz, pz_const_mul]
  ring

theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  rw [Work.Spaces.Dth, Work.Spaces.Dth, pth_const_mul]
  ring

theorem pzIter_const_mul (c : ℝ) (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, ih, pz_const_mul, Work.Spaces.pzIter_succ]

theorem pthIter_const_mul (c : ℝ) (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, ih, pth_const_mul, Work.Spaces.pthIter_succ]

theorem DzIter_const_mul (c : ℝ) (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DzIter_succ, ih, Dz_const_mul, Work.Spaces.DzIter_succ]

theorem DthIter_const_mul (c : ℝ) (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, ih, Dth_const_mul, Work.Spaces.DthIter_succ]

theorem mixed_const_mul (c : ℝ) (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

theorem HkIntegrand_const_mul (A c : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand A k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand A k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_const_mul]
    ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ * Work.Spaces.Wt A z θ) ^ 2
          else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left h, mixed_const_mul]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [h1, h2]
  ring

/-! ## Continuity of the perturbation -/



/-! ## The main theorem -/



end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.exists_profileData_g_visible =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.meridianResid_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.R1G

/-! ## Derivatives of `ρ` and of the cut-off `χ(ρ/L)` -/

/-- `r' ↦ ρ(r',z) = √(r'²+z²)` has radial derivative `r/ρ` at `r > 0` (the radial counterpart of
`Work.Cyl.hasDerivAt_rhoP_snd`). -/
lemma hasDerivAt_rhoP_fst' (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.const_add (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
    funext r'; rw [Work.Cyl.rhoP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp





/-! ## The product rule for the curried partials -/



/-! ## The meridian residual of a cut field -/


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.meridianResid_ssVort_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.profileResid_eq_gEqResidual =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

open Work.Construction Work.Coercivity Work.Spaces


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.vortEqWithDeficit_iff_meridian =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.vortEqWithDeficit_iff_meridian_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G


end Work.R1G
end
-- ===== merged: Submission.Work.R1G.vorticity_psiField_bslOp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The vorticity of the self-similar stream-function field, in the elliptic variables

For the stream function `ψ(r,z) = ρ(r,z)² Ψ(ρ(r,z)^p, θ(r,z))` (the polar ansatz (PolarBSL) of
Elgindi's §Setup), the `ℝ³` vorticity of the associated no-swirl field `psiField ψ` is
`-L(Ψ) e_θ`, where `L = bslOp p` is the elliptic operator of the self-similar variables.

This is the composition of the two established halves of the computation:

* `Work.Cyl.vorticity_psiField` : off the axis, `∇ × (psiField ψ) = -(cylOp ψ) e_θ`, where
  `cylOp` is the axisymmetric elliptic operator `-∂_rr - ∂_zz - (1/r)∂_r + 1/r²` of (3dBSL);
* `Work.Elliptic.cylOp_polar` : `cylOp (ρ²Ψ(ρ^p,·)) r z = bslOp p Ψ (ρ^p) (θ)`, the polar change
  of variables (PolarBSL) of the elliptic section.

The only extra ingredient is that the polar ansatz is `C²` at the point `(radial x, axial x)`,
which follows from `ContDiffAt`-stability of `ρ = √(r²+z²)` (away from the origin) and of
`θ = arctan(z/r)` (away from the axis), together with the given regularity of `Ψ` at
`(ρ(x)^p, θ(x))`.

Main statement: `Work.R1G.vorticity_psiField_bslOp`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Real Topology Matrix

namespace Work.R1G

/-! ## The dictionary between `(ρ, θ)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

/-- `ρ(x) = rhoP (radial x) (axial x)`: the three-dimensional radius `ρ = √(r²+x₃²)` is the
plane polar radius of the pair `(r, x₃)` of cylindrical coordinates. -/
theorem rhoP_radial_axial (x : R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radial_sq]

/-- `θ(x) = thetaP (radial x) (axial x)`: with our definitions this is `rfl`. -/
theorem thetaP_radial_axial (x : R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl

/-! ## The polar ansatz is `C²` off the axis -/

/-- **The polar stream-function ansatz is `C²` off the axis.**  If `Ψ` is `C²` at
`(ρ(x)^p, θ(x))` and `0 < radial x`, then `(r,z) ↦ ρ(r,z)² Ψ(ρ(r,z)^p, θ(r,z))` is `C²` at
`(radial x, axial x)`.

This is the regularity hypothesis needed to apply the curl identity
`Work.Cyl.vorticity_psiField` to the polar ansatz: near a point with `radial x > 0` the map
`(r,z) ↦ (ρ(r,z), θ(r,z))` is `C²` (the origin is excluded by `ρ ≥ radial x > 0` and the axis by
`radial x > 0`), and the composed function `(a,b) ↦ a² Ψ(a^p, b)` is `C²` at `(ρ x, θ x)`. -/
theorem contDiffAt_rhoP_mul_rpow_comp (p : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΨ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2)
      (Work.Cyl.rho x ^ p, Work.Cyl.theta x)) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2
        * Ψ (Work.Cyl.rhoP q.1 q.2 ^ p) (Work.Cyl.thetaP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
  have hrho : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x :=
    rhoP_radial_axial x
  have hrhone : Work.Cyl.rho x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hx (Work.Cyl.radial_le_rho x))
  -- the map `(r,z) ↦ (ρ(r,z), θ(r,z))` is `C²` at `(radial x, axial x)`
  have hpair : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      (Work.Cyl.rhoP q.1 q.2, Work.Cyl.thetaP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    apply ContDiffAt.prodMk
    · -- `ρ = √(r²+z²)`, and `r²+z² ≠ 0` at the point since `radial x > 0`
      have hsq : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2)
          (Work.Cyl.radial x, Work.Cyl.axial x) := by fun_prop
      have hne : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2)
          (Work.Cyl.radial x, Work.Cyl.axial x) ≠ 0 := by
        have : 0 < Work.Cyl.radial x ^ 2 := pow_pos hx 2
        positivity
      have h := (Real.contDiffAt_sqrt hne).comp
        (Work.Cyl.radial x, Work.Cyl.axial x) hsq
      simpa [Work.Cyl.rhoP, Function.comp_def] using h
    · -- `θ = arctan(z/r)`, with `r ≠ 0` at the point
      have hdiv : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / q.1)
          (Work.Cyl.radial x, Work.Cyl.axial x) :=
        ContDiffAt.div contDiffAt_snd contDiffAt_fst (ne_of_gt hx)
      have h := (Real.contDiff_arctan.contDiffAt).comp
        (Work.Cyl.radial x, Work.Cyl.axial x) hdiv
      simpa [Work.Cyl.thetaP, Function.comp_def] using h
  -- the model function `(a,b) ↦ a² Ψ(a^p, b)` is `C²` at `(ρ x, θ x)`
  have hG : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 * Ψ (q.1 ^ p) q.2)
      (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x),
        Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)) := by
    rw [hrho]
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2)
        (Work.Cyl.rho x, Work.Cyl.theta x) := by fun_prop
    have h2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ (q.1 ^ p) q.2)
        (Work.Cyl.rho x, Work.Cyl.theta x) := by
      have hpr : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ p)
          (Work.Cyl.rho x, Work.Cyl.theta x) :=
        (Real.contDiffAt_rpow_const (x := Work.Cyl.rho x) (n := 2)
          (Or.inl hrhone)).comp (Work.Cyl.rho x, Work.Cyl.theta x) contDiffAt_fst
      have h := hΨ.comp (Work.Cyl.rho x, Work.Cyl.theta x)
        (hpr.prodMk contDiffAt_snd)
      simpa [Function.comp_def, Function.uncurry] using h
    exact h1.mul h2
  -- assemble the composition
  rw [show (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2
        * Ψ (Work.Cyl.rhoP q.1 q.2 ^ p) (Work.Cyl.thetaP q.1 q.2))
      = (fun q : ℝ × ℝ => q.1 ^ 2 * Ψ (q.1 ^ p) q.2) ∘
        (fun q : ℝ × ℝ => (Work.Cyl.rhoP q.1 q.2, Work.Cyl.thetaP q.1 q.2)) from rfl]
  exact hG.comp (Work.Cyl.radial x, Work.Cyl.axial x) hpair

/-! ## The main statement -/

/-- **The vorticity of the polar-ansatz stream-function field, in the elliptic variables.**

For the stream function `ψ(r,z) = ρ(r,z)² Ψ(ρ(r,z)^p, θ(r,z))` of the self-similar variables
`R = ρ^p`, `θ`, the `ℝ³` vorticity of the no-swirl field `u = psiField ψ` is

  `∇ × u = -(LΨ) e_θ`,  `LΨ = bslOp p Ψ (ρ(x)^p) θ(x)`,

i.e. the elliptic operator of (PolarBSL) evaluated at the point `(ρ(x)^p, θ(x))` of the
self-similar half plane.  This is `Work.Cyl.vorticity_psiField` (the curl identity of (3dBSL)) fed
with `Work.Elliptic.cylOp_polar` (the polar change of variables (PolarBSL)); the polar ansatz is
`C²` off the axis by `Work.R1G.contDiffAt_rhoP_mul_rpow_comp`. -/
theorem vorticity_psiField_bslOp (p : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΨ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2)
      (Work.Cyl.rho x ^ p, Work.Cyl.theta x)) :
    FiniteTimeSingularity.vorticity
        (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
          * Ψ (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z))) x
      = -(Work.Elliptic.bslOp p Ψ (Work.Cyl.rho x ^ p) (Work.Cyl.theta x))
          • Work.Cyl.eTheta x := by
  have hρ : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) ^ p = Work.Cyl.rho x ^ p :=
    congrArg (· ^ p) (rhoP_radial_axial x)
  have hψ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (fun r z => Work.Cyl.rhoP r z ^ 2
        * Ψ (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z)) q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    contDiffAt_rhoP_mul_rpow_comp p Ψ x hx hΨ
  have hΨ' : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2)
      (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) ^ p,
        Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)) := by
    rw [hρ, thetaP_radial_axial x]; exact hΨ
  rw [Work.Cyl.vorticity_psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Ψ (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z)) x hψ hx,
    Work.Elliptic.cylOp_polar p Ψ (Work.Cyl.radial x) (Work.Cyl.axial x) hx hΨ',
    hρ, thetaP_radial_axial x]

end Work.R1G
end
