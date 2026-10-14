import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst
import Submission.Work.CoreResiduals.timeDeriv_ssVort_lam
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.BiotSavart
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
import Submission.Work.FTS.Physical.Meridian
import Submission.Work.FTS.Physical.Omega
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.LWP.VorticityAPI
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.Defs
import Submission.Work.Stability.PthFstarAdd
import Submission.Work.Stability.PzFstarAdd
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSIdent.Axi.contDiff_axiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C¹`-regularity of the no-swirl field `axiField a b`

The axisymmetric no-swirl field with reduced radial profile `a` and axial profile `b` is

  `axiField a b x = a (r², x₃) • (x₀, x₁, 0) + b (r², x₃) • e₃`,   `r² = x₀² + x₁²`, `x₃ = x 2`.

Since `x ↦ (r², x₃)` is a polynomial (hence smooth) map and `x ↦ (x₀, x₁, 0)`, `x ↦ e₃` are
linear, the field inherits the regularity of the profiles: if `a` and `b` are jointly `C¹`, so is
`axiField a b`.  Here we prove this in the form needed by the Biot--Savart identification
(`ContDiff ℝ 1`), by reducing to the three coordinates and using the product rule.

The two profile hypotheses are exactly `ContDiff ℝ 1 (Function.uncurry a)` and
`ContDiff ℝ 1 (Function.uncurry b)`, i.e. joint `C¹`-regularity of `(w, z) ↦ a w z`.

The coordinates of the field are

* `(axiField a b x) 0 = a (r², x₃) * x₀`,
* `(axiField a b x) 1 = a (r², x₃) * x₁`,
* `(axiField a b x) 2 = b (r², x₃)`,

which is what the proof checks via `contDiff_piLp`.
-/

namespace Work.FTS.BSIdent.Axi


end Work.FTS.BSIdent.Axi
end
-- ===== merged: Submission.Work.FTS.BSIdent.Curl.exists_mem_Uax_rho_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Curl

open scoped Real


end Work.FTS.BSIdent.Curl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.PhiOdd_neg_theta_of_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

/-- Oddness of `PhiOdd` in `θ`, with the vanishing hypothesis of `Φ` at `θ = 0` required only at
the positive point `w` at which the identity is evaluated.

This is `Work.FTS.BSIdent.PhiOdd_neg_theta` with a weakened hypothesis: the only case of the
case analysis in which `Φ` is evaluated at `θ = 0` is `θ = 0`, and there the first coordinate is
`w` (else `Φ` is evaluated at `±θ` with `θ ≠ 0`). -/
theorem PhiOdd_neg_theta_of_pos {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0) {w θ : ℝ} (hw : 0 < w) :
    Work.FTS.BSIdent.PhiOdd Φ w (-θ) τ = -Work.FTS.BSIdent.PhiOdd Φ w θ τ := by
  by_cases h : 0 ≤ θ
  · by_cases h' : 0 ≤ -θ
    · have hθ0 : θ = 0 := le_antisymm (by linarith) h
      subst hθ0
      simp [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl, h0 w hw]
    · rw [Work.FTS.BSIdent.PhiOdd_of_neg h', Work.FTS.BSIdent.PhiOdd_of_nonneg h, neg_neg]
  · have hpos : 0 ≤ -θ := by linarith
    rw [Work.FTS.BSIdent.PhiOdd_of_neg h, Work.FTS.BSIdent.PhiOdd_of_nonneg hpos, neg_neg]

end Work.FTS.BSIdent.Cyl.DecayAux
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_PhiOdd_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem abs_PhiOdd_le {Φ : Work.FTS.BSIdent.Fam} {τ C₀ q lam : ℝ} (hC₀ : 0 ≤ C₀)
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0)
    (hrate : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2) :
    |Work.FTS.BSIdent.PhiOdd Φ w θ τ| ≤ C₀ * (Real.pi / 2 - |θ|) ^ q * (1 + w) ^ (-lam) := by
  rcases lt_trichotomy θ 0 with hneg | hzero | hpos
  · rw [Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hneg), abs_neg, abs_of_neg hneg]
    exact hrate w (-θ) hw (neg_pos.mpr hneg) (by rw [abs_of_neg hneg] at hθ; exact hθ)
  · subst hzero
    rw [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl, h0 w hw, abs_zero]
    exact mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (by linarith [Real.pi_pos]) q))
      (le_of_lt (Real.rpow_pos_of_pos (by linarith) (-lam)))
  · rw [Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hpos), abs_of_pos hpos]
    exact hrate w θ hw hpos (by rwa [abs_of_pos hpos] at hθ)

end Work.FTS.BSIdent.Cyl.DecayAux
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.div_psiField_merPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The reconstructed velocity field is divergence free

`Work.Cyl.div_psiField` proves `div (psiField ψ) x = 0` at every point `x` off the axis at which
the stream function `ψ` is `C²`.  The hypotheses available for the design's meridian stream
function `merPsi` are weaker: we only know `ψ` is `C²` at the points `(r,z)` with `r > 0` and
`z ≠ 0` (and that the resulting field is globally `C¹`).

The set of points where that hypothesis fails — the axis `r = 0` together with the plane
`x₃ = 0` (the set `Work.FTS.BSIdent.Uaxᶜ`) — is a finite union of hyperplanes, hence has empty
interior: it is *dense* in `ℝ³` that the hypothesis holds (`dense_Uax` below).  Since
`ContDiff ℝ 1 u` makes `x ↦ div u x` continuous, the divergence — which vanishes on `Uax` —
vanishes on the closure of `Uax`, i.e. everywhere.  This is the content of
`div_psiField_merPsi`.
-/

set_option autoImplicit false

namespace Work.FTS.BSIdent.Cyl

/-! ## Continuity of the trace of a continuous linear endomorphism of `ℝ³` -/

/-- The trace, as a function of a continuous linear endomorphism of `ℝ³`, is continuous: it is a
linear map on the finite dimensional space `ℝ³ →L[ℝ] ℝ³`. -/
private theorem continuous_trace_clm :
    Continuous (fun L : Work.Cyl.R3 →L[ℝ] Work.Cyl.R3 => LinearMap.trace ℝ Work.Cyl.R3 L) := by
  let T : (Work.Cyl.R3 →L[ℝ] Work.Cyl.R3) →ₗ[ℝ] ℝ :=
    { toFun := fun L => LinearMap.trace ℝ Work.Cyl.R3 L
      map_add' := by intro L M; simp
      map_smul' := by intro c L; simp }
  exact LinearMap.continuous_of_finiteDimensional T

/-! ## Density of the coordinate hyperplane complements -/

/-- For each coordinate direction of `ℝ³`, the set of points with non-vanishing coordinate is
dense: from any point one reaches it by a displacement `(r/2) • e i` which does not undo the
coordinate unless the point is already exactly `-(r/2) • e i` on it — and in that case the point
itself already has a non-vanishing `i`-th coordinate. -/
private theorem dense_coord_ne_zero (i : Fin 3) : Dense {x : Work.Cyl.R3 | x i ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  rcases eq_or_ne (x i) 0 with hx | hx
  · refine ⟨x + (r / 2) • FiniteTimeSingularity.e i, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : x + (r / 2) • FiniteTimeSingularity.e i - x
          = (r / 2) • FiniteTimeSingularity.e i := by abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2),
        show ‖FiniteTimeSingularity.e i‖ = 1 from by simp [FiniteTimeSingularity.e]]
      linarith
    · show (x + (r / 2) • FiniteTimeSingularity.e i) i ≠ 0
      have h2 : (x + (r / 2) • FiniteTimeSingularity.e i) i = r / 2 := by
        simp [FiniteTimeSingularity.e, hx]
      rw [h2]; linarith
  · exact ⟨x, by simpa using hr, hx⟩

/-- The domain of the identification `Uax = {x₃ ≠ 0, x₀² + x₁² ≠ 0}` (the complement of the axis
and of the plane `x₃ = 0`) is dense in `ℝ³`: it contains the intersection of the two open dense
sets `{x₃ ≠ 0}` and `{x₀ ≠ 0}`. -/
private theorem dense_Uax : Dense (Work.FTS.BSIdent.Uax : Set Work.Cyl.R3) := by
  have h1 : Dense ({x : Work.Cyl.R3 | x 2 ≠ 0} : Set Work.Cyl.R3) := dense_coord_ne_zero 2
  have h2 : Dense ({x : Work.Cyl.R3 | x 0 ≠ 0} : Set Work.Cyl.R3) := dense_coord_ne_zero 0
  have h2' : Dense ({x : Work.Cyl.R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} : Set Work.Cyl.R3) :=
    Dense.mono (fun x hx => by
      intro hc
      have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      exact hx (sq_eq_zero_iff.mp h0)) h2
  have hopen : IsOpen ({x : Work.Cyl.R3 | x 2 ≠ 0} : Set Work.Cyl.R3) :=
    (isOpen_ne (x := (0 : ℝ))).preimage (by fun_prop)
  have hint := Dense.inter_of_isOpen_left h1 h2' hopen
  convert hint using 1
  ext x; simp [Work.FTS.BSIdent.Uax]

/-! ## The theorem -/

theorem div_psiField_merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ)
    (hC1 : ContDiff ℝ 1 (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)))
    (hsm : ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi α A B Φ C p.1 p.2 t) (r, z)) :
    FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) = 0 := by
  -- the divergence is continuous, being the trace of the (continuous) derivative of a `C¹` field
  have hcont : Continuous (fun x => FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x) := by
    show Continuous (fun x => (fderiv ℝ
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x).trace ℝ
        Work.Cyl.R3)
    exact continuous_trace_clm.comp (hC1.continuous_fderiv (by simp))
  -- it vanishes wherever the meridional slice of the stream function is `C²`
  have hvan : Set.EqOn (fun x => FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x)
      (fun _ => (0 : ℝ)) (Work.FTS.BSIdent.Uax) := by
    intro x hx
    exact Work.Cyl.div_psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t) x
      (hsm (Work.Cyl.radial x) (Work.Cyl.axial x)
        (Work.FTS.BSIdent.radial_pos_of_mem_Uax hx)
        (Work.FTS.BSIdent.axial_ne_zero_of_mem_Uax hx))
      (Work.FTS.BSIdent.radial_pos_of_mem_Uax hx)
  -- `Uax` is dense, so a continuous function vanishing on it vanishes everywhere
  funext x
  have hcl := Set.EqOn.closure hvan hcont continuous_const
  rw [dense_Uax.closure_eq] at hcl
  exact hcl (Set.mem_univ x)

end Work.FTS.BSIdent.Cyl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.psiField_r_mul_V_eq_axiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `V`-form of the stream function field `psiField`

The stream function `ψ(r,z) = r · V(r², z)` depends on the radial variable only through `r²`, so the
velocity field it generates is an `axiField` (a field whose radial profile is a function of `r²`).
This file computes that form:

  `psiField (fun r z => r * V (r^2) z)
     = axiField (fun w z => ∂_z V(w,z)) (fun w z => -2 V(w,z) - 2 w ∂_w V(w,z))`.

Concretely, `psiField ψ = cylField (∂_zψ) (-(ψ/r) - ∂_rψ)` and, by the product and chain rules,

* `∂_z ψ = r · ∂_z V(r²,·)`, so the radial component of the field is
  `∂_zψ/r = ∂_z V(r²,·)`, a function of `r²`;
* `∂_r ψ = V(r²,z) + 2r² ∂_wV(r²,z)` and `ψ/r = V(r²,z)`, so the axial component is
  `-2V(r²,z) - 2r² ∂_wV(r²,z)` — which is `b(r²,z)` for `b(w,z) = -2V(w,z) - 2w ∂_wV(w,z)`.

The hypothesis `V(0,z) = 0` is what makes the identity hold *on the axis* `r = 0`: there
`ψ(0,z) = 0` so the axial profile `ψ/r` contributes `0`, while the product rule gives
`∂_rψ(0,z) = V(0,z) = 0`; correspondingly `b(0,z) = -2V(0,z) - 0 = 0`.  Off the axis the identity
is a pure product/chain rule computation.
-/

noncomputable section

namespace Work.FTS.BSIdent.Cyl

/-! ## Differentiability of the slices of `V` -/






end Work.FTS.BSIdent.Cyl
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.sublinear_axiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl


end Work.FTS.BSIdent.Cyl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Defs.contDiffAt_Phi_of_merPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C²` regularity of the profile `Φ` from the `C²` regularity of `merPsi`

The meridian stream function of the reconstruction is

  `merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ), θ(r,z), τ)`,  `τ = clockInv C t`,

where `Φ̂ = PhiOdd Φ` is the odd extension in `θ`, `ρ(r,z) = √(r²+z²)` and `θ(r,z) = arctan(z/r)`.

On the branch `θ > 0` the odd extension is the identity, so *off* the degenerate set
`{r = 0} ∪ {z = 0}` the function `H(r,z) := Φ̂(ρ(r,z)^p/B(τ), θ(r,z), τ)` differs from `merPsi` only
by the explicit `C²` factor `ρ²·A(τ)⁻¹`, which is *nonzero* at a point with `ρ > 0` as soon as
`A(τ) ≠ 0`.  Hence the hypothesis that `merPsi` is `C²` off the degenerate set transfers to `H`.

The second ingredient is the *explicit local inverse* of the polar dictionary: the map

  `Q(w,θ) = ((w·B(τ))^{1/p}·cos θ, (w·B(τ))^{1/p}·sin θ)`

is `C^∞` at `(w,θ)` for `w > 0`, it maps `(w,θ)` to the point `(r₀,z₀)` with
`ρ(r₀,z₀) = (w·B(τ))^{1/p}` and `θ(r₀,z₀) = θ`, and near `(w,θ)` it satisfies
`ρ(Q(w,θ))^p/B(τ) = w`, `θ(Q(w,θ)) = θ`.  Composing `H` with `Q` therefore gives the `C²`-ness of
`(w,θ) ↦ Φ̂(w,θ,τ)` at `(w,θ)`, and on a neighbourhood of `(w,θ)` (where the second coordinate stays
in `(0, π/2)`) the odd extension agrees with `Φ`.  This is the inverse-function-theorem-free form of
the statement; the only hypothesis needed about `A` is `A(τ) ≠ 0` (without it `merPsi` is
identically zero, since `(0:ℝ)⁻¹ = 0` — see `NOTES_contDiffAt_Phi_of_contDiffAt_merPsi.md`).
-/

namespace Work.FTS.BSIdent.Defs

open scoped Topology

/-- Polar reconstruction: the meridian point with coordinates `(R cos Θ, R sin Θ)` has `ρ = R`
whenever `R > 0`. -/
private lemma rhoP_mul_cos_sin {R Θ : ℝ} (hR : 0 < R) :
    Work.Cyl.rhoP (R * Real.cos Θ) (R * Real.sin Θ) = R := by
  rw [Work.Cyl.rhoP]
  have h : (R * Real.cos Θ) ^ 2 + (R * Real.sin Θ) ^ 2 = R ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq Θ]
  rw [h, Real.sqrt_sq hR.le]

/-- Polar reconstruction: the meridian point with coordinates `(R cos Θ, R sin Θ)` has `θ = Θ`
whenever `R > 0` and `-(π/2) < Θ < π/2`. -/
private lemma thetaP_mul_cos_sin {R Θ : ℝ} (hR : 0 < R) (hΘ : -(Real.pi / 2) < Θ)
    (hΘ' : Θ < Real.pi / 2) :
    Work.Cyl.thetaP (R * Real.cos Θ) (R * Real.sin Θ) = Θ := by
  rw [Work.Cyl.thetaP]
  have htan : R * Real.sin Θ / (R * Real.cos Θ) = Real.tan Θ := by
    rw [Real.tan_eq_sin_div_cos, mul_div_mul_left _ _ hR.ne']
  rw [htan, Real.arctan_tan hΘ hΘ']

theorem contDiffAt_Phi_of_merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) (hα : 0 < α)
    (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hψ : ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi α A B Φ C p.1 p.2 t) (r, z))
    {w θ : ℝ} (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hp_pos : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hwB : 0 < w * B (Physical.clockInv C t) := mul_pos hw hB
  -- ### The preimage point `(r₀, z₀)` of `(w, θ)` under the polar dictionary
  set ρ₀ : ℝ := (w * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; exact Real.rpow_pos_of_pos hwB _
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  set r₀ : ℝ := ρ₀ * Real.cos θ with hr₀def
  set z₀ : ℝ := ρ₀ * Real.sin θ with hz₀def
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; exact mul_pos hρ₀pos hcos
  have hz₀ne : z₀ ≠ 0 := by rw [hz₀def]; exact ne_of_gt (mul_pos hρ₀pos hsin)
  have hrhoP : Work.Cyl.rhoP r₀ z₀ = ρ₀ := by
    rw [hr₀def, hz₀def]; exact rhoP_mul_cos_sin hρ₀pos
  have hthetaP : Work.Cyl.thetaP r₀ z₀ = θ := by
    rw [hr₀def, hz₀def]
    exact thetaP_mul_cos_sin hρ₀pos (by linarith) hθ2
  -- ### Step 1: the `C²`-ness of the odd extension, read off `hψ` by removing the explicit factor
  have hH : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP q.1 q.2) (Physical.clockInv C t)) (r₀, z₀) := by
    have hmer := hψ r₀ z₀ hr₀pos hz₀ne
    have hρc : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r₀, z₀) := by
      have h2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r₀, z₀) := by fun_prop
      have h3 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r₀, z₀) ≠ 0 := by
        show r₀ ^ 2 + z₀ ^ 2 ≠ 0
        positivity
      simpa [Work.Cyl.rhoP, Function.comp_def] using
        (Real.contDiffAt_sqrt (n := 2) h3).comp (r₀, z₀) h2
    have hfac : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Physical.clockInv C t))⁻¹)
        (r₀, z₀) :=
      (hρc.pow 2).mul contDiffAt_const
    have hne : Work.Cyl.rhoP r₀ z₀ ^ 2 * (A (Physical.clockInv C t))⁻¹ ≠ 0 := by
      rw [hrhoP]
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hρ₀pos)) (inv_ne_zero hA)
    refine (hmer.div hfac hne).congr_of_eventuallyEq ?_
    have hnb : ∀ᶠ q : ℝ × ℝ in 𝓝 (r₀, z₀),
        Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Physical.clockInv C t))⁻¹ ≠ 0 :=
      hfac.continuousAt.eventually_ne hne
    filter_upwards [hnb] with q hq
    simp only [Pi.div_apply]
    rw [Work.FTS.BSIdent.merPsi_apply]
    exact (mul_div_cancel_left₀ _ hq).symm
  -- ### Step 2: the explicit local inverse `Q` of the polar dictionary is `C²` at `(w, θ)`
  have hbase : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 * B (Physical.clockInv C t)) (w, θ) := by
    fun_prop
  have hpow : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α))
      (w, θ) :=
    hbase.rpow_const_of_ne (by simpa using hwB.ne')
  have hQ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.cos q.2,
       (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.sin q.2))
      (w, θ) := by
    have hc : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.cos q.2) (w, θ) := by fun_prop
    have hs : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.sin q.2) (w, θ) := by fun_prop
    exact (hpow.mul hc).prodMk (hpow.mul hs)
  have hcomp := hH.comp (w, θ) hQ
  -- ### Step 3: `Q` inverts the polar dictionary near `(w, θ)`, hence the composite is `Φ̂`
  have hPhiOdd : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ q.1 q.2 (Physical.clockInv C t)) (w, θ) := by
    refine hcomp.congr_of_eventuallyEq ?_
    have hpos_nb : ∀ᶠ q : ℝ × ℝ in 𝓝 (w, θ), 0 < q.1 * B (Physical.clockInv C t) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => q.1 * B (Physical.clockInv C t)) (w, θ) := by
        fun_prop
      exact hcont.eventually (isOpen_Ioi.mem_nhds hwB)
    have hth_nb : ∀ᶠ q : ℝ × ℝ in 𝓝 (w, θ),
        -(Real.pi / 2) < q.2 ∧ q.2 < Real.pi / 2 := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => q.2) (w, θ) := continuousAt_snd
      exact (hcont.eventually
          (isOpen_Ioi.mem_nhds (by change -(Real.pi / 2) < θ; linarith))).and
        (hcont.eventually (isOpen_Iio.mem_nhds hθ2))
    filter_upwards [hpos_nb, hth_nb] with q hq hqth
    simp only [Function.comp_apply]
    have hRpos : 0 < (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) :=
      Real.rpow_pos_of_pos hq _
    have h1 : Work.Cyl.rhoP
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.cos q.2)
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.sin q.2)
        = (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) :=
      rhoP_mul_cos_sin hRpos
    have h2 : Work.Cyl.thetaP
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.cos q.2)
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.sin q.2)
        = q.2 :=
      thetaP_mul_cos_sin hRpos hqth.1 hqth.2
    have h3 : ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α))
          ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) = q.1 := by
      rw [← Real.rpow_mul (le_of_lt hq), one_div_mul_cancel hp_pos.ne', Real.rpow_one]
      exact mul_div_cancel_right₀ q.1 hB.ne'
    rw [h1, h3, h2]
  -- ### Step 4: near `(w, θ)` the second coordinate is positive, i.e. `Φ̂ = Φ`
  refine hPhiOdd.congr_of_eventuallyEq ?_
  have hth_nb : ∀ᶠ q : ℝ × ℝ in 𝓝 (w, θ), 0 < q.2 := by
    have hcont : ContinuousAt (fun q : ℝ × ℝ => q.2) (w, θ) := continuousAt_snd
    exact hcont.eventually (isOpen_Ioi.mem_nhds (by change 0 < θ; exact hθ))
  filter_upwards [hth_nb] with q hq
  exact (Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hq)).symm

end Work.FTS.BSIdent.Defs
end
-- ===== merged: Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C²` regularity of the meridian slice of `merPsi`

`merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ), θ(r,z), τ)`, `τ = clockInv C t`,
where `Φ̂ = PhiOdd Φ` is the odd extension in `θ` and `θ(r,z) = arctan(z/r)`.

Off the degenerate set `r > 0`, `z ≠ 0` the point `(r,z)` sees the *interior* of one of the two
branches of the odd extension: `θ(r,z) ≠ 0` (because `z ≠ 0`, `r > 0`), and by continuity the sign
of `θ` is constant on a neighbourhood of `(r,z)`.  On that neighbourhood `Φ̂` agrees with either
`Φ` (branch `θ > 0`) or the smooth reflection `(w,θ) ↦ -Φ(w,-θ)` (branch `θ < 0`), so the
hypothesis `hsm` — the `C²`-ness of `Φ(·,·,τ)` on the open quadrant — applies.

The lemma is the `hsm2` hypothesis of `Work.FTS.BSIdent.hid`; it is a purely analytic
(non-elliptic) statement about the polar dictionary.
-/

open scoped Topology

namespace Work.FTS.BSIdent.Defs

theorem contDiffAt_merPsi_slice (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ)
    (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi α A B Φ C p.1 p.2 t) (r, z) := by
  set τ := Physical.clockInv C t with hτ
  -- ### Step 1: the polar dictionary `ρ`, `ρ^p/B(τ)`, `θ` is `C²` in `(r,z)`
  have hρ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) := by fun_prop
    have h2 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) ≠ 0 := by
      show r ^ 2 + z ^ 2 ≠ 0
      positivity
    have h3 := (Real.contDiffAt_sqrt (n := 2) h2).comp (r, z) h1
    simpa [Work.Cyl.rhoP, Function.comp_def] using h3
  have hρp : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ) (r, z) := by
    have h4 := hρ.rpow_const_of_ne (p := Work.FTS.Regularity.pExp α)
      (Work.Cyl.rhoP_ne_zero hr z)
    simpa [div_eq_mul_inv] using
      h4.mul (contDiffAt_const (c := (B τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (B τ)⁻¹) (r, z))
  have hθ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / q.1) (r, z) := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa using hr.ne'
    have h3 := Real.contDiff_arctan.contDiffAt.comp (r, z) h1
    simpa [Work.Cyl.thetaP, Function.comp_def] using h3
  -- ### Step 2: the self-similar argument is positive, and `θ(r,z) ≠ 0`
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  have hθ0 : Work.Cyl.thetaP r z ≠ 0 := by
    simp only [Work.Cyl.thetaP]
    exact fun h => (div_ne_zero hz hr.ne') (Real.arctan_eq_zero_iff.mp h)
  rcases lt_or_gt_of_ne hθ0 with hneg | hpos
  · -- ### Step 3a: the branch `θ < 0`, i.e. `Φ̂ = -Φ(w,-θ)`
    have hpos' : 0 < -Work.Cyl.thetaP r z := by linarith
    have hlt' : -Work.Cyl.thetaP r z < Real.pi / 2 := by
      have h := Real.neg_pi_div_two_lt_arctan (z / r)
      simp only [Work.Cyl.thetaP]
      linarith
    have hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, -Work.Cyl.thetaP r z) :=
      hsm _ _ hw hpos' hlt'
    have hnegθ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => -Work.Cyl.thetaP q.1 q.2) (r, z) := hθ.neg
    have hcomp := hΦ.comp (r, z) (hρp.prodMk hnegθ)
    have hc : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (-(Work.Cyl.thetaP q.1 q.2)) τ) (r, z) := by
      simpa [Function.comp_def] using hcomp
    have hfinal : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => (A τ)⁻¹ * (-Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (-(Work.Cyl.thetaP q.1 q.2)) τ)) (r, z) :=
      (contDiffAt_const (c := (A τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (A τ)⁻¹) (r, z)).mul
        hc.neg
    have hprod : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2 *
          ((A τ)⁻¹ * (-Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (-(Work.Cyl.thetaP q.1 q.2)) τ))) (r, z) :=
      (hρ.pow 2).mul hfinal
    refine hprod.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | Work.Cyl.thetaP q.1 q.2 < 0} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hnb] with q hq
    rw [Work.FTS.BSIdent.merPsi_apply, Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hq)]
    ring
  · -- ### Step 3b: the branch `θ > 0`, i.e. `Φ̂ = Φ(w,θ)`
    have hlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
      simpa only [Work.Cyl.thetaP] using Real.arctan_lt_pi_div_two (z / r)
    have hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, Work.Cyl.thetaP r z) :=
      hsm _ _ hw hpos hlt
    have hcomp := hΦ.comp (r, z) (hρp.prodMk hθ)
    have hc : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP q.1 q.2) τ) (r, z) := by
      simpa [Function.comp_def] using hcomp
    have hfinal : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => (A τ)⁻¹ * Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
          (Work.Cyl.thetaP q.1 q.2) τ) (r, z) :=
      (contDiffAt_const (c := (A τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (A τ)⁻¹) (r, z)).mul hc
    have hprod : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2 *
          ((A τ)⁻¹ * Φ (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP q.1 q.2) τ)) (r, z) :=
      (hρ.pow 2).mul hfinal
    refine hprod.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | 0 < Work.Cyl.thetaP q.1 q.2} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hnb] with q hq
    rw [Work.FTS.BSIdent.merPsi_apply, Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hq)]
    ring

end Work.FTS.BSIdent.Defs
end
-- ===== merged: Submission.Work.FTS.BSIdent.Defs.dense_Uax =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Denseness of the domain `Uax` of the Biot–Savart identification

`Uax = {x₃ ≠ 0, x₀² + x₁² ≠ 0}` is the complement of the axis `r = 0` and of the plane `x₃ = 0`,
i.e. of a finite union of hyperplanes of `ℝ³`.  Its complement therefore has empty interior, so
`Uax` is dense: every point of `ℝ³` can be pushed into `Uax` by an arbitrarily small displacement.

Concretely, `{x₂ ≠ 0}` is dense (a point with `x₂ = 0` is moved to `x + (r/2) e₂`, whose second
coordinate is `r/2 ≠ 0`), and `{x₀² + x₁² ≠ 0}` contains the dense set `{x₀ ≠ 0}`.  Both sets are
open, so their intersection — which is `Uax` — is dense.
-/

set_option autoImplicit false

namespace Work.FTS.BSIdent.Defs

/-- Every coordinate hyperplane complement in `ℝ³` is dense: from a point whose `i`-th coordinate
vanishes one reaches the complement by the displacement `(r/2) • eᵢ`. -/
private theorem dense_coord_ne_zero (i : Fin 3) :
    Dense {x : EuclideanSpace ℝ (Fin 3) | x i ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  rcases eq_or_ne (x i) 0 with hx | hx
  · refine ⟨x + (r / 2) • FiniteTimeSingularity.e i, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : x + (r / 2) • FiniteTimeSingularity.e i - x
          = (r / 2) • FiniteTimeSingularity.e i := by abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2),
        show ‖FiniteTimeSingularity.e i‖ = 1 from by simp [FiniteTimeSingularity.e]]
      linarith
    · show (x + (r / 2) • FiniteTimeSingularity.e i) i ≠ 0
      have h2 : (x + (r / 2) • FiniteTimeSingularity.e i) i = r / 2 := by
        simp [FiniteTimeSingularity.e, hx]
      rw [h2]; linarith
  · exact ⟨x, by simpa using hr, hx⟩

/-- **`Uax` is dense in `ℝ³`.**  It is the intersection of the two open dense sets `{x₃ ≠ 0}` and
`{x₀² + x₁² ≠ 0}`. -/
theorem dense_Uax : Dense (Work.FTS.BSIdent.Uax : Set Work.FTS.BSIdent.R3) := by
  have h1 : Dense ({x : Work.FTS.BSIdent.R3 | x 2 ≠ 0} : Set Work.FTS.BSIdent.R3) :=
    dense_coord_ne_zero 2
  have h2 : Dense ({x : Work.FTS.BSIdent.R3 | x 0 ≠ 0} : Set Work.FTS.BSIdent.R3) :=
    dense_coord_ne_zero 0
  have h2' : Dense ({x : Work.FTS.BSIdent.R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} :
      Set Work.FTS.BSIdent.R3) :=
    Dense.mono (fun x hx => by
      intro hc
      have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      exact hx (sq_eq_zero_iff.mp h0)) h2
  have hopen : IsOpen ({x : Work.FTS.BSIdent.R3 | x 2 ≠ 0} : Set Work.FTS.BSIdent.R3) :=
    (isOpen_ne (x := (0 : ℝ))).preimage (by fun_prop)
  have hint := Dense.inter_of_isOpen_left h1 h2' hopen
  convert hint using 1
  ext x; simp [Work.FTS.BSIdent.Uax, and_comm]

end Work.FTS.BSIdent.Defs
end
-- ===== merged: Submission.Work.FTS.BSIdent.Liouville.biotSavart_congr_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Liouville

theorem biotSavart_congr_ae {ω ω' : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (h : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure Work.FTS.BSIdent.R3), ω y = ω' y)
    (x : Work.FTS.BSIdent.R3) :
    Work.LWP.biotSavart ω x = Work.LWP.biotSavart ω' x := by
  unfold Work.LWP.biotSavart
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

end Work.FTS.BSIdent.Liouville
end
-- ===== merged: Submission.Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff`

A `C¹` vector field on `ℝ³` has continuous curl (vorticity).  Indeed

  `vorticity u x = ∑ i, eᵢ × (Du(x) eᵢ)`

is a fixed *continuous* (indeed linear) function of the Fréchet derivative `Du(x)`, and `Du` is
continuous as soon as `u` is `C¹` (`ContDiff.continuous_fderiv`).  So the continuity of
`vorticity u` reduces to the continuity of the three elementary operations: evaluation of a
continuous linear map, the cross product on `Fin 3 → ℝ`, the finite sum, and of the linear
identification `WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³` — which is exactly the decomposition that
`fun_prop` discharges.

This is the `C^{1,0}` half of the regularity of the vorticity field used by the
Liouville-type/Biot–Savart part of the chapter: it yields `ContinuousOn` statements about
`(x,t) ↦ vorticity (u · t) x` (via `Continuous.continuousOn` and `continuous_apply`).
-/

open FiniteTimeSingularity
open scoped Topology Matrix

namespace Work.FTS.BSIdent.Liouville

/-- **The vorticity of a `C¹` field is continuous.**  `vorticity u x = curl (Du(x))` is a
continuous function of the derivative `Du(x)`, and `fderiv ℝ u` is continuous when `u` is `C¹`. -/
theorem continuous_vorticity_of_contDiff {u : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hu : ContDiff ℝ 1 u) :
    Continuous (FiniteTimeSingularity.vorticity u) := by
  -- `vorticity u x = ∑ᵢ eᵢ × (Du(x) eᵢ)` is a continuous function of `Du(x)`.
  have hf : Continuous (fun x => fderiv ℝ u x) := hu.continuous_fderiv (by norm_num)
  unfold FiniteTimeSingularity.vorticity
  fun_prop

end Work.FTS.BSIdent.Liouville
end
-- ===== merged: Submission.Work.FTS.BSIdent.OddExt.bslOp_PhiOdd_of_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `bslOp` of the odd extension in `θ`, at `θ < 0`

For `θ < 0` the odd extension `PhiOdd Φ` is in its reflected branch, `PhiOdd Φ z' θ' τ =
-Φ z' (-θ') τ`, and the elliptic operator `bslOp p` is *odd* under that reflection:

`bslOp p (PhiOdd Φ · · τ) z θ = -(bslOp p (Φ · · τ) z (-θ))`.

The whole content is that the reflection `θ' ↦ -θ'` turns each `θ`-derivative into the
corresponding derivative at `-θ` with the sign dictated by parity — `deriv_comp_neg`,
`deriv (fun t => f (-t)) x = -deriv f (-x)`, which holds *unconditionally* because `deriv` is a
total function.  Consequently

* `pz`, `pzIter 2`, `Ψ` itself and `-6Ψ` are all *odd* (the reflection fixes `z`),
* `pthIter 2` is odd (`∂_θ` of an odd slice is even, `∂_θθ` is odd again),
* `tan θ · Ψ` is *even*, so `∂_θ(tan θ · Ψ)` is odd,

and `bslOp` is built out of these; see `bslOp_of_odd_slice` below for the general statement.
Because `deriv` is total, no differentiability hypothesis is needed for the identity itself (the
hypothesis `hΦ` of the target statement is then unused).

Everything here is a pure `deriv` bookkeeping computation: the only tools are
`Filter.EventuallyEq.deriv_eq` (to replace a slice by its reflection on a neighbourhood) and
`deriv_comp_neg`.
-/

namespace Work.FTS.BSIdent.OddExt

open Set

/-- If two functions agree on the open half-line `θ < 0`, then so do their derivatives, at
every point of that half-line.  (Used to transfer a *pointwise* slice identity into an identity
of derivatives: the set `Iio 0` is open, hence a neighbourhood of each of its points.) -/
private theorem deriv_eq_of_eqOn_Iio {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Iio 0)) {x : ℝ}
    (hx : x < 0) : deriv f x = deriv g x :=
  (Set.EqOn.eventuallyEq_of_mem h (isOpen_Iio.mem_nhds hx)).deriv_eq

/-- **The reflection principle for `bslOp`.**  If `Ψ` is the odd reflection in `θ` of `Φs` on
the open half-line `θ' < 0`, i.e. `Ψ z θ' = -Φs z (-θ')` for all `z` and all `θ' < 0`, then for
every `θ < 0`

`bslOp p Ψ z θ = -(bslOp p Φs z (-θ))`.

No regularity hypotheses: `deriv` is total and `deriv_comp_neg` is unconditional. -/
theorem bslOp_of_odd_slice {p : ℝ} {Ψ Φs : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hrel : ∀ z' θ', θ' < 0 → Ψ z' θ' = -Φs z' (-θ')) (hθ : θ < 0) :
    Work.Elliptic.bslOp p Ψ z θ = -(Work.Elliptic.bslOp p Φs z (-θ)) := by
  -- the values
  have h1 : Ψ z θ = -Φs z (-θ) := hrel z θ hθ
  -- `∂_z` is odd (the reflection acts on the second variable only)
  have h2 : Work.Spaces.pz Ψ z θ = -(Work.Spaces.pz Φs z (-θ)) := by
    have hfun : (fun ζ => Ψ ζ θ) = fun ζ => -(Φs ζ (-θ)) := funext fun ζ => hrel ζ θ hθ
    simp only [Work.Spaces.pz]
    rw [hfun]
    simp
  -- `∂_z∂_z` is odd for the same reason
  have h3 : Work.Spaces.pzIter 2 Ψ z θ = -(Work.Spaces.pzIter 2 Φs z (-θ)) := by
    have hpzf : (fun ζ => Work.Spaces.pz Ψ ζ θ) = fun ζ => -(Work.Spaces.pz Φs ζ (-θ)) := by
      funext ζ
      have hfun : (fun ζ' => Ψ ζ' θ) = fun ζ' => -(Φs ζ' (-θ)) := funext fun ζ' => hrel ζ' θ hθ
      simp only [Work.Spaces.pz]
      rw [hfun]
      simp
    calc Work.Spaces.pzIter 2 Ψ z θ = deriv (fun ζ => Work.Spaces.pz Ψ ζ θ) z := rfl
      _ = deriv (fun ζ => -(Work.Spaces.pz Φs ζ (-θ))) z := by rw [hpzf]
      _ = -deriv (fun ζ => Work.Spaces.pz Φs ζ (-θ)) z := by simp
      _ = -(Work.Spaces.pzIter 2 Φs z (-θ)) := rfl
  -- `∂_θθ` is odd: the reflected slice is `s ↦ -(Φs z (-s))`, whose derivative at `s` is the
  -- derivative of the slice of `Φs` at `-s`, so one more differentiation flips the sign
  have h4 : Work.Spaces.pthIter 2 Ψ z θ = -(Work.Spaces.pthIter 2 Φs z (-θ)) := by
    have hE1 : Set.EqOn (fun t => deriv (fun u => Ψ z u) t)
        (fun t => deriv (fun u => -(Φs z (-u))) t) (Set.Iio 0) :=
      fun t ht => deriv_eq_of_eqOn_Iio (fun u hu => hrel z u hu) ht
    have step1 : deriv (fun t => deriv (fun u => Ψ z u) t) θ
        = deriv (fun t => deriv (fun u => -(Φs z (-u))) t) θ :=
      deriv_eq_of_eqOn_Iio hE1 hθ
    have hpt : ∀ t, deriv (fun u => -(Φs z (-u))) t = deriv (fun u => Φs z u) (-t) := by
      intro t
      simpa using deriv_comp_neg (fun u => -(Φs z u)) t
    calc Work.Spaces.pthIter 2 Ψ z θ
        = deriv (fun t => deriv (fun u => Ψ z u) t) θ := rfl
      _ = deriv (fun t => deriv (fun u => -(Φs z (-u))) t) θ := step1
      _ = deriv (fun t => deriv (fun u => Φs z u) (-t)) θ := by simp only [hpt]
      _ = -deriv (fun t => deriv (fun u => Φs z u) t) (-θ) := deriv_comp_neg _ θ
      _ = -(Work.Spaces.pthIter 2 Φs z (-θ)) := rfl
  -- `θ' ↦ tan θ' · Ψ z θ'` is *even* (`tan` is odd and the slice is odd), hence its derivative
  -- is odd
  have h5 : Work.Spaces.pth (fun z' θ' => Real.tan θ' * Ψ z' θ') z θ
      = -(Work.Spaces.pth (fun z' θ' => Real.tan θ' * Φs z' θ') z (-θ)) := by
    have hEqT : Set.EqOn (fun t => Real.tan t * Ψ z t) (fun t => Real.tan (-t) * Φs z (-t))
        (Set.Iio 0) := by
      intro t ht
      show Real.tan t * Ψ z t = Real.tan (-t) * Φs z (-t)
      rw [hrel z t ht, Real.tan_neg]
      ring
    calc Work.Spaces.pth (fun z' θ' => Real.tan θ' * Ψ z' θ') z θ
        = deriv (fun t => Real.tan t * Ψ z t) θ := rfl
      _ = deriv (fun t => Real.tan (-t) * Φs z (-t)) θ := deriv_eq_of_eqOn_Iio hEqT hθ
      _ = -deriv (fun t => Real.tan t * Φs z t) (-θ) :=
            deriv_comp_neg (fun t => Real.tan t * Φs z t) θ
      _ = -(Work.Spaces.pth (fun z' θ' => Real.tan θ' * Φs z' θ') z (-θ)) := rfl
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, h1, h2, h3, h4, h5]
  ring

set_option linter.unusedVariables false in
/-- **`bslOp` of the odd extension at `θ < 0`.**  The reflected branch of `PhiOdd` is
`θ' ↦ -Φ z (-θ') τ` on all of `θ' < 0`, so `bslOp_of_odd_slice` applies verbatim. -/
theorem bslOp_PhiOdd_of_neg {p : ℝ} {Φ : Work.FTS.BSIdent.Fam} {z θ τ : ℝ} (hθ : θ < 0)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, -θ)) :
    Work.Elliptic.bslOp p (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = -(Work.Elliptic.bslOp p (fun z' θ' => Φ z' θ' τ) z (-θ)) := by
  refine bslOp_of_odd_slice (Ψ := fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ)
    (Φs := fun z' θ' => Φ z' θ' τ) ?_ hθ
  intro z' θ' hθ'
  exact Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ')

end Work.FTS.BSIdent.OddExt
end
-- ===== merged: Submission.Work.FTS.BSIdent.OddExt.bslOp_PhiOdd_of_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The odd extension in `θ` does not change `bslOp` for `θ > 0`

The odd extension `PhiOdd Φ` of a self-similar family `Φ` agrees with `Φ` on the whole open
half-plane `θ > 0`.  Since `bslOp` is built from the partial derivatives `pz`, `pzIter 2`, `pth`
and `pthIter 2` — each of which is a *derivative in one variable at a fixed value of the other*,
hence depends only on the germ of the corresponding slice — the value of `bslOp` at a point
`(z,θ)` with `θ > 0` is unchanged by passing to the odd extension.

The proof is therefore pure germ bookkeeping:

* the `z`-slices at the fixed angle `θ > 0` are *equal as functions* (not merely eventually
  equal), so `pz` and `pzIter 2` agree;
* the `θ`-slices are equal on the open set `θ' > 0`, hence eventually equal near `θ`; this gives
  `pth` and, applied at every `θ' > 0`, also `pthIter 2` (via `Filter.EventuallyEq.deriv_eq`).

No differentiability hypothesis on `Φ` is needed: `deriv` is a total function and the two
functions being differentiated have the same germ.
-/

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.BSIdent.OddExt

variable {Φ : Work.FTS.BSIdent.Fam}

/-- For `θ > 0` the odd extension takes the value of the original family. -/
theorem PhiOdd_eq_self_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.FTS.BSIdent.PhiOdd Φ z θ τ = Φ z θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hθ)

/-- The `θ`-slices of `PhiOdd Φ` and of `Φ` agree eventually near every `θ > 0`. -/
theorem PhiOdd_eventuallyEq_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    (fun θ' => Work.FTS.BSIdent.PhiOdd Φ z θ' τ) =ᶠ[𝓝 θ] fun θ' => Φ z θ' τ :=
  (eventually_gt_nhds hθ).mono fun _ h' => PhiOdd_eq_self_of_pos (Φ := Φ) h'

/-- `∂_z` of the odd extension at `θ > 0`. -/
theorem pz_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pz (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pz (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => Work.FTS.BSIdent.PhiOdd Φ z' θ τ) = fun z' => Φ z' θ τ from
    funext fun z' => PhiOdd_eq_self_of_pos (Φ := Φ) hθ]

/-- `∂_z^2` of the odd extension at `θ > 0`. -/
theorem pzIter_two_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pzIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pzIter 2 (fun z' θ' => Φ z' θ' τ) z θ := by
  show deriv (fun z' => deriv (fun z'' => Work.FTS.BSIdent.PhiOdd Φ z'' θ τ) z') z
      = deriv (fun z' => deriv (fun z'' => Φ z'' θ τ) z') z
  rw [show (fun z' => deriv (fun z'' => Work.FTS.BSIdent.PhiOdd Φ z'' θ τ) z')
      = fun z' => deriv (fun z'' => Φ z'' θ τ) z' from
    funext fun z' => pz_PhiOdd_of_pos (Φ := Φ) (z := z') hθ]

/-- `∂_θ` of the odd extension at `θ > 0`. -/
theorem pth_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pth (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pth (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Spaces.pth]
  exact (PhiOdd_eventuallyEq_of_pos (Φ := Φ) (z := z) hθ).deriv_eq

/-- `∂_θ^2` of the odd extension at `θ > 0`. -/
theorem pthIter_two_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pthIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pthIter 2 (fun z' θ' => Φ z' θ' τ) z θ := by
  show deriv (fun θ' => Work.Spaces.pth
        (fun z' θ'' => Work.FTS.BSIdent.PhiOdd Φ z' θ'' τ) z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (fun z' θ'' => Φ z' θ'' τ) z θ') θ
  refine (Filter.EventuallyEq.deriv_eq ?_)
  exact (eventually_gt_nhds hθ).mono fun _ h' => pth_PhiOdd_of_pos (Φ := Φ) (z := z) h'

/-- `∂_θ(tan θ · ·)` of the odd extension at `θ > 0`. -/
theorem pth_tan_mul_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pth (fun z' θ' => Real.tan θ' * Φ z' θ' τ) z θ := by
  simp only [Work.Spaces.pth]
  refine (Filter.EventuallyEq.deriv_eq ?_)
  exact Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun θ' : ℝ => Real.tan θ'))
    (PhiOdd_eventuallyEq_of_pos (Φ := Φ) (z := z) hθ)

/-- `Lzero` of the odd extension at `θ > 0`. -/
theorem Lzero_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Elliptic.Lzero (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Elliptic.Lzero (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Elliptic.Lzero, pthIter_two_PhiOdd_of_pos (Φ := Φ) hθ,
    pth_tan_mul_PhiOdd_of_pos (Φ := Φ) hθ, PhiOdd_eq_self_of_pos (Φ := Φ) hθ]

theorem bslOp_PhiOdd_of_pos {p : ℝ} {Φ : Work.FTS.BSIdent.Fam} {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Elliptic.bslOp p (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Elliptic.bslOp p (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Elliptic.bslOp_apply, pzIter_two_PhiOdd_of_pos (Φ := Φ) hθ,
    pz_PhiOdd_of_pos (Φ := Φ) hθ, Lzero_PhiOdd_of_pos (Φ := Φ) hθ]

end Work.FTS.BSIdent.OddExt
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.OddExt.bslOp_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.OddExt

/-!
# Homogeneity of the elliptic operator `bslOp` under multiplication by a constant

`Work.Elliptic.bslOp p Ψ = -p²z²∂_zzΨ - p(5+p)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` is a linear differential operator, whence
`bslOp p (c · Ψ) = c · bslOp p Ψ` pointwise.  No differentiability hypothesis is needed:
Mathlib's `deriv` is totalised, but it still commutes with multiplication by a constant
*unconditionally* (`deriv_const_mul_field`), because at a non-differentiable point both sides
vanish.

The only work is to transfer that homogeneity to the iterated operators `pzIter 2`, `pz`,
`pthIter 2` and to the `tan θ · ·` slot of `L₀` (which needs the pointwise reassociation
`tan θ · (c · Ψ) = c · (tan θ · Ψ)`).
-/

/-! ## Homogeneity of the individual derivatives (pointwise) -/

private lemma pz_cm_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) z θ = c * Work.Spaces.pz f z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field c

private lemma pth_cm_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) z θ = c * Work.Spaces.pth f z θ := by
  rw [Work.Spaces.pth, Work.Spaces.pth]
  exact deriv_const_mul_field c

private lemma pzIter_cm_apply (c : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter n (fun z θ => c * f z θ) z θ = c * Work.Spaces.pzIter n f z θ := by
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ]
      have heq : Work.Spaces.pzIter k (fun z θ => c * f z θ)
          = fun z θ => c * Work.Spaces.pzIter k f z θ := funext fun z => funext fun θ => ih z θ
      rw [heq, pz_cm_apply, Work.Spaces.pzIter_succ]

private lemma pthIter_cm_apply (c : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter n (fun z θ => c * f z θ) z θ = c * Work.Spaces.pthIter n f z θ := by
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ]
      have heq : Work.Spaces.pthIter k (fun z θ => c * f z θ)
          = fun z θ => c * Work.Spaces.pthIter k f z θ := funext fun z => funext fun θ => ih z θ
      rw [heq, pth_cm_apply, Work.Spaces.pthIter_succ]

/-- The `tan θ · ·` slot of `L₀` commutes with a constant, after the reassociation
`tan θ · (c · Ψ) = c · (tan θ · Ψ)` of the differentiated function. -/
private lemma pth_tan_cm_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * (c * f z' θ')) z θ
      = c * Work.Spaces.pth (fun z' θ' => Real.tan θ' * f z' θ') z θ := by
  rw [Work.Spaces.pth, Work.Spaces.pth]
  rw [show (fun θ' => Real.tan θ' * (c * f z θ')) = (fun θ' => c * (Real.tan θ' * f z θ'))
      from funext fun θ' => by ring]
  exact deriv_const_mul_field c

/-! ## Homogeneity of `bslOp` -/

theorem bslOp_const_mul (p c : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp p (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Elliptic.bslOp p Ψ z θ := by
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
  rw [pzIter_cm_apply c 2 Ψ z θ, pz_cm_apply c Ψ z θ, pth_tan_cm_apply c Ψ z θ,
    pthIter_cm_apply c 2 Ψ z θ]
  ring

end Work.FTS.BSIdent.OddExt
end
-- ===== merged: Submission.Work.FTS.BSIdent.OddExt.pthIter_PhiOdd_of_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.OddExt

open Filter
open scoped Topology

/-! ## Derivatives of the odd extension at a negative point

Write `H s = if 0 ≤ s then G s else -G (-s)` for the odd extension of a one-variable function `G`.
At a point `θ < 0` one has, as long as `G` is smooth enough at `-θ`,

  `H'(θ) = G'(-θ)`,   `H''(θ) = -G''(-θ)`.

The two lemmas below are the formal versions of these identities (everything is expressed directly
in terms of `deriv`, so that they apply to `Work.Spaces.pthIter`, which is an iterated `deriv`). -/




end Work.FTS.BSIdent.OddExt
end
-- ===== merged: Submission.Work.FTS.BSIdent.OddExt.pzIter_PhiOdd_of_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_z²` of the odd extension in `θ`, at `θ < 0`

For `θ < 0` the odd extension `PhiOdd Φ` is in its reflected branch,
`PhiOdd Φ z' θ' τ = -Φ z' (-θ') τ`, and the reflection `θ' ↦ -θ'` *fixes* `z`.  Hence the
`z`-slices of the two families are *equal as functions*, and every `z`-derivative picks up
exactly one sign:

`∂_z^k (PhiOdd Φ · · τ) z θ = -(∂_z^k (Φ · · τ) z (-θ))`.

Only the case `k = 2` is recorded here (`k = 0` is `PhiOdd_of_neg` itself, `k = 1` is the
sibling identity used in `bslOp_PhiOdd_of_neg`).  Since `deriv` is a total function and the two
slices agree *everywhere* (not merely on a germ), no regularity hypothesis on `Φ` is needed.
-/

namespace Work.FTS.BSIdent.OddExt


end Work.FTS.BSIdent.OddExt
end
-- ===== merged: Submission.Work.FTS.BSIdent.Parity.isOdd_physVel_neg_physOmega =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Parity

open Work.FTS.Regularity


end Work.FTS.BSIdent.Parity
end
-- ===== merged: Submission.Work.FTS.BSIdent.Parity.isOdd_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Parity

/-!
# Parity (`FiniteTimeSingularity.IsOdd`) is preserved by subtraction

`FiniteTimeSingularity.IsOdd u` says that for each `i` the component `uᵢ` is an odd function of
the `i`-th coordinate and an even function of the other two coordinates.  Since
`R3 = EuclideanSpace ℝ (Fin 3)` is definitionally `Fin 3 → ℝ`, both the pointwise subtraction of
vector fields and the extraction of a component are (definitionally) pointwise, so the statement
reduces to the two elementary facts that the difference of two odd functions is odd and the
difference of two even functions is even.
-/




end Work.FTS.BSIdent.Parity
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Corrected =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.BSIdent

set_option autoImplicit false

/-- **The corrected stream-function field.**  Off the axis this is `Cyl.psiField ψ`; on the axis
`r = 0` it is the value `−2 L z • e_z` of the continuous extension, `L` being the axis level
`z ↦ lim_{r→0⁺} ψ(r,z)/r` of the stream function. -/
def psiFieldCorr (ψ : ℝ → ℝ → ℝ) (L : ℝ → ℝ) : R3 → R3 :=
  fun x => if Work.Cyl.radial x = 0 then (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ
    else Work.Cyl.psiField ψ x

@[simp] theorem psiFieldCorr_apply (ψ : ℝ → ℝ → ℝ) (L : ℝ → ℝ) (x : R3) :
    psiFieldCorr ψ L x
      = if Work.Cyl.radial x = 0 then (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ
        else Work.Cyl.psiField ψ x := rfl

/-- Off the axis the corrected field is the Lean stream-function field. -/
theorem psiFieldCorr_of_radial_ne {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {x : R3}
    (hx : Work.Cyl.radial x ≠ 0) : psiFieldCorr ψ L x = Work.Cyl.psiField ψ x := by
  rw [psiFieldCorr_apply, if_neg hx]

/-- On the axis the corrected field takes the extension value `−2 L z • e_z`. -/
theorem psiFieldCorr_of_radial_eq {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {x : R3}
    (hx : Work.Cyl.radial x = 0) :
    psiFieldCorr ψ L x = (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ := by
  rw [psiFieldCorr_apply, if_pos hx]

/-- **The agreement clause of route C.**  On `Uax = {x₃ ≠ 0, r ≠ 0}` the corrected field is the
Lean field `Cyl.psiField ψ`; this is exactly the `hv` hypothesis of
`Work.FTS.BSIdent.hid_of_weyl`. -/
theorem psiFieldCorr_eq_psiField_of_mem_Uax {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {x : R3}
    (hx : x ∈ Uax) : psiFieldCorr ψ L x = Work.Cyl.psiField ψ x := by
  refine psiFieldCorr_of_radial_ne fun h0 => ?_
  have hmem : x 0 ^ 2 + x 1 ^ 2 = 0 := by
    have h1 : Work.Cyl.radSq x = 0 := by
      have h2 : (Real.sqrt (Work.Cyl.radSq x)) ^ 2 = (0 : ℝ) := by
        have := congrArg (fun t : ℝ => t ^ 2) h0
        simpa [Work.Cyl.radial] using this
      rwa [Real.sq_sqrt (by simp only [Work.Cyl.radSq]; positivity)] at h2
    simpa [Work.Cyl.radSq] using h1
  exact hx.2 (by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])

end Work.FTS.BSIdent
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.continuousAt_pdZ_G_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity at `θ = 0` of the `θ`-derivative of the odd extension of `Φ`

Let `Φ` be a family of self-similar profiles which, near every point `(w, θ)` of the strip
`-1 < w`, `|θ| < π/2 + 1`, is `C²` as a function of `(w, θ)` (hypothesis `hsm`), and which
vanishes on the axis `θ = 0` for `w > 0` (`h0`).  Then the `θ`-derivative of the odd extension
in `θ`,

  `G = fun w θ => PhiOdd Φ w θ τ = if 0 ≤ θ then Φ w θ τ else -(Φ w (-θ) τ)`,

is continuous at `(w₀, 0)` for every `w₀ > 0`.

Mathematically the reason is that the odd extension of a `C¹` function vanishing at `0` is again
`C¹`, with derivative the *even* function `θ ↦ ∂_θΦ(w, |θ|, τ)`: the two one-sided derivatives at
`θ = 0` agree precisely because `Φ w 0 τ = 0`, and the resulting derivative is continuous because
`∂_θΦ` is continuous (indeed, because `(w, θ) ↦ ∂_θΦ(w, θ, τ)`, which is the Fréchet derivative
of `Φ` evaluated in the direction `(0,1)`, is continuous by `ContDiffAt.continuousAt_fderiv`).

The formal content is therefore

* a pointwise evaluation of `pdZ G` — `pdZ_PhiOdd_eq_deriv` below, splitting on the sign of `θ`
  (`θ > 0` and `θ < 0` are the two smooth branches; `θ = 0` is the odd-extension-at-`0` lemma
  `hasDerivAt_oddExtension_zero`), and
* the identification of `fderiv ℝ Φ · (0,1)` with the `θ`-slice derivative
  (`deriv_slice_eq_fderiv`), which together with the continuity of `fderiv` gives the result.

Both auxiliary facts are proved separately (`hasDerivAt_oddExtension_zero`,
`deriv_slice_eq_fderiv`).
-/

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

/-- **The pointwise value of the `θ`-derivative of the odd extension** in the strip
`|θ| < 1`, `w > 0`: it is the `θ`-derivative of `Φ` evaluated at `|θ|` (the derivative of the
odd extension is even).  This is the pointwise core of `continuousAt_pdZ_G_zero`. -/
theorem pdZ_PhiOdd_eq_deriv {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < 1) :
    Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ
      = deriv (fun θ' => Φ w θ' τ) |θ| := by
  have hd0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, 0) := by
    refine ((hsm w 0 (by linarith) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).of_le ?_).differentiableAt_one
    norm_num
  show deriv (fun θ' => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) θ = deriv (fun θ' => Φ w θ' τ) |θ|
  rcases lt_trichotomy θ 0 with h | h | h
  · -- `θ < 0`: the odd branch, differentiated with the chain rule
    rw [abs_of_neg h]
    have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => -Φ w (-θ') τ := by
      filter_upwards [isOpen_Iio.mem_nhds h] with θ' hθ'
      rw [Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ')]
    rw [Filter.EventuallyEq.deriv_eq hev]
    change deriv (-(fun θ' : ℝ => Φ w (-θ') τ)) θ = deriv (fun θ' : ℝ => Φ w θ' τ) (-θ)
    rw [deriv.neg]
    have h2 : deriv (fun θ' : ℝ => Φ w (-θ') τ) θ = - deriv (fun y : ℝ => Φ w y τ) (-θ) :=
      deriv_comp_neg (fun y : ℝ => Φ w y τ) θ
    rw [h2]
    ring
  · -- `θ = 0`: the odd extension is differentiable there with derivative `∂_θ Φ w 0 τ`
    subst h
    simp only [abs_zero]
    have hfun : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ)
        = fun θ : ℝ => if 0 ≤ θ then Φ w θ τ else -Φ w (-θ) τ := rfl
    have hcur : HasDerivAt (fun t : ℝ => (w, t)) (0, 1) 0 :=
      (hasDerivAt_const 0 w).prodMk (hasDerivAt_id 0)
    have hsl : HasDerivAt (fun θ' => Φ w θ' τ)
        (fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, 0) (0, 1)) 0 :=
      hd0.hasFDerivAt.comp_hasDerivAt 0 hcur
    have hc := hasDerivAt_oddExtension_zero (h0 w hw) hsl
    rw [hfun, hc.deriv]
    exact (deriv_slice_eq_fderiv (F := fun x y => Φ x y τ) hd0).symm
  · -- `θ > 0`: the smooth branch
    rw [abs_of_pos h]
    have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => Φ w θ' τ := by
      filter_upwards [isOpen_Ioi.mem_nhds h] with θ' hθ'
      rw [Work.FTS.BSIdent.PhiOdd_of_nonneg hθ'.le]
    rw [Filter.EventuallyEq.deriv_eq hev]

theorem continuousAt_pdZ_G_zero {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) p.1 p.2)
      (w₀, 0) := by
  -- `Φ(·,·,τ)` is `C²`, hence `fderiv` is continuous at `(w₀, 0)` (`ContDiffAt` version)
  have hC2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, 0) :=
    hsm w₀ 0 (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hfd : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) q) (w₀, 0) :=
    hC2.continuousAt_fderiv (by norm_num)
  have hfd1 : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) q (0, 1)) (w₀, 0) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).continuous.continuousAt).comp hfd
  -- composing with the (continuous) folding map `p ↦ (p.1, |p.2|)`
  have hpair : ContinuousAt (fun p : ℝ × ℝ => (p.1, |p.2|)) (w₀, 0) :=
    continuous_fst.continuousAt.prodMk
      (continuous_abs.continuousAt.comp continuous_snd.continuousAt)
  have hpair2 : Filter.Tendsto (fun p : ℝ × ℝ => (p.1, |p.2|)) (𝓝 (w₀, 0)) (𝓝 (w₀, 0)) := by
    simpa using hpair.tendsto
  have hcont : ContinuousAt (fun p : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (p.1, |p.2|) (0, 1)) (w₀, 0) := by
    have ht : Filter.Tendsto (fun p : ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (p.1, |p.2|) (0, 1)) (𝓝 (w₀, 0))
        (𝓝 (fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, |0|) (0, 1))) := by
      simpa [Function.comp_def] using hfd1.tendsto.comp hpair2
    exact ht
  refine hcont.congr ?_
  -- on the neighbourhood `|p.1 - w₀| < w₀/2`, `|p.2| < 1` the two functions agree
  have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, 0), |p.1 - w₀| < w₀ / 2 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
    · simp only [Set.mem_ofPred_eq]; rw [sub_self, abs_zero]; linarith
  have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, 0), |p.2| < 1 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
    · simp
  filter_upwards [h1, h2] with p hp1 hp2
  have hpw : 0 < p.1 := by
    have h := abs_lt.mp hp1
    linarith [h.1, h.2, hw₀]
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (p.1, |p.2|) := by
    have h₁ : -1 < p.1 := by linarith
    have h₂ : -Real.pi / 2 - 1 < |p.2| := by linarith [abs_nonneg p.2, Real.pi_pos]
    have h₃ : |p.2| < Real.pi / 2 + 1 := by linarith [Real.pi_pos]
    exact ((hsm p.1 |p.2| h₁ h₂ h₃).of_le (by norm_num)).differentiableAt_one
  rw [pdZ_PhiOdd_eq_deriv hsm h0 hpw hp2]
  exact (deriv_slice_eq_fderiv (F := fun x y => Φ x y τ) hd).symm

end Work.FTS.BSIdent.Weyl.Levels
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.physVort_slice_eq_swirlField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

/-- **The `τ`-slice of the physical vorticity is a swirl field.**

The physical vorticity of the reconstruction is, at each physical time `τ`,

  `physVort α A B g x τ = (A τ)⁻¹ • F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x)`

with `F = profile (3α) (gSlice g τ)` the full self-similar profile at time `τ`.  Since the
cylindrical coordinates `(r, x₃)` of `ℝ³` and the polar coordinates `(ρ, θ)` are related by
`Cyl.rho x = Cyl.rhoP (Cyl.radial x) (Cyl.axial x)` and `Cyl.theta x = Cyl.thetaP (Cyl.radial x)
(Cyl.axial x)`, this field is the *swirl field* of the `(r, x₃)`-profile

  `(r, z) ↦ (A τ)⁻¹ · profile (3α) (gSlice g τ) (rhoP r z ^ 3α / B τ) (thetaP r z)`,

i.e. of the same formula written in the planar variables.  This is the bridge that lets the
vorticity of the construction be handled with the `BSSwirl` machinery (curl/div of a swirl field).
-/
theorem physVort_slice_eq_swirlField (α τ : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) :
    (Work.FTS.Regularity.physVort α A B g · τ)
      = Work.FTS.BSSwirl.swirlField (fun r z => (A τ)⁻¹ *
          Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
            (Work.FTS.Regularity.gSlice g τ)
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z)) := by
  funext x
  -- both sides are `c x • Cyl.eTheta x`; unfold the two definitions of the fields
  simp only [Work.FTS.Regularity.physVort, Work.FTS.BSSwirl.swirlField,
    Work.ConstructionInstance.omegaSz]
  -- the scalar prefactor of the left side is `(A τ)⁻¹ * F(...)`
  rw [smul_smul, Work.ConstructionInstance.rho_eq_rhoP x]
  -- the angles agree definitionally: `θ(x) = arctan(x₃/r) = thetaP (radial x) (axial x)`
  simp only [Work.Cyl.theta, Work.Cyl.thetaP]

end Work.FTS.BSIdent.Weyl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.weakCurl_zero_of_pointwise_curl =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory Filter
open scoped Topology

namespace Work.FTS.BSIdent.Weyl

theorem weakCurl_zero_of_pointwise_curl {D : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hDcont : Continuous D)
    (hDdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt D (fderiv ℝ D x) x)
    (hcurl0 : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → FiniteTimeSingularity.vorticity D x = 0)
    {Ψ : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hΨcs : HasCompactSupport Ψ) :
    ∫ x, inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x) = 0 := by
  -- the field `D × Ψ` whose divergence is the difference of the two curl pairings
  have hWdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y))
        (fderiv ℝ (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x) x := by
    intro x hx0 hx2
    have h := Work.FTS.BSSwirl.hasFDerivAt_crossR3 (hDdiff x hx0 hx2)
      (((hΨ 1).differentiable_one x).hasFDerivAt)
    simpa only [h.fderiv] using h
  have hWcont : Continuous (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) :=
    (Work.FTS.BSSwirl.contDiff_crossR3 (contDiff_zero.mpr hDcont) (hΨ 0)).continuous
  have hWcs : HasCompactSupport (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨcs ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by simp [h0]))
  -- the pointwise Weyl identity, with `∇×D = 0` off the planes
  have hpt : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 →
      FiniteTimeSingularity.div (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x
        = - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x) := by
    intro x hx0 hx2
    have h := Work.FTS.BSSwirl.inner_vorticity_sub_eq_div (V := D) (Ψ := Ψ) (x := x)
      (hDdiff x hx0 hx2).differentiableAt ((hΨ 1).differentiable_one x)
    rw [hcurl0 x hx0 hx2, inner_zero_left, zero_sub] at h
    exact h.symm
  have hae : (fun x => FiniteTimeSingularity.div
        (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x)
      =ᵐ[volume] (fun x => - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x)) := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with x hx
    exact hpt x hx.1 hx.2
  -- the curl of a compactly supported smooth field is compactly supported
  have hvortcs : HasCompactSupport (FiniteTimeSingularity.vorticity Ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨcs ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    refine hx ?_
    have h0 : Ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport Ψ).isOpen_compl.mem_nhds hcon] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hd : fderiv ℝ Ψ x = 0 := by rw [h0.fderiv_eq]; simp
    rw [Work.FTS.BSSwirl.vorticity_eq_sum_crossR3]
    simp [hd]
  -- `div (D × Ψ)` is integrable: it agrees a.e. with the continuous compactly supported
  -- `-⟪D, ∇×Ψ⟫` (this is where the local integrability of `fderiv ℝ D` would have been used)
  have hint : Integrable (fun x => - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x)) := by
    have hcont : Continuous (fun x => - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x)) :=
      (continuous_inner.comp (hDcont.prodMk (Work.FTS.BSSwirl.continuous_vorticity (hΨ 1)))).neg
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact hvortcs ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by simp [h0]))
  have hWint : Integrable
      (fun x => FiniteTimeSingularity.div (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x) :=
    hint.congr hae.symm
  -- the divergence theorem off the two planes, and the conclusion
  have h0 := Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes hWcont hWcs hWdiff hWint
  rw [MeasureTheory.integral_congr_ae hae] at h0
  rw [MeasureTheory.integral_neg] at h0
  exact neg_eq_zero.mp h0

end Work.FTS.BSIdent.Weyl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.weakGrad_zero_of_pointwise_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

theorem weakGrad_zero_of_pointwise_div {D : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hDcont : Continuous D)
    (hDdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt D (fderiv ℝ D x) x)
    (hdiv0 : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → FiniteTimeSingularity.div D x = 0)
    {φ : Work.FTS.BSIdent.R3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφcs : HasCompactSupport φ) :
    ∫ x, inner ℝ (D x) (gradient φ x) = 0 := by
  -- `φ` is differentiable, and so is `φ • D` off the two coordinate planes
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hcont : Continuous (φ • D) := hφ.continuous.smul hDcont
  have hcs : HasCompactSupport (φ • D) := hφcs.smul_right
  have hdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (φ • D) (fderiv ℝ (φ • D) x) x := fun x hx0 hx2 =>
    (hφd.differentiableAt.smul ((hDdiff x hx0 hx2).differentiableAt)).hasFDerivAt
  -- the divergence of `φ • D` is a.e. the integrand, the pointwise part `φ · div D` vanishing
  have hae : (fun y => FiniteTimeSingularity.div (φ • D) y)
      =ᵐ[MeasureTheory.volume] fun y => inner ℝ (D y) (gradient φ y) := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with y hy
    rw [Work.FTS.PressureOn.div_smul_eq hφd.differentiableAt
      ((hDdiff y hy.1 hy.2).differentiableAt), hdiv0 y hy.1 hy.2, mul_zero, zero_add]
    exact real_inner_comm (D y) (gradient φ y)
  -- `⟪D, ∇φ⟫` is integrable (continuous, compactly supported), hence so is `div (φ • D)`
  have hintD : MeasureTheory.Integrable (fun y => inner ℝ (D y) (gradient φ y)) :=
    Work.FTS.PressureOn.integrable_inner_gradient hDcont hφ hφcs
  have hDivInt : MeasureTheory.Integrable (fun y => FiniteTimeSingularity.div (φ • D) y) :=
    hintD.congr hae.symm
  -- the divergence theorem off the two planes
  have h := Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
    (W := φ • D) hcont hcs hdiff hDivInt
  rw [← MeasureTheory.integral_congr_ae hae]
  exact h

end Work.FTS.BSIdent.Weyl
end
-- ===== merged: Submission.Work.FTS.FireFix.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology NNReal ENNReal Matrix

set_option autoImplicit false

namespace Work.FTS.FireFix

/-- `ℝ³`, definitionally `Work.LWP.R3`, `Work.Cyl.R3`, `Work.FTS.Physical.R3`,
`Work.FTS.PressureOn.R3` and `Work.FTS.Top.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A family `(z,θ,τ) ↦ Φ z θ τ` of self-similar profiles.  Same as
`Work.FTS.Galerkin.Fam` and `Work.FTS.MeridianDyn.Fam`. -/
abbrev Fam : Type := ℝ → ℝ → ℝ → ℝ

/-! ## The open set of the pointwise vorticity equation -/

/-- **The complement of the singular set** (design §1): `ℝ³` minus the axis `x₀ = x₁ = 0` and the
plane `x₂ = 0`.  On it the polar coordinates are non-degenerate and the pointwise vorticity
equation `∂ₜω + (u·∇)ω = (ω·∇)u` is available; its complement is a null set.

Definitionally the `Uax` of `Work.FTS.PressureOn` (hence of the design), so that the local
vorticity equation below can be fed to `PressureReconstructionOn`. -/
abbrev Uax : Set R3 := Work.FTS.PressureOn.Uax


/-- `Uax` is open. -/
theorem isOpen_Uax : IsOpen Uax := Work.FTS.PressureOn.isOpen_Uax

/-! ## The stream function of the reconstruction -/

/-- **The design's meridian stream function of the reconstruction**,

  `merPsi α A B Φ C r z t = ρ(r,z)² · (A(τ(t)))⁻¹ · Φ(ρ(r,z)^{3α}/B(τ(t)), θ(r,z), τ(t))`,

with `τ(t) = clockInv C t`, `ρ(r,z) = √(r²+z²)`, `θ(r,z) = arctan(z/r)`.

This is `Work.FTS.MeridianDyn.merPsi (3α) A B Φ C` — the definition of the *meridian bridge*
area, which is the area that proves the meridian equation `hmer` of the firing theorem below.
Note that the *odd extension in `θ`* of `Φ` (the design's `Φ̂`, formalised as
`Work.FTS.BSIdent.PhiOdd`) is the caller's choice of the family `Φ`: the natural instantiation
of the firing theorem passes `Φ := Φ̂`, so that the stream function is odd in `z` — as it must be
for the odd velocity (`BS` of an odd vorticity is odd).

The exponent argument is the profile exponent `pExp α = 3α` (design correction 1 and
`Work.FTS.Regularity.pExp`), so this reads as in the design. -/
noncomputable abbrev merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Work.FTS.Physical.PhysClock) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C

theorem merPsi_apply (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Work.FTS.Physical.PhysClock) (r z t : ℝ) :
    merPsi α A B Φ C r z t
      = Work.Cyl.rhoP r z ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹
        * Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP r z) (Work.FTS.Physical.clockInv C t) := rfl

/-! ## The three named inputs, re-exported at the design's reading -/

/-- **The Biot–Savart law for swirl vorticity** (design §1, item 7a of the dispatch list), the
honest replacement for the false `Work.LWP.BiotSavartLaw`: for a compactly supported `α`-Hölder
swirl field `f(r,z) • e_θ` with `0 < α < 1`, the Biot–Savart velocity inverts the curl and is
divergence-free.  Proved by the `BSSwirl` area (`Work.FTS.BSSwirl.biotSavartSwirl`). -/
abbrev BiotSavartSwirl : Prop := Work.FTS.BSSwirl.BiotSavartSwirl

/-- **The pressure reconstruction of the physical solution** (design §1, item 5): from the
physical vorticity of a compactly supported swirl profile whose Biot–Savart velocity is jointly
`C^{1,α}` on the strips and which solves the pointwise vorticity equation on `Uax`, there is a
pressure `p`, jointly `C¹` on `ℝ³ × [0,T)`, with `∂ₜu + (u·∇)u + ∇p = 0` on `ℝ³ × (0,T)`.
Proved by the `PressureOn` area. -/
abbrev PressureReconstructionOn (α : ℝ≥0) : Prop := Work.FTS.PressureOn.PressureReconstructionOn α

/-- **The meridian (scalar) form of the fake-time equation on a time window** (design §1,
item 9): the pointwise vanishing of `Work.CoreResiduals.meridianResid` for `r > 0`, `z ≠ 0` and
`t ∈ (0,T)`.  Proved by the `MeridianDyn` area
(`Work.FTS.MeridianDyn.meridianEq_of_dynEq`). -/
abbrev MeridianEqOn (W ψ : ℝ → ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  Work.FTS.MeridianDyn.MeridianEqOn W ψ T

/-- **The corrected regularity package** (design §0 correction 5), the output of the `RegPkgGal`
area: `Work.FTS.Regularity.RegPkg` with the false Lipschitz angular clause replaced by the true
Hölder clause `|g z θ τ − g z θ' τ| ≤ K z² |θ − θ'|^α`. -/
abbrev RegPkg' (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.RegPkgGal.RegPkg' α S A B g

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Algebra.meridianResid_algebra_dyn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Algebra

theorem meridianResid_algebra_dyn {p z r ρsq Z a sp κ₁ κ₂ f fτ f1 f2 g g1 g2 : ℝ}
    (hr : r ≠ 0) (hρ : ρsq = r ^ 2 + z ^ 2) :
    κ₁ * sp * a * f + a * sp * fτ + a * κ₂ * sp * Z * f1
      + (a * (2 * z * g + p * Z * z * g1 + r * g2))
          * (a * (f1 * (p * Z * (r / ρsq)) - f2 * (z / ρsq)))
      + (-(ρsq * (a * g) / r) - a * (2 * r * g + p * Z * r * g1 - z * g2))
          * (a * (f1 * (p * Z * (z / ρsq)) + f2 * (r / ρsq)))
      - (a * (2 * z * g + p * Z * z * g1 + r * g2) / r) * (a * f)
      = a * sp * (fτ + κ₁ * f + κ₂ * (Z * f1))
        + (a ^ 2 / 2) * (2 * (-3 * g - p * Z * g1) * f2
            + 2 * p * (g2 - (z / r) * g) * (Z * f1)
            - 2 * ((2 * z * g + p * z * Z * g1 + r * g2) / r) * f) := by
  subst hρ
  have h : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Work.FTS.MeridianDyn.Algebra
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.gRHS_sub_gDynRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

open scoped Real Topology

/-- **The bridge identity of the dynamic meridian reduction**: the *stationary* `g`-right-hand
side `gRHS` at the τ-dependent modulation constants `(μ̄(τ), λ(τ))` differs from the *dynamical*
one `gDynRHS` of the Stability layer by exactly the `AK`-multiple

`(2αμ̄(τ) − μ̄ − L₁₂(Transport g)(0)) · AK`,

which is the forcing that the reference-rate reduction produces (`F_* − D_zF_* = 2α·AK`) once
the paper's choice `λ = -2μ/(1+μ)` (i.e. `μ+λ+μλ = -μ`, the dictionary `κ*b* = 1-μ`) is used.

The proof is pointwise algebra: both sides carry the same `N₀`, `N` and `N_*` terms
(`Ftot α g τ` and `Ftau α g τ` are the same function), so only the `F_*`/`D_zF_*` forcing and the
`AK·L₁₂(Transport g)(0)` term survive; the substitutions `κ = 1+μ`, `b = 1+λ`, `μ+λ+μλ = -μ` and
`D_zF_* = F_* − 2α·AK` reduce the difference to the stated `AK`-coefficient.

**No change is needed for the sign fix.**  The statement is *generic* in `muDyn` (the modulation
constant enters only as the opaque function `Work.FTS.Galerkin.muDyn α Φ g`), so it stays true
verbatim when `muDyn` becomes `Construction.mufunS`; what changes is that the `AK`-coefficient
`2α·muDyn − μ̄ − L₁₂(Transport g)(0)` is now *identically zero* (`two_mul_muDyn`,
`FTS_MUFUN_SIGN.md` §5) — which is exactly why the defect hypothesis disappears from `DynEqF` and
`Main`.  The only edit here is this docstring. -/
theorem gRHS_sub_gDynRHS {α : ℝ} (hα : 0 < α) {g Φ : Work.FTS.MeridianDyn.Fam}
    {M : Work.Stability.ModState} {z θ τ : ℝ} (hz : -1 < z)
    (hne : 1 + Work.FTS.Galerkin.muDyn α Φ g τ ≠ 0)
    (hκ : M.kappa τ = 1 + Work.FTS.Galerkin.muDyn α Φ g τ)
    (hb : M.b τ = 1 + Work.FTS.Galerkin.lamDyn α Φ g τ) :
    Work.Construction.gRHS α (Work.FTS.Galerkin.muDyn α Φ g τ)
        (Work.FTS.Galerkin.lamDyn α Φ g τ) (Work.Construction.Ftau α g τ)
        (Work.FTS.Galerkin.slice Φ τ) (Work.FTS.Galerkin.slice g τ) z θ
      - Work.Stability.gDynRHS α M g Φ z θ τ
      = (2 * α * Work.FTS.Galerkin.muDyn α Φ g τ
            - Work.Construction.mubar
                (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
                  (Work.FTS.Galerkin.slice g τ))
                (Work.Construction.N α (Work.Construction.Ftau α g τ)
                  (Work.FTS.Galerkin.slice Φ τ))
            - Work.Construction.L12 (Work.Coercivity.Transport
                (Work.FTS.Galerkin.slice g τ)) 0)
          * Work.Construction.AK α z θ := by
  -- the paper's choice `λ = -2μ/(1+μ)`: the dictionary identity `μ + λ + μλ = -μ`.
  have hlam : Work.FTS.Galerkin.muDyn α Φ g τ
      + Work.Construction.lamfun (Work.FTS.Galerkin.muDyn α Φ g τ)
      + Work.FTS.Galerkin.muDyn α Φ g τ
        * Work.Construction.lamfun (Work.FTS.Galerkin.muDyn α Φ g τ)
      = -Work.FTS.Galerkin.muDyn α Φ g τ := by
    rw [Work.Construction.lamfun]
    field_simp
    ring
  -- `κ - 1 = μ`
  have hκ' : M.kappa τ - 1 = Work.FTS.Galerkin.muDyn α Φ g τ := by rw [hκ]; ring
  -- `b - 1 = λ`
  have hb' : M.b τ - 1 = Work.FTS.Galerkin.lamDyn α Φ g τ := by rw [hb]; ring
  -- `κ b - 1 = -μ` (the dictionary `κ* b* = 1 - μ` at the dynamical rates).
  have hkb : M.kappa τ * M.b τ - 1 = -Work.FTS.Galerkin.muDyn α Φ g τ := by
    have h2 : Work.Construction.lamfun (Work.FTS.Galerkin.muDyn α Φ g τ)
        = Work.FTS.Galerkin.lamDyn α Φ g τ := rfl
    rw [hκ, hb, ← h2]
    nlinarith [hlam]
  -- `D_z F_* = F_* - 2α·AK`.
  have hDz : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = Work.Construction.Fstar α z θ - 2 * α * Work.Construction.AK α z θ := by
    have h := Work.Construction.Fstar_sub_DzFstar (α := α) (z := z) (θ := θ) hα hz
    linarith
  -- unfold the two right-hand sides.
  simp only [Work.Construction.gRHS, Work.Stability.gDynRHS]
  -- rewrite the definitionally-equal vocabulary of the two layers.
  rw [show Work.Stability.Ftot α g τ = Work.Construction.Ftau α g τ from rfl,
    show Work.Stability.slice g τ = Work.FTS.Galerkin.slice g τ from rfl,
    show Work.Stability.slice Φ τ = Work.FTS.Galerkin.slice Φ τ from rfl]
  -- substitute the four identities and close by polynomial algebra.
  rw [hkb, hκ', hb', hDz]
  ring

end Work.FTS.MeridianDyn.Bridge
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Chain.pdR_dynPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem pdR_dynPsi {p : ℝ} {a b σ : ℝ → ℝ} {Φ : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hΦ : Work.Cyl.DiffAt2 (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r' z' t) r z
      = a t * (2 * r * Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
          + Work.Cyl.rhoP r z ^ 2 *
              (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
                  (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                  * (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2))
                - Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
                    (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                    * (z / Work.Cyl.rhoP r z ^ 2))) := by
  -- `dynPsi` is the constant-rate `ssPsi` at the `σ t`-slice of `Φ`, rescaled by `a t * b t`.
  have hab : (fun r' z' => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r' z' t)
      = fun r' z' => (a t * b t) * Work.CoreResiduals.ssPsi p b
          (fun Z Θ => Φ Z Θ (σ t)) r' z' t := by
    funext r' z'
    simp only [Work.FTS.MeridianDyn.dynPsi_apply, Work.CoreResiduals.ssPsi]
    field_simp
  rw [hab]
  -- a constant factor (in `r'`) pulls out of `∂_r`, unconditionally in the differentiability gap
  have hc : Work.Cyl.pdR (fun r' z' => (a t * b t) * Work.CoreResiduals.ssPsi p b
        (fun Z Θ => Φ Z Θ (σ t)) r' z' t) r z
      = (a t * b t) * Work.Cyl.pdR (fun r' z' => Work.CoreResiduals.ssPsi p b
        (fun Z Θ => Φ Z Θ (σ t)) r' z' t) r z := by
    rw [Work.Cyl.pdR, Work.Cyl.pdR]
    by_cases hc0 : (a t * b t) = 0
    · simp [hc0]
    · by_cases hd : DifferentiableAt ℝ
          (fun r' => Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) r' z t) r
      · rw [deriv_const_mul _ hd]
      · have hnd : ¬ DifferentiableAt ℝ (fun r' => (a t * b t) *
            Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) r' z t) r := by
          intro h
          apply hd
          have h1 : (fun y => (a t * b t)⁻¹ * ((a t * b t) *
                Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) y z t))
              = fun r' => Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) r' z t := by
            funext y
            rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
          have h2 := h.const_mul (a t * b t)⁻¹
          rwa [h1] at h2
        rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd,
          mul_zero]
  rw [hc, Work.CoreResiduals.pdR_ssPsi_lam (p := p) (lam := b)
    (Φ := fun Z Θ => Φ Z Θ (σ t)) hr hb hΦ]
  field_simp

end Work.FTS.MeridianDyn.Chain
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Chain.pdR_dynVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem pdR_dynVort {p : ℝ} {a b σ : ℝ → ℝ} {F : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hF : Work.Cyl.DiffAt2 (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => Work.FTS.MeridianDyn.dynVort p a b σ F r' z' t) r z
      = a t * (Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2))
          - Work.Cyl.pdZ (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (z / Work.Cyl.rhoP r z ^ 2)) := by
  -- `∂_r ρ = r/ρ`.
  have hρ : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
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
  -- `∂_r Θ = -z/ρ²`.
  have hθ : HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z)
      (-z / Work.Cyl.rhoP r z ^ 2) r := by
    have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
      have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
      have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
        funext x; simp [Pi.div_apply]
      rw [hfun] at h
      convert h using 1
      simp
    have h := hdiv.arctan
    have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
      funext r'; rw [Work.Cyl.thetaP]
    rw [hfun]
    convert h using 1
    rw [Work.Cyl.rhoP]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  -- `∂_r (ρ^p) = p·ρ^p·(r/ρ²)`.
  have hρp : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2)) r := by
    have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
    have h := (Real.hasDerivAt_rpow_const (x := Work.Cyl.rhoP r z) (p := p) (Or.inl hne)).comp
      r hρ
    have hfun : ((fun x : ℝ => x ^ p) ∘ fun r' => Work.Cyl.rhoP r' z)
        = fun r' => Work.Cyl.rhoP r' z ^ p := by
      funext x; rfl
    rw [hfun] at h
    convert h using 1
    rw [Real.rpow_sub_one hne]
    field_simp
  -- `∂_r (ρ^p/b t) = p·(ρ^p/b t)·(r/ρ²)`.
  have hR : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b t)
      (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2)) r := by
    have h := hρp.div_const (b t)
    convert h using 1
    ring
  -- The two-variable chain rule along the radial slice.
  have hcomp := Work.Cyl.hasDerivAt_comp_two (fun Z Θ => F Z Θ (σ t))
      (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b t) (fun r' : ℝ => Work.Cyl.thetaP r' z)
      (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2))
      (-z / Work.Cyl.rhoP r z ^ 2) r hF hR hθ
  have hcm := hcomp.const_mul (a t)
  rw [Work.Cyl.pdR]
  change deriv (fun r' : ℝ =>
      a t * F (Work.Cyl.rhoP r' z ^ p / b t) (Work.Cyl.thetaP r' z) (σ t)) r = _
  rw [hcm.deriv]
  ring

end Work.FTS.MeridianDyn.Chain
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Chain.pdZ_dynPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial chain rule for the dynamic stream-function ansatz `dynPsi`

`Work.FTS.MeridianDyn.dynPsi p a b σ Φ r z t = ρ(r,z)² · a(t) · Φ (ρ(r,z)^p/b(t)) (θ(r,z)) (σ t)`
with `ρ = √(r²+z²)` and `θ = arctan(z/r)`.  Since

* `∂_z (ρ²) = 2·ρ·∂_zρ = 2z`,
* `∂_z (ρ^p/b) = p · (ρ^p/b) · (z/ρ²)` (`Work.Cyl.hasDerivAt_rhoP_rpow_div_snd`), and
* `∂_z θ = r/ρ²` (`Work.Cyl.hasDerivAt_thetaP_snd`),

the product rule together with the two-variable chain rule (`Work.Cyl.hasDerivAt_comp_two`) gives
the axial chain rule of the dynamic ansatz; this is the `σ`/`b`-dependent generalisation of
`Work.CoreResiduals.pdZ_ssPsi_lam` (the constant-rate case `lam = b`, `a = b⁻¹`, `σ = id`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.FTS.MeridianDyn.Chain

theorem pdZ_dynPsi {p : ℝ} {a b σ : ℝ → ℝ} {Φ : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hΦ : Work.Cyl.DiffAt2 (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r' z' t) r z
      = a t * (2 * z * Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
          + Work.Cyl.rhoP r z ^ 2 *
              (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
                  (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                  * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
                + Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
                    (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                    * (r / Work.Cyl.rhoP r z ^ 2))) := by
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  -- the two-variable chain rule for `z' ↦ Φ (ρ(r,z')^p/b t) (θ(r,z')) (σ t)`
  have hchain : HasDerivAt
      (fun z' : ℝ => Φ (Work.Cyl.rhoP r z' ^ p / b t) (Work.Cyl.thetaP r z') (σ t))
      (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
          (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_comp_two (fun Z Θ => Φ Z Θ (σ t))
      (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b t) (fun z' : ℝ => Work.Cyl.thetaP r z')
      (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
      (r / Work.Cyl.rhoP r z ^ 2) z hΦ
      (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (b t) hr)
      (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  -- multiply by the outer amplitude `a t`
  have hpsi : HasDerivAt
      (fun z' : ℝ => a t * Φ (Work.Cyl.rhoP r z' ^ p / b t) (Work.Cyl.thetaP r z') (σ t))
      (a t * (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
          (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2))) z :=
    hchain.const_mul (a t)
  -- `∂_z (ρ²) = 2·ρ·(z/ρ) = 2z`
  have hsq : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) (2 * z) z := by
    have h := (Work.Cyl.hasDerivAt_rhoP_snd r z hr).pow 2
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one] at h
    have hval : 2 * Work.Cyl.rhoP r z * (z / Work.Cyl.rhoP r z) = 2 * z := by
      field_simp
    exact h.congr_deriv hval
  -- product rule
  have hprod := hsq.mul hpsi
  rw [Work.Cyl.pdZ]
  rw [show (fun z' : ℝ => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r z' t)
      = ((fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) *
          fun z' : ℝ => a t * Φ (Work.Cyl.rhoP r z' ^ p / b t)
            (Work.Cyl.thetaP r z') (σ t)) from by
        funext z'
        simp only [Work.FTS.MeridianDyn.dynPsi_apply, Pi.mul_apply]
        ring]
  rw [hprod.deriv]
  ring

end Work.FTS.MeridianDyn.Chain
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Chain.pdZ_dynVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem pdZ_dynVort {p : ℝ} {a b σ : ℝ → ℝ} {F : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hF : Work.Cyl.DiffAt2 (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => Work.FTS.MeridianDyn.dynVort p a b σ F r' z' t) r z
      = a t * (Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
          + Work.Cyl.pdZ (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2)) := by
  -- The two-variable chain rule for `z' ↦ F (ρ(r,z')^p/b t) (Θ(r,z')) (σ t)` at `(ρ^p/b t, Θ)`.
  have hchain := Work.Cyl.hasDerivAt_comp_two (fun Z Θ => F Z Θ (σ t))
    (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b t) (fun z' : ℝ => Work.Cyl.thetaP r z')
    (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
    (r / Work.Cyl.rhoP r z ^ 2) z hF
    (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (b t) hr)
    (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  -- Pull the amplitude prefactor `a t` out of the derivative and unfold `dynVort` and `pdZ`.
  have hmain := hchain.const_mul (a t)
  rw [Work.Cyl.pdZ]
  show deriv (fun z' : ℝ =>
      a t * F (Work.Cyl.rhoP r z' ^ p / b t) (Work.Cyl.thetaP r z') (σ t)) z = _
  rw [hmain.deriv]

end Work.FTS.MeridianDyn.Chain
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Chain.timeDeriv_dynVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem timeDeriv_dynVort {p : ℝ} {a b σ : ℝ → ℝ} {F : Work.FTS.MeridianDyn.Fam}
    {r z t A' B' sp fτ : ℝ}
    (ha : HasDerivAt a A' t) (hb : HasDerivAt b B' t) (hσ : HasDerivAt σ sp t)
    (hbne : b t ≠ 0)
    (hG : Work.Cyl.DiffAt2 (fun Z s => F Z (Work.Cyl.thetaP r z) s)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t))
    (hfτ : HasDerivAt (fun s => F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) s)
      fτ (σ t)) :
    deriv (fun s => Work.FTS.MeridianDyn.dynVort p a b σ F r z s) t
      = A' * F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
        + a t * (sp * fτ - (B' / b t) * (Work.Cyl.rhoP r z ^ p / b t)
            * Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
                (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) := by
  -- the derivative of the rescaled radial variable `s ↦ ρ^p / b s`
  have hZ : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p / b s)
      (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t)) t := by
    have h0 : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p * (b s)⁻¹)
        (Work.Cyl.rhoP r z ^ p * (-B' / (b t) ^ 2)) t :=
      (hb.inv hbne).const_mul (Work.Cyl.rhoP r z ^ p)
    have hfun : (fun s : ℝ => Work.Cyl.rhoP r z ^ p * (b s)⁻¹)
        = fun s : ℝ => Work.Cyl.rhoP r z ^ p / b s := by
      funext s; rw [div_eq_mul_inv]
    have hval : Work.Cyl.rhoP r z ^ p * (-B' / (b t) ^ 2)
        = -(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t) := by
      field_simp
    rw [hfun, hval] at h0
    exact h0
  -- the chain rule in the two fake-time variables `(Z, S) = (ρ^p/b, σ)`
  have hcomp : HasDerivAt
      (fun s : ℝ => F (Work.Cyl.rhoP r z ^ p / b s) (Work.Cyl.thetaP r z) (σ s))
      (Work.Cyl.pdR (fun Z S => F Z (Work.Cyl.thetaP r z) S)
          (Work.Cyl.rhoP r z ^ p / b t) (σ t)
          * (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t))
        + Work.Cyl.pdZ (fun Z S => F Z (Work.Cyl.thetaP r z) S)
            (Work.Cyl.rhoP r z ^ p / b t) (σ t) * sp) t :=
    Work.Cyl.hasDerivAt_comp_two (fun Z S => F Z (Work.Cyl.thetaP r z) S)
      (fun s : ℝ => Work.Cyl.rhoP r z ^ p / b s) σ
      (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t)) sp t hG hZ hσ
  have hprod : HasDerivAt
      (fun s : ℝ => a s * F (Work.Cyl.rhoP r z ^ p / b s) (Work.Cyl.thetaP r z) (σ s))
      (A' * F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
        + a t * (Work.Cyl.pdR (fun Z S => F Z (Work.Cyl.thetaP r z) S)
            (Work.Cyl.rhoP r z ^ p / b t) (σ t)
            * (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t))
          + Work.Cyl.pdZ (fun Z S => F Z (Work.Cyl.thetaP r z) S)
              (Work.Cyl.rhoP r z ^ p / b t) (σ t) * sp)) t := ha.mul hcomp
  -- the fake-time derivative of the slice is `fτ` (the `S`-partial), and the `Z`-partial is the
  -- partial of the frozen slice at `σ t` (definitionally)
  have hpdZ : Work.Cyl.pdZ (fun Z S => F Z (Work.Cyl.thetaP r z) S)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t) = fτ := by
    simp only [Work.Cyl.pdZ, hfτ.deriv]
  have hpdR : Work.Cyl.pdR (fun Z S => F Z (Work.Cyl.thetaP r z) S)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t)
      = Work.Cyl.pdR (fun Z Θ' => F Z Θ' (σ t)) (Work.Cyl.rhoP r z ^ p / b t)
          (Work.Cyl.thetaP r z) := by
    simp only [Work.Cyl.pdR]
  rw [show (fun s : ℝ => Work.FTS.MeridianDyn.dynVort p a b σ F r z s)
      = (fun s : ℝ => a s * F (Work.Cyl.rhoP r z ^ p / b s) (Work.Cyl.thetaP r z) (σ s))
      from rfl]
  rw [hprod.deriv, hpdZ, hpdR]
  ring

end Work.FTS.MeridianDyn.Chain
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Clock.amplitude_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Clock

open Work.FTS.Physical (clockInv clockInv_nonneg clockInv_hasDerivAt)

/-- **The derivative of the reciprocal amplitude `(A ∘ clockInv)⁻¹`.**

The amplitude `A` of the dynamic rescaling solves `A' = -(1+μ)A` in fake time, and the extended
inverse clock `clockInv C` is differentiable on `(0,T)` with derivative `(C.A (clockInv C t))⁻¹`.
Composing (`HasDerivAt.comp`), the chain rule gives

  `d/dt (A(τ(t))) = (-(1+μ(τ(t)))·A(τ(t)))·(C.A(τ(t)))⁻¹`,

and the reciprocal rule (`HasDerivAt.inv`, legitimate because `A(τ(t)) > 0`) turns this into the
stated derivative

  `d/dt (A(τ(t)))⁻¹ = (1+μ(τ(t)))·(C.A(τ(t)))⁻¹·(A(τ(t)))⁻¹`,

since `-(f')/A² = (1+μ)·(C.A)⁻¹·A/A²`.  Note that the `C.A` factor comes from the derivative of
the clock, whereas the `A`-factor and `μ` come from the amplitude equation: the two functions
`A` and `C.A` need not coincide for the identity to hold. -/
theorem amplitude_hasDerivAt {A : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock} {t : ℝ}
    (hAd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ)
    (hApos : 0 < A (Work.FTS.Physical.clockInv C t))
    (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (fun s => (A (Work.FTS.Physical.clockInv C s))⁻¹)
      ((1 + C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        * (A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
  have hτ : 0 ≤ clockInv C t := clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hclock : HasDerivAt (clockInv C) ((C.A (clockInv C t))⁻¹) t := clockInv_hasDerivAt C ht
  have hA : HasDerivAt A (-(1 + C.mu (clockInv C t)) * A (clockInv C t)) (clockInv C t) :=
    hAd (clockInv C t) hτ
  -- chain rule: differentiate `A ∘ clockInv`
  have hcomp : HasDerivAt (fun s => A (clockInv C s))
      ((-(1 + C.mu (clockInv C t)) * A (clockInv C t)) * (C.A (clockInv C t))⁻¹) t :=
    hA.comp t hclock
  -- reciprocal rule, then collapse to the stated derivative
  refine (hcomp.inv (ne_of_gt hApos)).congr_deriv ?_
  field_simp

end Work.FTS.MeridianDyn.Clock
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Clock.scale_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Clock

/-- **The derivative of a scale function along the physical clock.**

If `B` solves the (fake-time) linear ODE `B' = -(1 - μ) · B` on the nonnegative half-line, then the
composition `s ↦ B(τ(s))` of `B` with the inverse clock `τ = clockInv C` is differentiable at every
physical time `t ∈ (0,T)`, with derivative

  `-(1 - μ(τ(t))) · A(τ(t))⁻¹ · B(τ(t))`.

This is the chain rule: `d/ds B(τ(s)) = B'(τ(s))·τ'(s)`, the derivative of the clock being
`A(τ(s))⁻¹` (`Work.FTS.Physical.clockInv_hasDerivAt`).  The hypothesis `hBd` is only available on
`[0,∞)` in fake time, which is exactly where `τ(t)` lives for `t ∈ (0,T)`. -/
theorem scale_hasDerivAt {B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock} {t : ℝ}
    (hBd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ)
    (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (fun s => B (Work.FTS.Physical.clockInv C s))
      (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        * B (Work.FTS.Physical.clockInv C t)) t := by
  have hτ : 0 ≤ Work.FTS.Physical.clockInv C t :=
    Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hB : HasDerivAt B
      (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
        * B (Work.FTS.Physical.clockInv C t)) (Work.FTS.Physical.clockInv C t) :=
    hBd (Work.FTS.Physical.clockInv C t) hτ
  have hclock : HasDerivAt (Work.FTS.Physical.clockInv C)
      (C.A (Work.FTS.Physical.clockInv C t))⁻¹ t :=
    Work.FTS.Physical.clockInv_hasDerivAt C ht
  have hcomp := hB.comp t hclock
  have heq : (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
          * B (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        = -(1 - C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          * B (Work.FTS.Physical.clockInv C t) := by
    ring
  rw [heq] at hcomp
  exact hcomp

end Work.FTS.MeridianDyn.Clock
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.MeridianDyn.Odd.meridianResid_odd`

The meridian residual `Work.CoreResiduals.meridianResid` is **odd in `z`** whenever the vorticity
profile `W` and the stream function `ψ` are pointwise odd in the axial variable `z` (i.e. the
physical meridional half-plane `z > 0` determines the whole picture through the reflection
`z ↦ -z`).

Term by term: writing `f = W r · t` and `g = ψ r · t` for the two `z`-slices,

* `∂ₜW` is odd in `z`, because `z ↦ W r z s` is pointwise `-` the reflected slice for every
  time `s`, and `deriv` is additive (`deriv.neg`); this needs **no** differentiability
  hypothesis, since `deriv` is total and totalised to `0` off the differentiable points —
  oddness at `z` and at `-z` are interchangeable pointwise, so the junk values match too;
* `∂_zψ` and `∂_zW` are **even** in `z`: the derivative of an odd function is even
  (`deriv_neg_of_odd`, from the unconditional identity `deriv_comp_neg`);
* `∂_rW` and `∂_rψ` are odd in `z`: for fixed `r` the `r`-slice at `-z` is pointwise `-` the
  slice at `z`, so its derivative is the negative (`deriv.neg`);
* `W r z t`, `ψ r z t` are odd by hypothesis.

The residual is
`∂ₜW + (∂_zψ)(∂_rW) + ( -(ψ/r) - ∂_rψ )(∂_zW) - ((∂_zψ)/r)W`, an odd·even / odd·odd
combination of these, hence odd.  The factor `1/r` is *not* differentiated and plays no role
beyond the (harmless) hypothesis `r ≠ 0` carried by the statement.
-/

namespace Work.FTS.MeridianDyn.Odd



end Work.FTS.MeridianDyn.Odd
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Smooth.profFamOdd_contDiffAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Smooth

open Filter Set
open scoped Topology

/-! ## Smoothness of the two factors of the profile `F_*` -/

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C¹` at every interior angle `Θ ∈ (0, π/2)`.

The base `sinθ·cos²θ` is strictly positive there, so the (total) real power is `C¹` by
`Real.contDiffAt_rpow_const`. -/
lemma contDiffAt_Gam (α : ℝ) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ1 : Θ < Real.pi / 2) :
    ContDiffAt ℝ 1 (fun θ : ℝ => Work.Spaces.Gam α θ) Θ := by
  have hbase : ContDiffAt ℝ 1 (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Θ := by fun_prop
  have hne : Real.sin Θ * Real.cos Θ ^ 2 ≠ 0 := by
    have h1 : 0 < Real.sin Θ := Real.sin_pos_of_pos_of_lt_pi hΘ (by linarith [hΘ1, Real.pi_pos])
    have h2 : 0 < Real.cos Θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hΘ, Real.pi_pos], hΘ1⟩
    positivity
  have hrpow := Real.contDiffAt_rpow_const (x := Real.sin Θ * Real.cos Θ ^ 2) (p := α / 3)
    (n := 1) (Or.inl hne)
  have hmain : ContDiffAt ℝ 1
      ((fun x : ℝ => x ^ (α / 3)) ∘ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)) Θ :=
    hrpow.comp Θ hbase
  exact hmain

/-- The singular profile
`F_*(z,θ) = α·(Γ(θ)/c(α))·(2z/(1+z)²)` is `C¹` at every point with `z > 0` and
`0 < θ < π/2`: it is a product of a `C¹` function of `θ` (`Γ/c`, `c` constant) and the rational
function `z ↦ 2z/(1+z)²`, which is `C¹` at `Z > 0` (its pole sits at `z = -1`). -/
lemma contDiffAt_Fstar (α τ : ℝ) {Z Θ : ℝ} (hZ : 0 < Z) (hΘ : 0 < Θ)
    (hΘ1 : Θ < Real.pi / 2) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Construction.Fstar α p.1 p.2.1) (Z, Θ, τ) := by
  have hsnd2 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => p.2.1) (Z, Θ, τ) := by fun_prop
  have hfst : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => p.1) (Z, Θ, τ) := by fun_prop
  have hG' : ContDiffAt ℝ 1 ((Work.Spaces.Gam α) ∘ (fun p : ℝ × ℝ × ℝ => p.2.1)) (Z, Θ, τ) :=
    (contDiffAt_Gam α hΘ hΘ1).comp (Z, Θ, τ) hsnd2
  have hG : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Spaces.Gam α p.2.1) (Z, Θ, τ) := hG'
  have hG2 : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ × ℝ => α * (Work.Spaces.Gam α p.2.1 / Work.Spaces.c α)) (Z, Θ, τ) :=
    (contDiffAt_const (c := α)).mul (hG.div_const (Work.Spaces.c α))
  have hF : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FM.Fstar p.1) (Z, Θ, τ) := by
    have hz : ContDiffAt ℝ 1 (fun z : ℝ => Work.FM.Fstar z) Z := by
      change ContDiffAt ℝ 1 (fun z : ℝ => 2 * z / (1 + z) ^ 2) Z
      fun_prop (disch := positivity)
    have hF' : ContDiffAt ℝ 1 ((fun z : ℝ => Work.FM.Fstar z) ∘ (fun p : ℝ × ℝ × ℝ => p.1))
        (Z, Θ, τ) := hz.comp (Z, Θ, τ) hfst
    exact hF'
  exact hG2.mul hF

/-! ## The target -/


end Work.FTS.MeridianDyn.Smooth
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.PdZGammaZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity at `θ = 0` of the `θ`-derivative of the odd extension of `Φ`

Let `Φ` be a family of self-similar profiles which, near every point `(w, θ)` of the strip
`-1 < w`, `|θ| < π/2 + 1`, is `C²` as a function of `(w, θ)` (hypothesis `hsm`), and which
vanishes on the axis `θ = 0` for `w > 0` (`h0`).  Then the `θ`-derivative of the odd extension
in `θ`,

  `G = fun w θ => PhiOdd Φ w θ τ = if 0 ≤ θ then Φ w θ τ else -(Φ w (-θ) τ)`,

is continuous at `(w₀, 0)` for every `w₀ > 0`.

Mathematically the reason is that the odd extension of a `C¹` function vanishing at `0` is again
`C¹`, with derivative the *even* function `θ ↦ ∂_θΦ(w, |θ|, τ)`: the two one-sided derivatives at
`θ = 0` agree precisely because `Φ w 0 τ = 0`, and the resulting derivative is continuous because
`∂_θΦ` is continuous (indeed, because `(w, θ) ↦ ∂_θΦ(w, θ, τ)`, which is the Fréchet derivative
of `Φ` evaluated in the direction `(0,1)`, is continuous by `ContDiffAt.continuousAt_fderiv`).

The formal content is therefore

* a pointwise evaluation of `pdZ G` — `pdZ_PhiOdd_eq_deriv` below, splitting on the sign of `θ`
  (`θ > 0` and `θ < 0` are the two smooth branches; `θ = 0` is the odd-extension-at-`0` lemma
  `hasDerivAt_oddExtension_zero`), and
* the identification of `fderiv ℝ Φ · (0,1)` with the `θ`-slice derivative
  (`deriv_slice_eq_fderiv`), which together with the continuity of `fderiv` gives the result.

Both auxiliary facts are proved separately (`hasDerivAt_oddExtension_zero`,
`deriv_slice_eq_fderiv`).
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

/-- **The pointwise value of the `θ`-derivative of the odd extension** in the strip
`|θ| < 1`, `w > 0`: it is the `θ`-derivative of `Φ` evaluated at `|θ|` (the derivative of the
odd extension is even).  This is the pointwise core of `continuousAt_pdZ_G_zero`. -/
theorem pdZ_PhiOdd_eq_deriv {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < 1) :
    Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ
      = deriv (fun θ' => Φ w θ' τ) |θ| := by
  have hd0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, 0) := by
    refine ((hsm w 0 (by linarith) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).of_le ?_).differentiableAt_one
    norm_num
  show deriv (fun θ' => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) θ = deriv (fun θ' => Φ w θ' τ) |θ|
  rcases lt_trichotomy θ 0 with h | h | h
  · -- `θ < 0`: the odd branch, differentiated with the chain rule
    rw [abs_of_neg h]
    have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => -Φ w (-θ') τ := by
      filter_upwards [isOpen_Iio.mem_nhds h] with θ' hθ'
      rw [Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ')]
    rw [Filter.EventuallyEq.deriv_eq hev]
    change deriv (-(fun θ' : ℝ => Φ w (-θ') τ)) θ = deriv (fun θ' : ℝ => Φ w θ' τ) (-θ)
    rw [deriv.neg]
    have h2 : deriv (fun θ' : ℝ => Φ w (-θ') τ) θ = - deriv (fun y : ℝ => Φ w y τ) (-θ) :=
      deriv_comp_neg (fun y : ℝ => Φ w y τ) θ
    rw [h2]
    ring
  · -- `θ = 0`: the odd extension is differentiable there with derivative `∂_θ Φ w 0 τ`
    subst h
    simp only [abs_zero]
    have hfun : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ)
        = fun θ : ℝ => if 0 ≤ θ then Φ w θ τ else -Φ w (-θ) τ := rfl
    have hcur : HasDerivAt (fun t : ℝ => (w, t)) (0, 1) 0 :=
      (hasDerivAt_const 0 w).prodMk (hasDerivAt_id 0)
    have hsl : HasDerivAt (fun θ' => Φ w θ' τ)
        (fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, 0) (0, 1)) 0 :=
      hd0.hasFDerivAt.comp_hasDerivAt 0 hcur
    have hc := hasDerivAt_oddExtension_zero (h0 w hw) hsl
    rw [hfun, hc.deriv]
    exact (deriv_slice_eq_fderiv (F := fun x y => Φ x y τ) hd0).symm
  · -- `θ > 0`: the smooth branch
    rw [abs_of_pos h]
    have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => Φ w θ' τ := by
      filter_upwards [isOpen_Ioi.mem_nhds h] with θ' hθ'
      rw [Work.FTS.BSIdent.PhiOdd_of_nonneg hθ'.le]
    rw [Filter.EventuallyEq.deriv_eq hev]

theorem continuousAt_pdZ_G_zero {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) p.1 p.2)
      (w₀, 0) := by
  -- `Φ(·,·,τ)` is `C²`, hence `fderiv` is continuous at `(w₀, 0)` (`ContDiffAt` version)
  have hC2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, 0) :=
    hsm w₀ 0 (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hfd : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) q) (w₀, 0) :=
    hC2.continuousAt_fderiv (by norm_num)
  have hfd1 : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) q (0, 1)) (w₀, 0) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).continuous.continuousAt).comp hfd
  -- composing with the (continuous) folding map `p ↦ (p.1, |p.2|)`
  have hpair : ContinuousAt (fun p : ℝ × ℝ => (p.1, |p.2|)) (w₀, 0) :=
    continuous_fst.continuousAt.prodMk
      (continuous_abs.continuousAt.comp continuous_snd.continuousAt)
  have hpair2 : Filter.Tendsto (fun p : ℝ × ℝ => (p.1, |p.2|)) (𝓝 (w₀, 0)) (𝓝 (w₀, 0)) := by
    simpa using hpair.tendsto
  have hcont : ContinuousAt (fun p : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (p.1, |p.2|) (0, 1)) (w₀, 0) := by
    have ht : Filter.Tendsto (fun p : ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (p.1, |p.2|) (0, 1)) (𝓝 (w₀, 0))
        (𝓝 (fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, |0|) (0, 1))) := by
      simpa [Function.comp_def] using hfd1.tendsto.comp hpair2
    exact ht
  refine hcont.congr ?_
  -- on the neighbourhood `|p.1 - w₀| < w₀/2`, `|p.2| < 1` the two functions agree
  have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, 0), |p.1 - w₀| < w₀ / 2 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
    · simp only [Set.mem_ofPred_eq]; rw [sub_self, abs_zero]; linarith
  have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, 0), |p.2| < 1 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
    · simp
  filter_upwards [h1, h2] with p hp1 hp2
  have hpw : 0 < p.1 := by
    have h := abs_lt.mp hp1
    linarith [h.1, h.2, hw₀]
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (p.1, |p.2|) := by
    have h₁ : 0 < p.1 := hpw
    have h₂ : -Real.pi / 2 - 1 < |p.2| := by linarith [abs_nonneg p.2, Real.pi_pos]
    have h₃ : |p.2| < Real.pi / 2 + 1 := by linarith [Real.pi_pos]
    exact ((hsm p.1 |p.2| h₁ h₂ h₃).of_le (by norm_num)).differentiableAt_one
  rw [pdZ_PhiOdd_eq_deriv hsm h0 hpw hp2]
  exact (deriv_slice_eq_fderiv (F := fun x y => Φ x y τ) hd).symm

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.Min.FstarFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


/-!
# `ProfDerivData` for the *finite-order* regularity package `RegPkgMin`

This file proves `Work.FTS_FinalLeaves.profDerivData_min_proved`, the `RegPkgMin`-version of
`Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed`: the seven static derivation fields
of the meridian bridge follow from

* the *finite-order* regularity package `Work.FTS.StrongGlobal.RegPkgMin α g` — whose spatial
  clause is `ContDiffOn ℝ 4` of every slice on the open quadrant, together with the honest
  `ℋ⁴`-membership — and
* the interior `C²`-regularity of the stream function `Φ` on the open quadrant.

The only analytic content (as in the `RegPkg` version) is the two `L₁₂`-facts about the full
profile `F_τ = F_* + g(·,·,τ)`: integrability of the density `L₁₂dens K F_τ` on `(0,∞)` and its
continuity at `z > 0`.  Both are obtained by *additivity* of the density
(`Work.FTS.LocData.L12dens_add_of_integrableOn`) from the two summands:

* the slice `g(·,·,τ)`, where `ContDiffOn ℝ 4` + `HkMem α 4` suffice (the `L₁₂`-facts of the
  open-quadrant finite-order class, proved in sibling modules of the `Pieces` directory);
* the explicit profile `F_* α`, where everything is elementary.

Note the statement carries **no hypothesis** on `α`: `Work.Spaces.c α` may well vanish (it does
for `α ≤ -9/2`, where the integrand of `c` fails to be integrable and Mathlib's total integral
returns `0`), and in that case `F_* α` vanishes identically (because `Γ(θ)/0 = 0`), so the
profile contributes nothing.  The two cases are separated once, in `Fstar_L12_facts`.
-/

/-- `√x ≤ |x| + 1` (local copy of the helper of the same name in `HardyAlt`). -/
theorem sqrt_le_abs_add_one (x : ℝ) : Real.sqrt x ≤ |x| + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [le_abs_self x, abs_nonneg x, sq_abs x, sq_nonneg x]

/-! ## `F_* α` and its `L₁₂`-density

`Work.Construction.Fstar α z θ = α·(Γ(θ)/c α)·2z/(1+z)²`, so its density is the explicit
function `s ↦ α·F_*(s)/s` (`Work.FM.Fstar s = 2s/(1+s)²`) *provided* `c α ≠ 0`; when `c α = 0`
the profile vanishes identically. -/

/-- **The density of `L₁₂` at the profile `F_*`**, in the case `c α ≠ 0`: it is the elementary
function `α·F_*(s)/s`.  This is `Work.Construction.L12dens_Fstar` with the two hypotheses
`0 < α`, `α ≤ 1` — which were only used to supply `c α ≠ 0` — replaced by `c α ≠ 0`. -/
theorem L12dens_Fstar_of_c_ne_zero {α : ℝ} (hc : Work.Spaces.c α ≠ 0) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s
      = α * (Work.FM.Fstar s / s) := by
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

/-- The angular integrand `Γ·K` of the normalisation constant is integrable as soon as
`c α ≠ 0` (Mathlib's total integral vanishes on a non-integrable function). -/
theorem integrableOn_GamK_of_c_ne_zero {α : ℝ} (hc : Work.Spaces.c α ≠ 0) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
  by_contra h
  refine hc ?_
  show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ) = 0
  exact MeasureTheory.integral_undef h

/-- **Integrability of the angular slice of `F_* α`** in the case `c α ≠ 0`: the integrand
`θ ↦ K θ · F_* α z θ / z` is a constant multiple of `Γ·K`, which is integrable by
`integrableOn_GamK_of_c_ne_zero`. -/
theorem Fstar_slice_integrableOn_of_c_ne_zero {α : ℝ} (hc : Work.Spaces.c α ≠ 0) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α z θ / z) Work.Spaces.Iθ := by
  have hKGam := integrableOn_GamK_of_c_ne_zero hc
  intro z hz
  have hconst : MeasureTheory.IntegrableOn
      (fun θ => (α * Work.FM.Fstar z / (z * Work.Spaces.c α))
        * (Work.Spaces.Gam α θ * Work.Spaces.K θ)) Work.Spaces.Iθ :=
    hKGam.const_mul _
  refine hconst.congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Work.Construction.Fstar]
  first | (field_simp; ring) | field_simp

/-- `F_* α` vanishes identically when `c α = 0` (because `Γ(θ)/0 = 0`). -/
theorem Fstar_eq_zero_of_c_eq_zero {α : ℝ} (hc : Work.Spaces.c α = 0) :
    Work.Construction.Fstar α = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Construction.Fstar, hc, div_zero, mul_zero, zero_mul]

/-- **The three `L₁₂`-facts about the profile `F_* α`, for every real `α`**: the angular slice is
integrable for every `z > 0`, the `L₁₂`-density is integrable on `(0,∞)`, and it is continuous at
every `z > 0`.  The case `c α = 0` is degenerate (`F_* α ≡ 0`). -/
theorem Fstar_L12_facts (α : ℝ) :
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α z θ / z) Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Work.Construction.L12dens (Work.Construction.Fstar α)) (Set.Ioi 0)
    ∧ (∀ z : ℝ, 0 < z → ContinuousAt
        (Work.Construction.L12dens (Work.Construction.Fstar α)) z) := by
  by_cases hc : Work.Spaces.c α = 0
  · have h0 : Work.Construction.Fstar α = fun _ _ => 0 := Fstar_eq_zero_of_c_eq_zero hc
    have hden : Work.Construction.L12dens (Work.Construction.Fstar α) = fun _ => (0 : ℝ) := by
      funext s
      rw [Work.Construction.L12dens, Work.FM.L12dens, h0]
      simp
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      have hzero : (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α z θ / z)
          = fun _ => (0 : ℝ) := by
        funext θ; simp only [h0]; ring
      rw [hzero]; exact integrableOn_zero
    · rw [hden]; exact integrableOn_zero
    · intro z hz; rw [hden]; exact continuousAt_const
  · have hsl := Fstar_slice_integrableOn_of_c_ne_zero hc
    have hval : ∀ s : ℝ, Work.Construction.L12dens (Work.Construction.Fstar α) s
        = α * (Work.FM.Fstar s / s) := fun s => L12dens_Fstar_of_c_ne_zero hc s
    -- integrability of the explicit density
    have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => 2 / (1 + s) ^ 2) (Set.Ioi 0) :=
      Work.FTS.MeridianDyn.Bridge.Pieces.integrableOn_two_div_one_add_sq 0 le_rfl
    have hmul : MeasureTheory.IntegrableOn (fun s : ℝ => α * (2 / (1 + s) ^ 2)) (Set.Ioi 0) :=
      hbase.const_mul α
    have hcongr : Set.EqOn (fun s : ℝ => α * (2 / (1 + s) ^ 2))
        (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Set.Ioi 0) := by
      intro s hs
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hkey : Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
        unfold Work.FM.Fstar
        field_simp
      show α * (2 / (1 + s) ^ 2) = α * (Work.FM.Fstar s / s)
      rw [hkey]
    have hint : MeasureTheory.IntegrableOn
        (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Set.Ioi 0) :=
      hmul.congr_fun hcongr measurableSet_Ioi
    refine ⟨hsl, ?_, ?_⟩
    · exact hint.congr_fun (fun s _ => (hval s).symm) measurableSet_Ioi
    · intro z hz
      have hfun : Work.Construction.L12dens (Work.Construction.Fstar α)
          = fun s : ℝ => α * (Work.FM.Fstar s / s) := funext hval
      rw [hfun]
      have hF : ContinuousAt (fun s : ℝ => Work.FM.Fstar s) z := by
        have h1 : ContinuousAt (fun s : ℝ => (2 : ℝ) * s) z :=
          continuousAt_const.mul continuousAt_id
        have h2 : ContinuousAt (fun s : ℝ => ((1 : ℝ) + s) ^ 2) z :=
          (continuousAt_const.add continuousAt_id).pow 2
        have h3 : ((1 : ℝ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
        have h4 : ContinuousAt (fun s : ℝ => (2 : ℝ) * s / (1 + s) ^ 2) z := h1.div h2 h3
        have heq : (fun s : ℝ => (2 : ℝ) * s / (1 + s) ^ 2) = Work.FM.Fstar := rfl
        rwa [heq] at h4
      exact (hF.div continuousAt_id (ne_of_gt hz)).const_mul α

end Work.FTS_FinalLeaves.Min
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.Min.SliceTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Slice differentiability from `ContDiffOn ℝ 4` on the open quadrant -/

/-- A function whose uncurried form is `C⁴` on the open quadrant has `z`-differentiable slices
at every point of the open quadrant. -/
theorem differentiableAt_slice_z_of_contDiffOn {h : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun z' => h z' θ) z := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 4 (Function.uncurry h) (z, θ) :=
    hC.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
  have hfun : (fun z' : ℝ => h z' θ)
      = (Function.uncurry h ∘ fun z' : ℝ => (z', θ)) := by
    funext z'; rfl
  rw [hfun]
  exact (hcd.differentiableAt (by norm_num)).comp z (by fun_prop)

/-- A function whose uncurried form is `C⁴` on the open quadrant has `θ`-differentiable slices
at every point of the open quadrant. -/
theorem differentiableAt_slice_theta_of_contDiffOn {h : ℝ → ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun θ' => h z θ') θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 4 (Function.uncurry h) (z, θ) :=
    hC.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
  have hfun : (fun θ' : ℝ => h z θ')
      = (Function.uncurry h ∘ fun θ' : ℝ => (z, θ')) := by
    funext θ'; rfl
  rw [hfun]
  exact (hcd.differentiableAt (by norm_num)).comp θ (by fun_prop)

/-- `Ftau α g τ = F_* α + slice g τ`, as functions. -/
theorem Ftau_eq_Fstar_add_slice (α : ℝ) (g : Work.FTS.Galerkin.Fam) (τ : ℝ) :
    Work.Construction.Ftau α g τ
      = (fun z θ => Work.Construction.Fstar α z θ + Work.FTS.Galerkin.slice g τ z θ) := by
  funext z θ
  rfl

/-- **The `D_z`/`∂_θ` splitting of `F_τ = F_* + g(τ)` from `C⁴`-regularity of the slice.**

This is `Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split` with the strong hypothesis `RegPkg`
(joint `C^∞`) replaced by the slice's `C⁴`-regularity on the open quadrant, which is exactly the
spatial clause of `RegPkgMin`. -/
theorem Dzg_pthg_split_c4 {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hC : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
          = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            + Work.Spaces.Dz (Work.FTS.Galerkin.slice g τ) z θ) ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
          = Work.Spaces.pth (Work.Construction.Fstar α) z θ
            + Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ) := by
  constructor
  · intro z θ hQd
    obtain ⟨hz, hθ⟩ := hQd
    have hz0 : 0 < z := hz
    have hF : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
      Work.Stability.differentiableAt_Fstar_slice α θ z (by linarith)
    have hg : DifferentiableAt ℝ (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z :=
      differentiableAt_slice_z_of_contDiffOn hC hz hθ
    have hft : (fun z' => Work.Construction.Ftau α g τ z' θ)
        = (fun z' => Work.Construction.Fstar α z' θ)
          + (fun z' => Work.FTS.Galerkin.slice g τ z' θ) := by
      funext z'; rfl
    show z * deriv (fun z' => Work.Construction.Ftau α g τ z' θ) z
        = z * deriv (fun z' => Work.Construction.Fstar α z' θ) z
          + z * deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z
    rw [hft, deriv_add hF hg]
    ring
  · intro z θ hQd
    obtain ⟨hz, hθ⟩ := hQd
    have hF : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
      Work.Stability.differentiableAt_Fstar_slice_theta α z θ hθ
    have hg : DifferentiableAt ℝ (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ :=
      differentiableAt_slice_theta_of_contDiffOn hC hz hθ
    have hft : (fun θ' => Work.Construction.Ftau α g τ z θ')
        = (fun θ' => Work.Construction.Fstar α z θ')
          + (fun θ' => Work.FTS.Galerkin.slice g τ z θ') := by
      funext θ'; rfl
    show deriv (fun θ' => Work.Construction.Ftau α g τ z θ') θ
        = deriv (fun θ' => Work.Construction.Fstar α z θ') θ
          + deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ
    rw [hft, deriv_add hF hg]

/-! ## The derivatives of the singular part `Θ`, with no hypothesis on `α` -/

/-- `∂_θ Θ = (1/(2α))·cos(2θ)·L₁₂(F)`, for **every** real `α` (`α = 0`: both sides vanish).
This is `Work.Construction.pth_Theta_eq` without its `0 < α` hypothesis. -/
theorem pth_Theta_eq_any {α : ℝ} {F : ℝ → ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pth (Work.Construction.Theta α F) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ) * Work.Construction.L12 F z := by
  rcases eq_or_ne α 0 with rfl | hα
  · have h0 : Work.Construction.Theta 0 F = fun _ _ => (0 : ℝ) := by
      funext z θ; simp [Work.Construction.Theta]
    rw [h0]
    simp [Work.Spaces.pth]
  · have hfun : Work.Construction.Theta α F
        = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Real.sin (2 * θ)) := by
      funext z θ
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [hfun, Work.Construction.pth_mul_radial]
    have hsin : deriv (fun t : ℝ => (1 / (4 * α)) * Real.sin (2 * t)) θ
        = (1 / (4 * α)) * (2 * Real.cos (2 * θ)) := by
      rw [deriv_const_mul_field (v := fun s : ℝ => Real.sin (2 * s)) (u := (1 / (4 * α))),
        Work.Construction.deriv_sin_two]
    rw [hsin]
    first | (field_simp; ring) | field_simp | ring

/-- `z∂_z Θ = -(1/(4α))·sin(2θ)·(F,K)`, for **every** real `α` (`α = 0`: both sides vanish).
This is `Work.Construction.Dz_Theta_eq` without its `0 < α` hypothesis. -/
theorem Dz_Theta_eq_any {α z θ : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) (hz : 0 < z) :
    Work.Spaces.Dz (Work.Construction.Theta α F) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK F z := by
  rcases eq_or_ne α 0 with rfl | _hα
  · have h0 : Work.Construction.Theta 0 F = fun _ _ => (0 : ℝ) := by
      funext z θ; simp [Work.Construction.Theta]
    rw [h0]
    simp [Work.Spaces.Dz, Work.Spaces.pz]
  · have hder : HasDerivAt (fun r : ℝ => Work.Construction.L12 F r)
        (-(Work.Construction.L12dens F z)) z :=
      Work.FM.hasDerivAt_L12 hint hcont (by linarith)
    have hfun : Work.Construction.Theta α F
        = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
      funext z θ; rw [Work.Construction.Theta]; ring
    have hpz : Work.Spaces.pz (Work.Construction.Theta α F) z θ
        = -(Work.Construction.L12dens F z) * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
      rw [hfun, Work.Construction.pz_mul_radial, hder.deriv]
    rw [Work.Spaces.Dz, hpz,
      show z * (-(Work.Construction.L12dens F z) * ((1 / (4 * α)) * Work.Construction.s2 θ))
        = -(1 / (4 * α)) * Work.Construction.s2 θ
            * (z * Work.Construction.L12dens F z) by ring,
      Work.Construction.mul_L12dens_eq_FK (ne_of_gt hz)]

/-- The `z`-slice of `Θ α F` is differentiable whenever `L₁₂ F` is, for every real `α`. -/
theorem differentiableAt_Theta_slice_z {α z θ : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Theta α F z' θ) z := by
  rcases eq_or_ne α 0 with rfl | _hα
  · have h0 : Work.Construction.Theta 0 F = fun _ _ => (0 : ℝ) := by
      funext z θ; simp [Work.Construction.Theta]
    rw [h0]
    exact differentiableAt_const 0
  · have hder : HasDerivAt (fun r : ℝ => Work.Construction.L12 F r)
        (-(Work.Construction.L12dens F z)) z :=
      Work.FM.hasDerivAt_L12 hint hcont (by linarith)
    have hfun : Work.Construction.Theta α F
        = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
      funext z θ; rw [Work.Construction.Theta]; ring
    rw [hfun]
    exact (hder.mul_const ((1 / (4 * α)) * Work.Construction.s2 θ)).differentiableAt

/-- The `θ`-slice of `Θ α F` is differentiable everywhere, for every real `α`. -/
theorem differentiableAt_Theta_slice_theta {α z θ : ℝ} {F : ℝ → ℝ → ℝ} :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α F z θ') θ := by
  have hfun : (fun θ' => Work.Construction.Theta α F z θ')
      = fun θ' => ((1 / (4 * α)) * Work.Construction.L12 F z) * Work.Construction.s2 θ' := by
    funext θ'; rw [Work.Construction.Theta]; ring
  rw [hfun]
  have hs : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    show DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ
    fun_prop
  exact hs.const_mul _

end Work.FTS_FinalLeaves.Min
end
