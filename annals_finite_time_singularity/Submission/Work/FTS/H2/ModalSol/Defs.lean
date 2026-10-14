import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.psiTrunc_pair_identities =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false

/-!
# The two diagonal identities for the truncated mode series `psiTrunc`

For `psiTrunc α F N z θ = ∑_{m ≤ N} acoeff α m F z · eFam m θ` (the `N`-th partial sum of the
mode series for `bslOp α Ψ = F`, `FTS/PhiStar/Series/Defs.lean`) and the Dirichlet eigenbasis
`eFam m = cos θ · gC (2m+1)(sin θ)` of `Work.Elliptic.Lzero` with eigenvalues
`lam m = 2m(2m+5)`, the two weighted diagonal identities hold:

* `∫_{Iθ} (psiTrunc …)² cos θ = ∑_{m ≤ N} (∫_{Iθ} eFam m² cos θ) · (acoeff α m F z)²`
  (finite Parseval: expand the square into the double sum and use the orthogonality
  `Gegenbauer.eFam_orthogonal` off the diagonal);
* `∫_{Iθ} (Lzero (psiTrunc …)) · (psiTrunc …) · cos θ
     = ∑_{m ≤ N} lam m · (∫_{Iθ} eFam m² cos θ) · (acoeff α m F z)²`
  (`Lzero` acts diagonally, `Gegenbauer.eFam_Lzero`, and the cross terms die by orthogonality).

Both sides are finite sums, so no measurability, integrability or convergence hypothesis is
needed anywhere: the modes are `C^∞` (`FTS/PhiStar/Series/psiTrunc_solves.lean`, `contDiff_eFam`).
The only analytic bookkeeping is that `Lzero`'s `tan θ`-term needs `cos θ ≠ 0`, which holds on
`Iθ` except at the single null point `θ = π/2` (`cos_ne_zero_of_mem_Iθ`, `ae_ne_pi_half_volume`).

The two independent bricks are `PairIdent.eFam_finSum_bilin` (bilinear finite Parseval for the
basis, any coefficients) and `PairIdent.lzero_finSum_eFam` (the pointwise diagonal action of
`Lzero` on an arbitrary finite mode combination).
-/

/-- On `Iθ = [0, π/2]` the only zero of `cos` is the right endpoint, so away from `π/2` the
cosine does not vanish.  This is the hypothesis under which the eigenfunction identity
`Gegenbauer.eFam_Lzero` is available. -/
lemma cos_ne_zero_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : θ ≠ Real.pi / 2) :
    Real.cos θ ≠ 0 := by
  have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 h
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩)

/-- The single point `π/2` is null, so `cos θ ≠ 0` holds almost everywhere on `Iθ`. -/
lemma ae_ne_pi_half_volume : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  have h : {θ : ℝ | ¬ θ ≠ Real.pi / 2} = ({Real.pi / 2} : Set ℝ) := by ext θ; simp
  rw [h]
  exact MeasureTheory.measure_singleton _


end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.pzMoment_le_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the radial weight `w` -/

/-- The radial weight `w(z) = (1+z)²/z²` is positive for `z > 0`. -/
theorem w_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Work.Spaces.w s := by
  rw [Work.Spaces.w]
  positivity

/-- `s·w(s) = (1+s)²/s ≥ 1` for `s > 0`: the factor by which the Cauchy–Schwarz step
overcounts is bounded by `1`. -/
theorem one_le_mul_w {s : ℝ} (hs : 0 < s) : 1 ≤ s * Work.Spaces.w s := by
  have hsw : s * Work.Spaces.w s = (1 + s) ^ 2 / s := by
    rw [Work.Spaces.w]
    field_simp
  rw [hsw, le_div_iff₀ hs]
  nlinarith [sq_nonneg s]

/-! ## Cauchy–Schwarz in square-root form -/

/-- The Cauchy–Schwarz inequality for the Bochner integral in its `√`-form. -/
theorem abs_setIntegral_mul_le_sqrt {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MemLp u 2 (volume.restrict s)) (hv : MemLp v 2 (volume.restrict s)) :
    |∫ x in s, u x * v x| ≤ Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := by
  have hcs := Work.Spaces.cs_integral hu hv
  have hA : 0 ≤ ∫ x in s, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  calc |∫ x in s, u x * v x| = Real.sqrt ((∫ x in s, u x * v x) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x in s, u x ^ 2) * (∫ x in s, v x ^ 2)) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := Real.sqrt_mul hA _

/-! ## The two Cauchy–Schwarz factors -/

/-- The `L²`-factor carrying `D_z f = z ∂_z f`; its square is a summand of `HkIntegrand`. -/
def slU (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun θ => Work.Spaces.DzIter 1 f s θ
    * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))

/-- The dual `L²`-factor, carrying the profile `sinθcos²θ` and the reciprocal weight. -/
def slV (_f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ
    / Work.Spaces.w s

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On the open interval the two factors multiply back to `D_z f · sinθcos²θ`. -/
theorem slU_mul_slV {f : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    slU f s θ * slV f s θ = Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ := by
  have hx : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _)
  have hW : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos_of_pos hs)
  have hcancel : (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w s) = 1 := by
    field_simp
  calc slU f s θ * slV f s θ
      = (Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ)
        * ((Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w s)) := by
        simp only [slU, slV]; ring
    _ = Work.Spaces.DzIter 1 f s θ * Work.Elliptic.sinCos2 θ := by rw [hcancel, mul_one]

/-- The dual factor is bounded by `1/w(s)` in absolute value on the open interval:
`sin(2θ)^{η/2} ≤ 1` and `|sinθcos²θ| ≤ 1`. -/
theorem slV_sq_le {f : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (slV f s θ) ^ 2 ≤ (1 / Work.Spaces.w s) ^ 2 := by
  have hx : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hsp : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hx) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hc : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
    Work.FTS.EllipticEst.abs_sinCos2_le_one ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hprod : |(Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx) _)]
    simpa using mul_le_mul hsp hc (abs_nonneg _) zero_le_one
  have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      * Work.Elliptic.sinCos2 θ) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hprod
  have hW2 : 0 < (Work.Spaces.w s) ^ 2 := pow_pos (w_pos_of_pos hs) 2
  simp only [slV, div_pow, one_pow]
  exact div_le_div_of_nonneg_right hsq (le_of_lt hW2)

/-! ## Continuity of the two factors on the open interval -/



theorem continuousOn_slV (f : ℝ → ℝ → ℝ) (s : ℝ) :
    ContinuousOn (slV f s) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
  have hcos : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      Real.continuous_sin.continuousOn.mul ((Real.continuous_cos.continuousOn).pow 2)
    exact h.congr (fun θ _ => rfl)
  exact (hrpow.mul hcos).div_const (Work.Spaces.w s)

/-! ## The moment bound -/


end Work.FTS.CoercivityFix.Coer1T.Hardy
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HalfSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The half-strip smoothness class of the `ℛ`-transfer.**  A function `f` is `SmoothHalf` if

* every angular slice `θ ↦ f z θ` with `z ∈ [0,∞)` is smooth on an open neighbourhood of
  `[0, π/2]` (`Work.FTS.EllipticEst.SliceSmooth`);
* `f` is jointly `C^∞` on the half-strip `z > 0`, `θ ∈ (-1, π/2+1)`.

This is weaker than `Work.Spaces.SmoothNbhd` (which also demands smoothness on `z < 0`) and is
exactly what the slicewise Hardy/Poincaré estimates use.  In particular it is satisfied by
`Ξ = Work.Elliptic.EllResid α F Ψ` for the data of `EllHyp α k F Ψ`. -/
def SmoothHalf (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, SliceSmooth (fun θ => f z θ)) ∧
    ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))

/-- `SmoothHalf` implies smoothness on the open quadrant. -/
theorem SmoothHalf.smoothOpen {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) : SmoothOpen f := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Q0
  refine (h.2.mono ?_).of_le le_top
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  exact ⟨hz, by linarith, by linarith [Real.pi_pos]⟩


/-- The `θ`-slice of a `SmoothHalf` function, at every `z ∈ [0,∞)`. -/
theorem SmoothHalf.slice {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    SliceSmooth (fun θ => f z θ) := h.1 z hz




end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ang_a_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.ang_a_weak` — the angular (mixed) part of the level-`2` estimate for `A = z²∂_z²Ψ`

Target (`Work.FTS.EllipticEst.TT.ang_a_weak`): there is a universal `C > 0` with

```
∀ α F Ψ, 0 < α → α ≤ 1/4 → EllWeakPos α 2 F Ψ →
  α⁴ · ( |D_θ A · Wt α|²_{L²} + |D_z D_θ A · Wt α|²_{L²} + |D_θ² A · Wt α|²_{L²} ) ≤ C · |F|²_{ℋ²}
```

where `A := z²∂_z²Ψ = D_z²Ψ - D_zΨ` and `Wt α = w · sin(2θ)^{-γ/2}`.  The left-hand side is
exactly the *mixed* (`i ≥ 1`) part of `HkSq α 2 A`; the pure (`D_z`-only) part of that norm is
handled elsewhere (`est_two_weak`'s `pure_two_weak`).

## The identities provided here

Writing the equation `bslOp α Ψ = F` in the `D_z`-form
`-α²D_z²Ψ - 5αD_zΨ + LzeroΨ = F` (valid because `-(α²z²)∂_z²Ψ = -α²(D_z²Ψ - D_zΨ)`):

* `DzIter_two_split` : `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open quadrant;
* `Lzero_eq_of_bsl` : `Lzero1 Ψ = F + α² D_z²Ψ + 5α D_zΨ` on the open quadrant.

The `θ`-derivative of the second identity,
`∂_θ(Lzero1 Ψ) = ∂_θF + α² D_z²(∂_θΨ) + 5α D_z(∂_θΨ)`
(equivalently `D_θ(Lzero1 Ψ) = D_θF + α² D_z²(D_θΨ) + 5α D_z(D_θΨ)`), together with
`α²A = Lzero1 Ψ - F - α(5+α)D_zΨ`, is what reduces every term of the target to

* a component of `|F|_{ℋ²}` (`D_θF`, `D_θ²F`, `D_zD_θF`), or
* a *slice* quantity controlled by the level-`0` (`η`-weighted) estimate for the data
  `(D_z^jΨ, D_z^jF)`, `j ≤ 2`, and for the datum `A`,
* or a term carrying an extra factor `α`.

Those level-`0` estimates are the content of `H2W/level0Ae` (the paper's Steps 1–3 of
`prop:H2`; its three inputs are delegated to `AngAWeak/step1Ae`, `AngAWeak/step2Ae`,
`AngAWeak/step3Ae`), and are *not* part of this file.
-/

noncomputable section

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The angular operator of a `z`-slice is the corresponding slice of `Work.Elliptic.Lzero`. -/
theorem Lzero1_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := rfl

/-- The elementary split `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open quadrant (product rule for
`z ↦ z ∂_zΨ`). -/
theorem DzIter_two_split {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
  have hderiv : deriv (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ) z
      = Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ := by
    have h := ((hasDerivAt_id z).mul (hsm.hasDerivAt_slice_pzIter 1 hθ hz)).deriv
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ)
        = (id * fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ) := by
      funext z'
      simp only [Pi.mul_apply, id_eq]
      rfl
    rw [hfun, h]
    simp only [id_eq, one_mul]
    rfl
  have hfun : (fun z' : ℝ => Work.Spaces.Dz Ψ z' θ)
      = fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ := rfl
  show z * deriv (fun z' : ℝ => Work.Spaces.Dz Ψ z' θ) z
      = z * Work.Spaces.pz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
  rw [hfun, hderiv]
  ring

/-- **The equation in the `D_z`-form.**  On the open quadrant the `θ`-slice equation
`bslOp α Ψ = F` reads `Lzero1 Ψ = F + α² D_z²Ψ + 5α D_zΨ`. -/
theorem Lzero_eq_of_bsl {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = F z θ + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ + 5 * α * Work.Spaces.Dz Ψ z θ := by
  intro z hz θ hθ0 hθ1
  have hsplit := DzIter_two_split hsm hz ⟨hθ0, hθ1⟩
  have heq := hEq z hz θ hθ0 hθ1
  rw [Work.Elliptic.bslOp_apply] at heq
  have hDz1 : Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ := rfl
  have hL : Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + α * (5 + α) * (z * Work.Spaces.pz Ψ z θ) := by linarith [heq]
  rw [Lzero1_slice_eq, hL, hsplit, hDz1]
  ring


/-- `∂_θ` commutes with `D_z` on the open quadrant. -/
theorem pth_Dz_eq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)))
  show deriv (fun θ' => z * Work.Spaces.pz f z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ
  rw [deriv_const_mul_field]
  change z * Work.Spaces.pth (Work.Spaces.pz f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ
  rw [(Work.Spaces.pz_pth_comm hcd).symm]




end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.SliceDerivSelfOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-- If a `C^∞` slice takes the same value at the two endpoints `0` and `π/2`, then its
derivative vanishes somewhere in `Iθ = [0, π/2]` (Rolle / Lagrange mean value theorem). -/
private lemma deriv_zero_exists_of_endpoints {u : ℝ → ℝ} (hsm : SliceSmoothO u)
    (h0 : u 0 = u (Real.pi / 2)) : ∃ θ₀ ∈ Work.Spaces.Iθ, deriv u θ₀ = 0 := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub2 : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  have hle : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcont : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := hsm.continuousOn.mono hsub
  have hdiff : DifferentiableOn ℝ u (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.differentiableOn (by norm_num)).mono hsub2
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hle hcont hdiff
  refine ⟨c, ⟨le_of_lt hc.1, le_of_lt hc.2⟩, ?_⟩
  rw [hcd]
  have hz : u (Real.pi / 2) - u 0 = 0 := by rw [← h0]; ring
  simp [hz]

/-- The second derivative of a `C^∞` slice is continuous on `Iθ`. -/
private lemma sliceV_continuousOn {u : ℝ → ℝ} (hsm : SliceSmoothO u) :
    ContinuousOn (sliceV u) Work.Spaces.Iθ := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub

/-- If the derivative of a `C^∞` slice vanishes at some `θ₀ ∈ Iθ`, then everywhere on `Iθ`
the derivative is bounded by the full integral of `|u''|` over `Iθ` (fundamental theorem of
calculus plus the triangle inequality for the integral). -/
private lemma abs_deriv_le_integral_abs_sliceV {u : ℝ → ℝ} (hsm : SliceSmoothO u) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Work.Spaces.Iθ) (hz : deriv u θ₀ = 0) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |deriv u θ| ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (sliceV u) Work.Spaces.Iθ := sliceV_continuousOn hsm
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |sliceV u x|)
      = ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  have hgi : IntervalIntegrable (fun x => |sliceV u x|) volume 0 (Real.pi / 2) :=
    hcont.abs.intervalIntegrable_of_Icc hle
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ₀
  have huIcc : Set.uIcc θ₀ θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hθ₀.1 h1, le_trans h2 hθ.2⟩
    · exact ⟨le_trans hθ.1 h1, le_trans h2 hθ₀.2⟩
  have hFTC : (∫ x in θ₀..θ, sliceV u x) = deriv u θ - deriv u θ₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hd1.mono (huIcc.trans hsub))
  have hvaleq : deriv u θ = ∫ x in θ₀..θ, sliceV u x := by
    rw [hFTC, hz, sub_zero]
  rw [hvaleq]
  rcases le_total θ₀ θ with hle2 | hle2
  · have h1 : |∫ x in θ₀..θ, sliceV u x| ≤ ∫ x in θ₀..θ, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ₀..θ, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ₀.1 hle2 hθ.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · have hsym : (∫ x in θ₀..θ, sliceV u x) = -(∫ x in θ..θ₀, sliceV u x) :=
      intervalIntegral.integral_symm ..
    have h1 : |∫ x in θ..θ₀, sliceV u x| ≤ ∫ x in θ..θ₀, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ..θ₀, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ.1 hle2 hθ₀.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [hsym, abs_neg]
    linarith

/-- Boundary (FTC) bound for the first derivative of a `C^∞` slice with equal endpoint values,
with `A = ∫_{Iθ} (u'')² sin(2θ)^{-η}`:

`(∂_θ u θ)² ≤ A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

This is `Work.FTS.EllipticEst.slice_deriv_sq_le` with the analytic class `SliceSmooth` replaced
by the honest `C^∞` class `SliceSmoothO`. -/
theorem slice_deriv_sq_le_open {u : ℝ → ℝ} (hsm : SliceSmoothO u)
    (h0 : u 0 = u (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  -- Rolle: pick `θ₀ ∈ Iθ` with `deriv u θ₀ = 0` (the mean value theorem, since `u` has the
  -- same value at `0` and `π/2`).
  obtain ⟨θ₀, hθ₀, hz⟩ := deriv_zero_exists_of_endpoints hsm h0
  -- Cauchy–Schwarz on the slice, with the second derivative as the `g` of `slice_cs_weighted`.
  have hvcont : ContinuousOn (sliceV u) Work.Spaces.Iθ := sliceV_continuousOn hsm
  have hcs := Work.FTS.EllipticEst.slice_cs_weighted (g := sliceV u) hvcont hint
  intro θ hθ
  -- FTC from `θ₀` to `θ`: `deriv u θ = ∫_{θ₀}^{θ} u''`, hence `|deriv u θ| ≤ ∫_{Iθ} |u''|`.
  have habs := abs_deriv_le_integral_abs_sliceV hsm hθ₀ hz θ hθ
  have hsq : (deriv u θ) ^ 2 ≤ (∫ x in Work.Spaces.Iθ, |sliceV u x|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  linarith [hcs, hsq]

/-- **Boundary bound for a `C^∞` slice vanishing at both angular endpoints.**  With
`A = ∫_{Iθ} (u'')² sin(2θ)^{-η}` (an honest finite number by the hypothesis),

`(u θ)² ≤ (π/2)² · A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

This is `Work.FTS.EllipticEst.Blocks.slice_self_sq_le` with the analytic class `SliceSmooth`
replaced by the honest `C^∞` class `SliceSmoothO`, and calling the `C^∞` version
`slice_deriv_sq_le_open` above. -/
theorem slice_self_sq_le_open {u : ℝ → ℝ} (hsm : SliceSmoothO u)
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2
      ≤ (Real.pi / 2) ^ 2 * ((∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
  -- The slice vanishes at both angular endpoints, so `slice_deriv_sq_le_open` (proved for equal
  -- endpoint values) bounds `(∂_θ u)²` by `A · ∫ sin(2θ)^η` on all of `Iθ`.
  have hend : u 0 = u (Real.pi / 2) := by rw [h0, h1]
  have hderiv := slice_deriv_sq_le_open hsm hend hint
  -- `u` is `C¹` on a neighbourhood of `Iθ`, hence on every sub-interval `uIcc 0 θ`.
  have hcd : ContDiffOn ℝ 1 u (Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm.of_le 1
  intro θ hθ
  have hθI := hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
  have hθ0 : (0 : ℝ) ≤ θ := hθI.1
  have hθpi : θ ≤ Real.pi / 2 := hθI.2
  -- abbreviations for the two integrals of the statement
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hx))
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hx) _)
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  -- pointwise bound for the first derivative on `Iθ`
  have hderivAB : ∀ x ∈ Work.Spaces.Iθ, (deriv u x) ^ 2 ≤ A * B := hderiv
  have hpoint : ∀ x ∈ Work.Spaces.Iθ, |deriv u x| ≤ Real.sqrt (A * B) := fun x hx =>
    Real.abs_le_sqrt (hderivAB x hx)
  -- fundamental theorem of calculus: `u θ = ∫_0^θ ∂_θ u` (and `u 0 = 0`)
  have huIcc : Set.uIcc (0 : ℝ) θ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hFTC : (∫ x in (0 : ℝ)..θ, deriv u x) = u θ - u 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono huIcc)
  have hu_eq : u θ = ∫ x in (0 : ℝ)..θ, deriv u x := by rw [hFTC, h0]; ring
  -- the integral is bounded by the length of the interval times the pointwise bound
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) θ, ‖deriv u x‖ ≤ Real.sqrt (A * B) := by
    intro x hx
    rw [Set.mem_uIoc] at hx
    have hxI : x ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_of_lt h1, le_trans h2 hθpi⟩
      · exact ⟨le_trans hθ0 (le_of_lt h1), by linarith [h2, Real.pi_pos]⟩
    rw [Real.norm_eq_abs]
    exact hpoint x hxI
  have hnorm : ‖∫ x in (0 : ℝ)..θ, deriv u x‖ ≤ Real.sqrt (A * B) * |θ - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have habs : |u θ| ≤ Real.sqrt (A * B) * (Real.pi / 2) := by
    have h1' : ‖u θ‖ ≤ Real.sqrt (A * B) * |θ - 0| := by
      rw [hu_eq]; exact hnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ0), sub_zero] at h1'
    exact le_trans h1' (mul_le_mul_of_nonneg_left hθpi (Real.sqrt_nonneg _))
  have hsq : (u θ) ^ 2 ≤ (Real.sqrt (A * B) * (Real.pi / 2)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc (u θ) ^ 2 ≤ (Real.sqrt (A * B) * (Real.pi / 2)) ^ 2 := hsq
    _ = (Real.sqrt (A * B)) ^ 2 * (Real.pi / 2) ^ 2 := by ring
    _ = (A * B) * (Real.pi / 2) ^ 2 := by rw [Real.sq_sqrt hAB]
    _ = (Real.pi / 2) ^ 2 * (A * B) := by ring

end Work.FTS.EllipticEst.ThetaU
end
-- ===== merged: Submission.Work.FTS.H2.ModalSol.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol

set_option autoImplicit false

/-! ## The witness of the existence statement -/

/-- **The modal weak solution**: the limit of the partial sums of the mode series
`Σ_m acoeff α m F z · eFam m θ` (with the junk value `sInf ∅ = 0` where the limit does not
exist — on the open quadrant it always does). -/
def Psi (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  sInf {l : ℝ | Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
    Filter.atTop (nhds l)}

/-- The defining property of `Psi`: a converging sequence of partial sums has `Psi` as its
limit. -/
theorem Psi_eq_of_tendsto {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ l : ℝ}
    (hl : Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds l)) : Psi α F z θ = l := by
  have hset : {l' : ℝ | Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds l')} = {l} := by
    ext l'
    constructor
    · intro h'
      exact tendsto_nhds_unique h' hl
    · intro h'
      rw [Set.mem_singleton_iff] at h'
      rw [h']
      exact hl
  rw [Psi, hset, csInf_singleton]

/-- From the Cauchy property of the partial sums, `Psi` is their limit. -/
theorem Psi_tendsto_of_cauchy {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hC : CauchySeq (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)) :
    Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds (Psi α F z θ)) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hC
  rw [Psi_eq_of_tendsto hl]
  exact hl

/-! ## The Dirichlet values -/

/-- The angular modes vanish at `θ = 0`. -/
theorem psiTrunc_apply_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α F N z 0 = 0 := by
  rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_eq_zero]
  intro m _
  have h3 : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
    have h4 : Work.FTS.PhiStar.Gegenbauer.eFam m 0
        = Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0 := by
      simp [Work.FTS.PhiStar.Gegenbauer.eFam]
    rw [h4, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]
  rw [h3, mul_zero]

/-- The angular modes vanish at `θ = π/2`. -/
theorem psiTrunc_apply_pi_half (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α F N z (π / 2) = 0 := by
  rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_eq_zero]
  intro m _
  have h3 : Work.FTS.PhiStar.Gegenbauer.eFam m (π / 2) = 0 := by
    simp [Work.FTS.PhiStar.Gegenbauer.eFam]
  rw [h3, mul_zero]

/-- `Psi` vanishes at `θ = 0` (for every `z`). -/
theorem Psi_apply_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : Psi α F z 0 = 0 := by
  refine Psi_eq_of_tendsto ?_
  have h : (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z 0) = fun _ => (0 : ℝ) :=
    funext (fun N => psiTrunc_apply_zero α F N z)
  rw [h]
  exact tendsto_const_nhds

/-- `Psi` vanishes at `θ = π/2` (for every `z`). -/
theorem Psi_apply_pi_half (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : Psi α F z (π / 2) = 0 := by
  refine Psi_eq_of_tendsto ?_
  have h : (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z (π / 2)) = fun _ => (0 : ℝ) :=
    funext (fun N => psiTrunc_apply_pi_half α F N z)
  rw [h]
  exact tendsto_const_nhds

/-! ## A box around a compact subset of the quadrant -/

/-- A nonempty compact subset of the open quadrant is contained in a product of closed
intervals which is itself contained in the open quadrant. -/
theorem exists_box_of_isCompact_subset_Q0 {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (hsub : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ d < π / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  have hfst : ∀ p ∈ K, (0 : ℝ) < p.1 := fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp (hsub hp)).1
  have hsnd0 : ∀ p ∈ K, (0 : ℝ) < p.2 :=
    fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp (hsub hp)).2.1
  have hsnd1 : ∀ p ∈ K, p.2 < π / 2 :=
    fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp (hsub hp)).2.2
  obtain ⟨a, ha0, ha⟩ := hK.exists_forall_le' continuous_fst.continuousOn hfst
  obtain ⟨c, hc0, hc⟩ := hK.exists_forall_le' continuous_snd.continuousOn hsnd0
  obtain ⟨pz, hpzK, hpzg⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  obtain ⟨pθ, hpθK, hpθg⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
  obtain ⟨p, hpK⟩ := hne
  refine ⟨a, pz.1, c, pθ.2, ha0, ha pz hpzK, hc0, hc pθ hpθK,
    lt_of_le_of_lt (hpθg hpθK) (hsnd1 pθ hpθK), ?_⟩
  intro q hq
  exact ⟨⟨ha q hq, hpzg hq⟩, ⟨hc q hq, hpθg hq⟩⟩

end Work.FTS.H2.ModalSol
end
end
