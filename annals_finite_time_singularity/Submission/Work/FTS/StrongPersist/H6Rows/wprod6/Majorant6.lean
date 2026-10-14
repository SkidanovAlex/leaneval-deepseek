import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp slicewise Hardy inequality for `U = z∂_zu` in the class `AeData`

The target `Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae`: for a datum
`h : H2W.Ae.AeData α u G` and the two `ℋ⁰`-honesties of the slots

* `U u = z ∂_z u` (`Work.FTS.EllipticEst.AeI1Fts.U`, definitionally `H2W.Ae.grad u`) and
* `V u = z ∂_z ∂_θ u` (`Work.FTS.EllipticEst.AeI1Fts.V`, the Clairaut twin of `∂_θ(U u)`),

one has, for almost every `z > 0`,

`∫_θ U² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_θ V² sin(2θ)^{-η}`,

with the *sharp* constant `(1+η)^{-2}` (`η = Work.Spaces.eta = 99/100`) and no correction term.

This is exactly the hypothesis `hsl` of `H2W.SlotA.weightedNLePp` (the `z`-integration step of
the `I₁` chain) — the slicewise input that `N_bound` (`40000`) does *not* provide.

## Proof

At a.e. `z > 0`:

* `N_bound h hV` supplies the integrability of the left-hand integrand of the slice (`hintN`);
* `HkMem α 0 (U u)` gives `∫_θ U² sin(2θ)^{-η} < ∞` (`hintA`), `HkMem α 0 (V u)` gives
  `∫_θ (∂_θU)² sin(2θ)^{-η} < ∞` (`hintD`, using `slice_deriv_eq` to replace `∂_θ(U u z ·)` by
  `V u z ·`);
* the cross term `∫_θ |U ∂_θU cos(2θ) sin(2θ)^{-1-η}|` is dominated pointwise by
  `(U² cos²(2θ) sin(2θ)^{-(2+η)} + (∂_θU)² sin(2θ)^{-η})/2` (AM–GM after splitting
  `sin^{-1-η} = sin^{-(2+η)/2}·sin^{-η/2}`), hence integrable (`hintC`).

Then `H2W.SlotA.sharpHardyCosWeight_open` — the completion-of-squares / θ-IBP Hardy inequality
on the *open* interval, whose four integrability hypotheses are precisely `hintA`, `hintC`,
`hintN`, `hintD` — gives the claim, with `∂_θU` rewritten back to `V` a.e.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Slice integrability: `∫_θ f² σ < ∞` from `HkMem α 0 f` -/



/-! ## The cross term -/


/-! ## The target -/


end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.AeW2SliceBundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeW2SliceBundle` — the a.e. slice integrability bundle of the level-`0` a.e. class

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate,
for almost every `z > 0` the six angular fibres occurring in the truncated level-`0` energy
identity are integrable on `Iθ = [0,π/2]`:

`bslOp α u · u`, `Lzero u · u`, `∂_zzu · u`, `∂_zu · u`, `(z ∂_zu)²`, `u²`.

The proof is *pointwise in `z`* (the a.e. statement is therefore immediate): for `z > 0`

* the unweighted angular squares of `u`, `∂_zu` and `∂_zzu` are integrable because
  `HkMem α 0` of `u` (`Dispatch.hkMem_uM`), of `z ∂_zu` (`Dispatch.hkMem_gradUD`) and of
  `z²∂_zzu` (a field of `AeData`) gives the *weighted* integrability
  (`AngAWeak.integrableOn_slice_sq_mul_w_sq`), and the weight `w z ≠ 0` may be divided out;
  `G` is the same with the field `AeData.memG`;
* the products `G·u`, `(∂_zu)·u`, `(∂_zzu)·u` follow from `2|XY| ≤ X² + Y²` and the continuity
  of the slices on the open angular interval;
* `Lzero u · u` is *not* obtained from the `tan θ`-form of `Lzero` (whose middle term is not
  controlled by the available squares) but from the identity
  `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu` on the open quadrant, which is `bslOp α u = G`
  (`AeData.eq`) rearranged;
* `bslOp α u · u` agrees with `G·u` on *all* of `Iθ`, since at the two endpoints the factor `u`
  vanishes (`AeData.dirZero`, `AeData.dirPi`) so both products are `0`.
-/

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter

set_option autoImplicit false

/-- The unweighted angular square of a level-`0` honest function is integrable on `Iθ`, for
`z > 0`: divide the weight `(w z)²` out of `AngAWeak.integrableOn_slice_sq_mul_w_sq`. -/
private theorem aew2_integrableOn_sq_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_mul_w_sq hmem (le_of_lt hz)).1.congr_fun
      (fun θ _ => by ring) measurableSet_Icc
  exact Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const hw h1

/-- `AM–GM` for a product of two functions whose angular squares are integrable. -/
private theorem aew2_integrableOn_mul_of_sq {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => f θ * g θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((hf.add hg).const_mul (1 / 2)) hmeas ?_
  filter_upwards with θ
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ)]

/-- A function continuous on the **open** quadrant has an a.e. strongly measurable angular
slice at every `z > 0`. -/
private theorem aew2_aesm_slice {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.AngAWeak.Qd) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.FTS.EllipticEst.AngAWeak.aestronglyMeasurable_of_continuousOn_Ioo <| by
    have hc : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry f p)
        Work.FTS.EllipticEst.AngAWeak.Qd := hf
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => Work.FTS.EllipticEst.AngAWeak.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)

end Work.FTS.EllipticEst.Cores.Pieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeTruncSigmaIdD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `w²` is `C²` on `(0,∞)`. -/
theorem wsq_contDiffOn_two : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp [Work.Spaces.w]
  rw [hfun]
  refine ContDiffOn.pow (ContDiffOn.div ?_ ?_ ?_) 2
  · fun_prop
  · fun_prop
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

/-- `w²` is continuous on `(0,∞)`. -/
theorem wsq_continuousOn : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
  (wsq_contDiffOn_two).continuousOn

/-- **The `σ`-θ-weighted truncated radial energy identity** (the `G`-form of
`truncRadialIbpTheta`).  For data in the almost-everywhere class, a `C²` cut-off `χ` supported in
`[a,b] ⊂ (0,∞)` with `0 ≤ χ ≤ 1`, and with `ω = χ·w²`,

`∫_z ω ∫_θ σ (G·u) = α²∫_z ω ∫_θ σ (z∂_zu)² + ∫_z ω ∫_θ σ ((Lzero u)·u)
   - (α²/2)∫_z (z²ω)'' ∫_θ σ u² + ((α(5+α))/2)∫_z (zω)' ∫_θ σ u²`,

`σ = sin(2θ)^{-η}`.  This is `truncRadialIbpTheta` combined with the equation
`bslOp α u = -(α²z²)∂_zzu - α(5+α)z∂_zu + Lzero u = G` on the open quadrant. -/
theorem aeTruncSigmaIdD (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (χ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hχ : ContDiff ℝ 2 χ)
    (hχsupp : ∀ z, z ∉ Set.Icc a b → χ z = 0)
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) :
    (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * Work.FTS.EllipticEst.sEta θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ))
        + (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ
                * Work.FTS.EllipticEst.sEta θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hUsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
  have hGsm : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hUsm)
      (fun z θ hz hθ1 hθ2 => hA.eq z hz θ hθ1 hθ2)
  -- the weight `ω = χ w²`
  have hωd : ContDiffOn ℝ 2 (fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (hχ.contDiffOn).mul wsq_contDiffOn_two
  have hωsupp : ∀ z, z ∉ Set.Icc a b → χ z * (Work.Spaces.w z) ^ 2 = 0 := by
    intro z hz
    rw [hχsupp z hz, zero_mul]
  have hωbdd : ∀ z, |χ z * (Work.Spaces.w z) ^ 2| ≤ (Work.Spaces.w z) ^ 2 := by
    intro z
    rw [abs_mul, abs_of_nonneg (hχ01 z).1, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
    calc χ z * (Work.Spaces.w z) ^ 2 ≤ 1 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hχ01 z).2 (sq_nonneg _)
      _ = (Work.Spaces.w z) ^ 2 := by ring
  -- the pointwise (a.e. on the quadrant) split `G u = (Lzero u) u - P u`
  have hsplit_pt : ∀ᵐ p ∂nuFts, G p.1 p.2 * u p.1 p.2
      = Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2
        - ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2) := by
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have heq := hA.eq p.1 hp1 p.2 hp2.1 hp2.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hG : G p.1 p.2 = Work.Elliptic.Lzero u p.1 p.2
        - (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) := by linarith [heq]
    rw [hG]; ring
  -- the three joint integrands (`nuFts`-integrable)
  have hIP : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
        + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts :=
    (tRibp_integrablePair (α := α) (u := u) (fun z => χ z * (Work.Spaces.w z) ^ 2) ha hab
      hA.smooth hgrad hA.memRad2 hu hωd hωsupp hωbdd).1
  have hIcont : ContinuousOn (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) (tRibp_continuousOn_sEta.mul
      (hGsm.continuousOn.mul hUsm.continuousOn))
    · exact (hχ.continuous).continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · exact wsq_continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hIG : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 G p.1 p.2) nuFts :=
    integrable_HkIntegrand_of_smoothOpen hGsm hA.memG
  have hIU : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 u p.1 p.2) nuFts :=
    integrable_HkIntegrand_of_smoothOpen hUsm hu
  have hIGU : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2))) nuFts := by
    refine ((hIG.add hIU).const_mul (1 / 2)).mono'
      (aesm_prod_of_continuousOn_Q0 hIcont) ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hσ : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    obtain ⟨z, θ⟩ := p
    have h1 : |χ z * (Work.Spaces.w z) ^ 2| ≤ (Work.Spaces.w z) ^ 2 := hωbdd z
    have h2 : |Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)|
        ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
      have h3 : |G z θ * u z θ| ≤ (1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) := by
        have h := abs_mul (G z θ) (u z θ)
        nlinarith [sq_nonneg (|G z θ| - |u z θ|), sq_abs (G z θ), sq_abs (u z θ), h]
      rw [abs_mul, abs_of_nonneg hσ]
      calc Work.FTS.EllipticEst.sEta θ * |G z θ * u z θ|
          ≤ Work.FTS.EllipticEst.sEta θ * ((1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 hσ
        _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |χ z * (Work.Spaces.w z) ^ 2| *
          |Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)|
        ≤ (Work.Spaces.w z) ^ 2 * ((1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (sq_nonneg _)
      _ = 1 / 2 * (Work.Spaces.HkIntegrand α 0 G z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) := by
          rw [HkIntegrand_zero_D α G hθ, HkIntegrand_zero_D α u hθ]; ring
  -- `fL = fG + fP` a.e.
  have hIL : MeasureTheory.Integrable (fun p : ℝ × ℝ => χ p.1 * (Work.Spaces.w p.1) ^ 2 *
      (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) nuFts := by
    refine (hIGU.add hIP).congr ?_
    filter_upwards [hsplit_pt] with p hp
    simp only [Pi.add_apply]
    rw [hp]
    ring
  -- the split at the level of the double integral
  have hsplit_double : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)) ∂nuFts)
      = (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
          (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)) ∂nuFts)
        - (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
          (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)) ∂nuFts) := by
    have h1 : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
          (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)) ∂nuFts)
        = ∫ p, (χ p.1 * (Work.Spaces.w p.1) ^ 2 *
              (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))
            - χ p.1 * (Work.Spaces.w p.1) ^ 2 *
              (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2
                * Work.Spaces.pzIter 2 u p.1 p.2
                + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) ∂nuFts := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hsplit_pt] with p hp
      rw [hp]; ring
    rw [h1, MeasureTheory.integral_sub hIL hIP]
  -- the iterated form of each double integral
  have hnuG : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * (G p.1 p.2 * u p.1 p.2)) ∂nuFts)
      = ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)) := by
    rw [show nuFts = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl]
    rw [MeasureTheory.integral_prod _ hIGU]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          χ z * (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)) from by
      funext z
      exact MeasureTheory.integral_const_mul _ _]
  have hnuL : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)) ∂nuFts)
      = ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)) := by
    rw [show nuFts = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl]
    rw [MeasureTheory.integral_prod _ hIL]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          χ z * (Work.Spaces.w z) ^ 2
            * (Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)) from by
      funext z
      exact MeasureTheory.integral_const_mul _ _]
  have hnuP : (∫ p, χ p.1 * (Work.Spaces.w p.1) ^ 2 *
        (Work.FTS.EllipticEst.sEta p.2 * ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)) ∂nuFts)
      = ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)) := by
    rw [show nuFts = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl]
    rw [MeasureTheory.integral_prod _ hIP]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          χ z * (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
            ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)) from by
      funext z
      exact MeasureTheory.integral_const_mul _ _]
  -- the `z`-level identity in `Ioi 0` form
  have hIbp := truncRadialIbpTheta (α := α) (u := u) (fun z => χ z * (Work.Spaces.w z) ^ 2)
    ha hab hA.smooth hgrad hA.memRad2 hu hωd hωsupp hωbdd
  have hmain : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
      = α ^ 2 * (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun y : ℝ => y ^ 2 * (χ y * (Work.Spaces.w y) ^ 2))) z *
              (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun y : ℝ => y * (χ y * (Work.Spaces.w y) ^ 2)) z *
              (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
    rw [← hnuG, hsplit_double, hnuL, hnuP, hIbp]
    ring
  -- transport `Ioi 0` to `Iz` and rewrite the weight
  have hIoi : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi2 : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi3 : (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.Lzero u z θ * u z θ)))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ
              * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi4 : (∫ z in Set.Ioi 0,
        deriv (deriv (fun y : ℝ => y ^ 2 * (χ y * (Work.Spaces.w y) ^ 2))) z *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    have hfun : (fun y : ℝ => y ^ 2 * (χ y * (Work.Spaces.w y) ^ 2))
        = fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2 := by
      funext y; ring
    rw [hfun]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hIoi5 : (∫ z in Set.Ioi 0,
        deriv (fun y : ℝ => y * (χ y * (Work.Spaces.w y) ^ 2)) z *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz,
          deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z) z
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    have hfun : (fun y : ℝ => y * (χ y * (Work.Spaces.w y) ^ 2))
        = fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y := by
      funext y; ring
    rw [hfun]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  rw [hIoi, hIoi2, hIoi3, hIoi4, hIoi5] at hmain
  exact hmain


end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.Lzero1_integral_eq_neg_limit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Endpt

/-!
# The endpoint moment identity `∫_{Iθ} (Lzero1 u) · sin θ cos²θ = -lim_{0⁺} u`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` is the angular operator of the elliptic section and
`φ = sin θ cos²θ` lies in the kernel of its formal adjoint (`Work.Elliptic.LzeroAdj_sinCos2`).
The function

  `Φ θ = -u'(θ) · sinθcos²θ + u(θ) · cos θ cos 2θ`

is a primitive of `(Lzero1 u) · φ` on `(0, π/2)` (`Work.Elliptic.hasDerivAt_Lzero_antideriv`),
so the fundamental theorem of calculus on `0..π/2` identifies the integral with the boundary
values of `Φ`: it vanishes at `π/2` (both `sinθcos²θ` and `cos θ cos 2θ` vanish there) and
equals `lim_{0⁺} u` at `0⁺` (`|sinθcos²θ| ≤ θ` kills the term carrying `u'`, while
`cos θ cos 2θ → 1` leaves `u(0⁺)`).

Two ingredients make the FTC legitimate under the present hypotheses, and both are available in
the workspace:

* `Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit` carries out the FTC and the evaluation
  of both boundary terms, assuming only that `u` is bounded with bounded derivative;
* `Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta` supplies that boundedness from the
  hypothesis `h2`: since `sEta θ = sin(2θ)^{-η} ≥ 1` on `(0, π/2)`, `h2` first yields
  `u'' ∈ L¹((0,π/2))`, hence `u'` is bounded by the fundamental theorem of calculus, and one
  further integration bounds `u` itself.

So the only hypothesis the present statement adds to the moment identity is the existence of the
left endpoint limit `u → α`, and the integral is `-α`. -/


end Work.FTS.EllipticEst.Endpt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.WeakMoment.PzSliceIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.WeakMoment

set_option autoImplicit false

/-! ## Elementary helpers -/






/-! ## The main result -/


end Work.FTS.EllipticEst.WeakMoment
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.WProd6

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The pointwise majorant of the `𝒲^{6,∞}`-priced product rule.**

Summing the seven pure `D_z`-slots (`hzslot`) and the at most 49 mixed slots (`hmslot`) of
`HkIntegrand α 6 (f·g)`, using `HkIntegrand α 6 g ≤ GmajW6 α g`. -/
theorem prod_majorant_winf6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : WlInfMem α 6 f)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : HkMem α 6 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ Cz * (WlInf α 6 f) ^ 2 * HkIntegrand α 6 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ (7 * Cz + 49 * Cm) * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ GmajW6 α g z θ := GmajW6_nonneg hα g hθ
  have hbase : 0 ≤ (7 * Cz + 49 * Cm) * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : HkIntegrand α 6 g z θ ≤ GmajW6 α g z θ :=
        HkIntegrand_le_GmajW6 hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (6 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ 7 * (Cz * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1),
              (DzIter i (fun z θ => f z θ * g z θ) z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (6 + 1), (Cz * (WlInf α 6 f) ^ 2
                * GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi6 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 7 * (Cz * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (mixed j i (fun z θ => f z θ * g z θ) z θ
                * Wt α z θ) ^ 2 else 0))
          ≤ 49 * (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
                (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 6
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 49 * (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [HkIntegrand]
      calc (∑ i ∈ Finset.range (6 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
          ≤ 7 * (Cz * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ)
            + 49 * (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (7 * Cz + 49 * Cm) * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ := by
            ring
    · have hsin : Real.sin (2 * θ) = 0 := sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand6_eq_zero_of_sin_two_eq_zero (α := α) (F := fun z θ => f z θ * g z θ)
        (by rw [gam]; linarith) hsin]
      exact hbase

end Work.FTS.StrongPersist.H6Rows.WProd6
end
end
