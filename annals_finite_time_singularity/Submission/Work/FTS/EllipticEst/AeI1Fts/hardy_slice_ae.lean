import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen

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

private theorem slice_sigE_int {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Iθo := by
  have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hz
  have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f z θ)
      Work.Spaces.Iθ := hf.1 z hzmem
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => by
      rw [hkIntegrand_zero_eq_of_mem α f hθ]; ring) measurableSet_Icc
  have h3 : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Work.Spaces.Iθ := by
    have h4 : MeasureTheory.Integrable
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.const_mul h2 _
    refine MeasureTheory.IntegrableOn.congr_fun h4 (fun θ _ => ?_) measurableSet_Icc
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hwpos)), one_mul]
  exact MeasureTheory.IntegrableOn.congr_set_ae h3
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := Real.pi/2))

/-- The `∂_θ`-version: the slice `θ ↦ ∂_θ (U u z θ)` is `V u z ·` on the open interval, so the
weighted square of the slice derivative of `U` is integrable as soon as `V u ∈ ℋ⁰`. -/
private theorem slice_deriv_sigE_int {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hV : Work.Spaces.HkMem α 0 (V u)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => U u z θ') θ) ^ 2 * sigE θ) Iθo :=
  MeasureTheory.IntegrableOn.congr_fun (slice_sigE_int (f := V u) hV hz)
    (fun θ hθ => by rw [slice_deriv_eq hS hz hθ]) measurableSet_Ioo

/-! ## The cross term -/

/-- **AM–GM domination of the cross integrand.**  Splitting
`sin(2θ)^{-1-η} = sin(2θ)^{-(2+η)/2}·sin(2θ)^{-η/2}` and applying `2ab ≤ a² + b²` to
`a = |W| |cos(2θ)| sin(2θ)^{-(2+η)/2}`, `b = |W'| sin(2θ)^{-η/2}` dominates
`|W W' cos(2θ) sin(2θ)^{-1-η}|` by `(W²cos²(2θ)sin(2θ)^{-(2+η)} + W'²sin(2θ)^{-η})/2`, so the
cross term is integrable as soon as the two diagonal terms are. -/
private theorem slice_cross_int {W W' : ℝ → ℝ}
    (hN : MeasureTheory.IntegrableOn
      (fun θ => (W θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta)) Iθo)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (W' θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Iθo)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => W θ * W' θ * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta))
      (MeasureTheory.volume.restrict Iθo)) :
    MeasureTheory.IntegrableOn
      (fun θ => W θ * W' θ * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)) Iθo := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.Integrable.const_mul (MeasureTheory.Integrable.add hN hD) (1/2)) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsp : (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hp2 : ((Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2)) ^ 2
      = (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta) := by
    rw [pow_two, ← Real.rpow_add hs]; congr 1; ring
  have hq2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2)) ^ 2
      = (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [pow_two, ← Real.rpow_add hs]; congr 1; ring
  show ‖W θ * W' θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)‖
      ≤ 1 / 2 * (W θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta)
          + W' θ ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hs.le _), hsp]
  have e1 : (|W θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2)) ^ 2
      = W θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta) := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hp2]
  have e2 : (|W' θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2)) ^ 2
      = W' θ ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [mul_pow, sq_abs, hq2]
  have h := two_mul_le_add_sq
    (|W θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2))
    (|W' θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2))
  nlinarith [h, e1, e2]

/-! ## The target -/

theorem hardy_slice_ae {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * Work.FTS.EllipticEst.AeI1Fts.sig2 θ)
        ≤ (1 / (1 + Work.Spaces.eta) ^ 2)
            * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hNae := (N_bound h hV).1
  filter_upwards [hNae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hNz hz
  -- open-interval smoothness of the two slices
  have hSlin : ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo := by
    refine (hS.Dz).curry_θ hz |>.of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hVlin : ContDiffOn ℝ 1 (fun θ => V u z θ) Iθo := by
    refine (hS.pth).Dz.curry_θ hz |>.of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  -- the slice `θ ↦ U u z θ` is differentiable on the open interval
  have hv : ∀ θ ∈ Iθo, HasDerivAt (fun θ' => U u z θ') (deriv (fun θ' => U u z θ') θ) θ :=
    fun θ hθ => ((hSlin.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  -- the four integrability hypotheses of the sharp Hardy inequality
  have hIntE : MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * sigE θ) Iθo :=
    slice_sigE_int hU hz
  have hIntN : MeasureTheory.IntegrableOn
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta)) Iθo := by
    refine MeasureTheory.IntegrableOn.congr_fun hNz (fun θ _ => ?_) measurableSet_Ioo
    have h2 : sig2 θ = (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta) := by
      rw [show (-2 - Work.Spaces.eta : ℝ) = -(2 + Work.Spaces.eta) by ring]; rfl
    rw [h2]
  have hIntD : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => U u z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Iθo := by
    refine MeasureTheory.IntegrableOn.congr_fun (slice_deriv_sigE_int hS hV hz)
      (fun θ _ => ?_) measurableSet_Ioo
    rfl
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => U u z θ * deriv (fun θ' => U u z θ') θ * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)) (MeasureTheory.volume.restrict Iθo) := by
    have hcontU : ContinuousOn (fun θ => U u z θ) Iθo := hSlin.continuousOn
    have hcontV : ContinuousOn (fun θ => V u z θ) Iθo := hVlin.continuousOn
    have hcontD : ContinuousOn (fun θ => deriv (fun θ' => U u z θ') θ) Iθo :=
      hcontV.congr (fun θ hθ => slice_deriv_eq hS hz hθ)
    have hcontc : ContinuousOn (fun θ => Real.cos (2 * θ)) Iθo :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hsin2 : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_id)
    have hconts : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)) Iθo :=
      hsin2.continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
    exact (((hcontU.mul hcontD).mul hcontc).mul hconts).aestronglyMeasurable measurableSet_Ioo
  have hIntC := slice_cross_int hIntN hIntD hmeas
  -- the sharp Hardy inequality on the slice
  have hmain := Work.FTS.EllipticEst.H2W.SlotA.sharpHardyCosWeight_open
      Work.Spaces.eta Work.Spaces.eta_pos Work.Spaces.eta_lt_one
      (fun θ => U u z θ) hv hIntE hIntC hIntN hIntD
  -- rewrite the two exponentials into the notation of the target
  have hRHS : (∫ θ in Iθo, (deriv (fun θ' => U u z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [slice_deriv_eq hS hz hθ]
    rfl
  rw [hRHS] at hmain
  have hLHS : (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      = ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    have h2 : sig2 θ = (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta) := by
      rw [show (-2 - Work.Spaces.eta : ℝ) = -(2 + Work.Spaces.eta) by ring]; rfl
    rw [h2]
  rw [hLHS]
  exact hmain

end Work.FTS.EllipticEst.AeI1Fts
