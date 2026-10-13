/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-integral of the radial tail `zTail` is bounded by `HkSq`

`Work.FTS.ClassC.zTail g θ = ∫⁻_s ofReal ((D_z g(s,θ))² · w(s)²)` is the radial tail of `g`
at the angle `θ` (`Submission/Work/FTS/ClassC/TailDefs.lean`).  Here we show that its integral
in `θ` is dominated by the squared `H^k`-norm of `g`:

`∫⁻_θ zTail g θ ≤ ofReal (HkSq α k g)`   for `SmoothOpen g`, `HkMem α k g`, `1 ≤ k`.

The proof is the `∫⁻`-form of `L2Sq_DzIter_le_HkSq` at the pure `D_z`-slot `i = 1`, but *with
the open-quadrant smoothness class* `SmoothOpen` (openness is all that is needed: it supplies
the a.e. strong measurability of the uncurried integrand for the product of the two restricted
measures, via `Work.Spaces.aesm_of_continuousOn_Qd`) and for an *arbitrary* order `k ≥ 1`.
The general form is recorded below as `lintegral_DzIter_le_HkSq_open`; the statement of this
file is its `i = 1` instance, using `DzIter 1 = Dz`.

The route (no per-slice integrability of the *plain* slot is ever needed):

* `lintegral_lintegral_swap` exchanges the two `∫⁻` (Tonelli for `ℝ≥0∞`-valued functions);
* for each `s ∈ Iz` the angular `∫⁻` of `ofReal` is compared, via `lintegral_mono_ae`, with
  `∫⁻_θ ofReal (HkIntegrand α k g s θ)`, which is `ofReal` of the *Lebesgue* integral of the
  integrand by `ofReal_integral_eq_lintegral_ofReal` — this is where `HkMem` supplies the
  integrability of `θ ↦ HkIntegrand` (and the comparison itself is pointwise a.e.: on the open
  interval `(0,π/2)` the weight `sin(2θ)^{-η} ≥ 1` turns the plain slot into the `η`-weighted
  one, and the two endpoints are null);
* the marginal `∫⁻_s ofReal (∫_θ HkIntegrand α k g s θ)` is `ofReal (HkSq α k g)` by the
  second half of `HkMem`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.TailDefs
import Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **The ENNReal `D_z`-slot estimate in the open-quadrant smoothness class, for an arbitrary
order `k`.**  For `g` of class `C^∞` on the open quadrant and `HkMem α k g`, and for any
`i ≤ k`,

  `∫⁻_θ ∫⁻_s ofReal (D_z^i g(s,θ)² · w(s)²) ≤ ofReal (HkSq α k g)`.

This is `Work.Spaces.Slots.lintegral_DzIter_le_HkSq_of_smooth` (which asks for the stronger
`SmoothNbhd`, i.e. smoothness on a neighbourhood of the *closed* quadrant, and is stated for
`k = 4`) with `SmoothNbhd` relaxed to `SmoothOpen` and `k` arbitrary: the only place where the
smoothness is used is the a.e. strong measurability of the uncurried integrand, which holds for
merely continuous (indeed `SmoothOpen`) data, cf. `Work.Spaces.aesm_of_continuousOn_Qd`. -/
theorem lintegral_DzIter_le_HkSq_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  -- Continuity of the (uncurried) integrand on the open quadrant.
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
      rw [hfun]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt hp.1)
    exact h1.pow 2
  have hcontF : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.SmoothOpen.DzIter hso i).continuousOn).pow 2).mul hcontW
  -- A.e. strong measurability of the integrand for the product of the restricted measures.
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((Work.Spaces.DzIter i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    haesm.aemeasurable.ennreal_ofReal
  -- Tonelli: exchange the two `∫⁻`.
  have hswap : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))) :=
    MeasureTheory.lintegral_lintegral_swap hmeas
  -- Pointwise comparison with the `H^k`-integrand on the open angular interval.
  have hpt : ∀ s θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g s θ := by
    intro s θ h0 h1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta h0 h1
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α k g s θ i hi
    have heq : (Work.Spaces.DzIter i g s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
      have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
        norm_num
      rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
      ring
    calc (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        = (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hone (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Work.Spaces.DzIter i g s θ
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
      _ ≤ Work.Spaces.HkIntegrand α k g s θ := hkey
  -- The slicewise comparison (a.e. in `θ`, then `ofReal` of the honest angular integral).
  have hstep : ∀ s ∈ Work.Spaces.Iz,
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) := by
    intro s hs
    calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k g s θ)) :=
          MeasureTheory.lintegral_mono_ae (Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo
            (fun θ h0 h1 => ENNReal.ofReal_le_ofReal (hpt s θ h0 h1)))
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 s hs)
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g s θ)).symm
  -- The marginal `∫⁻` is `ofReal` of `HkSq`.
  have hfinal : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
    rw [Work.Spaces.HkSq]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Eventually.of_forall fun s =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g s θ)).symm
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))) :=
        hswap.symm
    _ ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)) :=
        MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iz
            from measurableSet_Ici) hstep)
    _ = ENNReal.ofReal (Work.Spaces.HkSq α k g) := hfinal

/-- **The `θ`-integral of the radial tail of `g` is bounded by the squared `H^k`-norm.**
For `g` of class `C^∞` on the open quadrant with `HkMem α k g` (`1 ≤ k`),

`∫⁻_θ zTail g θ = ∫⁻_θ ∫⁻_s ofReal (D_z g(s,θ)² w(s)²) ≤ ofReal (HkSq α k g)`. -/
theorem zTail_lintegral_le_HkSq {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) (hk : 1 ≤ k) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => Work.FTS.ClassC.zTail g θ)
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  have h := lintegral_DzIter_le_HkSq_open (g := g) hso hmem 1 hk
  simpa [Work.FTS.ClassC.zTail] using h

end Work.FTS.ClassC
