import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.logJensen
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.MuStepB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-- **The two-kernel domination estimate (pure measure theory), with a constant uniform in all the
data.**

There is a single constant `K > 0` with the following property.  For all `F, X : ℝ → ℝ → ℝ` and all
`δ, ε ∈ (0, 1/2]`, if for a.e. `z > 0` one has for every `θ ∈ Iθ`

  `|F z θ| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |X (e^t) s| ds) dt`

(where `sKer δ` is the smooth bump of total mass `1` supported in `[-δ,δ]` and
`KJ ε θ s = sKer ε (θ-s) + sKer ε (θ+s) + sKer ε (θ+s-π)`), if the slices of `F` and `X` are
`σ_η`-honest, `∫_z w(z)² ∫_θ (X z θ)² σ_η(θ)` is integrable on `Iz`, `F` is a.e. measurable for the
product of the restrictions to `(0,∞)` and `Iθ` and `(t,s) ↦ X (e^t) s` is a.e. measurable for
`volume.prod (volume.restrict Iθ)`, then

  `∫_z w(z)² ∫_θ (F z θ)² σ_η(θ) ≤ K · ∫_z w(z)² ∫_θ (X z θ)² σ_η(θ)`

on `Iz`, and the left-hand side is integrable on `Iz`.

Route: Cauchy–Schwarz/Jensen for the product probability-type kernel
(`(∫∫ kδ·KJ·|X|)² ≤ 3 ∫∫ kδ·KJ·X²`, using `∫ sKer δ = 1` and `∫_{Iθ} KJ ε θ s ds ≤ 3`), Tonelli
(everything nonnegative; `hXmeas` for the `(t,s)`-side, `hFmeas` for the `z`-side), the two
Schur/weight comparisons

* `∫_{Iθ} σ_η(θ) KJ ε θ s dθ ≤ K₁ σ_η(s)` for a.e. `s ∈ Iθ` (`KJ_schur_ae`, from
  `Work.FTS.EllSol.K5cAux.thWeightCmp`; `K₁` is a *fixed* number, which is what makes the constant
  uniform in `F, X, δ, ε`),
* `∫_z w(z)² sKer δ (log z - t) dz ≤ 5 (w (e^t))² e^t` (substitute `z = e^{t+u}`; `wExpCmp` gives
  `w(e^{t+u})²e^{t+u} ≤ 5 w(e^t)²e^t` for `|u| ≤ δ ≤ 1/2`, together with `∫ sKer δ = 1`),

and the change of variables `y = e^t` (`MeasureTheory.integral_comp_exp`, as in `logJensen`) to
identify `∫_t (w (e^t))² e^t ∫_s X(e^t,s)² σ_η(s) ds dt` with `∫_y w(y)² ∫_s X(y,s)² σ_η(s) ds dy`.
The constant `15 K₁` works.  Useful tools: `MeasureTheory.Measure.prod_restrict`,
`MeasureTheory.Measure.restrict_congr_set`, `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`. -/
theorem mollMasterUnif : ∃ K : ℝ, 0 < K ∧ ∀ (F X : ℝ → ℝ → ℝ) (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ 1 / 2 →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ θ ∈ Work.Spaces.Iθ,
      |F z θ| ≤ ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X (Real.exp t) s|)) →
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) →
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (X z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) →
    (MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (X z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iz) →
    (AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) →
    (AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) →
    ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ≤ K * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (X z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) ∧
    MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iz := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.K5cAux.thWeightCmp
  refine ⟨15 * K₁, by positivity, ?_⟩
  intro F X δ ε hδ hδ2 hε hε2 hdom hFhon hXhon hXint hFmeas hXmeas
  -- nonnegativity of the slice functionals
  have hGFnn : ∀ z : ℝ, 0 ≤ ∫ θ in Iθ, (F z θ) ^ 2 * σθ θ := fun z =>
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  have hGXnn : ∀ z : ℝ, 0 ≤ ∫ θ in Iθ, (X z θ) ^ 2 * σθ θ := fun z =>
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  -- (1) `muMHat F` is `ofReal` of the honest `z`-integrand
  have hM1 : muMHat F = ∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ)) := by
    have hpos : ∀ᵐ z ∂(volume.restrict Iz), 0 < z := by
      rw [mu_Ioi]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hz)
    change (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)))
        = ∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ))
    refine lintegral_congr_ae ?_
    filter_upwards [hpos] with z hz
    have h2 : (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ))
        = ENNReal.ofReal (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hFhon z hz)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))).symm
    rw [h2]
    exact muWHat_mul_ofReal (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ) (hGFnn z) z
  -- (2) the numerical bound
  have hMN : muMHat F ≤ ENNReal.ofReal (15 * K₁ * (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))) := by
    refine le_trans (mu_MHat_le hδ hδ2 hε hε2 hdom hFhon hXhon hXmeas) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mu_NHat_le hδ hδ2 hε hXhon hXmeas hK₁pos (fun u hu => hK₁ ε u hε hε2 hu))
      (by norm_num : (0 : ℝ≥0∞) ≤ 3)) ?_
    rw [mu_expChange X hXhon hXint]
    -- arithmetic with the explicit constant
    have harith : (3 : ℝ≥0∞) * (ENNReal.ofReal (5 * K₁) * ENNReal.ofReal
          (∫ z in Iz, (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)))
        = ENNReal.ofReal (15 * K₁ * (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))) := by
      have h5n : ENNReal.ofReal (5 : ℝ) = (5 : ℝ≥0∞) := ENNReal.ofReal_natCast 5
      have h15n : ENNReal.ofReal (15 : ℝ) = (15 : ℝ≥0∞) := ENNReal.ofReal_natCast 15
      have h5 : ENNReal.ofReal (5 * K₁) = (5 : ℝ≥0∞) * ENNReal.ofReal K₁ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), h5n]
      have h15 : ENNReal.ofReal (15 * K₁ * (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)))
          = (15 : ℝ≥0∞) * (ENNReal.ofReal K₁ * ENNReal.ofReal
              (∫ z in Iz, (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15) hK₁pos.le),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 15), h15n, mul_assoc]
      rw [h15, h5]
      ring
    rw [harith]
  -- (3) a.e. strong measurability of the `z`-slice
  have hAESM : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ)) (volume.restrict Iz) := by
    have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
        ((F p.1 p.2) ^ 2 * σθ p.2))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Iθ)) :=
      (((mu_measurable_w.pow_const 2).comp measurable_fst).aemeasurable.mul
        (((measurable_id.pow_const 2).comp_aemeasurable hFmeas).mul
          ((Work.FTS.EllipticEst.integrableOn_thEta.1).aemeasurable.comp_snd))).aestronglyMeasurable
    have hraw := hjoint.integral_prod_right'
    rw [mu_Ioi]
    refine (aestronglyMeasurable_congr ?_).mp hraw
    exact Eventually.of_forall (fun z => MeasureTheory.integral_const_mul
      ((Work.Spaces.w z) ^ 2) (fun θ : ℝ => (F z θ) ^ 2 * σθ θ))
  -- (4) finiteness and integrability
  have hFin : (∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ))) < ⊤ :=
    lt_of_le_of_lt (le_of_eq hM1.symm) (lt_of_le_of_lt hMN ENNReal.ofReal_lt_top)
  have hInt : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ)) (volume.restrict Iz) :=
    ⟨hAESM, by
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (hGFnn z)))]
      exact hFin⟩
  -- (5) the inequality
  refine ⟨?_, hInt⟩
  have hXside_nn : 0 ≤ ∫ z in Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ) :=
    integral_nonneg_of_ae (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (hGXnn z)))
  have hkey : ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (F z θ) ^ 2 * σθ θ)) ≤ ENNReal.ofReal (15 * K₁) *
        ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (hGFnn z))), ← hM1]
    refine hMN.trans (le_of_eq ?_)
    exact ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15) hK₁pos.le)
  refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hXside_nn)).mp ?_
  exact hkey.trans (le_of_eq (ENNReal.ofReal_mul
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15) hK₁pos.le)).symm)

end Work.FTS.EllSol.EllPkgAux.MollDom
