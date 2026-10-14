import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mollMasterUnif =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WProdWin.mslot_le_winf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WProdWin

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular and weight algebra -/

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

/-- The square of the `f`-side angular factor `(α + sin 2θ) sin(2θ)^{α/5}` is
`(α + sin 2θ)² sin(2θ)^{2α/5}`. -/
private theorem phi_sq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

/-- `(α + sin 2θ)² sin(2θ)^{2α/5} ≤ 4` for `0 < α ≤ 1` and `0 < θ < π/2`. -/
private theorem psi2_le_four {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·W)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]
  ring

/-! ## The `g`-side step: the mean-term hypothesis produces the `TW`-block of `GmajW` -/

private theorem mslot_gside_le {α CB : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hgm : Work.Spaces.HkMem α 4 g)
    (hCB : ∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    {d : ℕ} (hd : d ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ max CB 1 * GmajW α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ TW α θ := TW_nonneg hα.le hθI
  -- the mean-term block is nonnegative
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α g d z))
  have hg1 : (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      ≤ max CB 1 * ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  -- the mean term and the single `Aang` term are both dominated by `HgInt`/`∑Aang`
  have hmem : d ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ d' ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α g d' z) hmem
  have hw : (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2) ≤ HgInt α g z :=
    w_sq_mul_slice_le_HgInt hgm (by omega) hz
  have hXle : (Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt α g z + (Work.Spaces.gam α - 1)⁻¹
          * ∑ d' ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  -- `(D_z^d g · W)² · (α+sin2θ)²sin(2θ)^{2α/5} = (D_z^d g · w)² · TW`
  rw [mul_Wt_sq hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) = TW α θ := by
    rw [TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2 * TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) * TW α θ
      ≤ GmajW α g z θ := by
    simp only [GmajW]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 4 g z θ))
  calc (max CB 1 * ((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) * TW α θ
      = max CB 1 * (((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) := by ring
    _ ≤ max CB 1 * GmajW α g z θ := mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

theorem mslot_le_winf (CB : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      (∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 f) ^ 2
            * Work.FTS.OpenPkg.WProdWin.GmajW α g z θ := by
  have hCpos : (0 : ℝ) < 2 * 10 ^ 12 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 12 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 12 * (1 + max CB 1), hCpos, ?_⟩
  intro α f g hα hα1 hf hfm hg hgm hCB I J hI hIJ z θ hz hθ0 hθ1
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
    inv_nonneg.mpr (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hGnn : 0 ≤ GmajW α g z θ := GmajW_nonneg hα g hθI
  have hTWnn : 0 ≤ TW α θ := TW_nonneg hα.le hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hHkG : Work.Spaces.HkIntegrand α 4 g z θ ≤ GmajW α g z θ := HkIntegrand_le_GmajW hα g hθI
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hKper_nn : (0 : ℝ) ≤ 65536 * 40000 * (1 + max CB 1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hJ4 : J ≤ 4 := by omega
  have hI4 : I ≤ 4 := by omega
  have hA2nn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  -- Leibniz in the open class
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I f g hf hg z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((Work.Spaces.mixed b a f z θ)
        * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) with hYdef
  have hYsplit : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ)
          * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand of the double sum
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
        * GmajW α g z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul (Work.Spaces.choose_sq_le_256 I a (by omega) hI4)
              (Work.Spaces.choose_sq_le_256 J b (by omega) hJ4) (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on `g`
      have hIa : 1 ≤ I - a := by omega
      have hma : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ 40000 * (Work.Spaces.WlInf α 4 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
            Work.FTS.OpenPkg.DzIter_le_WlInf_open (α := α) (f := f) (b := b) (z := z) (θ := θ)
              hf hfm (by omega) hz hθ
          have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 := Work.Spaces.sq_le_sq_of_abs_le h
          show (Work.Spaces.DzIter b f z θ) ^ 2 ≤ 40000 * (Work.Spaces.WlInf α 4 f) ^ 2
          nlinarith [h1, sq_nonneg (100 * Work.Spaces.WlInf α 4 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := f) (a := a) (b := b)
            (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
          calc (Work.Spaces.mixed b a f z θ) ^ 2
              ≤ (100 * (Work.Spaces.WlInf α 4 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                Work.Spaces.sq_le_sq_of_abs_le h
            _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
                rw [mul_pow, mul_pow, phi_sq hθ]; ring
            _ ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 * 4 :=
                mul_le_mul_of_nonneg_left (psi2_le_four hα hα1 hθ) (sq_nonneg _)
            _ = 40000 * (Work.Spaces.WlInf α 4 f) ^ 2 := by ring
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (I - a) (J - b) hIa (by omega)
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (40000 * (Work.Spaces.WlInf α 4 f) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (40000 * (Work.Spaces.WlInf α 4 f) ^ 2)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hma (sq_nonneg _)
          _ ≤ (40000 * (Work.Spaces.WlInf α 4 f) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ :=
              mul_le_mul_of_nonneg_left hmg (by nlinarith [hWsq])
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((40000 * (Work.Spaces.WlInf α 4 f) ^ 2)
              * Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ := by
            rw [show 65536 * ((40000 * (Work.Spaces.WlInf α 4 f) ^ 2)
                  * Work.Spaces.HkIntegrand α 4 g z θ)
                = (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 f) ^ 2
                  * Work.Spaces.HkIntegrand α 4 g z θ) from by ring]
            calc (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 f) ^ 2
                  * Work.Spaces.HkIntegrand α 4 g z θ)
                ≤ (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hCBB0]) (mul_nonneg hWsq hGnn)
              _ = 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ := by ring
    · -- all `θ`-derivatives fall on `f`: the mean-term hypothesis is used
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b ≤ 3 := by omega
      have hmb : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have h := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := f) (a := a) (b := b)
          (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
        calc (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 4 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le h
          _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq hθ]; ring
      have hT : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        have he : Work.Spaces.mixed (J - b) (I - a) g = Work.Spaces.DzIter (J - b) g := by
          rw [hsub, Work.Spaces.mixed_zero_right]
        rw [he]
      have hgside : ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ max CB 1 * GmajW α g z θ :=
        mslot_gside_le (α := α) (CB := CB) (g := g) (d := J - b) hα hgm hCB hdJ hz hθ
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hT]
          _ ≤ ((100 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1 * GmajW α g z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ := by
            rw [show 65536 * ((100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ)
                = (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ) from by ring]
            have hAB : (65536 * 10000 * (max CB 1) : ℝ)
                ≤ 65536 * 40000 * (1 + max CB 1) := by nlinarith [hCBB0]
            calc (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ)
                ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have h1 : (I : ℝ) ≤ 4 := by exact_mod_cast hI4
    have h2 : (J : ℝ) ≤ 4 := by exact_mod_cast hJ4
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
            * GmajW α g z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
            * GmajW α g z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
                * GmajW α g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
              * GmajW α g z θ) := by rw [hsumconst]; ring
    _ ≤ 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
            * GmajW α g z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ ≤ (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ := by
        rw [show 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
              * GmajW α g z θ)
            = (625 * (65536 * 40000 * (1 + max CB 1))) * ((Work.Spaces.WlInf α 4 f) ^ 2
              * GmajW α g z θ) from by ring]
        have hle : 625 * (65536 * 40000 * (1 + max CB 1)) ≤ 2 * 10 ^ 12 * (1 + max CB 1) := by
          nlinarith [hCBB0]
        calc (625 * (65536 * 40000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ)
            ≤ (2 * 10 ^ 12 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
                * GmajW α g z θ := by ring

end Work.FTS.OpenPkg.WProdWin
end
end
