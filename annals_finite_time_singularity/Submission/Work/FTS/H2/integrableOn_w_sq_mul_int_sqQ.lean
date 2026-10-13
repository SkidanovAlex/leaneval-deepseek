import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Auxiliary facts

Three `SmoothQuad`-in-place-of-`SmoothNbhd` versions of the pieces of
`Work.Elliptic.integrableOn_w_sq_mul_int_sq` (equivalently
`Work.FTS.EllipticEst.Blocks.L12Gen.integrableOn_w_sq_mul_int_sq_k`): the a.e. domination of
the pure `D_z^j` slot by the `ℋ⁴`-integrand, the product-integrability of the `ℋ⁴`-integrand,
and the product-integrability of `(D_z^j g)² w²`.  Only the second differs substantively from
the `SmoothNbhd` version: continuity of the integrand on the *open* quadrant
(`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`) replaces continuity on a neighbourhood
of the closed quadrant. -/

private abbrev quadO : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma quadO_subset_quadU : quadO ⊆ Work.Spaces.quadU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact ⟨Set.mem_Ioi.mpr (by have h := Set.mem_Ioi.mp hz; linarith), hθ⟩

/-- A.e. pointwise domination of the pure `D_z^j` slot by the `ℋ⁴`-integrand.  No smoothness
hypothesis is needed: on the open quadrant `w² ≤ (w / sin(2θ)^{η/2})²` because
`0 < sin(2θ) ≤ 1` there. -/
private theorem ae_DzIter_sq_mul_w_sq_le_HkIntegrand_Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    {j : ℕ} (hj : j ≤ 4) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by
  filter_upwards [Work.Elliptic.ae_mem_Qd_prod] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  have hsinp := Work.Elliptic.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hsin : 0 < Real.sin (2 * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : 0 ≤ (Work.Spaces.DzIter j g p.1 p.2) ^ 2 := sq_nonneg _
  have hw2 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  calc (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      ≤ (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
        nlinarith [mul_nonneg hsq hw2, hsinp]
    _ = (Work.Spaces.DzIter j g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        have hs : 0 ≤ Real.sin (2 * p.2) := hsin.le
        have hsq' : (Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)) ^ 2
            = Real.sin (2 * p.2) ^ (Work.Spaces.eta) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
          norm_num
        rw [mul_pow, div_pow, hsq', div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g p.1 p.2 j hj

/-- Product-integrability of the `ℋ⁴`-integrand for `SmoothQuad` data. -/
private theorem HkIntegrand_integrable_prod_Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 g hsm)
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hcongr1 : ∫⁻ (p : ℝ × ℝ), ‖Work.Spaces.HkIntegrand α 4 g p.1 p.2‖ₑ
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      = ∫⁻ (p : ℝ × ℝ), ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    lintegral_congr fun p => Real.enorm_eq_ofReal (Work.Spaces.HkIntegrand_nonneg α 4 g p.1 p.2)
  rw [hcongr1]
  rw [MeasureTheory.lintegral_prod _
    (AEMeasurable.ennreal_ofReal (AEStronglyMeasurable.aemeasurable haesm))]
  have hcongr2 : ∫⁻ (z : ℝ), ∫⁻ (θ : ℝ), ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g z θ)
        ∂(volume.restrict Work.Spaces.Iθ) ∂(volume.restrict Work.Spaces.Iz)
      = ∫⁻ (z : ℝ), ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 g z θ)
        ∂(volume.restrict Work.Spaces.Iz) := by
    refine lintegral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).symm
  rw [hcongr2]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 g z θ)]
  exact ENNReal.ofReal_lt_top

/-- Product-integrability of `(D_z^j g)² w²` for `SmoothQuad` data. -/
private theorem integrable_prod_DzIter_sq_mul_w_sq_Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hsm' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      Work.Spaces.quadU := hsm
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2) ^ 2) quadO :=
    (((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hsm' j).continuousOn).mono
      quadO_subset_quadU).pow 2
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) quadO := by
    simp only [Work.Spaces.w]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  refine MeasureTheory.Integrable.mono' (HkIntegrand_integrable_prod_Q α g hsm hmem)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hcont1.mul hcont2)) ?_
  filter_upwards [ae_DzIter_sq_mul_w_sq_le_HkIntegrand_Q α g hj] with p hp
  rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]

/-- The pure `D_z^j` slot comparison in the interior class: the `z`-integral of the weighted
angular energy `∫_θ (D_z^j g)²` is dominated by `HkSq α 4 g`.  This is
`Work.Elliptic.integrableOn_w_sq_mul_int_sq` with `Work.FTS.LocData.SmoothQuad` (genuine
`C^∞` on the open quadrant) and `HkMem` in place of the analyticity hypothesis
`Work.Spaces.SmoothNbhd`.  A sibling to copy from is
`Work.FTS.EllipticEst.Blocks.L12Gen.integrableOn_w_sq_mul_int_sq_k` (also `SmoothNbhd`, same
proof), or `Work.Elliptic.integrableOn_w_sq_mul_int_sq`.

Route (identical to the sibling, replacing the analyticity input by `SmoothQuad`):
for `z > 0` and a.e. `θ ∈ Iθ` one has `(D_z^j g z θ)²·(w z)² ≤ HkIntegrand α 4 g z θ`
(`Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd`, or `Work.Spaces.sq_le_HkIntegrand_z` plus
`sin(2θ)^{η/2} ≤ 1`), so the weighted angular energy is dominated by `∫_θ HkIntegrand`, which is
integrable in `θ` for every `z ∈ Iz` and integrable in `z` over `Iz` by `hmem`.  Measurability of
the two-variable integrand `(z,θ) ↦ (D_z^j g z θ)²(w z)²` comes from its *continuity* on the open
quadrant (`Work.FTS.LocData.contDiffOn_DzIter` + `Work.Spaces.aesm_of_continuousOn_Qd`), and the
outer function `z ↦ ∫_θ (D_z^j g z θ)²(w z)²` is a.e. strongly measurable by
`AEStronglyMeasurable.integral_prod_right'`; `Integrable.mono'` against `hmem.2` gives the
integrability, `integral_mono_ae` plus `∫_z ∫_θ HkIntegrand = HkSq` (definitional) gives the
bound.  A worked example of exactly this bookkeeping with `SmoothQuad` in place of `SmoothNbhd`
is `Work.FTS.H2.slotM_quad` in `Submission/Work/FTS/H2/LinfQ.lean`. -/
theorem integrableOn_w_sq_mul_int_sqQ (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)) Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
        ≤ Work.Spaces.HkSq α 4 g := by
  have hprod := integrable_prod_DzIter_sq_mul_w_sq_Q α g hsm hmem hj
  have hInt2 := HkIntegrand_integrable_prod_Q α g hsm hmem
  have hkey : (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
      = fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    funext z
    rw [MeasureTheory.integral_mul_const]
    ring
  have hHk : (∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = Work.Spaces.HkSq α 4 g := (MeasureTheory.integral_prod _ hInt2).trans rfl
  constructor
  · rw [hkey]
    exact MeasureTheory.Integrable.integral_prod_left hprod
  · rw [hkey, ← MeasureTheory.integral_prod _ hprod]
    have h := MeasureTheory.integral_mono_ae hprod hInt2
      (ae_DzIter_sq_mul_w_sq_le_HkIntegrand_Q α g hj)
    rw [hHk] at h
    exact h

end Work.FTS.H2
