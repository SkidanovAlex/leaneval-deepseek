import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.NHonest
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_RegExport.RXR1.slice_diff_weighted
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.landau_1d
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.VPDefs
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpMod.N_L12_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS.SharpMod


end Work.FTS.GalFields.RHS.SharpMod
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharp_N_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS


end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.EpsE4RAsm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bundle of the target's inner hypotheses -/

/-- **The hypotheses of the restated target *after* `α₄`**: the datum's angular vanishing and
regularity, the two elliptic/star packages, the modulation clause, and the two datum bounds. -/
def E4Data (α C₀ K Ce Cs : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) : Prop :=
  0 ≤ K ∧
  (∀ z : ℝ, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧
  (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
    Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) ∧
  Work.FTS.VocabO2.StarPkgo2 α Cs Φs ∧
  MuLamOK α C₀ Φs E ∧
  (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) ∧
  Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 ∧
  Xn6 α g₀ ≤ K * α ^ 2

/-! ## The three analytic chapters -/




/-! ## The assembly -/


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.PzJepsStrict =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The strict datum bound at the barrier's scale.**

For a datum of the `hd`-class with `Xn α g₀ ≤ α²`, the projected mollified datum
`x₀ = Pz (J_ε g₀)` — which is `J_ε g₀` itself, by the `l12`-clause of `EpsDatum` — satisfies
`Xn α x₀ < √(clo/Cup) · C₀ α²` for all sufficiently small `ε`, provided
`1 < √(clo/Cup) · C₀`.  This is exactly the numeric condition that `BarrierThreshold.h0_of_datum_ratio`
needs to place the datum strictly below the barrier level `clo·(C₀α²)²`. -/
theorem Pz_Jeps_lt_ratio {α C₀ clo Cup : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hclo : 0 < clo) (hCup : 0 < Cup) (hC₀ : 0 < C₀)
    (hratio : 1 < Real.sqrt (clo / Cup) * C₀)
    (hd : ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum α ρ ε g₀)
    (h4 : Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Pz (Work.FTS.StrongEps.Jeps ρ ε g₀))
        < Real.sqrt (clo / Cup) * (C₀ * α ^ 2) := by
  classical
  set s : ℝ := Real.sqrt (clo / Cup) * C₀ with hs
  have hs1 : 1 < s := hratio
  -- the intermediate constant, strictly between `1` and `s`
  set C' : ℝ := (s + 1) / 2 with hC'
  have hC'1 : 1 < C' := by rw [hC']; linarith
  obtain ⟨ε₁, hε₁, hball⟩ :=
    Jeps_smallBall_one_lt (α := α) (C₀ := C') (ρ := ρ) (g₀ := g₀) hρ hα hα1 hC'1 hd h4
  refine ⟨ε₁, hε₁, fun ε hε => ?_⟩
  have hlt : C' * α ^ 2 < s * α ^ 2 := by
    have h2 := pow_pos hα 2
    exact mul_lt_mul_of_pos_right (by rw [hC']; linarith) h2
  -- the projection is the identity on `J_ε g₀`
  have hPz : Pz (Work.FTS.StrongEps.Jeps ρ ε g₀) = Work.FTS.StrongEps.Jeps ρ ε g₀ :=
    Pz_self_of_l12 ((hd ε hε.1).2.2.l12)
  rw [hPz]
  have hgoal : s * α ^ 2 = Real.sqrt (clo / Cup) * (C₀ * α ^ 2) := by
    rw [hs]; ring
  exact lt_of_le_of_lt (hball ε hε) (by rw [← hgoal]; exact hlt)

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiP_div_cos` — the `U`-slot part of the stream function, divided by `cos θ`, is `ℋ⁰`

The producers of the `StreamBdry` chain run on the *particular solution* `psiP α Φ` of the
level-`0` ODE `α·D_z P + 3P = -sin(2θ)·U'(Φ)`.  This module shows that on the open quadrant
(where the fixed-point relation `Φ = psiP α Φ` holds) the quotient `Φ/cos θ` is in `ℋ⁰`, with
the quantitative bound `HkSq α 0 (Φ/cos) ≤ C · HkSq α 0 U'` and the per-slice bound
`∫_θ HkIntegrand α 0 (Φ/cos) z θ ≤ C(1 + 1/z)(M² + HkSq α 0 U')`, where `|U'| ≤ M` on the
quadrant.

The four ingredients are the modules imported above:

* `psiP_pointwise_cs` — the pointwise Cauchy–Schwarz bound
  `(Φ/cos θ)² ≤ (4/(3α))∫₀¹ v^β U'(zv,θ)² dv` on the quadrant;
* `slice_le_Gf` — the level-`0` slice of `Φ/cos` is dominated by `(4/(3α))·Gf α U'`, where
  `Gf α U z = w(z)²∫₀¹ v^β M₁(zv) dv` is the radial density of the angular moment
  `M₁(z) = ∫_θ U(z,θ)² sin(2θ)^{-η} dθ` (this is the Fubini step on the finite product
  `Iθ × (0,1)`);
* `Gf_le` — `Gf α U` is integrable on `(0,∞)` with `∫ Gf ≤ (1/β)·HkSq α 0 U`;
* `kernel_le_small` — the small-`z` bound `∫₀¹ v^β M₁(zv) dv ≤ z³·HkSq α 0 U`.

The assembly below additionally uses the direct `θ`-route at large `z`
(`∫₀¹ v^β U(zv,θ)² dv ≤ M²/(β+1)` pointwise in `θ`), which is the local lemma
`kernel_pointwise_le`. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **Pointwise kernel bound at fixed `θ`.**  For `z > 0`, `θ ∈ (0,π/2)` and `|U| ≤ M` on the
open quadrant: `∫₀¹ v^β U(zv,θ)² dv ≤ M²/(β+1)`. -/
theorem kernel_pointwise_le {α M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |U z θ| ≤ M)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∫ v in (0 : ℝ)..1, v ^ (beta α) * (U (z * v) θ) ^ 2)
      ≤ M ^ 2 * (1 / (beta α + 1)) := by
  have hβ : -1 < beta α := by linarith [beta_pos hα hα1]
  have hval : (∫ v in (0 : ℝ)..1, M ^ 2 * v ^ (beta α)) = M ^ 2 * (1 / (beta α + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hβ), Real.one_rpow,
      Real.zero_rpow (by linarith : beta α + 1 ≠ 0)]
    ring
  have hint : IntegrableOn (fun v : ℝ => v ^ (beta α)) (Set.Ioc (0 : ℝ) 1) := by
    have h2 := intervalIntegrable_iff.mp
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hβ)
    rwa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h2
  rw [← hval, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    ?_ ?_ ?_
  · show ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        (0 : ℝ) ≤ v ^ (beta α) * (U (z * v) θ) ^ 2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun v hv => mul_nonneg
      (Real.rpow_nonneg (le_of_lt hv.1) _) (sq_nonneg _)
  · exact hint.integrable.const_mul (M ^ 2)
  · show ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        v ^ (beta α) * (U (z * v) θ) ^ 2 ≤ M ^ 2 * v ^ (beta α)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun v hv => ?_
    have hv0 : 0 < v := hv.1
    have h2 := hbnd (z * v) θ (Set.mem_prod.mpr ⟨mul_pos hz hv0, hθ⟩)
    have h3 : (U (z * v) θ) ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    calc v ^ (beta α) * (U (z * v) θ) ^ 2 ≤ v ^ (beta α) * M ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (le_of_lt hv0) _)
      _ = M ^ 2 * v ^ (beta α) := by ring


/-- **`psiP/cos θ ∈ ℋ⁰` with its quantitative and slice bounds, controlled by the `U`-slot.**
For `Φ` smooth on the open quadrant with `Φ = psiP α Φ` there (no gauge summand), `U' := Uprime α Φ`
bounded by `M` on the quadrant and `HkMem α 0 U'`, the quotient `Φ/cos θ` is in `ℋ⁰`, with
`HkSq α 0 (Φ/cos θ) ≤ C * HkSq α 0 U'` and the per-slice bound
`∫_θ HkIntegrand α 0 (Φ/cos) z θ ≤ C (1 + 1/z) (M² + HkSq α 0 U')` for every `z > 0`.
Route (`psiP α Φ z θ = -(sin 2θ/α) ∫_0^1 v^(3/α-1) U'(zv,θ) dv`): Cauchy–Schwarz in `v` gives
`(Φ z θ/cos θ)² ≤ (4/(3α)) ∫_0^1 v^(3/α-1) U'(zv,θ)² dv` (using `sin²2θ/cos²θ = 4 sin²θ ≤ 4`).
- `ℋ⁰`: Tonelli, the substitution `t = zv` and `w(t/v) ≤ w(t)` for `0 < v ≤ 1` give
  `HkSq α 0 (Φ/cos) ≤ (4/(3(3-α))) HkSq α 0 U'`.
- slice: with `M₁(t) = ∫_θ U'(t,θ)² sin(2θ)^{-η} dθ`,
  `∫_θ (Φ z θ/cos θ)² sin(2θ)^{-η} dθ ≤ (4/(3α)) z^{-3/α} ∫_0^z t^{3/α-1} M₁(t) dt`;
  for `z ≤ 1` bound the inner integral by `z^{3/α+3} HkSq α 0 U'` (as `t^{-4} ≤ w(t)²`) and use
  `w(z)²z³ = (1+z)⁴/z ≤ 16/z`; at `z ≥ 1` use `|Φ/cos| ≤ 2M/3` and `w(z)² ≤ 16`.
Membership uses the per-slice finiteness of `M₁` from `HkMem α 0 U'` and the (a.e.) measurability
from `SmoothOpen Φ`; `w(0) = 0` gives the `z = 0` conjunct. -/
theorem psiP_div_cos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ → ℝ → ℝ) (M : ℝ), 0 ≤ M →
      Work.FTS.EllipticEst.SmoothOpen Φ →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Φ z θ = Work.FTS.StreamBdryIface.psiP α Φ z θ) →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M) →
      Work.Spaces.HkMem α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) →
      Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
        ≤ C * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) ∧
      (∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ C * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ))) := by
  refine ⟨max (64 / (3 * α)) (64 * 10 ^ 4 / 9), by positivity, ?_⟩
  intro Φ M hM0 hsm hpsi hbnd hmem
  have hβ : 0 < beta α := beta_pos hα hα1
  -- `(4/(3α))·(1/β) ≤ C`
  have hCle : (4 / (3 * α)) * (1 / beta α) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := by
    have hb : beta α = 3 / α - 1 := rfl
    have h4 : (4 / (3 * α)) * (1 / (3 / α - 1)) = 4 / (3 * (3 - α)) := by
      have h1 : (0 : ℝ) < α := hα
      have h2 : (3 : ℝ) / α - 1 ≠ 0 := by linarith [hβ, hb]
      have h3 : (3 : ℝ) - α ≠ 0 := by linarith
      field_simp
    have h5 : 4 / (3 * (3 - α)) ≤ 64 / (3 * α) := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 3 * (3 - α)) (by linarith : (0 : ℝ) < 3 * α)]
      nlinarith [hα1, hα]
    calc (4 / (3 * α)) * (1 / beta α) = (4 / (3 * α)) * (1 / (3 / α - 1)) := by rw [hb]
      _ = 4 / (3 * (3 - α)) := h4
      _ ≤ 64 / (3 * α) := h5
      _ ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_max_left _ _
  -- smoothness and measurability of the quotient
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.cos θ) :=
    Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hsm
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hXsm.continuousOn_HkIntegrand α 0
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- the delegated pieces
  have hpt := Work.FTS_EllLimOK.ProducerH.psiP_pointwise_cs hα hM0 hpsi hbnd
  have hslice := Work.FTS_EllLimOK.ProducerH.slice_le_Gf hα hM0 hsm hbnd hpt
  obtain ⟨hGfint, hGfbd⟩ := Gf_le hα hα1 hmem
  have slice_nonneg : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ := fun z =>
    MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
  -- the pointwise bound on `(Φ/cos θ)²`
  have hX2 : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Φ z θ / Real.cos θ) ^ 2 ≤ (4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1))) := by
    intro z hz θ hθ
    have h1 := hpt z θ (Set.mem_prod.mpr ⟨hz, hθ⟩)
    have h2 := kernel_pointwise_le hα hα1 hbnd hz hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
  -- the a.e. bound on the level-`0` integrand
  have hHk_ae : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
        ≤ ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro z hz
    have heq : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
        = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.restrict_Ioo_eq_restrict_Icc
    rw [← heq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [HkIntegrand_eq_w2_sig α (fun z θ => Φ z θ / Real.cos θ) hθI]
    have hs : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg hθI
    have hx := hX2 z hz θ hθ
    have hw := sq_nonneg (Work.Spaces.w z)
    nlinarith [hx, hs, hw, mul_nonneg hw hs]
  have hSigInt : IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using integrableOn_sin_rpow_neg
  have hSigVal : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ) ≤ 10 ^ 4 := by
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using integral_sin_rpow_le
  -- the membership
  have hmemX : Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Real.cos θ) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
      · subst hz0
        have hzero : (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) 0 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          rw [HkIntegrand_zero_eq']
          simp [Work.Spaces.w]
        rw [hzero]
        exact integrableOn_zero
      · refine Integrable.mono'
          ((hSigInt.integrable).const_mul
            ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))) ?_ ?_
        · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
        · filter_upwards [hHk_ae z hzpos] with θ hθ
          rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
          exact hθ
    · have hIz : MeasureTheory.volume.restrict Work.Spaces.Iz
          = MeasureTheory.volume.restrict (Set.Ioi 0) := by
        rw [Work.Spaces.Iz]
        exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
      have hmaj : Integrable (fun z : ℝ =>
          (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        rw [hIz]
        exact hGfint.integrable.const_mul _
      refine Integrable.mono' hmaj haesm.integral_prod_right' ?_
      rw [hIz, MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [Real.norm_of_nonneg (slice_nonneg z)]
      rcases eq_or_lt_of_le (le_of_lt (Set.mem_Ioi.mp hz)) with hz0 | hzpos
      · subst hz0
        have hzero : (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) 0 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          rw [HkIntegrand_zero_eq']
          simp [Work.Spaces.w]
        have hGf0 : Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) 0 = 0 := by
          rw [Gf]
          simp [Work.Spaces.w]
        rw [hzero, integral_zero, hGf0]
        norm_num
      · exact hslice z hzpos
  -- the `HkSq` bound
  have hHkSqnn : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
    rw [Work.Spaces.HkSq]
    exact MeasureTheory.integral_nonneg fun z => MeasureTheory.setIntegral_nonneg
      measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
  have hHkSq_le : Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
      ≤ ((4 / (3 * α)) * (1 / beta α))
          * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ) := by
      show ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
      exact Filter.Eventually.of_forall fun z => slice_nonneg z
    have hae : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z) := by
      show ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun z hz => hslice z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg hnn
      (hGfint.integrable.const_mul _) hae
    rw [show (∫ z in Set.Ioi (0 : ℝ), (4 / (3 * α))
        * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z)
        = (4 / (3 * α)) * ∫ z in Set.Ioi (0 : ℝ),
            Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z from
      MeasureTheory.integral_const_mul _ _] at hmono
    calc Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ := rfl
      _ = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ := by
          rw [Work.Spaces.Iz]
          exact MeasureTheory.integral_Ici_eq_integral_Ioi
      _ ≤ (4 / (3 * α)) * ∫ z in Set.Ioi (0 : ℝ),
            Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z := hmono
      _ ≤ (4 / (3 * α)) * ((1 / beta α)
            * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) :=
          mul_le_mul_of_nonneg_left hGfbd (by positivity)
      _ = ((4 / (3 * α)) * (1 / beta α))
            * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by ring
  -- the per-slice bound
  have hslice_le : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
        ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
          * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
    intro z hz
    rcases le_total z 1 with hz1 | hz1
    · -- small `z`: use `Gf` and the kernel bound
      have hzpos : 0 < z := hz
      have hk := Work.FTS_EllLimOK.ProducerH.kernel_le_small hα hmem hz
      have hmain : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
              * ∫ v in (0 : ℝ)..1,
                  v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v)) := by
        have h := hslice z hz
        rwa [Gf] at h
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hstep : (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
            * ∫ v in (0 : ℝ)..1, v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v))
          ≤ (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
              * (z ^ 3 * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hw2) (by positivity)
      have hw2z3 : (Work.Spaces.w z) ^ 2 * z ^ 3 = (1 + z) ^ 4 / z := by
        rw [show (Work.Spaces.w z) ^ 2 * z ^ 3 = ((Work.Spaces.w z) ^ 2 * z ^ 4) / z from by
          field_simp]
        rw [w_sq_mul_z4 (ne_of_gt hz)]
      have hc₀ : (0 : ℝ) ≤ 4 / (3 * α) := by positivity
      have hfin : (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
            * (z ^ 3 * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)))
          ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
        have hpow : (1 + z) ^ 4 ≤ 16 := by
          have h1 : 1 + z ≤ 2 := by linarith
          have h2 : (0 : ℝ) ≤ 1 + z := by linarith
          calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h2 h1 4
            _ = 16 := by norm_num
        have hC : 64 / (3 * α) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_max_left _ _
        have hCnn : (0 : ℝ) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_of_lt (by positivity)
        have h1z : 1 / z ≤ 1 + 1 / z := by linarith
        have h1zn : 0 ≤ 1 / z := by positivity
        have hH : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := hHkSqnn
        have hMnn : 0 ≤ M ^ 2 := sq_nonneg M
        have hstep1 : (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
              * (z ^ 3 * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)))
            = (4 / (3 * α)) * ((1 + z) ^ 4 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
          rw [← hw2z3]; ring
        have hstep2 : (4 / (3 * α)) * ((1 + z) ^ 4 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)
            ≤ (4 / (3 * α)) * (16 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
          refine mul_le_mul_of_nonneg_right ?_ hH
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hpow (le_of_lt hzpos)) hc₀
        have hstep3 : (4 / (3 * α)) * (16 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)
            ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
              * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
          have h4 : (4 / (3 * α)) * (16 / z) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z) := by
            have h5 : (4 / (3 * α)) * (16 / z) = (64 / (3 * α)) * (1 / z) := by ring
            rw [h5]
            exact mul_le_mul hC h1z h1zn (by positivity)
          have h6 := mul_le_mul_of_nonneg_right h4 hH
          refine le_trans h6 ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        rw [hstep1]
        exact le_trans hstep2 hstep3
      exact le_trans hmain (le_trans hstep hfin)
    · -- large `z`
      have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
      have hθb : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
              * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ := by
        have h := MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
          ((hSigInt.integrable).const_mul _) (hHk_ae z hzpos)
        rwa [MeasureTheory.integral_const_mul] at h
      have hw16 : (Work.Spaces.w z) ^ 2 ≤ 16 := by
        have h2 : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
          rw [Work.Spaces.w]
          field_simp
          ring
        rw [h2]
        have h3 : 1 + 1 / z ≤ 2 := by
          have h4 : 1 / z ≤ 1 := by
            rw [div_le_one hzpos]
            exact hz1
          linarith
        have h4 : (0 : ℝ) ≤ 1 + 1 / z := by positivity
        have h5 : (1 + 1 / z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h4 h3 4
        have h6 : ((1 + 1 / z) ^ 2) ^ 2 = (1 + 1 / z) ^ 4 := by ring
        rw [h6]
        norm_num at h5 ⊢
        linarith
      have hβ1 : (4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1))) ≤ (4 / 9) * M ^ 2 := by
        have hb : beta α + 1 = 3 / α := by
          have h : beta α = 3 / α - 1 := rfl
          rw [h]; field_simp; ring
        rw [hb, one_div, inv_div]
        have h1 : (4 / (3 * α)) * (M ^ 2 * (α / 3)) = (4 / 9) * M ^ 2 := by
          field_simp
          ring
        rw [h1]
      have hfin : ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ)
          ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
        have hC : 64 * 10 ^ 4 / 9 ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_max_right _ _
        have hCnn : (0 : ℝ) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_of_lt (by positivity)
        have h1z : 1 ≤ 1 + 1 / z := by
          have : 0 ≤ 1 / z := by positivity
          linarith
        have hMnn : 0 ≤ M ^ 2 := sq_nonneg M
        have hHnn' : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := hHkSqnn
        have hsig : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ :=
          MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
            (fun θ hθ => Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
        have hprod : ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ)
            ≤ 16 * ((4 / 9) * M ^ 2) * 10 ^ 4 := by
          have h1 : (Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1))))
              ≤ 16 * ((4 / 9) * M ^ 2) :=
            mul_le_mul hw16 hβ1 (by positivity) (by positivity)
          exact mul_le_mul h1 hSigVal hsig (by positivity)
        have hval : 16 * ((4 / 9) * M ^ 2) * 10 ^ 4 = (64 * 10 ^ 4 / 9) * M ^ 2 := by ring
        rw [hval] at hprod
        have h8 : (64 * 10 ^ 4 / 9) * M ^ 2
            ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z) * M ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hMnn
          simpa using mul_le_mul hC h1z zero_le_one hCnn
        have h9 : max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z) * M ^ 2
            ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
              * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        exact le_trans hprod (le_trans h8 h9)
      exact le_trans hθb hfin
  exact ⟨hmemX, le_trans hHkSq_le (mul_le_mul_of_nonneg_right hCle hHkSqnn), hslice_le⟩

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.diffRow1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary auxiliary lemmas -/

/-- `HkNorm` only sees the values on the open quadrant. -/
theorem HkNorm_congr_Qd (α : ℝ) (k : ℕ) {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g :=
  congrArg Real.sqrt (Work.FTS.EllipticEst.HkSq_congr_open α k h)

/-- Congruence of `|·|_{ℋ⁴}` on the open quadrant. -/
theorem Xn_congr_Qd {α : ℝ} {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.Nonlin.Xn α f = Work.FTS.Nonlin.Xn α g :=
  HkNorm_congr_Qd α 4 h

/-- The field `Sn` only sees the profile through its pointwise values. -/
theorem Sn_congr {α : ℝ} {Φs : Fn} {E : Fn → Fn} {X Y : Fn}
    (h : ∀ z θ : ℝ, X z θ = Y z θ) : Sn α Φs E X = Sn α Φs E Y := by
  have hXY : X = Y := funext (fun z => funext (h z))
  rw [hXY]

/-- Monotonicity of the envelope in its second argument on the nonnegative half-line. -/
theorem Env_mono {α X Y : ℝ} (hα : 0 ≤ α) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    Work.FTS_MuLipC.Env α X ≤ Work.FTS_MuLipC.Env α Y := by
  have h1 : Real.sqrt α * X ≤ Real.sqrt α * Y :=
    mul_le_mul_of_nonneg_left hXY (Real.sqrt_nonneg α)
  have h2 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * Y ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (Real.rpow_nonneg hα _)
  rw [Work.FTS_MuLipC.Env, Work.FTS_MuLipC.Env]
  linarith

/-- `√α·α^{5/2} = α³`, hence `√α·α² ≤ α²` for `α ≤ 1`: the two elementary facts behind
`Env_scaled`. -/
theorem sqrt_alpha_mul_sq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt α * α ^ 2 ≤ α ^ 2 := by
  have hs : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  calc Real.sqrt α * α ^ 2 ≤ 1 * α ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg α)
    _ = α ^ 2 := one_mul _

/-- `α^{-3/2}·(α²)² ≤ α²` for `0 < α ≤ 1`. -/
theorem rpow_neg_mul_four {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(3 / 2 : ℝ)) * (α ^ 2) ^ 2 ≤ α ^ 2 := by
  have hsq : α ^ 2 = α ^ (2 : ℝ) := by rw [Real.rpow_two, pow_two]
  have h : α ^ (-(3 / 2 : ℝ)) * α ^ (2 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hα]
    have h2 : -(3 / 2 : ℝ) + 2 = 1 / 2 := by norm_num
    rw [h2]
    exact Real.rpow_le_one hα.le hα1 (by norm_num)
  rw [hsq]
  calc α ^ (-(3 / 2 : ℝ)) * (α ^ (2 : ℝ)) ^ 2
      = (α ^ (-(3 / 2 : ℝ)) * α ^ (2 : ℝ)) * α ^ (2 : ℝ) := by
        rw [pow_two]
        ring
    _ ≤ 1 * α ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hα.le _)
    _ = α ^ (2 : ℝ) := one_mul _

/-- The scaled envelope: `Env α (B·α²) ≤ (1+B+B²)·α²` for `0 < α ≤ 1` and `B ≥ 0`. -/
theorem Env_scaled {α B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B) :
    Work.FTS_MuLipC.Env α (B * α ^ 2) ≤ (1 + B + B ^ 2) * α ^ 2 := by
  have hsq : 0 ≤ α ^ 2 := sq_nonneg α
  have h1 : Real.sqrt α * (B * α ^ 2) ≤ B * α ^ 2 := by
    calc Real.sqrt α * (B * α ^ 2) = B * (Real.sqrt α * α ^ 2) := by ring
      _ ≤ B * α ^ 2 := mul_le_mul_of_nonneg_left (sqrt_alpha_mul_sq hα hα1) hB
  have h2 : α ^ (-(3 / 2 : ℝ)) * (B * α ^ 2) ^ 2 ≤ B ^ 2 * α ^ 2 := by
    have hmain := rpow_neg_mul_four hα hα1
    have hfac : α ^ (-(3 / 2 : ℝ)) * (B * α ^ 2) ^ 2
        = B ^ 2 * (α ^ (-(3 / 2 : ℝ)) * (α ^ 2) ^ 2) := by
      rw [mul_pow]
      ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hmain (sq_nonneg B)
  rw [Work.FTS_MuLipC.Env]
  linarith

/-! ## The analytic core -/

/-- **The core estimate.**  For `ClassC` profiles `f`, `f'` with `|f|_{ℋ⁴}, |f'|_{ℋ⁴} ≤ C·α²`
(`C ≥ 0`) and every `t > 0`,

`|L₁₂(Sn f)(0) - L₁₂(Sn f')(0)| ≤ (K₁/t)·Env α (√2·(2√2·C·α² + t·|f - f'|_{ℋ⁴}))`. -/
theorem l12_diff_le {α C Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {f f' : Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hf' : Work.FTS.ClassC.ClassC α f')
    (hXf : Work.FTS.Nonlin.Xn α f ≤ C * α ^ 2)
    (hXf' : Work.FTS.Nonlin.Xn α f' ≤ C * α ^ 2)
    {t : ℝ} (ht : 0 < t) :
    |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
      ≤ (Work.FTS_MuLamOK.KMu1 Ce Cs / t) * Work.FTS_MuLipC.Env α
          (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
            + t * Work.FTS.Nonlin.Xn α (f - f'))) := by
  classical
  have hCα : 0 ≤ C * α ^ 2 := mul_nonneg hC (sq_nonneg α)
  have hK1pos : 0 < Work.FTS_MuLamOK.KMu1 Ce Cs := Work.FTS_MuLamOK.KMu1_pos Ce Cs
  -- ### the class-friendly difference and the four scaled profiles
  have hd' : Work.FTS.ClassC.ClassC α (f + (-1 : ℝ) • f') :=
    Work.FTS.ClassC.classC_add hf (Work.FTS.ClassC.classC_smul (-1) hf')
  have hu : Work.FTS.ClassC.ClassC α (f + f') := Work.FTS.ClassC.classC_add hf hf'
  have hP1 : Work.FTS.ClassC.ClassC α ((f + f') + t • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_add hu (Work.FTS.ClassC.classC_smul t hd')
  have hP2 : Work.FTS.ClassC.ClassC α ((f + f') + (-t) • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_add hu (Work.FTS.ClassC.classC_smul (-t) hd')
  have hP3 : Work.FTS.ClassC.ClassC α (t • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_smul t hd'
  have hP4 : Work.FTS.ClassC.ClassC α ((-t) • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_smul (-t) hd'
  -- ### the honesty of the six fields, in the field's own spelling
  have sl : ∀ {g : Fn} (hg : Work.FTS.ClassC.ClassC α g),
      ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Sn α Φs E g r θ / r) Work.Spaces.Iθ :=
    fun {g} hg => (NHonest hα hα1 hg.reg (Work.FTS.ClassC.classC_hkMem_four hg)
      hstar.toStarPkgo (hell g hg)).2.2.1
  have dn : ∀ {g : Fn} (hg : Work.FTS.ClassC.ClassC α g),
      MeasureTheory.IntegrableOn (fun r => Work.Construction.L12dens (Sn α Φs E g) r)
        (Set.Ioi (0 : ℝ)) :=
    fun {g} hg => (NHonest hα hα1 hg.reg (Work.FTS.ClassC.classC_hkMem_four hg)
      hstar.toStarPkgo (hell g hg)).2.2.2
  -- ### the field polarization identity in the class-friendly spelling
  have hpol := SnPol hα hα1 hEadd hEsmul hstar hell hf hf' (ne_of_gt ht)
  have hbrid : ∀ {X Y : Fn}, (∀ z θ : ℝ, X z θ = Y z θ) → Sn α Φs E X = Sn α Φs E Y :=
    fun h => Sn_congr h
  have hp1 : Sn α Φs E (f + f' + t • (f - f'))
      = Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring)
  have hp2 : Sn α Φs E (f + f' - t • (f - f'))
      = Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring)
  have hp3 : Sn α Φs E (t • (f - f')) = Sn α Φs E (t • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring)
  have hp4 : Sn α Φs E (-(t • (f - f'))) = Sn α Φs E ((-t) • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring)
  have hpol' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Sn α Φs E f z θ - Sn α Φs E f' z θ
        = (1 / (4 * t)) * (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f')) z θ
            + Sn α Φs E (t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((-t) • (f + (-1 : ℝ) • f')) z θ) := by
    intro z θ hz hθ0 hθ1
    rw [hpol z θ hz hθ0 hθ1, hp1, hp2, hp3, hp4]
  -- ### the `L₁₂`-identity
  have hsub := L12_sub_eq (a := Sn α Φs E f) (b := Sn α Φs E f') (z := 0)
    (sl hf) (sl hf') (dn hf) (dn hf')
  have hcongr : Work.Construction.L12
        (fun z θ => Sn α Φs E f z θ - Sn α Φs E f' z θ) 0
      = Work.Construction.L12 (fun z θ => (1 / (4 * t))
          * (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f')) z θ
            + Sn α Φs E (t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((-t) • (f + (-1 : ℝ) • f')) z θ)) 0 :=
    L12_congrQd (le_refl 0) (fun z θ hz hθ0 hθ1 => hpol' z θ hz hθ0 hθ1)
  have halt4 := L12_alt4 (z := 0) (le_refl 0)
    (sl hP1) (sl hP2) (sl hP3) (sl hP4) (dn hP1) (dn hP2) (dn hP3) (dn hP4)
  have hkey : Work.Construction.L12 (Sn α Φs E f) 0
        - Work.Construction.L12 (Sn α Φs E f') 0
      = (1 / (4 * t)) * (Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
          + Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0) := by
    rw [hsub, hcongr, L12_const_mul, halt4]
  -- ### the single-profile row at the four scaled profiles
  have hrow : ∀ {g : Fn}, Work.FTS.ClassC.ClassC α g →
      |Work.Construction.L12 (Sn α Φs E g) 0| ≤ Work.FTS_MuLamOK.KMu1 Ce Cs
        * Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α g) :=
    fun hg => Work.FTS_MuLamOK.KMu1_row Ce Cs hα hα1 hg.reg
      (Work.FTS.ClassC.classC_hkMem_four hg) hstar.toStarPkgo (hell _ hg)
  -- ### the sizes of the four profiles
  have hdiff : ∀ z θ : ℝ, (f - f') z θ = (f + (-1 : ℝ) • f') z θ := by
    intro z θ
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hXd : Work.FTS.Nonlin.Xn α (f + (-1 : ℝ) • f')
      = Work.FTS.Nonlin.Xn α (f - f') :=
    (Xn_congr_Qd (fun z θ _ _ _ => hdiff z θ)).symm
  have hXu : Work.FTS.Nonlin.Xn α (f + f') ≤ 2 * Real.sqrt 2 * C * α ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α (f + f')
        ≤ Real.sqrt 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α f') :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hf.reg)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hf'.reg)
        (Work.FTS.ClassC.classC_hkMem_four hf) (Work.FTS.ClassC.classC_hkMem_four hf')
    have h2 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α f')
        ≤ Real.sqrt 2 * (C * α ^ 2 + C * α ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hXf hXf') (Real.sqrt_nonneg 2)
    have h3 : Real.sqrt 2 * (C * α ^ 2 + C * α ^ 2) = 2 * Real.sqrt 2 * C * α ^ 2 := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hX3 : Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f'))
      = t * Work.FTS.Nonlin.Xn α (f - f') := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => t * (f + (-1 : ℝ) • f') z θ)
        = |t| * Work.FTS.Nonlin.Xn α (f + (-1 : ℝ) • f') :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 t
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hd'.reg)
    rw [show (t • (f + (-1 : ℝ) • f'))
        = fun z θ => t * (f + (-1 : ℝ) • f') z θ from rfl, h1, abs_of_pos ht, hXd]
  have hX4 : Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f'))
      = t * Work.FTS.Nonlin.Xn α (f - f') := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => (-t) * (f + (-1 : ℝ) • f') z θ)
        = |-t| * Work.FTS.Nonlin.Xn α (f + (-1 : ℝ) • f') :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-t)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hd'.reg)
    rw [show ((-t) • (f + (-1 : ℝ) • f'))
        = fun z θ => (-t) * (f + (-1 : ℝ) • f') z θ from rfl, h1, abs_neg, abs_of_pos ht, hXd]
  have hXadd1 : Work.FTS.Nonlin.Xn α ((f + f') + t • (f + (-1 : ℝ) • f'))
      ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')) := by
    have h1 : Work.FTS.Nonlin.Xn α ((f + f') + t • (f + (-1 : ℝ) • f'))
        ≤ Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f'))) :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hu.reg)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hP3.reg)
        (Work.FTS.ClassC.classC_hkMem_four hu) (Work.FTS.ClassC.classC_hkMem_four hP3)
    have h2 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f')))
        ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f')) :=
      mul_le_mul_of_nonneg_left (add_le_add hXu (le_of_eq hX3)) (Real.sqrt_nonneg 2)
    linarith
  have hXadd2 : Work.FTS.Nonlin.Xn α ((f + f') + (-t) • (f + (-1 : ℝ) • f'))
      ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')) := by
    have h1 : Work.FTS.Nonlin.Xn α ((f + f') + (-t) • (f + (-1 : ℝ) • f'))
        ≤ Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f'))) :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hu.reg)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hP4.reg)
        (Work.FTS.ClassC.classC_hkMem_four hu) (Work.FTS.ClassC.classC_hkMem_four hP4)
    have h2 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f')))
        ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f')) :=
      mul_le_mul_of_nonneg_left (add_le_add hXu (le_of_eq hX4)) (Real.sqrt_nonneg 2)
    linarith
  -- ### assembly
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α (f - f') := Work.Spaces.HkNorm_nonneg α 4 _
  have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
      + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
  have hb1 := hrow hP1
  have hb2 := hrow hP2
  have hb3 := hrow hP3
  have hb4 := hrow hP4
  have e1 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α ((f + f') + t • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) hXadd1
  have e2 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α ((f + f') + (-t) • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) hXadd2
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have harg : ∀ {Y : ℝ}, Y = t * Work.FTS.Nonlin.Xn α (f - f') →
      Y ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')) := by
    intro Y hY
    rw [hY]
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 * C * α ^ 2 := by positivity
    have h3 : 0 ≤ t * Work.FTS.Nonlin.Xn α (f - f') := mul_nonneg ht.le hXn0
    calc t * Work.FTS.Nonlin.Xn α (f - f')
        ≤ Real.sqrt 2 * (t * Work.FTS.Nonlin.Xn α (f - f')) := by
          simpa using mul_le_mul_of_nonneg_right hsqrt2 h3
      _ ≤ Real.sqrt 2 * (t * Work.FTS.Nonlin.Xn α (f - f')
            + 2 * Real.sqrt 2 * C * α ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
            + t * Work.FTS.Nonlin.Xn α (f - f')) := by ring
  have e3 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) (harg hX3)
  have e4 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) (harg hX4)
  have hB0 : 0 ≤ 1 / (4 * t) := by positivity
  calc |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
      = |(1 / (4 * t)) * (Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
          + Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0)| := by
        rw [hkey]
    _ = (1 / (4 * t)) * |(Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
          + Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0)| := by
        rw [abs_mul, abs_of_nonneg hB0]
    _ ≤ (1 / (4 * t)) * (|Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0|
          + |Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0|
          + |Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0|
          + |Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0|) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        set A := Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
        set B := Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
        set Cc := Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
        set D := Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0
        have h1 : |(A - B + Cc) - D| ≤ |A - B + Cc| + |D| := by
          rw [sub_eq_add_neg]
          simpa using abs_add_le (A - B + Cc) (-D)
        have h2 : |A - B + Cc| ≤ |A - B| + |Cc| := abs_add_le (A - B) Cc
        have h3 : |A - B| ≤ |A| + |B| := by
          rw [sub_eq_add_neg]
          simpa using abs_add_le A (-B)
        linarith
    _ ≤ (1 / (4 * t)) * (Work.FTS_MuLamOK.KMu1 Ce Cs * (Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')))
          + Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')))
          + Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')))
          + Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f'))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        have hK0 : 0 ≤ Work.FTS_MuLamOK.KMu1 Ce Cs := hK1pos.le
        nlinarith [hb1, hb2, hb3, hb4, e1, e2, e3, e4, hEnv0, hK0]
    _ = (Work.FTS_MuLamOK.KMu1 Ce Cs / t) * Work.FTS_MuLipC.Env α (Real.sqrt 2
          * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f'))) := by
        field_simp
        ring

/-! ## The target -/

/-- **The difference row of `N`** (`DiffRow1 α C₀ Φs E`, `Submission/Work/FTS_MuLipC/Defs.lean`):
for `ClassC α` profiles `f`, `f'` of `ℋ⁴`-size `≤ C₀α²` (with `C₀α² ≤ 1`), the `L₁₂`-zero-mode of
the bilinear field `Sn α Φs E g = N α (F_*+g) (Φ_s + E g)` is Lipschitz in the profile, with a
constant depending on `α, C₀, Ce, Cs` only.  The map `E` is additive and `ℝ`-homogeneous (it is a
linear map in the application — the additivity and homogeneity are exactly what the polarization
at the scaled profiles `±t·d`, `u ± t·d` needs), `Φ_s` satisfies the star package, and `E g`
satisfies the elliptic package at every `ClassC` profile `g`.  Read
`Submission/Work/FTS_MuLipC/NOTES.md` for the route. -/
theorem diffRow1 {α C₀ Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hsmall : C₀ * α ^ 2 ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f)) :
    Work.FTS_MuLipC.DiffRow1 α C₀ Φs E := by
  classical
  -- ### the constants
  set K₁ : ℝ := Work.FTS_MuLamOK.KMu1 Ce Cs with hK₁
  have hK₁pos : 0 < K₁ := Work.FTS_MuLamOK.KMu1_pos Ce Cs
  have hK₁0 : 0 ≤ K₁ := hK₁pos.le
  set c : ℝ := max C₀ 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hcC : C₀ ≤ c := le_max_left _ _
  set B₁ : ℝ := Real.sqrt 2 * (2 * Real.sqrt 2 * c + 1) with hB₁
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  set B₂ : ℝ := 1 + B₁ + B₁ ^ 2 with hB₂
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; positivity
  refine ⟨K₁ * B₂ + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hXc : Work.FTS.Nonlin.Xn α f ≤ c * α ^ 2 :=
    le_trans hXf (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  have hXc' : Work.FTS.Nonlin.Xn α f' ≤ c * α ^ 2 :=
    le_trans hXf' (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  set X : ℝ := Work.FTS.Nonlin.Xn α (f - f') with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 _
  rcases lt_or_eq_of_le hX0 with hXpos | hXzero
  · -- ### the main case `|f - f'|_{ℋ⁴} > 0`
    set t : ℝ := α ^ 2 / X with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htX : t * X = α ^ 2 := by
      rw [ht]
      field_simp
    have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
    rw [← hX, htX] at hle
    have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + α ^ 2) = B₁ * α ^ 2 := by
      rw [hB₁]
      ring
    rw [hV] at hle
    have hEnv : Work.FTS_MuLipC.Env α (B₁ * α ^ 2) ≤ B₂ * α ^ 2 := by
      rw [hB₂]
      exact Env_scaled hα hα1 hB₁0
    have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α (B₁ * α ^ 2) :=
      Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
    have htinv : K₁ / t = K₁ * X / α ^ 2 := by
      rw [ht]
      field_simp
    calc |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
        ≤ (K₁ / t) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := hle
      _ = (K₁ * X / α ^ 2) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := by rw [htinv]
      _ ≤ (K₁ * X / α ^ 2) * (B₂ * α ^ 2) := by
          refine mul_le_mul_of_nonneg_left hEnv ?_
          positivity
      _ = K₁ * B₂ * X := by
          field_simp
      _ ≤ (K₁ * B₂ + 1) * X := by nlinarith [hX0, hB₂0, hK₁0]
  · -- ### the degenerate case `|f - f'|_{ℋ⁴} = 0`
    have hzero : |Work.Construction.L12 (Sn α Φs E f) 0
        - Work.Construction.L12 (Sn α Φs E f') 0| = 0 := by
      refine le_antisymm ?_ (abs_nonneg _)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      set t : ℝ := K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1 with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
      rw [← hX, hXzero.symm] at hle
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← pow_two]
        exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + t * 0) = (4 * c) * α ^ 2 := by
        have hmid : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2) = (4 * c) * α ^ 2 := by
          calc Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2)
              = (Real.sqrt 2 * Real.sqrt 2) * (2 * c * α ^ 2) := by ring
            _ = 2 * (2 * c * α ^ 2) := by rw [hsq2]
            _ = (4 * c) * α ^ 2 := by ring
        rw [mul_zero, add_zero, hmid]
      rw [hV] at hle
      have hEnv : Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 :=
        Env_scaled hα hα1 (by positivity)
      have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) :=
        Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
      have hnum0 : 0 ≤ K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 := by positivity
      have hfin : (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ ε := by
        calc (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2)
            ≤ (K₁ / t) * ((1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) := by
              refine mul_le_mul_of_nonneg_left hEnv ?_
              positivity
          _ = (K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) / t := by
              field_simp
          _ ≤ ε := by
              rw [ht]
              rw [div_le_iff₀ (by positivity : 0 < K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1)]
              field_simp
              nlinarith [hε.le, hnum0]
      linarith [hle, hfin]
    rw [hzero]
    exact mul_nonneg (by positivity) hX0

end Work.FTS_MuLipC.RowN
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.diffRow0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN0

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "L12" => Work.Construction.L12
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Xn" => Work.FTS.Nonlin.Xn
local notation "Hk" => Work.Spaces.HkIntegrand

/-- `ClassC` is closed under subtraction. -/
theorem classC_sub {α : ℝ} {f f' : Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hf' : Work.FTS.ClassC.ClassC α f') : Work.FTS.ClassC.ClassC α (f - f') := by
  have h := Work.FTS.ClassC.classC_add hf (Work.FTS.ClassC.classC_smul (-1) hf')
  have heq : f + (-1 : ℝ) • f' = f - f' := by
    funext z θ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← heq]
  exact h

/-- The majorant of the Hardy-weighted angular energy of the single field `Sn0 α g`. -/
def Phi1 (α : ℝ) (g : Fn) : ℝ → ℝ :=
  fun r => 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α g)
      * (∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ)
    + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α g) * (1 / (1 + r)) ^ 2)

theorem Phi1_nonneg {α : ℝ} (g : Fn) : ∀ r, 0 ≤ Phi1 α g r := by
  intro r
  have hA := Work.FTS.StrongPersist.H6Pair6Aux.A₀_nonneg α (Xn α g)
  have hB := Work.FTS.StrongPersist.H6Pair6Aux.B₀_nonneg α (Xn α g)
  have hΨ : 0 ≤ ∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ := by
    apply MeasureTheory.integral_nonneg
    intro θ
    exact Work.Spaces.HkIntegrand_nonneg α 4 g r θ
  have hc : 0 ≤ (1 / (1 + r)) ^ 2 := by positivity
  exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hA hΨ)
    (mul_nonneg (mul_nonneg (by positivity) hB) hc))

theorem integrableOn_Phi1 {α : ℝ} {g : Fn} (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Phi1 α g) (Set.Ioi (0 : ℝ)) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun r => Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α g)
        * (∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ)) (Set.Ioi (0 : ℝ)) :=
    (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun r : ℝ => (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α g)
        * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  have hunf : Phi1 α g = fun r => 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α g)
        * (∫ θ in Work.Spaces.Iθ, Hk α 4 g r θ)
      + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α g)
        * (1 / (1 + r)) ^ 2) := rfl
  rw [hunf]
  exact (h1.add h2).const_mul 7

/-- **The difference row of `N₀`** (`DiffRow0 α C₀`, `Submission/Work/FTS_MuLipC/Defs.lean`):
for `ClassC α` profiles `f`, `f'` of `ℋ⁴`-size `≤ C₀α²` (with `C₀α² ≤ 1`), the `L₁₂`-zero-mode
of the quadratic field `Sn0 α g = N₀ α (F_*+g) g` is Lipschitz in the profile, with a constant
depending on `α` and `C₀` only.  Read `Submission/Work/FTS_MuLipC/NOTES.md` for the route
(polarization of the quadratic part against the proved single-profile row `KMu0_row`). -/
theorem diffRow0 {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hsmall : C₀ * α ^ 2 ≤ 1) :
    Work.FTS_MuLipC.DiffRow0 α C₀ := by
  refine ⟨3 * Real.sqrt (Mconst C₀ α) + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hC₀ : 0 ≤ C₀ := by
    have h0 : 0 ≤ Xn α f' := Work.Spaces.HkNorm_nonneg α 4 f'
    have h1 : 0 < α ^ 2 := pow_pos hα 2
    nlinarith [hXf', h0, h1]
  have hmemf : Work.Spaces.HkMem α 4 f := Work.FTS.ClassC.classC_hkMem_four hf
  have hmemf' : Work.Spaces.HkMem α 4 f' := Work.FTS.ClassC.classC_hkMem_four hf'
  have hCsub : Work.FTS.ClassC.ClassC α (f - f') := classC_sub hf hf'
  have hmemD : Work.Spaces.HkMem α 4 (f - f') := Work.FTS.ClassC.classC_hkMem_four hCsub
  have hddefD : ∀ z θ, (f - f') z θ = f z θ - f' z θ := fun z θ => rfl
  set Xd : ℝ := Xn α (f - f') with hXddef
  have hXd : Xn α (f - f') = Xd := rfl
  have hXdnn : 0 ≤ Xd := by
    rw [← hXd]; exact Work.Spaces.HkNorm_nonneg α 4 (f - f')
  -- continuity of the difference field on the open quadrant
  have hcontf : ContinuousOn (Function.uncurry (Sn0 α f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hf.reg hmemf
  have hcontf' : ContinuousOn (Function.uncurry (Sn0 α f'))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hf'.reg hmemf'
  have hcontD : ContinuousOn (Function.uncurry (fun z θ => Sn0 α f z θ - Sn0 α f' z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hcontf.sub hcontf'
  -- a.e. strong measurability of the weighted angular energy
  have hmeasD : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.OpenPkg.l12zero_energy_aesm hcontD
  -- slice integrability of the squared difference
  have hslD : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
    have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
    have hDM : DiffMaj α C₀ Xd (f - f') f' r
        = fun θ => 3 * (A1const C₀ α * Hk α 4 (f - f') r θ
            + A2const Xd α * Hk α 4 f' r θ
            + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
      funext θ
      rw [DiffMaj, A1const, A2const]
    have h3c : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    have hmaj : MeasureTheory.IntegrableOn (fun θ => DiffMaj α C₀ Xd (f - f') f' r θ)
        Work.Spaces.Iθ := by
      rw [hDM]
      exact (((hmemD.1 r hzr).const_mul (A1const C₀ α)).add
        ((hmemf'.1 r hzr).const_mul (A2const Xd α))).add h3c |>.const_mul 3
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Sn0 α f p.1 p.2 - Sn0 α f' p.1 p.2) ^ 2) (hcontD.pow 2) hr
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    have hIoo : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hpt := diff_pointwise_le hα hα1 hC₀ hXd hf.reg hf'.reg hCsub.reg hmemf hmemf' hmemD
      hddefD hXf hr hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        ≤ (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r := by nlinarith [hw1]
      _ ≤ DiffMaj α C₀ Xd (f - f') f' r θ := hpt
  -- the energy bound with the explicit majorant
  have hbdE : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ PhiC α C₀ Xd (f - f') f' r := by
    filter_upwards [diff_energy_le hα hα1 hC₀ hXdnn hXf hXd hf.reg hf'.reg hCsub.reg hmemf
      hmemf' hmemD hddefD] with r hr
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hw] at hr
    exact hr
  have hΦint : MeasureTheory.IntegrableOn (PhiC α C₀ Xd (f - f') f') (Set.Ioi (0 : ℝ)) :=
    integrableOn_PhiC hmemD hmemf'
  have hL12bound := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := fun z θ => Sn0 α f z θ - Sn0 α f' z θ) hslD hmeasD hΦint hbdE
  have hint : (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd (f - f') f' r) ≤ Mconst C₀ α * Xd ^ 2 :=
    int_PhiC_le hXdnn hmemD hmemf' hXd hXf' hC₀ hα
  -- the density integrability of the two single fields
  have hslf : ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ) ^ 2)
      Work.Spaces.Iθ :=
    N0_slice_sq_integrable hα hα1 hf.reg hmemf
  have hslf' : ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Sn0 α f' r θ) ^ 2)
      Work.Spaces.Iθ :=
    N0_slice_sq_integrable hα hα1 hf'.reg hmemf'
  have hEf : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Phi1 α f r := by
    filter_upwards [N0_weighted_energy_le hα hα1 hf.reg hmemf] with r hr
    have hL : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) := rfl
    have hR : Phi1 α f r = 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α f)
          * (∫ θ in Work.Spaces.Iθ, Hk α 4 f r θ)
        + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α f)
          * (1 / (1 + r)) ^ 2) := rfl
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hL, hR] at *
    exact hr
  have hEf' : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Phi1 α f' r := by
    filter_upwards [N0_weighted_energy_le hα hα1 hf'.reg hmemf'] with r hr
    have hL : (∫ θ in Work.Spaces.Iθ, (Sn0 α f' r θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Construction.N0 α (Work.Construction.Ftot α f') f' r θ) ^ 2) := rfl
    have hR : Phi1 α f' r = 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α f')
          * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α f')
          * (1 / (1 + r)) ^ 2) := rfl
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hL, hR] at *
    exact hr
  have hslf_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hslf r hr)
  have hslf'_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f' r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hslf' r hr)
  have hdensf : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Sn0 α f))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_energy hslf_ae
      (aesm_L12dens_of_continuousOn (F := Sn0 α f) hcontf)
      (integrableOn_Phi1 hmemf) (Phi1_nonneg f) hEf
  have hdensf' : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Sn0 α f'))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_energy hslf'_ae
      (aesm_L12dens_of_continuousOn (F := Sn0 α f') hcontf')
      (integrableOn_Phi1 hmemf') (Phi1_nonneg f') hEf'
  have hSaf : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Sn0 α f r θ / r) Work.Spaces.Iθ :=
    fun r hr => integrableOn_K_mul_div hr
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Sn0 α f p.1 p.2) hcontf hr)
      (hslf r hr)
  have hSaf' : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Sn0 α f' r θ / r) Work.Spaces.Iθ :=
    fun r hr => integrableOn_K_mul_div hr
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Sn0 α f' p.1 p.2) hcontf' hr)
      (hslf' r hr)
  have hsub := L12_sub_of_integrable (a := Sn0 α f) (b := Sn0 α f') hdensf hdensf' hSaf hSaf'
  have hM0 : 0 ≤ Mconst C₀ α := Mconst_nonneg C₀ α
  rw [hsub]
  calc |L12 (fun z θ => Sn0 α f z θ - Sn0 α f' z θ) 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd (f - f') f' r) := hL12bound
    _ ≤ 3 * Real.sqrt (Mconst C₀ α * Xd ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hint) (by norm_num)
    _ = 3 * Real.sqrt (Mconst C₀ α) * Xd := by
        rw [Real.sqrt_mul hM0, Real.sqrt_sq hXdnn]
        ring
    _ ≤ (3 * Real.sqrt (Mconst C₀ α) + 1) * Xd := by
        have hs : 0 ≤ Real.sqrt (Mconst C₀ α) := Real.sqrt_nonneg _
        nlinarith [hs, hXdnn]

end Work.FTS_MuLipC.RowN0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DzDthG_tau_mod` — B4: the `τ`-modulus of `D_z g̃`, `D_θ g̃`

`DzG α g z θ τ = D_z g̃(z,θ,τ)` and `DthG α g z θ τ = D_θ g̃(z,θ,τ)` for the sanitised family
`g̃ = gS α (tauExt g)`.  The lemma produces an `α`-Hölder modulus in the fake time `τ` on the
*closed* box `[0,∞) × Iθ × [0,S]`.

The proof has three ingredients.

* On the *open* quadrant `z > 0`, `0 < θ < π/2` the sanitiser and the right-Taylor extension are
  invisible: `gS α (tauExt g) z θ τ = g z θ τ` for `τ ≥ 0`, so the mixed slots agree there
  (`mixed_congr_of_isOpen`).  The weighted Lipschitz modulus in `τ` of the mixed slots of `g`
  is `RXR5.Pieces.mixed_slice_tau_modulus` (from the `LimApprox` clause of `DynOK'`), with the
  weight `z^{3/2}/(1+z)² ≤ 1`; Lipschitz on `[0,S]` is `α`-Hölder via
  `|Δτ| ≤ S^{1-α}|Δτ|^α`.
* On the two angular edges `θ = 0`, `θ = π/2` and on `z = 0` the families vanish identically:
  `g` vanishes at the angular edges (`RegPkgMin.vanish`), which makes the whole `z`-slice of
  `gS α (tauExt g)` vanish there, so the `z`-derivative is `0`; and `gS α (tauExt g)`
  vanishes at `z = 0`, so its `θ`-derivative is `0`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

/-! ## Elementary real facts -/

/-- Lipschitz on a compact interval is `α`-Hölder, with the factor `S^{1-α}`. -/
private lemma abs_sub_le_rpow {α S τ τ' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (_hS : 0 < S)
    (hτ : τ ∈ Icc (0:ℝ) S) (hτ' : τ' ∈ Icc (0:ℝ) S) :
    |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := by
  have ht0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have htS : |τ - τ'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h, Real.zero_rpow hα.ne', mul_zero]
  · have h1 : (0:ℝ) ≤ 1 - α := by linarith
    have h2 : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) := Real.rpow_le_rpow ht0 htS h1
    have h3 : |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α = |τ - τ'| := by
      rw [← Real.rpow_add h, show 1 - α + α = 1 by ring, Real.rpow_one]
    calc |τ - τ'| = |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α := h3.symm
      _ ≤ S ^ (1 - α) * |τ - τ'| ^ α := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ht0 _)

/-- `z^{3/2} ≤ (1+z)²` for `z ≥ 0`. -/
private lemma rpow_three_halves_le_sq_add_one {z : ℝ} (hz : 0 ≤ z) :
    z ^ ((3:ℝ)/2) ≤ (1 + z) ^ 2 := by
  rcases lt_or_ge z 1 with h | h
  · calc z ^ ((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hz h.le (by norm_num)
      _ ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  · calc z ^ ((3:ℝ)/2) ≤ z ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)
      _ ≤ (1 + z) ^ (2:ℝ) := Real.rpow_le_rpow hz (by linarith) (by norm_num)
      _ = (1 + z) ^ 2 := Real.rpow_two (1+z)

/-- the weighted interior factor of `mixed_slice_tau_modulus` is `≤ 1` on `z ≥ 0`. -/
private lemma rpow_three_halves_div_sq_le_one {z : ℝ} (hz : 0 ≤ z) :
    z ^ ((3:ℝ)/2) / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact rpow_three_halves_le_sq_add_one hz

/-! ## The sanitiser and the right-Taylor extension on the closed box -/

/-- On the closed angular interval and for `τ ≥ 0`, the sanitised family is the original one. -/
private lemma gS_tauExt_eq_of_pos {α : ℝ} {g : Fam} {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ π / 2) (hτ : 0 ≤ τ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ = g z θ τ := by
  have h1 : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ
      = Work.FTS.FinalV2.tauExt g z θ τ := by
    simp [Work.FTS.FinalV2.gS, hz, hθ0, hθ1]
  rw [h1, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- The mixed slots of the sanitised family agree with those of `g` on the open quadrant. -/
private lemma mixed_gS_tauExt_eq {α : ℝ} {g : Fam} {τ z θ : ℝ} (j i : ℕ)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) (hτ : 0 ≤ τ) :
    Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z θ
      = Work.Spaces.mixed j i (slice g τ) z θ := by
  have hagree : Set.EqOn
      (Function.uncurry (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ))
      (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z', θ'⟩ hzθ'
    obtain ⟨hz', hθ'⟩ := hzθ'
    exact gS_tauExt_eq_of_pos (α := α) (g := g) hz' hθ'.1.le hθ'.2.le hτ
  have h := Work.FTS.RegPkgGal.mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hagree j i
  exact h (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ0, hθ1⟩)

/-! ## Vanishing on the degenerate set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` -/

private lemma gS_tauExt_zero_theta0 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z 0 τ = 0 := by
  by_cases hz : 0 < z
  · have h := gS_tauExt_eq_of_pos (α := α) (g := g) (z := z) (θ := 0) (τ := τ)
      hz le_rfl Real.pi_div_two_pos.le hτ
    rw [h]
    exact (hmin.vanish τ hτ z hz.le).1
  · simp [Work.FTS.FinalV2.gS, hz]

private lemma gS_tauExt_zero_pi2 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z (π / 2) τ = 0 := by
  by_cases hz : 0 < z
  · have h := gS_tauExt_eq_of_pos (α := α) (g := g) (z := z) (θ := π / 2) (τ := τ)
      hz Real.pi_div_two_pos.le le_rfl hτ
    rw [h]
    exact (hmin.vanish τ hτ z hz.le).2
  · simp [Work.FTS.FinalV2.gS, hz]

/-- At `θ = 0` the whole `z`-slice of the sanitised family vanishes, hence so does `D_z`. -/
private lemma DzG_eq_zero_theta0 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) : DzG α g z 0 τ = 0 := by
  have h1 : ∀ z' : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' 0 τ = 0 :=
    fun z' => gS_tauExt_zero_theta0 hτ hmin z'
  have h2 : (fun z' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' 0 τ)
      = fun _ => (0 : ℝ) := funext h1
  simp only [DzG, Work.Spaces.Dz, Work.Spaces.pz]
  rw [h2]
  simp

/-- At `θ = π/2` the whole `z`-slice of the sanitised family vanishes, hence so does `D_z`. -/
private lemma DzG_eq_zero_pi2 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) : DzG α g z (π/2) τ = 0 := by
  have h1 : ∀ z' : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' (π/2) τ = 0 :=
    fun z' => gS_tauExt_zero_pi2 hτ hmin z'
  have h2 : (fun z' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' (π/2) τ)
      = fun _ => (0 : ℝ) := funext h1
  simp only [DzG, Work.Spaces.Dz, Work.Spaces.pz]
  rw [h2]
  simp

/-- At `z = 0` the sanitised family vanishes identically, hence so does `D_θ`. -/
private lemma DthG_eq_zero_of_z {α : ℝ} {g : Fam} (θ τ : ℝ) : DthG α g 0 θ τ = 0 := by
  have hfun : (fun θ' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) 0 θ' τ)
      = fun _ => (0 : ℝ) := by
    funext θ'; simp [Work.FTS.FinalV2.gS]
  simp only [DthG, Work.Spaces.Dth, Work.Spaces.pth]
  rw [hfun]
  simp

/-- At `z = 0` the sanitised family vanishes identically, hence so does `D_z`. -/
private lemma DzG_eq_zero_of_z {α : ℝ} {g : Fam} (θ τ : ℝ) : DzG α g 0 θ τ = 0 := by
  simp [DzG, Work.Spaces.Dz]

theorem DzDthG_tau_mod {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.THL.DzG α g z θ τ - Work.FTS_RegExport.THL.DzG α g z θ τ'|
            ≤ L * |τ - τ'| ^ α ∧
        |Work.FTS_RegExport.THL.DthG α g z θ τ - Work.FTS_RegExport.THL.DthG α g z θ τ'|
            ≤ L * |τ - τ'| ^ α := by
  have hα1 : α ≤ 1 := by linarith
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g := hOK.1.1
  obtain ⟨L₀, hL₀0, hL₀⟩ :=
    Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus hOK.2 hαG hαG1 S hS
  have hL0 : 0 ≤ L₀ * S ^ (1 - α) := mul_nonneg hL₀0 (Real.rpow_nonneg hS.le _)
  refine ⟨L₀ * S ^ (1 - α), hL0, ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  have hτ0 : 0 ≤ τ := hτ.1
  have hτ'0 : 0 ≤ τ' := hτ'.1
  have hhd : |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := abs_sub_le_rpow hα hα1 hS hτ hτ'
  have hnn : (0:ℝ) ≤ |τ - τ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have htriv : (0:ℝ) ≤ L₀ * S ^ (1 - α) * |τ - τ'| ^ α := mul_nonneg hL0 hnn
  -- the mixed slots on the open quadrant, upgraded from Lipschitz to `α`-Hölder
  have hbound : ∀ (j i : ℕ), j + i ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z' θ'
        - Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ') z' θ'|
        ≤ L₀ * S ^ (1 - α) * |τ - τ'| ^ α := by
    intro j i hji z' θ' hz' hθ'0 hθ'1
    have e1 := mixed_gS_tauExt_eq (α := α) (g := g) (τ := τ) (z := z') (θ := θ')
      j i hz' hθ'0 hθ'1 hτ0
    have e2 := mixed_gS_tauExt_eq (α := α) (g := g) (τ := τ') (z := z') (θ := θ')
      j i hz' hθ'0 hθ'1 hτ'0
    have h3 := hL₀ τ hτ τ' hτ' j i (by omega) z' θ' hz' hθ'0 hθ'1
    calc |Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z' θ'
          - Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ') z' θ'|
        = |Work.Spaces.mixed j i (slice g τ) z' θ' - Work.Spaces.mixed j i (slice g τ') z' θ'| := by
          rw [e1, e2]
      _ ≤ L₀ * (z' ^ ((3:ℝ)/2) / (1 + z') ^ 2) * |τ - τ'| := h3
      _ ≤ L₀ * 1 * |τ - τ'| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (rpow_three_halves_div_sq_le_one hz'.le) hL₀0
      _ = L₀ * |τ - τ'| := by ring
      _ ≤ L₀ * (S ^ (1 - α) * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left hhd hL₀0
      _ = L₀ * S ^ (1 - α) * |τ - τ'| ^ α := by ring
  refine ⟨?_, ?_⟩
  · -- the `D_z` half
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [hθ0.symm, DzG_eq_zero_theta0 (α := α) (g := g) (τ := τ) hτ0 hmin z,
        DzG_eq_zero_theta0 (α := α) (g := g) (τ := τ') hτ'0 hmin z]
      simp only [sub_zero, abs_zero]
      exact htriv
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · rw [hθ1, DzG_eq_zero_pi2 (α := α) (g := g) (τ := τ) hτ0 hmin z,
          DzG_eq_zero_pi2 (α := α) (g := g) (τ := τ') hτ'0 hmin z]
        simp only [sub_zero, abs_zero]
        exact htriv
      · rcases eq_or_lt_of_le hz with hz0 | hzpos
        · rw [hz0.symm, DzG_eq_zero_of_z (α := α) (g := g) θ τ,
            DzG_eq_zero_of_z (α := α) (g := g) θ τ']
          simp only [sub_zero, abs_zero]
          exact htriv
        · exact hbound 1 0 (by norm_num) z θ hzpos hθ0 hθ1
  · -- the `D_θ` half
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [hθ0.symm]
      have h0 : DthG α g z 0 τ = 0 := by simp [DthG, Work.Spaces.Dth]
      have h0' : DthG α g z 0 τ' = 0 := by simp [DthG, Work.Spaces.Dth]
      rw [h0, h0', sub_zero, abs_zero]
      exact htriv
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · rw [hθ1]
        have hsin : Real.sin (2 * (π/2)) = 0 := by
          rw [show 2 * (π/2) = π by ring, Real.sin_pi]
        have h0 : DthG α g z (π/2) τ = 0 := by simp [DthG, Work.Spaces.Dth, hsin]
        have h0' : DthG α g z (π/2) τ' = 0 := by simp [DthG, Work.Spaces.Dth, hsin]
        rw [h0, h0', sub_zero, abs_zero]
        exact htriv
      · rcases eq_or_lt_of_le hz with hz0 | hzpos
        · rw [hz0.symm, DthG_eq_zero_of_z (α := α) (g := g) θ τ,
            DthG_eq_zero_of_z (α := α) (g := g) θ τ']
          simp only [sub_zero, abs_zero]
          exact htriv
        · exact hbound 0 1 (by norm_num) z θ hzpos hθ0 hθ1

end Work.FTS_RegExport.THL.L
end
end
