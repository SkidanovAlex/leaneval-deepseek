/-
Copyright: work module for the Elgindi finite-time singularity project.

# `fkThetaAux` — the two-dimensional inputs of the `(FK f)·D_θf` piece

Auxiliary lemmas of `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaIbpPiece`
(see `fkThetaEnd` for the estimate, `fkThetaIbpPiece` for the assembled statement):

* `fk_cont_FK` — continuity of `z ↦ (FK f)(z)` on `(0,∞)` for an interior-class datum;
* `fkTheta_ae_pos` — `z > 0` almost everywhere on `Iz = [0,∞)`;
* `fk_ibp_integrable` — the three `IntegrableOn (Iz ×ˢ Iθ)` hypotheses of the angular
  integration by parts `Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp` for an arbitrary bounded
  radial multiplier `g`, together with the outer and the a.e. slice integrability of the bare
  leaf-weighted slot.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.Construction.Basic
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000

/-! ## The angular moment of an interior-class datum is continuous on `(0,∞)` -/

/-- **Continuity of `z ↦ (FK f)(z)` on `(0,∞)`** for a datum of the interior class
(`SmoothOpen f`, `HkMem α 4 f`).  On `(0,∞)` the angular moment is the product of `z` with the
`L₁₂`-density of `f` (`Work.Construction.mul_L12dens_eq_FK`), and that density is continuous
there (`Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk`). -/
theorem fk_cont_FK {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) := by
  have hprod : ContinuousOn (fun z : ℝ => z * Work.Construction.L12dens f z) (Set.Ioi 0) :=
    continuousOn_id.mul fun z hz =>
      (Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk hSO hmem
        hz).continuousWithinAt
  refine hprod.congr (fun z hz => ?_)
  exact (Work.Construction.mul_L12dens_eq_FK (F := f) (ne_of_gt hz)).symm

/-- `z > 0` almost everywhere on `Iz = [0,∞)`. -/
theorem fkTheta_ae_pos :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  have hEq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hEq]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The integrability inputs of the angular integration by parts -/

/-- **The integrability inputs of the angular integration by parts with a radial multiplier.**

For an interior-class datum `f`, a radial multiplier `g` which is continuous on `(0,∞)` and
bounded by `A` there, a leaf exponent `q` (`q ≤ γ`, and `q ≤ η` when `a = 0`) and a slot
`(a,b)` of order `≤ 6`:

* the three products `h²·Φ`, `D_θh·h·Φ` and `h²·Φ·cos(2θ)` (with `Φ = g·w²`, all weighted by
  `σ^{-q}`) are integrable on `Iz ×ˢ Iθ` — these are the hypotheses of `wip_Dth_ibp`;
* the bare leaf-weighted slot `w²σ^{-q}·(D_z^bD_θ^af)²` is integrable on `Iz ×ˢ Iθ`, hence its
  `z`-marginal is integrable on `Iz` and its `θ`-slices are integrable for a.e. `z`.

The proof is pointwise domination: `|g z| ≤ A` and
`w²σ^{-q}(slot)² ≤ HkIntegrand α 6/7 f` (`leafdom_rpow`), plus the AM–GM splitting of
`|D_θh||h|` against the level-`6` and level-`7` integrands. -/
theorem fk_ibp_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} {A : ℝ} (g : ℝ → ℝ)
    (hα : 0 < α) (hA : 0 ≤ A) (hgc : ContinuousOn g (Set.Ioi 0))
    (hgA : ∀ z : ℝ, 0 < z → |g z| ≤ A)
    (hO : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem6 : Work.Spaces.HkMem α 6 f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {a b : ℕ} (hab : a + b ≤ 6) {q : ℝ}
    (hqle : q ≤ Work.Spaces.gam α) (hq0 : a = 0 → q ≤ Work.Spaces.eta) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2
          * (g z * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ
          * (g z * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2
          * (g z * (Work.Spaces.w z) ^ 2)
          * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) := by
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  have hQ0 : ∀ᵐ p ∂P, p ∈ Work.FTS.EllipticEst.Q0 := by
    rw [hP]; exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_mem_Q0
  have hsin_pos : ∀ᵐ p ∂P, 0 < Real.sin (2 * p.2) :=
    hQ0.mono fun p hp => by
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_nn : ∀ᵐ p ∂P, 0 ≤ Real.sin (2 * p.2) := hsin_pos.mono fun _ h => le_of_lt h
  have hsin_nn_θ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  -- the pointwise slot dominations
  have hleaf6 : ∀ᵐ p ∂P, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0] with p hp
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.StrongPersist.H6Pair6Aux.leafdom_rpow (α := α) (h := f) hα hab hqle hq0
      (Set.mem_Ici.mpr (le_of_lt hz)) ⟨h1, h2⟩
  have hleaf7 : ∀ᵐ p ∂P, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
      * (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
    filter_upwards [hQ0] with p hp
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.StrongPersist.H6Pair6Aux.leafdom_rpow (α := α) (h := f) hα
      (k := 7) (by omega) hqle (fun hc => absurd hc (by omega))
      (Set.mem_Ici.mpr (le_of_lt hz)) ⟨h1, h2⟩
  have hcomm : ∀ᵐ p ∂P, Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
      = Work.Spaces.mixed b (a + 1) f p.1 p.2 := by
    rw [hP]; exact Work.FTS.StrongPersist.H6Pair6Aux.dth_mixed_ae_eq hO a b
  have hI6 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2) P := by
    rw [hP]
    exact (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hO hmem6).1
  have hI7 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 7 f p.1 p.2) P := by
    rw [hP]
    exact (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hO hmem7).1
  have hmono67 : ∀ᵐ p ∂P, Work.Spaces.HkIntegrand α 6 f p.1 p.2
      ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 :=
    Filter.Eventually.of_forall fun p =>
      Work.Spaces.HkIntegrand_mono α 6 f p.1 p.2
  -- continuity inputs
  have hwQ : ContinuousOn (fun z : ℝ => g z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    hgc.mul Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq
  have hwQQ : ContinuousOn (fun p : ℝ × ℝ => g p.1 * (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    hwQ.comp continuous_fst.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hhc : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 := (hO.mixed b a).continuousOn
  have hsqc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_uncurry_sq hhc
  have hdhc : ContinuousOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      Work.FTS.EllipticEst.Q0 := (hO.mixed b a).Dth.continuousOn
  have hphc : ContinuousOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_uncurry_mul hdhc hhc
  -- a.e. strong measurability of the three `Φ`-integrands
  have hm0 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (g z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_two_rpow_neg q).comp
        continuous_snd.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
    exact (hsqc.mul hwQQ).mul h3
  have hm1 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
        * (g z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_two_rpow_neg q).comp
        continuous_snd.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
    exact (hphc.mul hwQQ).mul h3
  have hm2 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (g z * (Work.Spaces.w z) ^ 2)
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2))
        Work.FTS.EllipticEst.Q0 := by fun_prop
    have h4 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_two_rpow_neg q).comp
        continuous_snd.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
    exact ((hsqc.mul hwQQ).mul h3).mul h4
  -- the a.e. dominations of the three `Φ`-integrands
  have hbd0 : ∀ᵐ p ∂P, ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
        * (g p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ A * Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf6, hsin_nn] with p hp hle hσ0
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hgn : |g p.1| ≤ A := hgA p.1 hz
    have hkey : ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (g p.1 * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)‖
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hsq,
        abs_of_nonneg hσq, abs_of_nonneg hW]
    rw [hkey]
    calc Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)
        ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (A * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgn hW) hsq) hσq
      _ = A * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q) * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by ring
      _ ≤ A * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
          mul_le_mul_of_nonneg_left hle hA
  have hbd1 : ∀ᵐ p ∂P, ‖Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2
        * (g p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ A * Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf7, hleaf6, hcomm, hsin_nn, hmono67]
      with p hp hle7 hle6 hcm hσ0 hm67
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hgn : |g p.1| ≤ A := hgA p.1 hz
    have e2 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have e3 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) :=
      abs_of_nonneg hσq
    have hkey : ‖Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2
          * (g p.1 * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)‖
        = |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, e2, e3]
    rw [hkey]
    have hD : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
        = |Work.Spaces.mixed b (a + 1) f p.1 p.2| := by rw [hcm]
    have ham : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
        ≤ ((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2 := by
      rw [hD]
      nlinarith [sq_nonneg (|Work.Spaces.mixed b (a + 1) f p.1 p.2|
        - |Work.Spaces.mixed b a f p.1 p.2|),
        sq_abs (Work.Spaces.mixed b (a + 1) f p.1 p.2),
        sq_abs (Work.Spaces.mixed b a f p.1 p.2)]
    have hs1 : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
        ≤ (((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2)
          * (A * (Work.Spaces.w p.1) ^ 2) :=
      mul_le_mul ham (mul_le_mul_of_nonneg_right hgn hW) (by positivity) (by positivity)
    calc |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)
        ≤ ((((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2)
          * (A * (Work.Spaces.w p.1) ^ 2))
          * (Real.sin (2 * p.2)) ^ (-q) := mul_le_mul_of_nonneg_right hs1 hσq
      _ = A
          * (((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f p.1 p.2 ^ 2) / 2
            + ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2) := by ring
      _ ≤ A * ((Work.Spaces.HkIntegrand α 7 f p.1 p.2) / 2
            + (Work.Spaces.HkIntegrand α 7 f p.1 p.2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          exact add_le_add (div_le_div_of_nonneg_right hle7 (by norm_num))
            (div_le_div_of_nonneg_right (hle6.trans hm67) (by norm_num))
      _ = A * Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by ring
  have hbd2 : ∀ᵐ p ∂P, ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
        * (g p.1 * (Work.Spaces.w p.1) ^ 2)
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ A * Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf6, hsin_nn] with p hp hle hσ0
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hgn : |g p.1| ≤ A := hgA p.1 hz
    have hkey : ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (g p.1 * (Work.Spaces.w p.1) ^ 2)
          * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)‖
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
          * |Real.cos (2 * p.2)| * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hsq,
        abs_of_nonneg hσq, abs_of_nonneg hW]
    rw [hkey]
    have hs1 : Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
        ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (A * (Work.Spaces.w p.1) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgn hW) hsq
    calc Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|g p.1| * (Work.Spaces.w p.1) ^ 2)
          * |Real.cos (2 * p.2)| * (Real.sin (2 * p.2)) ^ (-q)
        ≤ (Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (A * (Work.Spaces.w p.1) ^ 2))
          * 1 * (Real.sin (2 * p.2)) ^ (-q) :=
          mul_le_mul (mul_le_mul hs1 (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = A * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q) * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by ring
      _ ≤ A * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
          mul_le_mul_of_nonneg_left hle hA
  -- the three `IntegrableOn` conclusions on the product measure
  have hProd : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (g z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI6.const_mul A) hm0 hbd0
  have hProd1 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
        * (g z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI7.const_mul A) hm1 hbd1
  have hProd2 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (g z * (Work.Spaces.w z) ^ 2)
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI6.const_mul A) hm2 hbd2
  -- the bare leaf-weighted slot
  have hm3 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq.comp continuous_fst.continuousOn
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_two_rpow_neg q).comp
        continuous_snd.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
    exact (h1.mul h2).mul hsqc
  have hbd3 : ∀ᵐ p ∂P, ‖(Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hleaf6, hsin_nn] with p hle hσ0
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ0 _))
        (sq_nonneg _))]
    exact hle
  have hProd3 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P :=
    MeasureTheory.Integrable.mono' hI6 hm3 hbd3
  -- the marginal and the slices
  have hOut : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz := by
    have hsplit := (MeasureTheory.integrable_prod_iff hm3).mp hProd3
    have hfun : (fun z : ℝ => ∫ θ, ‖Function.uncurry (fun z θ =>
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) (z, θ)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      funext z
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hsin_nn_θ] with θ hθ
      show ‖(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2‖
        = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg hθ _)) (sq_nonneg _))]
      ring
    rw [hfun] at hsplit
    exact hsplit.2
  have hSlice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [hProd3.prod_right_ae, fkTheta_ae_pos] with z hz hzp
    have hcoe : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have h1 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      rw [h1]
      exact pow_ne_zero 2 (div_ne_zero (by positivity) (pow_ne_zero 2 (ne_of_gt hzp)))
    refine (hz.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr (Filter.Eventually.of_forall ?_)
    intro θ
    have hinv : ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2 = 1 := inv_mul_cancel₀ hcoe
    calc ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
          rw [hinv, one_mul]
  have hconv : ∀ F : ℝ × ℝ → ℝ, MeasureTheory.Integrable F P →
      MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro F hF
    rw [MeasureTheory.IntegrableOn,
      show (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) from
        (MeasureTheory.Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ).symm]
    exact hF
  exact ⟨hconv _ hProd, hconv _ hProd1, hconv _ hProd2, hOut, hSlice⟩


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
