/-
# `fkPsi6TermBound` — the level-table bound for the `FK f`-rows of the level-six pairing

For a level-six datum `f` (`T6Coef.DatData α f M`) and `b ≤ 6`, the `b`-th `D_z`-iterate of the
angular moment `FK f` is square-summable against the *matched* angular energy
`∫_θ HkIntegrand α (6 - b) f z θ` of the datum:

  `∫_z (D_z^b (FK f) z)² · (∫_θ HkIntegrand α (6 - b) f z θ) ≤ C · M² · |f|²_{ℋ⁶}`,

with a universal constant `C`.  This is the level table of the crux `fkMulHkSqLe`
(`fkLeafSqFKf.lean`), integrated in `z`: it prices each of the seven matched summands of the
dominating function `G = Σ_{b ≤ 6} (D_z^b (FK f))² · ∫_θ HkIntegrand α (6 - b) f`.

The proof is a two-case level table.  With `fkDzdIterSqLe`
(`(D_z^b (FK f) z)² ≤ C₁ · HkSq α (b+1) f` a.e. in `z`) and `HkSq α (b+1) f ≤ HkSq α 4 f ≤ M²`
whenever `b ≤ 3`, the *low* slots are bounded pointwise by `C₁ M²` and the matched angular energy
`∫_θ HkIntegrand α (6 - b) f` is integrable with integral `HkSq α (6 - b) f ≤ HkSq α 6 f`
(`HkMem α (6 - b) f`, by monotonicity of `HkMem`).  For `b ≥ 4` the roles are exchanged: the
angular level `6 - b ≤ 2` is small, so its slice is `≤ C₂ M² (w z)²` uniformly in `z`
(`psi6LowSlice`), and the `z`-integral is `fkMomentJetSq`
(`∫_z (D_z^b (FK f) z)² (w z)² ≤ C₃ HkSq α 6 f`).  In both cases the product is integrable by
a.e. domination (its two factors are a.e. strongly measurable: the moment by continuity on the
open quadrant, the angular slice by `SmoothOpen.continuousOn_HkIntegrand`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.topSlotZLe
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.psi6LowSlice
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two helpers on the restricted radial measure `volume.restrict Iz` -/

/-- **A.e. dominated product.**  If `X, Y ≥ 0` a.e., `X * Y ≤ g` a.e. and `g` is integrable, then
`X * Y` is integrable and `∫ X*Y ≤ ∫ g`. -/
private theorem integrable_mul_of_le {X Y g : ℝ → ℝ}
    (hXnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 ≤ X z)
    (hYnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 ≤ Y z)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hXaesm : MeasureTheory.AEStronglyMeasurable X
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hYaesm : MeasureTheory.AEStronglyMeasurable Y
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), X z * Y z ≤ g z) :
    MeasureTheory.Integrable (fun z => X z * Y z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∫ z in Work.Spaces.Iz, X z * Y z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  have hmul : MeasureTheory.AEStronglyMeasurable (fun z => X z * Y z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hXaesm.mul hYaesm
  have hint : MeasureTheory.Integrable (fun z => X z * Y z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hg hmul ?_
    filter_upwards [hXnn, hYnn, hle] with z hx hy hb
    rw [Real.norm_of_nonneg (mul_nonneg hx hy)]
    exact hb
  refine ⟨hint, ?_⟩
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg hle
  filter_upwards [hXnn, hYnn] with z hx hy
  exact mul_nonneg hx hy

/-! ## A.e. strong measurability of the two factors -/

/-- The `z`-marginal `z ↦ ∫_θ HkIntegrand α k f z θ` of the level-`k` integrand of an
open-quadrant smooth datum is a.e. strongly measurable on `Iz`: the uncurried integrand is
continuous on the open quadrant (`SmoothOpen.continuousOn_HkIntegrand`). -/
private theorem aesm_HkIntegrand_zMarginal {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _
    (hF.continuousOn_HkIntegrand α k)).integral_prod_right'

/-- The squared `D_z^j`-iterate of the angular moment is a.e. strongly measurable on `Iz`: it is
the `θ`-marginal of the jointly continuous (on the open quadrant)
`(z,θ) ↦ D_z^j f z θ · K θ`. -/
private theorem aesm_FK_DzIter_sq {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Construction.FK (Work.Spaces.DzIter j f) z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter j f p.1 p.2 * Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter j).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  exact (hjoint.integral_prod_right').pow 2

/-! ## The target -/

theorem fkPsi6TermBound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      ∀ b : ℕ, b ≤ 6 →
        MeasureTheory.Integrable (fun z => (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
        (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
          ≤ C * M ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fkDzdIterSqLe
  obtain ⟨C₂, hC₂pos, hC₂⟩ := psi6LowSlice
  obtain ⟨C₃, hC₃pos, hC₃⟩ := fkMomentJetSq
  refine ⟨C₁ + C₂ * C₃ + 1, by positivity, ?_⟩
  intro α hαmem f M hD b hb
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαmem
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  -- `HkSq α 4 f ≤ M ^ 2`
  have hM4 : Work.Spaces.HkSq α 4 f ≤ M ^ 2 := by
    have hXn : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ M := hD.bdd
    have h0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 f) := Real.sqrt_nonneg _
    calc Work.Spaces.HkSq α 4 f = (Real.sqrt (Work.Spaces.HkSq α 4 f)) ^ 2 :=
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ h0 hXn 2
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- the matched level is honest
  have h6b : 6 - b ≤ 6 := by omega
  have hmem6b : Work.Spaces.HkMem α (6 - b) f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm (6 - b) h6b hD.h6
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hD.h6
  -- a.e. strong measurabilities and nonnegativities of the two factors
  have hYaesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := aesm_HkIntegrand_zMarginal hsm
  have hXaesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.DzIter b
        (fun z _ => Work.Construction.FK f z) z 0) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hae := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hD.h6 b hb
    refine (aesm_FK_DzIter_sq hsm b).congr ?_
    filter_upwards [hae] with z hz
    rw [hz 0]
  have hYnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
    Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ
  have hXnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2 :=
    Filter.Eventually.of_forall fun z => sq_nonneg _
  rcases le_or_gt b 3 with hb3 | hb3
  · -- ## the low slots `b ≤ 3`
    have hXle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          ≤ C₁ * M ^ 2 := by
      filter_upwards [hC₁ hα0 hsm hD.h6 hD.h7 b hb] with z hz
      have hmono : Work.Spaces.HkSq α (b + 1) f ≤ Work.Spaces.HkSq α 4 f :=
        Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by omega) hmem4
      calc (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          ≤ C₁ * Work.Spaces.HkSq α (b + 1) f := hz
        _ ≤ C₁ * Work.Spaces.HkSq α 4 f :=
            mul_le_mul_of_nonneg_left hmono (le_of_lt hC₁pos)
        _ ≤ C₁ * M ^ 2 := mul_le_mul_of_nonneg_left hM4 (le_of_lt hC₁pos)
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (C₁ * M ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
      filter_upwards [hXle, hYnn] with z hx hy
      exact mul_le_mul_of_nonneg_right hx hy
    have hmain := integrable_mul_of_le hXnn hYnn (hmem6b.2.const_mul (C₁ * M ^ 2))
      hXaesm hYaesm hle
    refine ⟨hmain.1, ?_⟩
    have hIntY : (∫ z in Work.Spaces.Iz,
          (C₁ * M ^ 2) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (6 - b) f z θ))
        = (C₁ * M ^ 2) * Work.Spaces.HkSq α (6 - b) f := by
      rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    have hlast : C₁ * M ^ 2 * Work.Spaces.HkSq α 6 f
        ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
      have hleC : C₁ ≤ C₁ + C₂ * C₃ + 1 := by nlinarith [hC₂pos, hC₃pos]
      have hnn : 0 ≤ M ^ 2 * Work.Spaces.HkSq α 6 f := mul_nonneg hM2 hSnn
      calc C₁ * M ^ 2 * Work.Spaces.HkSq α 6 f
          = C₁ * (M ^ 2 * Work.Spaces.HkSq α 6 f) := by ring
        _ ≤ (C₁ + C₂ * C₃ + 1) * (M ^ 2 * Work.Spaces.HkSq α 6 f) :=
            mul_le_mul_of_nonneg_right hleC hnn
        _ = (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
        ≤ ∫ z in Work.Spaces.Iz, (C₁ * M ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := hmain.2
      _ = (C₁ * M ^ 2) * Work.Spaces.HkSq α (6 - b) f := hIntY
      _ ≤ (C₁ * M ^ 2) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α h6b hD.h6) (by positivity)
      _ = C₁ * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
      _ ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := hlast
  · -- ## the high slots `4 ≤ b ≤ 6`: the matched angular level is `6 - b ≤ 2`
    have hb4 : 4 ≤ b := by omega
    have hm2 : 6 - b ≤ 2 := by omega
    -- the matched slice, uniformly in `z > 0`
    have hYle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (C₂ * M ^ 2) * (Work.Spaces.w z) ^ 2 := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)]
        with z hne hzI
      have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hzI) (Ne.symm hne)
      have h := hC₂ α hαmem f hsm hmem4 (6 - b) hm2 z hzpos
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ C₂ * Work.Spaces.HkSq α 4 f * (Work.Spaces.w z) ^ 2 := h
        _ ≤ C₂ * M ^ 2 * (Work.Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hM4 (le_of_lt hC₂pos)) hw2
        _ = (C₂ * M ^ 2) * (Work.Spaces.w z) ^ 2 := by ring
    have hI3 := hC₃ α hαmem f hsm hD.h6 b hb
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (C₂ * M ^ 2) * ((Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      filter_upwards [hYle] with z hy
      rw [Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b z 0]
      calc (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)
          ≤ (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
              * ((C₂ * M ^ 2) * (Work.Spaces.w z) ^ 2) :=
            mul_le_mul_of_nonneg_left hy (sq_nonneg _)
        _ = (C₂ * M ^ 2) * ((Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
    have hmain := integrable_mul_of_le hXnn hYnn (hI3.1.const_mul (C₂ * M ^ 2))
      hXaesm hYaesm hle
    refine ⟨hmain.1, ?_⟩
    have hlast : C₂ * C₃ * M ^ 2 * Work.Spaces.HkSq α 6 f
        ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
      have hleC : C₂ * C₃ ≤ C₁ + C₂ * C₃ + 1 := by nlinarith [hC₁pos]
      have hnn : 0 ≤ M ^ 2 * Work.Spaces.HkSq α 6 f := mul_nonneg hM2 hSnn
      calc C₂ * C₃ * M ^ 2 * Work.Spaces.HkSq α 6 f
          = C₂ * C₃ * (M ^ 2 * Work.Spaces.HkSq α 6 f) := by ring
        _ ≤ (C₁ + C₂ * C₃ + 1) * (M ^ 2 * Work.Spaces.HkSq α 6 f) :=
            mul_le_mul_of_nonneg_right hleC hnn
        _ = (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter b
            (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
        ≤ ∫ z in Work.Spaces.Iz, (C₂ * M ^ 2) * ((Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := hmain.2
      _ = (C₂ * M ^ 2) * (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter b
              (fun w => Work.Construction.FK f w) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (C₂ * M ^ 2) * (C₃ * Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left hI3.2 (by positivity)
      _ = C₂ * C₃ * M ^ 2 * Work.Spaces.HkSq α 6 f := by ring
      _ ≤ (C₁ + C₂ * C₃ + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := hlast

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
