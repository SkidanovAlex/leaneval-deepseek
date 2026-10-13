/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg.i1Paper_weakMixedLimit` — the `χ_n ↑ 1` limit of the cut-off chain

The per-`(χ_n, ψ_δ)` inequality (`Deleg.TruncPairLe`, after the `ψ_δ ↓ 0` limit
`Deleg.PairLimit`) is passed to the limit `n → ∞` here: `Dcut u n → IP (Az u) (∂_θθu)`
(`AeColl.Dcut_tendsto`), `Acut u n → IP (Uz u) (Uz u)`, `Trcut u n → IP (cw·Uz u) (∂_θθu)`
(dominated convergence with the uniform bound on `z·(cut n)'`), and in the case where the weighted
slice energy `z ↦ w z² Gcut u z` is integrable also `Pcut u n → Vfull u`.  The transfer term is
then bounded by `2√⟨U,U⟩√⟨B,B⟩` (`H2W.SlotA.IP_cw_le`), and in the non-integrable case the
inequality `κ·Pcut u n ≥ 0` together with the limits gives the required lower bound on the pairing
`IP (Az u) (∂_θθu)` directly.
-/
/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg.i1Paper_weakMixed` — the paper-shaped `I₁` lower bound, weak mixed honesty

Target (byte-for-byte the requested statement): for the almost-everywhere class
`H2W.Ae.AeData` with `HkMem α 0 (grad u)`, the a.e. slicewise mixed honesty `(H1)` and the
unweighted outer finiteness `(H2)` of `V = z∂_z∂_θu`,

```
κ·α²·HkSq α 0 (∂_θ(grad u)) − C·α²·(⟨U,U⟩ + √⟨U,U⟩·√⟨B,B⟩) ≤ α²·⟨z²∂_zzu, B⟩
```

(`U = grad u = z∂_zu`, `B = ∂_θθu`, `κ = (1-η)/(1+η)`, `⟨f,g⟩ = AngSecond.IP f g`).

## Route

The cut-off chain of `Submission/Work/FTS/EllipticEst/AeColl/`:

* `Deleg.mixedCollarBound` — the 1-D collar bound `CollarBound Cw` (the `ψ_δ''`-moment of a
  slice `f` of `U` bounded by `Cw·K` times the two collar `σ`-energies of `f'`, using the
  endpoint rate);
* `Deleg.mixedTruncPairLe` — the per-`(χ_n, ψ_δ)` inequality `TruncPairLe Cw`
  (`κ·P_χψ ≤ D_χψ + Tr_χψ − 2η·A_χψ + Cw·K·Col_χδ`), from the proved 2-D cut-off identities
  `I1Wk.truncZIbp2` and `I1Wk.truncThetaIbpSep_split`;
* `Deleg.mixedPairLimit` — the `ψ_δ ↓ 0` limit at fixed `n` (`PairLimit Cw`);
* `mixedLimitBound` (below) — the `χ_n ↑ 1` limit, with the band term of
  `∂_z(χ_n w² z²)/z` controlled by `chiDerivLimit` and the Cauchy–Schwarz bound `IP_cw_le`
  on the transfer term;
* the final assembly (below), using `AeI1Fts.HkSq_pth_grad` and `I1Wk.aeGradTrace0` to produce
  the rate constant `K`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.crossThetaIbp
import Submission.Work.FTS.EllipticEst.H2W.SlotA.I1_z_ibp_open
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.AeColl.aeGradTraceRateUnw
import Submission.Work.FTS.EllipticEst.AeColl.limitBoundAux.pieces
import Submission.Work.FTS.EllipticEst.AeColl.limitBoundAux.pieces2
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Asm
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.chiDerivLimit
import Submission.Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.Final.FlatCut.cutMono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `χ_n ↑ 1` limit** of the cut-off chain: from the per-`n` inequality
`κ·Pcut u n ≤ Dcut u n + Trcut u n − 2η·Acut u n` (the output of `Deleg.PairLimit`), the target's
`Vfull`-form follows.  The transfer term is bounded by `2√⟨U,U⟩√⟨B,B⟩`
(`H2W.SlotA.IP_cw_le`) and its cutoff band vanishes by `chiDerivLimit`. -/
theorem mixedLimitBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    (∀ n : ℕ,
      kap * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n) →
    kap * Work.FTS.EllipticEst.AeColl.Vfull u
      ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
        + C * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                  (Work.FTS.EllipticEst.AeColl.Uz u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro α u G hAe hU hcut
  have heta2 : (0 : ℝ) ≤ 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hkap : 0 ≤ kap := by
    rw [kap]
    apply div_nonneg <;> rw [Work.Spaces.eta] <;> norm_num
  have hmAB := Work.FTS.EllipticEst.AeColl.IPMem_rad2_ang2 hAe
  have hmUU := Work.FTS.EllipticEst.AeColl.IPMem_grad_self hAe hU
  have hmBB := Work.FTS.EllipticEst.AeColl.IPMem_ang2_self hAe
  have hmUB := Work.FTS.EllipticEst.AeColl.IPMem_grad_ang2 hAe hU
  -- ## the limit of `Acut`
  have hAcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Acut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
        (Work.FTS.EllipticEst.AeColl.Uz u))) := by
    set GU : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.AeColl.Uz u z θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ with hGU
    have hinner : ∀ z : ℝ,
        (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ)^2)
        = ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.AeColl.Uz u z θ)^2
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
      intro z
      rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := Real.pi / 2))]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [Work.FTS.EllipticEst.AeColl.sigθ_eq]
      ring
    have hstep : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ
          * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        = Work.FTS.EllipticEst.AeColl.wt z * GU z := by
      intro z
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ
          * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
          = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.w2 z
              * (Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.FTS.EllipticEst.AngSecond.sig θ) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
      rw [h1, MeasureTheory.integral_const_mul]
      simp only [hGU, Work.FTS.EllipticEst.AeColl.wt_eq]
      congr 1
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hAcut_eq : ∀ n : ℕ, Work.FTS.EllipticEst.AeColl.Acut u n
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
            * (Work.FTS.EllipticEst.AeColl.wt z * GU z) := by
      intro n
      rw [Work.FTS.EllipticEst.AeColl.Acut]
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      rw [← MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      simp only [hGU]
      rw [hinner z]
      ring
    have hIP_eq : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u)
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AeColl.wt z * GU z := by
      rw [Work.FTS.EllipticEst.AngSecond.IP]
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      exact hstep z
    have hGUint : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.AeColl.wt z * GU z)
        Work.Spaces.Iz := hmUU.2.congr (Filter.Eventually.of_forall hstep)
    rw [funext hAcut_eq, hIP_eq]
    exact Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hGUint
  -- ## the limit of `Trcut`
  have hTrcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Trcut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
        (Work.Spaces.pthIter 2 u))) := by
    have hYI : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AeColl.YI u) Work.Spaces.Iz :=
      Work.FTS.EllipticEst.AeColl.YI_integrable hmUB
    have hcwf_cont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AeColl.cwf z)
        Work.Spaces.Iz := by
      have h := Work.FTS.EllipticEst.H2W.SlotA.continuousOn_cw
      simpa [Work.FTS.EllipticEst.AeColl.cwf, Work.FTS.EllipticEst.AngSecond.cw] using h
    have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0:ℝ) := by
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      have hne : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), z ≠ (0:ℝ) := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hne] with z hz hzI
      exact lt_of_le_of_ne hzI (Ne.symm hz)
    have hmain : Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z) Filter.atTop
        (nhds (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AeColl.cwf z * Work.FTS.EllipticEst.AeColl.YI u z)) := by
      obtain ⟨K, hKpos, hKbd, hKcut, hKd⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
      have hdom : MeasureTheory.Integrable
          (fun z => (K + 2) * ‖Work.FTS.EllipticEst.AeColl.YI u z‖)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (hYI.norm).const_mul (K + 2)
      have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
          (fun z => Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro n
        have hd : ContinuousOn (fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z * z
            + Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.cwf z)
            Work.Spaces.Iz :=
          ((((Work.FTS.EllipticEst.cut_contDiff n).continuous_deriv (by simp)).continuousOn.mul
              continuousOn_id).add
            (((Work.FTS.EllipticEst.cut_contDiff n).continuous).continuousOn.mul hcwf_cont))
        refine (hd.aestronglyMeasurable measurableSet_Ici).mul hYI.aestronglyMeasurable |>.congr ?_
        filter_upwards with z
        simp only [Work.FTS.EllipticEst.AeColl.cfun, Pi.mul_apply]
      have hbnd : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          ‖Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z‖
            ≤ (K + 2) * ‖Work.FTS.EllipticEst.AeColl.YI u z‖ := by
        intro n
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (Work.FTS.EllipticEst.AeColl.abs_cfun_le (fun z => hKbd n z) hz) (abs_nonneg _)
      have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.cfun n z
              * Work.FTS.EllipticEst.AeColl.YI u z)
            Filter.atTop (nhds (Work.FTS.EllipticEst.AeColl.cwf z
              * Work.FTS.EllipticEst.AeColl.YI u z)) := by
        filter_upwards [hpos] with z hz
        have h1 : Filter.Tendsto (fun n : ℕ => deriv (Work.FTS.EllipticEst.cut n) z * z)
            Filter.atTop (nhds 0) := by
          have hh := hKd z
          refine hh.congr' (Filter.Eventually.of_forall (fun n => ?_))
          ring
        have h2 : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z)
            Filter.atTop (nhds 1) := hKcut z hz
        have h3 : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z
            * Work.FTS.EllipticEst.AeColl.cwf z) Filter.atTop
            (nhds (Work.FTS.EllipticEst.AeColl.cwf z)) := by
          simpa using h2.mul_const (Work.FTS.EllipticEst.AeColl.cwf z)
        have h4 := (h1.add h3).mul_const (Work.FTS.EllipticEst.AeColl.YI u z)
        simpa [Work.FTS.EllipticEst.AeColl.cfun, mul_add, add_mul] using h4
      exact MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (F := fun n z => Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z)
        (f := fun z => Work.FTS.EllipticEst.AeColl.cwf z * Work.FTS.EllipticEst.AeColl.YI u z)
        (fun z => (K + 2) * ‖Work.FTS.EllipticEst.AeColl.YI u z‖) hmeas hdom hbnd hlim
    have hIPcw : Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
          (Work.Spaces.pthIter 2 u)
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AeColl.cwf z
            * Work.FTS.EllipticEst.AeColl.YI u z := by
      rw [Work.FTS.EllipticEst.AngSecond.IP]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      rw [Work.FTS.EllipticEst.AeColl.YI]
      have hpt : (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.Spaces.pthIter 2 u z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          = fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.cw z
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.Spaces.pthIter 2 u z θ
              * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
        funext θ; ring
      rw [hpt, MeasureTheory.integral_const_mul]
      rfl
    have hTrcut_Iz : ∀ n : ℕ, Work.FTS.EllipticEst.AeColl.Trcut u n
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AeColl.cfun n z
            * Work.FTS.EllipticEst.AeColl.YI u z := by
      intro n
      rw [Work.FTS.EllipticEst.AeColl.Trcut_eq_integral u n]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))
    rw [hIPcw]
    exact hmain.congr' (Filter.Eventually.of_forall (fun n => (hTrcut_Iz n).symm))
  -- ## the limit of `Dcut`
  have hDcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Dcut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
        (Work.Spaces.pthIter 2 u))) := Work.FTS.EllipticEst.AeColl.Dcut_tendsto hmAB
  -- ## the limit of the right-hand side
  have hRHS : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Dcut u n
        + Work.FTS.EllipticEst.AeColl.Trcut u n
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
              (Work.Spaces.pthIter 2 u)
          + Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
              (Work.Spaces.pthIter 2 u)
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u))) :=
    ((hDcut_t.add hTrcut_t).sub (hAcut_t.const_mul (2 * Work.Spaces.eta)))
  -- ## nonnegativity of the right-hand side
  have hPcut_nn : ∀ n : ℕ, 0 ≤ Work.FTS.EllipticEst.AeColl.Pcut u n := by
    intro n
    rw [Work.FTS.EllipticEst.AeColl.Pcut]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun z hz => ?_)
    refine mul_nonneg (mul_nonneg (Work.FTS.EllipticEst.cut_nonneg n z) ?_) ?_
    · rw [Work.FTS.EllipticEst.AeColl.wt]; positivity
    · refine MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => ?_)
      exact mul_nonneg (Work.FTS.EllipticEst.AeColl.sigθ_nonneg_of_mem
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)
  have hnonneg : ∀ n : ℕ, (0:ℝ) ≤ Work.FTS.EllipticEst.AeColl.Dcut u n
      + Work.FTS.EllipticEst.AeColl.Trcut u n
      - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n := by
    intro n
    have h1 := hcut n
    have h2 : 0 ≤ kap * Work.FTS.EllipticEst.AeColl.Pcut u n :=
      mul_nonneg hkap (hPcut_nn n)
    linarith
  have hlim0 : (0:ℝ) ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
          (Work.Spaces.pthIter 2 u)
      + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
          (Work.Spaces.pthIter 2 u)
      - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u) :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hRHS hnonneg
  -- ## the transfer bound, and the resulting lower bound on the pairing
  have hcwle : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
        (Work.Spaces.pthIter 2 u)
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
            (Work.FTS.EllipticEst.AeColl.Uz u))
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
            (Work.Spaces.pthIter 2 u)) :=
    Work.FTS.EllipticEst.H2W.SlotA.IP_cw_le _ _ hmUU hmBB hmUB
  have hUU0 : 0 ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
      (Work.FTS.EllipticEst.AeColl.Uz u) := Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _
  have hD_lower : -(2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u)
        + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
              (Work.Spaces.pthIter 2 u))))
      ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
          (Work.Spaces.pthIter 2 u) := by
    have h2 : -(2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
            (Work.FTS.EllipticEst.AeColl.Uz u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
              (Work.Spaces.pthIter 2 u)))
        ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u) := by
      nlinarith [hlim0, hcwle, hUU0, mul_nonneg heta2 hUU0,
        Real.sqrt_nonneg (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u))]
    have hs : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u))
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
            (Work.Spaces.pthIter 2 u))
        ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
            (Work.FTS.EllipticEst.AeColl.Uz u)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u)) := by linarith [hUU0]
    linarith [h2, hs]
  by_cases hint : MeasureTheory.Integrable
      (fun z => Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
  · -- ## the honest case: `Pcut u n → Vfull u`
    have hGint : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)
        Work.Spaces.Iz := by
      show MeasureTheory.Integrable
        (fun z => Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))]
      exact hint
    have hPcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Pcut u n)
        Filter.atTop (nhds (Work.FTS.EllipticEst.AeColl.Vfull u)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z
            * (Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z))
          Filter.atTop (nhds (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)) :=
        Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hGint
      have h2 : ∀ n : ℕ, Work.FTS.EllipticEst.AeColl.Pcut u n = ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z
            * (Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z) := by
        intro n
        rw [Work.FTS.EllipticEst.AeColl.Pcut_eq_integral u n]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))
      have h3 : Work.FTS.EllipticEst.AeColl.Vfull u = ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z := by
        rw [Work.FTS.EllipticEst.AeColl.Vfull_eq_integral u]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))
      rw [funext h2, h3]
      exact h1
    have hL : Filter.Tendsto (fun n : ℕ => kap * Work.FTS.EllipticEst.AeColl.Pcut u n)
        Filter.atTop (nhds (kap * Work.FTS.EllipticEst.AeColl.Vfull u)) :=
      hPcut_t.const_mul _
    have hle := le_of_tendsto_of_tendsto' hL hRHS hcut
    have hBB0 : 0 ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
        (Work.Spaces.pthIter 2 u) := Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _
    have hfin : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
        + Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
            (Work.Spaces.pthIter 2 u)
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u)
        ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
          + 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                    (Work.FTS.EllipticEst.AeColl.Uz u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by
      have h3 : 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u))
          ≤ 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                    (Work.FTS.EllipticEst.AeColl.Uz u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by linarith [hUU0]
      have h4 : 0 ≤ 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u) :=
        mul_nonneg heta2 hUU0
      linarith [hcwle, h3, h4]
    linarith [hle, hfin]
  · -- ## the junk case: `Vfull u = 0`
    have hzero : Work.FTS.EllipticEst.AeColl.Vfull u = 0 := by
      rw [Work.FTS.EllipticEst.AeColl.Vfull_eq_integral]
      exact MeasureTheory.integral_undef hint
    rw [hzero, mul_zero]
    linarith [hD_lower]

end

end Work.FTS.EllipticEst.Deleg
