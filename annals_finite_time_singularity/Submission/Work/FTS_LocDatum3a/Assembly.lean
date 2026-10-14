import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PressureOn.OffPlanes.offPlanes_ibp
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSqJepsPzPre
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_LocDatum3a.L12_Jeps_locG6
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The `k ≤ 8` assembly, reduced to the order-`8` slot estimate.**  Given the level-zero slot
bound `hC₀` for the mollified profile `J_ε f` (all `j + i ≤ 8`), the projected counterflow obeys
`HkSq α k (Pz (J_ε f)) ≤ C (C/ε)^{2k} EpsSq α f` for every `k ≤ 8`.

The proof is verbatim that of `HkSq_JepsPz_le` (the `k ≤ 6` case), with the order-`8` bump bound
`Work.FTS.EpsEngine.exists_HkNorm_bump_le8` and the cardinal constants `9`, `81`, `90`, `180`
coming from `k + 1 ≤ 9`. -/
theorem HkSq_JepsPz_le8_of_slot (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {C₀ : ℝ} (hC₀pos : 0 < C₀)
    (hC₀ : ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) →
        Work.FTS.StrongEps.EpsMem α f →
          Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) ∧
          ∀ j i : ℕ, j + i ≤ 8 →
            (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
                  * Work.FTS.StrongEps.epsW α z θ) ^ 2))
              ≤ ENNReal.ofReal (C₀ * (C₀ / ε) ^ (2 * (j + i))
                  * Work.FTS.StrongEps.EpsSq α f)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ k : ℕ, k ≤ 8 → ∀ f : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
        Work.Spaces.HkSq α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
          ≤ C * (C / ε) ^ (2 * (k : ℕ)) * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L12_zero_le_EpsSq
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.EpsEngine.exists_HkNorm_bump_le8
  have hpz : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hKpos : 0 < max C₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hK0 : 0 ≤ (max C₀ 1 : ℝ) := hKpos.le
  let Kc : ℝ := C₁ ^ 2 * max C₀ 1 / Work.FTS.StrongEps.pzNorm ^ 2
  have hKc0 : 0 ≤ Kc := by dsimp only [Kc]; positivity
  let Cfin : ℝ := max 1 (180 * max C₀ 1 + 2 * Kc * B ^ 2 + max C₀ 1)
  have hCfin1 : 1 ≤ Cfin := le_max_left _ _
  have hCfinpos : 0 < Cfin := lt_of_lt_of_le zero_lt_one hCfin1
  have hCfinK : max C₀ 1 ≤ Cfin := by
    refine le_trans (le_add_of_nonneg_left ?_) (le_max_right _ _)
    nlinarith [hK0, hKc0, sq_nonneg B]
  have hCfinbig : 180 * max C₀ 1 + 2 * Kc * B ^ 2 ≤ Cfin := by
    refine le_trans ?_ (le_max_right _ _)
    linarith [hK0]
  have hCfinmax : max C₀ 1 ≤ Cfin := hCfinK
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro α hα ε hε0 hε1 k hk f hf hfmem
  have hα0 : 0 < α := hα.1
  obtain ⟨hEpsMem, hslot0⟩ := hC₀ α hα ε hε0 hε1 f
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf) hfmem
  let hh : ℝ → ℝ → ℝ := Work.FTS.StrongEps.Jeps ρ ε f
  let S : ℝ := Work.FTS.StrongEps.EpsSq α f
  let r : ℝ := max C₀ 1 / ε
  let cc : ℝ := Work.Construction.L12 hh 0 / Work.FTS.StrongEps.pzNorm
  have hS0 : 0 ≤ S := Work.FTS.StrongEps.EpsSq_nonneg α f
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    exact (one_le_div hε0).mpr (le_trans hε1 (le_max_right _ _))
  have hso_h : Work.FTS.EllipticEst.SmoothOpen hh := by
    dsimp only [hh]
    exact Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf)
  have hsmh : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry hh) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall hh).mp hso_h
  have hsmb : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Work.FTS.StrongEps.bump) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp Work.FTS.StrongEps.smoothOpen_bump
  -- the slot bound with the normalised constant `max C₀ 1`
  have hslot : ∀ j i : ℕ, j + i ≤ 8 →
      (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.mixed j i hh z θ * epsW α z θ) ^ 2))
        ≤ ENNReal.ofReal (max C₀ 1 * r ^ (2 * (j + i)) * S) := by
    intro j i hji
    refine (hslot0 j i hji).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (C₀ / ε) ^ (2 * (j + i)) ≤ r ^ (2 * (j + i)) :=
      pow_le_pow_left₀ (by positivity)
        (by dsimp only [r]; gcongr; exact le_max_left _ _) _
    have h2 : C₀ * (C₀ / ε) ^ (2 * (j + i)) ≤ max C₀ 1 * r ^ (2 * (j + i)) :=
      mul_le_mul (le_max_left _ _) h1 (by positivity) hK0
    exact mul_le_mul_of_nonneg_right h2 hS0
  -- a.e. measurability of the `epsW`-mixed slots
  have haesm_mixed : ∀ (j i : ℕ), AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2)) nu := by
    intro j i
    have hc : ContinuousOn
        (fun q : ℝ × ℝ => Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) Quad :=
      (Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad hsmh j i).mul
        (continuousOn_epsW_quad α)
    have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2) nu :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_sq' hc)
    exact ENNReal.measurable_ofReal.comp_aemeasurable h1.aemeasurable
  let X : ℝ≥0∞ := ENNReal.ofReal (max C₀ 1 * r ^ (2 * k) * S)
  -- the `ℋᵏ`-slot bound for `h = J_ε f`
  have hA : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
      ≤ (90 : ℝ≥0∞) * X := by
    have step1 : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        ≤ ∫⁻ q, ENNReal.ofReal (EpsSlotSum α k hh q.1 q.2) ∂nu := by
      rw [nu_eq]
      exact MeasureTheory.setLIntegral_mono' (measurableSet_Ici.prod measurableSet_Icc)
        (fun q hq => ENNReal.ofReal_le_ofReal (HkIntegrand_le_EpsSlotSum hα0 k hh hq.2))
    refine step1.trans ?_
    have heq : (fun q : ℝ × ℝ => ENNReal.ofReal (EpsSlotSum α k hh q.1 q.2))
        = fun q : ℝ × ℝ =>
            (∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
              ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2))
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) :=
      funext fun q : ℝ × ℝ => ofReal_EpsSlotSum k hh q.1 q.2
    rw [heq]
    have hAeZ : AEMeasurable (fun q : ℝ × ℝ => ∑ a ∈ Finset.range (k + 1),
        ENNReal.ofReal ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2)) nu := by
      have h := Finset.aemeasurable_sum (Finset.range (k + 1))
        (f := fun (a : ℕ) (q : ℝ × ℝ) => ENNReal.ofReal
          ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2))
        (fun a _ => by simpa only [Work.Spaces.mixed_zero_right] using haesm_mixed a 0)
      exact h.congr (Eventually.of_forall fun q => by simp only [Finset.sum_apply])
    rw [MeasureTheory.lintegral_add_left' hAeZ]
    have hZ : (∫⁻ q, ∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
          ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
        ≤ (9 : ℝ≥0∞) * X := by
      rw [lintegral_finset_sum_aemeasurable _ (fun a _ => by
        simpa only [Work.Spaces.mixed_zero_right] using haesm_mixed a 0)]
      calc ∑ a ∈ Finset.range (k + 1), (∫⁻ q, ENNReal.ofReal
            ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
          ≤ ∑ _a ∈ Finset.range (k + 1), X := by
            refine Finset.sum_le_sum fun a ha => ?_
            have hak : a ≤ k := by
              rw [Finset.mem_range] at ha; omega
            have hconv : (∫⁻ q, ENNReal.ofReal
                  ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
                = ∫⁻ q, ENNReal.ofReal
                  ((Work.Spaces.mixed a 0 hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu := by
              rw [← Work.Spaces.mixed_zero_right a hh]
            rw [hconv, ← iter_eq_nu (haesm_mixed a 0)]
            refine (hslot a 0 (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
            have h1 : r ^ (2 * (a + 0)) ≤ r ^ (2 * k) :=
              pow_le_pow_right₀ hr1 (by omega)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 hK0) hS0
        _ = (Finset.range (k + 1)).card • X := Finset.sum_const X
        _ ≤ (9 : ℝ≥0∞) * X := by
            rw [nsmul_eq_mul, Finset.card_range]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast (by omega : k + 1 ≤ 9)
    have hM : (∫⁻ q, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
        ≤ (81 : ℝ≥0∞) * X := by
      rw [lintegral_finset_sum_aemeasurable _ (fun i _ => by
        have h := Finset.aemeasurable_sum (Finset.range (k + 1))
          (f := fun (j : ℕ) (q : ℝ × ℝ) => ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0))
          (fun j _ => by
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · simpa only [if_pos hc] using haesm_mixed j i
            · simpa only [if_neg hc, ENNReal.ofReal_zero] using
                (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)) nu))
        exact h.congr (Eventually.of_forall fun q => by simp only [Finset.sum_apply]))]
      calc ∑ i ∈ Finset.range (k + 1), (∫⁻ q, ∑ j ∈ Finset.range (k + 1),
            ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
          ≤ ∑ _i ∈ Finset.range (k + 1), (9 : ℝ≥0∞) * X := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [lintegral_finset_sum_aemeasurable _ (fun j _ => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · simpa only [if_pos hc] using haesm_mixed j i
              · simpa only [if_neg hc, ENNReal.ofReal_zero] using
                  (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)) nu))]
            calc ∑ j ∈ Finset.range (k + 1), (∫⁻ q, ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
                ≤ ∑ _j ∈ Finset.range (k + 1), X := by
                  refine Finset.sum_le_sum fun j hj => ?_
                  by_cases hc : 1 ≤ i ∧ i + j ≤ k
                  · have hfun : (fun q : ℝ × ℝ => ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                        (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0))
                        = fun q : ℝ × ℝ => ENNReal.ofReal
                          ((Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2) := by
                      funext q; rw [if_pos hc]
                    rw [hfun, ← iter_eq_nu (haesm_mixed j i)]
                    refine (hslot j i (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
                    have h1 : r ^ (2 * (j + i)) ≤ r ^ (2 * k) :=
                      pow_le_pow_right₀ hr1 (by omega)
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left h1 hK0) hS0
                  · have hfun : (fun q : ℝ × ℝ => ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                        (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0))
                        = fun _ : ℝ × ℝ => (0 : ℝ≥0∞) := by
                      funext q; rw [if_neg hc, ENNReal.ofReal_zero]
                    rw [hfun]
                    simp
              _ = (Finset.range (k + 1)).card • X := Finset.sum_const X
              _ ≤ (9 : ℝ≥0∞) * X := by
                  rw [nsmul_eq_mul, Finset.card_range]
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact_mod_cast (by omega : k + 1 ≤ 9)
        _ = (Finset.range (k + 1)).card • ((9 : ℝ≥0∞) * X) := Finset.sum_const _
        _ ≤ (9 : ℝ≥0∞) * ((9 : ℝ≥0∞) * X) := by
            rw [nsmul_eq_mul, Finset.card_range]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast (by omega : k + 1 ≤ 9)
        _ = (81 : ℝ≥0∞) * X := by rw [← mul_assoc]; norm_num
    calc (∫⁻ q, ∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
            ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
          + (∫⁻ q, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
        ≤ (9 : ℝ≥0∞) * X + (81 : ℝ≥0∞) * X := add_le_add hZ hM
      _ = (90 : ℝ≥0∞) * X := by rw [← add_mul]; norm_num
  -- the bump integral
  have hBint : (∫⁻ q, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
      ≤ ENNReal.ofReal (B ^ 2) := by
    rw [← ofReal_HkSq_eq_nuLint (Work.FTS.StrongEps.PZeroAux.hkMem_bump α k) hsmb]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hB α hα k hk
    rw [Work.Spaces.HkNorm] at h1
    have h2 : 0 ≤ Work.Spaces.HkSq α k Work.FTS.StrongEps.bump :=
      Work.Spaces.HkSq_nonneg α k _
    have h3 : (Real.sqrt (Work.Spaces.HkSq α k Work.FTS.StrongEps.bump)) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt h2] at h3
  -- the coefficient bound
  have hSe : Work.FTS.StrongEps.EpsSq α hh ≤ max C₀ 1 * S := by
    have h00 := hslot 0 0 (by norm_num : (0 : ℕ) + 0 ≤ 8)
    have h2 := ofReal_EpsSq_le_iter α hh
    have h3 : ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α hh)
        ≤ ENNReal.ofReal (max C₀ 1 * r ^ (2 * 0) * S) := h2.trans h00
    have h4 := (ENNReal.ofReal_le_ofReal_iff
      (by positivity : (0 : ℝ) ≤ max C₀ 1 * r ^ (2 * 0) * S)).mp h3
    simpa using h4
  have hcc : cc ^ 2 ≤ Kc * S := by
    have hl := hC₁ α hα hh hEpsMem
    have hl2 : (Work.Construction.L12 hh 0) ^ 2
        ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α hh)) ^ 2 := by
      nlinarith [hl, neg_abs_le (Work.Construction.L12 hh 0),
        le_abs_self (Work.Construction.L12 hh 0)]
    calc cc ^ 2
        = (Work.Construction.L12 hh 0) ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 := by
          dsimp only [cc]; rw [div_pow]
      _ ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α hh)) ^ 2
            / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right hl2 (by positivity)
      _ = C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α hh / Work.FTS.StrongEps.pzNorm ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Work.FTS.StrongEps.EpsSq_nonneg α hh)]
      _ ≤ C₁ ^ 2 * (max C₀ 1 * S) / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSe (sq_nonneg C₁))
            (by positivity)
      _ = Kc * S := by dsimp only [Kc]; ring
  -- smoothness of the projection
  have heqPz : Work.FTS.StrongEps.Pz hh
      = fun z θ => hh z θ + (-cc) * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    dsimp only [cc]
    ring
  have hsoPz : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Pz hh) := by
    rw [heqPz]
    exact Work.FTS.EllipticEst.smoothOpen_add hso_h
      (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-cc)
        Work.FTS.StrongEps.smoothOpen_bump)
  have hsmPz : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.Pz hh)) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoPz
  let gr : ℝ → ℝ → ℝ := fun z θ => (-cc) * Work.FTS.StrongEps.bump z θ
  have hsmgr : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry gr) Quad := by
    intro n
    have hfun : Function.uncurry gr
        = fun q : ℝ × ℝ => (-cc) * Work.FTS.StrongEps.bump q.1 q.2 := by
      funext q; rcases q with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (contDiffOn_const (c := -cc) (s := Quad)).mul (hsmb n)
  have hPzeq' : (fun z θ => hh z θ + gr z θ) = Work.FTS.StrongEps.Pz hh := by
    funext z θ
    show hh z θ + (-cc) * Work.FTS.StrongEps.bump z θ = Work.FTS.StrongEps.Pz hh z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    dsimp only [cc]
    ring
  have hptPz : ∀ q ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2)
        ≤ 2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2)
          + ENNReal.ofReal (2 * cc ^ 2) * ENNReal.ofReal
              (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) := by
    intro q hq
    have hsqrt := Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_sqrt_add_le α k hsmh hsmgr
      q.1 hq.1 q.2 hq.2
    rw [hPzeq'] at hsqrt
    have hA0 : 0 ≤ Work.Spaces.HkIntegrand α k hh q.1 q.2 :=
      Work.Spaces.HkIntegrand_nonneg α k hh q.1 q.2
    have hB0 : 0 ≤ Work.Spaces.HkIntegrand α k gr q.1 q.2 :=
      Work.Spaces.HkIntegrand_nonneg α k gr q.1 q.2
    have hX0 : 0 ≤ Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2 :=
      Work.Spaces.HkIntegrand_nonneg α k (Work.FTS.StrongEps.Pz hh) q.1 q.2
    have hsq : Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2
        ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k hh q.1 q.2)
            + Real.sqrt (Work.Spaces.HkIntegrand α k gr q.1 q.2)) ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
      rwa [Real.sq_sqrt hX0] at h
    have hAB : (Real.sqrt (Work.Spaces.HkIntegrand α k hh q.1 q.2)
          + Real.sqrt (Work.Spaces.HkIntegrand α k gr q.1 q.2)) ^ 2
        ≤ 2 * Work.Spaces.HkIntegrand α k hh q.1 q.2
          + 2 * Work.Spaces.HkIntegrand α k gr q.1 q.2 := by
      rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
      nlinarith [sq_nonneg (Real.sqrt (Work.Spaces.HkIntegrand α k hh q.1 q.2)
        - Real.sqrt (Work.Spaces.HkIntegrand α k gr q.1 q.2)), Real.sq_sqrt hA0,
        Real.sq_sqrt hB0]
    have hgr : Work.Spaces.HkIntegrand α k gr q.1 q.2
        = cc ^ 2 * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2 := by
      have h := Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k (-cc)
        Work.FTS.StrongEps.bump q.1 q.2
      rw [h]; ring
    have hreal : Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2
        ≤ 2 * Work.Spaces.HkIntegrand α k hh q.1 q.2
          + 2 * cc ^ 2 * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2 := by
      refine hsq.trans (hAB.trans (le_of_eq ?_))
      rw [hgr]; ring
    calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2)
        ≤ ENNReal.ofReal (2 * Work.Spaces.HkIntegrand α k hh q.1 q.2
            + 2 * cc ^ 2 * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 * Work.Spaces.HkIntegrand α k hh q.1 q.2)
            + ENNReal.ofReal (2 * cc ^ 2
                * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) :=
          ENNReal.ofReal_add
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
              (Work.Spaces.HkIntegrand_nonneg α k hh q.1 q.2))
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg cc))
              (Work.Spaces.HkIntegrand_nonneg α k Work.FTS.StrongEps.bump q.1 q.2))
      _ = 2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2)
            + ENNReal.ofReal (2 * cc ^ 2)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * cc ^ 2),
            show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  -- the integral level split
  have hAeA : AEMeasurable (fun q : ℝ × ℝ =>
      2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2)) nu :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (aesm_HkIntegrand_nu hsmh).aemeasurable).const_mul 2
  have hAeA' : AEMeasurable (fun q : ℝ × ℝ =>
      2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2))
      ((volume.prod volume).restrict (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (π / 2))) := by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume)
      (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) (π / 2))]
    exact hAeA
  have hPzsplit : (∫⁻ q, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2) ∂nu)
      ≤ 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        + ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu) := by
    rw [nu_eq]
    refine (MeasureTheory.setLIntegral_mono' (measurableSet_Ici.prod measurableSet_Icc)
      (fun q hq => hptPz q hq)).trans ?_
    rw [MeasureTheory.lintegral_add_left' hAeA',
      MeasureTheory.lintegral_const_mul' (2 : ℝ≥0∞) _
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
      MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (2 * cc ^ 2)) _
        ENNReal.ofReal_ne_top]
    exact le_rfl
  have hstep : 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        + ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
      ≤ ENNReal.ofReal ((180 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S) := by
    have h1 : 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        ≤ 2 * ((90 : ℝ≥0∞) * X) := mul_le_mul_of_nonneg_left hA (by norm_num)
    have h180 : 2 * ((90 : ℝ≥0∞) * X) = (180 : ℝ≥0∞) * X := by
      rw [← mul_assoc]; norm_num
    have h2 : ENNReal.ofReal (2 * cc ^ 2) ≤ ENNReal.ofReal (2 * Kc * S) :=
      ENNReal.ofReal_le_ofReal (by linarith [hcc])
    have h3 : ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
          (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
        ≤ ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2) :=
      mul_le_mul h2 hBint (zero_le) (by positivity)
    have hXeq : (180 : ℝ≥0∞) * X = ENNReal.ofReal (180 * (max C₀ 1 * r ^ (2 * k) * S)) := by
      dsimp only [X]
      rw [show (180 : ℝ≥0∞) = ENNReal.ofReal (180 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 180)]
    have hBeq : ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2)
        = ENNReal.ofReal (2 * Kc * S * B ^ 2) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    have hrpow : 1 ≤ r ^ (2 * k) := one_le_pow₀ hr1
    have hkey : 2 * Kc * S * B ^ 2 ≤ 2 * Kc * B ^ 2 * r ^ (2 * k) * S := by
      have h0 : 0 ≤ 2 * Kc * B ^ 2 * S := by positivity
      calc 2 * Kc * S * B ^ 2 = (2 * Kc * B ^ 2 * S) * 1 := by ring
        _ ≤ (2 * Kc * B ^ 2 * S) * r ^ (2 * k) := mul_le_mul_of_nonneg_left hrpow h0
        _ = 2 * Kc * B ^ 2 * r ^ (2 * k) * S := by ring
    have hfinal2 : 180 * (max C₀ 1 * r ^ (2 * k) * S) + 2 * Kc * S * B ^ 2
        ≤ (180 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S := by
      have hexp : (180 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S
          = 180 * (max C₀ 1 * r ^ (2 * k) * S) + 2 * Kc * B ^ 2 * r ^ (2 * k) * S := by
        ring
      rw [hexp]
      linarith [hkey]
    calc 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
          + ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
              (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
        ≤ 2 * ((90 : ℝ≥0∞) * X) + ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2) :=
          add_le_add h1 h3
      _ = (180 : ℝ≥0∞) * X + ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2) := by
          rw [h180]
      _ = ENNReal.ofReal (180 * (max C₀ 1 * r ^ (2 * k) * S))
            + ENNReal.ofReal (2 * Kc * S * B ^ 2) := by rw [hXeq, hBeq]
      _ = ENNReal.ofReal (180 * (max C₀ 1 * r ^ (2 * k) * S) + 2 * Kc * S * B ^ 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ((180 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S) :=
          ENNReal.ofReal_le_ofReal hfinal2
  have hfin : ENNReal.ofReal (Work.Spaces.HkSq α k (Work.FTS.StrongEps.Pz hh))
      ≤ ENNReal.ofReal (Cfin * (Cfin / ε) ^ (2 * k) * S) := by
    refine (ofReal_HkSq_le_nuLint hsmPz).trans (hPzsplit.trans (hstep.trans ?_))
    refine ENNReal.ofReal_le_ofReal ?_
    have hrle : r ≤ Cfin / ε := by
      dsimp only [r]
      exact div_le_div_of_nonneg_right hCfinK hε0.le
    have h2 : r ^ (2 * k) ≤ (Cfin / ε) ^ (2 * k) := pow_le_pow_left₀ hr0 hrle _
    have h3 : (180 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) ≤ Cfin * (Cfin / ε) ^ (2 * k) :=
      mul_le_mul hCfinbig h2 (by positivity) hCfinpos.le
    exact mul_le_mul_of_nonneg_right h3 hS0
  exact (ENNReal.ofReal_le_ofReal_iff
    (by positivity : (0 : ℝ) ≤ Cfin * (Cfin / ε) ^ (2 * k) * S)).mp hfin

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.PressureOn.div_vorticity_mul_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫ x, div ω x * ψ x = 0` for `ω = ∇ × u` (the divergence of a curl integrates to zero)

The main result `Work.FTS.PressureOn.div_vorticity_mul_eq_zero` is assembled here from two
ingredients:

* `Work.FTS.PressureOn.OffPlanes.offPlanes_ibp` — the per-coordinate integration by parts for a
  function `g` that is differentiable only off the two coordinate planes `x 0 = 0` and `x 2 = 0`
  (the standing hypothesis on `ω = ∇ × u`), applied to the coordinate functions `x ↦ ω x i`;
* `Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero` — the vanishing of the
  pairing `∫ x, ⟪∇ × u x, ∇ψ x⟫`, which is the step in which the curl structure of `ω` is used.

The plumbing in between is developped in this file: the coordinate functions and their
differentiability, the trace identity `div ω = ∑ i, ∂ᵢωᵢ` (almost everywhere, which is what makes
the identity available in the integral), the identity `⟪ω x, ∇ψ x⟫ = ∑ i, ω x i * ∂ᵢψ x`, and the
nullity of the two coordinate planes.
-/

open FiniteTimeSingularity MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

noncomputable section

/-! ## The coordinate functions of a vector field -/

/-- The `i`-th coordinate function of a vector field. -/
def coord (i : Fin 3) (ω : R3 → R3) : R3 → ℝ := fun x => WithLp.ofLp (ω x) i

@[simp] theorem coord_apply (i : Fin 3) (ω : R3 → R3) (x : R3) : coord i ω x = ω x i := rfl

theorem continuous_coord (i : Fin 3) {ω : R3 → R3} (hω : Continuous ω) :
    Continuous (coord i ω) :=
  (continuous_apply i).comp (ofLpCLM.continuous.comp hω)

theorem hasCompactSupport_coord (i : Fin 3) {ω : R3 → R3} (hω : HasCompactSupport ω) :
    HasCompactSupport (coord i ω) :=
  hω.mono (fun x hx => by
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [coord, h]))

/-- A vector field with bounded support (given as a pointwise norm bound on the nonzero values)
has compact support. -/
theorem hasCompactSupport_of_norm_bound {ω : R3 → R3} {R : ℝ}
    (h : ∀ x, ω x ≠ 0 → ‖x‖ ≤ R) : HasCompactSupport ω :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R)
    (fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact h x hx)

/-- **The derivative of a coordinate function** is the composition of the derivative of the field
with the projection onto that coordinate. -/
theorem fderiv_coord (i : Fin 3) {ω : R3 → R3} {x : R3} (hx : DifferentiableAt ℝ ω x) :
    fderiv ℝ (coord i ω) x
      = (ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x)) := by
  have h1 : HasFDerivAt (fun y : R3 => WithLp.ofLp (ω y))
      (ofLpCLM.comp (fderiv ℝ ω x)) x :=
    (ContinuousLinearMap.hasFDerivAt ofLpCLM).comp x hx.hasFDerivAt
  have h3 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i)).comp x h1
  exact h3.fderiv

/-- The evaluation form of `fderiv_coord`: the `i`-th coordinate of the partial derivative is
the partial derivative of the `i`-th coordinate function. -/
theorem fderiv_coord_apply (i j : Fin 3) {ω : R3 → R3} {x : R3} (hx : DifferentiableAt ℝ ω x) :
    fderiv ℝ (coord i ω) x (e j) = (fderiv ℝ ω x (e j)) i := by
  rw [fderiv_coord i hx]
  simp [ContinuousLinearMap.comp_apply, ofLpCLM_apply, ContinuousLinearMap.proj_apply]

/-- A coordinate function of a field differentiable off the two planes is differentiable off the
two planes. -/
theorem hasFDerivAt_coord_of_off_planes (i : Fin 3) {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    {x : R3} (h0 : x 0 ≠ 0) (h2 : x 2 ≠ 0) :
    HasFDerivAt (coord i ω)
      ((ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x))) x := by
  have hx := hωdiff x h0 h2
  have h1 : HasFDerivAt (fun y : R3 => WithLp.ofLp (ω y))
      (ofLpCLM.comp (fderiv ℝ ω x)) x :=
    (ContinuousLinearMap.hasFDerivAt ofLpCLM).comp x hx
  have h3 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i)).comp x h1
  exact h3

/-! ## The nullity of the coordinate planes -/

/-- A coordinate hyperplane in `Fin 3 → ℝ` is Lebesgue-null. -/
theorem volume_fin3_coord_eq_zero (i : Fin 3) (c : ℝ) :
    volume {p : Fin 3 → ℝ | p i = c} = 0 := by
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i c

/-- A coordinate hyperplane in `ℝ³` is Lebesgue-null. -/
theorem volume_coord_eq_zero (i : Fin 3) (c : ℝ) : volume {x : R3 | x i = c} = 0 := by
  have hset : {x : R3 | x i = c} = toLpCLE '' {p : Fin 3 → ℝ | p i = c} := by
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.ofLp x, by simpa [toLpCLE_apply] using hx, toLpCLE_apply (WithLp.ofLp x)⟩
    · rintro ⟨p, hp, rfl⟩
      simpa [toLpCLE_apply] using hp
  rw [hset, ← toLpCLE_measurePreserving.measure_preimage_emb toLpCLE_measurableEmbedding]
  rw [Set.preimage_image_eq _ toLpCLE.injective]
  exact volume_fin3_coord_eq_zero i c

/-- Almost every point of `ℝ³` is a point of differentiability of a field that is differentiable
off the two coordinate planes. -/
theorem ae_differentiableAt_of_off_planes {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ ω x := by
  filter_upwards [ae_coord_ne_zero] with x hx
  exact (hωdiff x hx.1 hx.2).differentiableAt

/-! ## The trace identity and the gradient identity -/

/-- **The trace identity, almost everywhere.**  Off the two coordinate planes `div ω` is the sum
of the coordinatewise partial derivatives. -/
theorem div_ae_eq_sum_fderiv_coord {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x) :
    div ω =ᵐ[volume] fun x => ∑ i, fderiv ℝ (coord i ω) x (e i) := by
  filter_upwards [ae_differentiableAt_of_off_planes hωdiff] with x hx
  rw [div_eq_sum_single]
  exact Finset.sum_congr rfl fun i _ => (fderiv_coord_apply i i hx).symm

/-- **The gradient identity.**  The inner product of `ω x` with `∇ψ x` is the sum of the
coordinatewise products. -/
theorem inner_gradient_eq_sum_fderiv (ω : R3 → R3) (ψ : R3 → ℝ) (x : R3) :
    inner ℝ (ω x) (gradient ψ x) = ∑ i, ω x i * fderiv ℝ ψ x (e i) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (gradient ψ x) i = fderiv ℝ ψ x (e i) := by
    rw [← inner_e_eq_apply (gradient ψ x) i, inner_gradient_left]
  rw [h1, RCLike.inner_apply]
  simp [mul_comm]

/-- The basis vector `e i` has norm one. -/
theorem norm_e (i : Fin 3) : ‖(e i : R3)‖ = 1 := by
  have h : (e i : R3) = EuclideanSpace.single i (1 : ℝ) := rfl
  rw [h, EuclideanSpace.norm_single, norm_one]

/-- **The `i`-th coordinate of a vector is bounded by its norm.** -/
theorem norm_coord_le (w : R3) (i : Fin 3) : ‖w i‖ ≤ ‖w‖ := by
  calc ‖w i‖ = |inner ℝ w (e i)| := by rw [Real.norm_eq_abs, inner_e_eq_apply]
    _ ≤ ‖w‖ * ‖(e i : R3)‖ := abs_real_inner_le_norm _ _
    _ = ‖w‖ := by rw [norm_e i, mul_one]

/-- **The derivative of a coordinate function is locally integrable.** -/
theorem locallyIntegrable_fderiv_coord (i : Fin 3) {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) :
    MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (coord i ω) x) := by
  have hae : (fun x => fderiv ℝ (coord i ω) x)
      =ᵐ[volume] fun x => (ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x)) := by
    filter_upwards [ae_differentiableAt_of_off_planes hωdiff] with x hx
    exact fderiv_coord i hx
  have hcont : Continuous fun L : R3 →L[ℝ] R3 =>
      (ContinuousLinearMap.proj i).comp (ofLpCLM.comp L) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ (coord i ω) x) volume :=
    ((hcont.measurable.comp_aemeasurable
      hωint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable).congr hae.symm
  refine hωint.mono hmeas ?_
  filter_upwards [hae] with x hx
  rw [hx]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun (v : R3) => ?_
  have h1 : ((ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x))) v
      = (fderiv ℝ ω x v) i := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ofLpCLM_apply]
  rw [h1]
  exact le_trans (norm_coord_le (fderiv ℝ ω x v) i) (ContinuousLinearMap.le_opNorm _ v)

/-- **Integrability of the coordinatewise product.**  The product of `ψ` with the `i`-th partial
derivative of a field differentiable off the two coordinate planes is integrable. -/
theorem integrable_mul_fderiv_coord_self {ω : R3 → R3} {ψ : R3 → ℝ} (i : Fin 3)
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    Integrable (fun x => ψ x * fderiv ℝ (coord i ω) x (e i)) := by
  have hae : (fun x => fderiv ℝ (coord i ω) x (e i))
      =ᵐ[volume] fun x => (fderiv ℝ ω x (e i)) i := by
    filter_upwards [ae_differentiableAt_of_off_planes hωdiff] with x hx
    exact fderiv_coord_apply i i hx
  have hcont : Continuous (fun L : R3 →L[ℝ] R3 => (L (e i)) i) := by fun_prop
  have hne : ‖(e i : R3)‖ = 1 := by
    have h : (e i : R3) = EuclideanSpace.single i (1 : ℝ) := rfl
    rw [h, EuclideanSpace.norm_single, norm_one]
  have hloc : LocallyIntegrable (fun x => (fderiv ℝ ω x (e i)) i) :=
    hωint.mono
      (hcont.measurable.comp_aemeasurable hωint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        refine le_trans (norm_coord_le _ i) ?_
        have h1 : ‖(fderiv ℝ ω x) (e i)‖ ≤ ‖fderiv ℝ ω x‖ * ‖(e i : R3)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        rw [hne, mul_one] at h1
        exact h1)
  have hloc' : LocallyIntegrable (fun x => fderiv ℝ (coord i ω) x (e i)) := hloc.congr hae.symm
  obtain ⟨C, hC⟩ := (hψcs.isCompact).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  have hK : IntegrableOn (fun x => fderiv ℝ (coord i ω) x (e i)) (tsupport ψ) :=
    hloc'.integrableOn_isCompact hψcs.isCompact
  refine Integrable.mono' (IntegrableOn.integrable_indicator
    (hK.norm.const_mul C) hψcs.isCompact.measurableSet) ?_ ?_
  · exact hψ.continuous.aestronglyMeasurable.mul hloc'.aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ tsupport ψ
    · rw [Set.indicator_of_mem hx, norm_mul]
      gcongr
      exact hC x hx
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]

/-- **The pairing of `div ω` with `ψ` as a sum of coordinate pairings.** -/
theorem integral_div_mul_eq_sum_fderiv_coord {ω : R3 → R3} {ψ : R3 → ℝ}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, div ω x * ψ x = ∑ i, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i) := by
  have hB : ∀ i : Fin 3, Integrable (fun x => ψ x * fderiv ℝ (coord i ω) x (e i)) :=
    fun i => integrable_mul_fderiv_coord_self i hωdiff hωint hψ hψcs
  have hsplit := div_ae_eq_sum_fderiv_coord hωdiff
  calc ∫ x, div ω x * ψ x
      = ∫ x, (∑ i, fderiv ℝ (coord i ω) x (e i)) * ψ x := by
        refine integral_congr_ae ?_
        filter_upwards [hsplit] with x hx
        rw [hx]
      _ = ∑ i, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i) := by
        rw [show (fun x : R3 => (∑ i, fderiv ℝ (coord i ω) x (e i)) * ψ x)
            = fun x => ∑ i, fderiv ℝ (coord i ω) x (e i) * ψ x from
          funext fun x => Finset.sum_mul Finset.univ (fun i => fderiv ℝ (coord i ω) x (e i)) (ψ x)]
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])
        · intro i _
          exact (hB i).congr (Filter.Eventually.of_forall fun x => by simp [mul_comm])

/-- **The pairing of `ω` with `∇ψ` as a sum of coordinate pairings.** -/
theorem integral_inner_gradient_eq_sum_fderiv_psi {ω : R3 → R3} {ψ : R3 → ℝ}
    (hωcont : Continuous ω) (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, inner ℝ (ω x) (gradient ψ x) = ∑ i, ∫ x, ω x i * fderiv ℝ ψ x (e i) := by
  have hB : ∀ i : Fin 3, Integrable (fun x => ω x i * fderiv ℝ ψ x (e i)) := by
    intro i
    have hcont1 : Continuous (fun x : R3 => fderiv ℝ ψ x (e i)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs1 : HasCompactSupport (fun x : R3 => fderiv ℝ ψ x (e i)) :=
      hasCompactSupport_fderiv_apply_e hψcs i
    have hcont : Continuous (fun x : R3 => ω x i * fderiv ℝ ψ x (e i)) :=
      ((continuous_apply i).comp (ofLpCLM.continuous.comp hωcont)).mul hcont1
    exact hcont.integrable_of_hasCompactSupport (hcs1.mul_left (f := fun x => ω x i))
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    filter_upwards with x
    rw [inner_gradient_eq_sum_fderiv]
  · intro i _
    exact hB i

theorem div_vorticity_mul_eq_zero {u ω : R3 → R3}
    (hu : ContDiff ℝ 1 u) (hcurl : ∀ x, FiniteTimeSingularity.vorticity u x = ω x)
    (hωcont : Continuous ω) (hsuppω : ∃ R, ∀ x, ω x ≠ 0 → ‖x‖ ≤ R)
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, FiniteTimeSingularity.div ω x * ψ x = 0 := by
  obtain ⟨R, hR⟩ := hsuppω
  have hcs : HasCompactSupport ω := hasCompactSupport_of_norm_bound hR
  -- Step 1: the per-coordinate integration by parts (differentiability off the planes)
  have hIBP : ∀ i : Fin 3, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i)
      = -∫ x, coord i ω x * fderiv ℝ ψ x (e i) := by
    intro i
    refine OffPlanes.offPlanes_ibp i (continuous_coord i hωcont)
      (hasCompactSupport_coord i hcs) ?_ (locallyIntegrable_fderiv_coord i hωdiff hωint) hψ hψcs
    intro x h0 h2
    simpa [fderiv_coord i ((hωdiff x h0 h2).differentiableAt)]
      using hasFDerivAt_coord_of_off_planes i hωdiff h0 h2
  -- Step 2: the two summation identities
  have hsum1 := integral_div_mul_eq_sum_fderiv_coord hωdiff hωint hψ hψcs
  have hsum2 := integral_inner_gradient_eq_sum_fderiv_psi hωcont hψ hψcs
  have hsum3 : (∑ i, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i))
      = -∑ i, ∫ x, coord i ω x * fderiv ℝ ψ x (e i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hIBP i
  have hfin : ∑ i, ∫ x, coord i ω x * fderiv ℝ ψ x (e i)
      = ∫ x, inner ℝ (ω x) (gradient ψ x) := by
    rw [hsum2]
    exact Finset.sum_congr rfl fun i _ =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [coord])
  -- Step 3: the pairing of `∇ψ` with the curl vanishes (the curl structure enters here)
  have hcurl0 : ∫ x, inner ℝ (ω x) (gradient ψ x) = 0 := by
    simpa only [hcurl] using CurlGrad.vorticity_gradient_integral_eq_zero hu hψ hψcs
  rw [hsum1, hsum3, hfin, hcurl0, neg_zero]

end

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E1_norm_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The level-`n` weighted slot bound for `L₁₂ f` in the open class: the `E1Open` version, with
the angular-moment input supplied by `E1Open.Qang_sq_w_sq_le_HkSq_O`. -/
theorem L12f_slot_le_O :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α n f :=
  E1Open.L12f_slot_le_O_of (CQ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
    (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _))
    (fun β m g hβ hβ1 hso hm i hi =>
      E1Open.Qang_sq_w_sq_le_HkSq_O m β g hβ hβ1 hso hm i hi)

/-- The level-`n` radial slot bound for `radA α f` on the open class. -/
theorem radA_slotSum_le :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cs * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
  E1Open.radA_slotSum_le_O L12f_slot_le_O


theorem E1_norm_O :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) :=
  E1Open.E1_norm_O_of radA_slotSum_le

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.MuBlockDiffSmoothMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The difference of two modulation blocks is `C^∞` on the open quadrant and honestly in
`ℋ⁴`.**

Both modulation constants `μ`, `μ̄` of the block are *scalars* which depend on the profile only
through integrals, so the block is the linear combination

  `muBlock α Φs E W = -μ̄(W)·AK α - μ(W)·W - κ(W)·(D_z W)`,   `κ(W) = μ+λ+μλ`, `λ = lamfun μ`,

of the *fixed* profile `AK α` and of `W` and `D_z W`.  Hence

  `muBlock W₁ - muBlock W₂ = -(μ̄₁-μ̄₂)·AK α - μ₁·(W₁-W₂) - (μ₁-μ₂)·W₂
        - κ₁·(D_z(W₁-W₂)) - (κ₁-κ₂)·D_z W₂`

on the open quadrant, and each of the five summands is smooth / in `ℋ⁴` provided by the data of
the two class-`C` profiles (plus the universal datum `AK α`).

The statement is independent of `Φs` and `E`, precisely because those enter the block only
through the two scalars `μ̄(W)` and `μ(W)`. -/
theorem MuBlockDiffSmoothMem {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hW₁ : Work.FTS.ClassC.ClassC α W₁) (hW₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
        - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ) ∧
    Work.Spaces.HkMem α 4 (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
        - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ) := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the difference profile `h = W₁ - W₂` and the fields derived from it
  have hh_sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub hW₁.reg hW₂.reg
  have hmem7h : Work.Spaces.HkMem α 7 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 7)
      (u := fun z θ => W₁ z θ + (-1 : ℝ) * W₂ z θ)
      (v := fun z θ => W₁ z θ - W₂ z θ)
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 7 hW₁.reg
        (Work.FTS.NonlinRows.smoothOpen_const_mul (-1 : ℝ) hW₂.reg)
        hW₁.mem (Work.FTS.LocData.HkMem_const_mul α 7 (-1 : ℝ) hW₂.mem))
      (fun z _ θ _ => by ring)
  have hmem5h : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hh_sm 5 (by norm_num) hmem7h
  have hmem4h : Work.Spaces.HkMem α 4 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hh_sm 4 (by norm_num) hmem7h
  have hmem4₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 4 (by norm_num) hW₂.mem
  have hmem5₂ : Work.Spaces.HkMem α 5 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 5 (by norm_num) hW₂.mem
  have hDzh_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ)) := hh_sm.Dz
  have hDzh_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hh_sm hmem5h
  have hDz₂_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz W₂) := hW₂.reg.Dz
  have hDz₂_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W₂) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hW₂.reg hmem5₂
  -- ## the fixed datum `AK α`
  have hAK_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hAK_mem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  -- ## the four scalars of the two blocks
  set mb₁ : ℝ := mubarOf α Φs E W₁ with hmb₁
  set mb₂ : ℝ := mubarOf α Φs E W₂ with hmb₂
  set mu₁ : ℝ := muOf α Φs E W₁ with hmu₁
  set mu₂ : ℝ := muOf α Φs E W₂ with hmu₂
  set ka₁ : ℝ := mu₁ + Work.Construction.lamfun mu₁
    + mu₁ * Work.Construction.lamfun mu₁ with hka₁
  set ka₂ : ℝ := mu₂ + Work.Construction.lamfun mu₂
    + mu₂ * Work.Construction.lamfun mu₂ with hka₂
  -- ## the five summands of the telescoped block
  set f₁ : ℝ → ℝ → ℝ := fun z θ => (-(mb₁ - mb₂)) * Work.Construction.AK α z θ with hf₁
  set f₂ : ℝ → ℝ → ℝ := fun z θ => (-mu₁) * (W₁ z θ - W₂ z θ) with hf₂
  set f₃ : ℝ → ℝ → ℝ := fun z θ => (-(mu₁ - mu₂)) * W₂ z θ with hf₃
  set f₄ : ℝ → ℝ → ℝ :=
    fun z θ => (-ka₁) * Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ with hf₄
  set f₅ : ℝ → ℝ → ℝ := fun z θ => (-(ka₁ - ka₂)) * Work.Spaces.Dz W₂ z θ with hf₅
  have hf₁_sm : Work.FTS.EllipticEst.SmoothOpen f₁ := by
    rw [hf₁]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hAK_sm
  have hf₂_sm : Work.FTS.EllipticEst.SmoothOpen f₂ := by
    rw [hf₂]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hh_sm
  have hf₃_sm : Work.FTS.EllipticEst.SmoothOpen f₃ := by
    rw [hf₃]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hW₂.reg
  have hf₄_sm : Work.FTS.EllipticEst.SmoothOpen f₄ := by
    rw [hf₄]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hDzh_sm
  have hf₅_sm : Work.FTS.EllipticEst.SmoothOpen f₅ := by
    rw [hf₅]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hDz₂_sm
  have hf₁_mem : Work.Spaces.HkMem α 4 f₁ := by
    rw [hf₁]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hAK_mem
  have hf₂_mem : Work.Spaces.HkMem α 4 f₂ := by
    rw [hf₂]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hmem4h
  have hf₃_mem : Work.Spaces.HkMem α 4 f₃ := by
    rw [hf₃]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hmem4₂
  have hf₄_mem : Work.Spaces.HkMem α 4 f₄ := by
    rw [hf₄]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hDzh_mem
  have hf₅_mem : Work.Spaces.HkMem α 4 f₅ := by
    rw [hf₅]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hDz₂_mem
  -- ## the telescoped block
  set u : ℝ → ℝ → ℝ := fun z θ =>
    (-(mb₁ - mb₂)) * Work.Construction.AK α z θ
      + (-mu₁) * (W₁ z θ - W₂ z θ)
      + (-(mu₁ - mu₂)) * W₂ z θ
      + (-ka₁) * Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
      + (-(ka₁ - ka₂)) * Work.Spaces.Dz W₂ z θ with hu
  have hu_sm : Work.FTS.EllipticEst.SmoothOpen u := by
    rw [hu]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_add
        (Work.FTS.NonlinRows.smoothOpen_add
          (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm) hf₃_sm) hf₄_sm) hf₅_sm
  have hu_mem : Work.Spaces.HkMem α 4 u := by
    rw [hu]
    exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4
      (Work.FTS.NonlinRows.smoothOpen_add (Work.FTS.NonlinRows.smoothOpen_add
        (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm) hf₃_sm) hf₄_sm) hf₅_sm
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4
        (Work.FTS.NonlinRows.smoothOpen_add (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm)
          hf₃_sm) hf₄_sm
        (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4
          (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm) hf₃_sm
          (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hf₁_sm hf₂_sm
            hf₁_mem hf₂_mem) hf₃_mem) hf₄_mem) hf₅_mem
  -- ## the pointwise telescoping identity on the open quadrant
  have key : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      u z θ = muBlock α Φs E W₁ z θ - muBlock α Φs E W₂ z θ := by
    intro z θ hz hθ0 hθ1
    have hDzlin : Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
        = Work.Spaces.Dz W₁ z θ - Work.Spaces.Dz W₂ z θ := by
      have h := Dz_add_of_smoothOpen (f := W₁) (f' := fun z θ => W₁ z θ - W₂ z θ) (k := W₂)
        hh_sm hW₂.reg (fun z θ => by ring)
      have h' := h z θ hz hθ0 hθ1
      linarith
    rw [hu]
    simp only [hmb₁, hmb₂, hmu₁, hmu₂, hka₁, hka₂, muBlock_apply, Work.Construction.Nstar]
    rw [hDzlin]
    ring
  refine ⟨?_, ?_⟩
  · -- ## the `SmoothOpen` conjunct
    refine Work.FTS.PhiStar.CoreAux.SmoothOpen.congr hu_sm ?_
    intro z θ hz hθ0 hθ1
    exact key z θ hz hθ0 hθ1
  · -- ## the `HkMem` conjunct
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 4) hu_mem ?_
    intro z hz θ hθ
    exact key z θ hz hθ.1 hθ.2

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The target.**  `J_ε` maps the weighted space `X` of the `ε`-scheme into the projected
`ℋᵏ`-space, at a cost of one factor `C/ε` per derivative. -/
theorem HkSq_JepsPz_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ k : ℕ, k ≤ 6 → ∀ f : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
        Work.Spaces.HkSq α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
          ≤ C * (C / ε) ^ (2 * (k : ℕ)) * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := EpsSqIter_mixed_Jeps_le6 ρ hρ
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L12_zero_le_EpsSq
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpz : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hKpos : 0 < max C₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hK0 : 0 ≤ (max C₀ 1 : ℝ) := hKpos.le
  let Kc : ℝ := C₁ ^ 2 * max C₀ 1 / Work.FTS.StrongEps.pzNorm ^ 2
  have hKc0 : 0 ≤ Kc := by dsimp only [Kc]; positivity
  let Cfin : ℝ := max 1 (112 * max C₀ 1 + 2 * Kc * B ^ 2 + max C₀ 1)
  have hCfin1 : 1 ≤ Cfin := le_max_left _ _
  have hCfinpos : 0 < Cfin := lt_of_lt_of_le zero_lt_one hCfin1
  have hCfinK : max C₀ 1 ≤ Cfin := by
    refine le_trans (le_add_of_nonneg_left ?_) (le_max_right _ _)
    nlinarith [hK0, hKc0, sq_nonneg B]
  have hCfinbig : 112 * max C₀ 1 + 2 * Kc * B ^ 2 ≤ Cfin := by
    refine le_trans ?_ (le_max_right _ _)
    linarith [hK0]
  have hCfinmax : max C₀ 1 ≤ Cfin := hCfinK
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro α hα ε hε0 hε1 k hk f hf hfmem
  have hα0 : 0 < α := hα.1
  obtain ⟨hEpsMem, hslot0⟩ := hC₀ α hα ε hε0 hε1 f
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf) hfmem
  let hh : ℝ → ℝ → ℝ := Work.FTS.StrongEps.Jeps ρ ε f
  let S : ℝ := Work.FTS.StrongEps.EpsSq α f
  let r : ℝ := max C₀ 1 / ε
  let cc : ℝ := Work.Construction.L12 hh 0 / Work.FTS.StrongEps.pzNorm
  have hS0 : 0 ≤ S := Work.FTS.StrongEps.EpsSq_nonneg α f
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    exact (one_le_div hε0).mpr (le_trans hε1 (le_max_right _ _))
  have hso_h : Work.FTS.EllipticEst.SmoothOpen hh := by
    dsimp only [hh]
    exact Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf)
  have hsmh : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry hh) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall hh).mp hso_h
  have hsmb : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Work.FTS.StrongEps.bump) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp Work.FTS.StrongEps.smoothOpen_bump
  -- the slot bound with the normalised constant `max C₀ 1`
  have hslot : ∀ j i : ℕ, j + i ≤ 6 →
      (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.mixed j i hh z θ * epsW α z θ) ^ 2))
        ≤ ENNReal.ofReal (max C₀ 1 * r ^ (2 * (j + i)) * S) := by
    intro j i hji
    refine (hslot0 j i hji).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (C₀ / ε) ^ (2 * (j + i)) ≤ r ^ (2 * (j + i)) :=
      pow_le_pow_left₀ (by positivity)
        (by dsimp only [r]; gcongr; exact le_max_left _ _) _
    have h2 : C₀ * (C₀ / ε) ^ (2 * (j + i)) ≤ max C₀ 1 * r ^ (2 * (j + i)) :=
      mul_le_mul (le_max_left _ _) h1 (by positivity) hK0
    exact mul_le_mul_of_nonneg_right h2 hS0
  -- a.e. measurability of the `epsW`-mixed slots
  have haesm_mixed : ∀ (j i : ℕ), AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2)) nu := by
    intro j i
    have hc : ContinuousOn
        (fun q : ℝ × ℝ => Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) Quad :=
      (Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad hsmh j i).mul
        (continuousOn_epsW_quad α)
    have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2) nu :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_sq' hc)
    exact ENNReal.measurable_ofReal.comp_aemeasurable h1.aemeasurable
  let X : ℝ≥0∞ := ENNReal.ofReal (max C₀ 1 * r ^ (2 * k) * S)
  -- the `ℋᵏ`-slot bound for `h = J_ε f`
  have hA : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
      ≤ (56 : ℝ≥0∞) * X := by
    have step1 : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        ≤ ∫⁻ q, ENNReal.ofReal (EpsSlotSum α k hh q.1 q.2) ∂nu := by
      rw [nu_eq]
      exact MeasureTheory.setLIntegral_mono' (measurableSet_Ici.prod measurableSet_Icc)
        (fun q hq => ENNReal.ofReal_le_ofReal (HkIntegrand_le_EpsSlotSum hα0 k hh hq.2))
    refine step1.trans ?_
    have heq : (fun q : ℝ × ℝ => ENNReal.ofReal (EpsSlotSum α k hh q.1 q.2))
        = fun q : ℝ × ℝ =>
            (∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
              ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2))
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) :=
      funext fun q : ℝ × ℝ => ofReal_EpsSlotSum k hh q.1 q.2
    rw [heq]
    have hAeZ : AEMeasurable (fun q : ℝ × ℝ => ∑ a ∈ Finset.range (k + 1),
        ENNReal.ofReal ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2)) nu := by
      have h := Finset.aemeasurable_sum (Finset.range (k + 1))
        (f := fun (a : ℕ) (q : ℝ × ℝ) => ENNReal.ofReal
          ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2))
        (fun a _ => by simpa only [Work.Spaces.mixed_zero_right] using haesm_mixed a 0)
      exact h.congr (Eventually.of_forall fun q => by simp only [Finset.sum_apply])
    rw [MeasureTheory.lintegral_add_left' hAeZ]
    have hZ : (∫⁻ q, ∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
          ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
        ≤ (7 : ℝ≥0∞) * X := by
      rw [lintegral_finset_sum_aemeasurable _ (fun a _ => by
        simpa only [Work.Spaces.mixed_zero_right] using haesm_mixed a 0)]
      calc ∑ a ∈ Finset.range (k + 1), (∫⁻ q, ENNReal.ofReal
            ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
          ≤ ∑ _a ∈ Finset.range (k + 1), X := by
            refine Finset.sum_le_sum fun a ha => ?_
            have hak : a ≤ k := by
              rw [Finset.mem_range] at ha; omega
            have hconv : (∫⁻ q, ENNReal.ofReal
                  ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
                = ∫⁻ q, ENNReal.ofReal
                  ((Work.Spaces.mixed a 0 hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu := by
              rw [← Work.Spaces.mixed_zero_right a hh]
            rw [hconv, ← iter_eq_nu (haesm_mixed a 0)]
            refine (hslot a 0 (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
            have h1 : r ^ (2 * (a + 0)) ≤ r ^ (2 * k) :=
              pow_le_pow_right₀ hr1 (by omega)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 hK0) hS0
        _ = (Finset.range (k + 1)).card • X := Finset.sum_const X
        _ ≤ (7 : ℝ≥0∞) * X := by
            rw [nsmul_eq_mul, Finset.card_range]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast (by omega : k + 1 ≤ 7)
    have hM : (∫⁻ q, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
        ≤ (49 : ℝ≥0∞) * X := by
      rw [lintegral_finset_sum_aemeasurable _ (fun i _ => by
        have h := Finset.aemeasurable_sum (Finset.range (k + 1))
          (f := fun (j : ℕ) (q : ℝ × ℝ) => ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0))
          (fun j _ => by
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · simpa only [if_pos hc] using haesm_mixed j i
            · simpa only [if_neg hc, ENNReal.ofReal_zero] using
                (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)) nu))
        exact h.congr (Eventually.of_forall fun q => by simp only [Finset.sum_apply]))]
      calc ∑ i ∈ Finset.range (k + 1), (∫⁻ q, ∑ j ∈ Finset.range (k + 1),
            ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
          ≤ ∑ _i ∈ Finset.range (k + 1), (7 : ℝ≥0∞) * X := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [lintegral_finset_sum_aemeasurable _ (fun j _ => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · simpa only [if_pos hc] using haesm_mixed j i
              · simpa only [if_neg hc, ENNReal.ofReal_zero] using
                  (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)) nu))]
            calc ∑ j ∈ Finset.range (k + 1), (∫⁻ q, ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
                ≤ ∑ _j ∈ Finset.range (k + 1), X := by
                  refine Finset.sum_le_sum fun j hj => ?_
                  by_cases hc : 1 ≤ i ∧ i + j ≤ k
                  · have hfun : (fun q : ℝ × ℝ => ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                        (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0))
                        = fun q : ℝ × ℝ => ENNReal.ofReal
                          ((Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2) := by
                      funext q; rw [if_pos hc]
                    rw [hfun, ← iter_eq_nu (haesm_mixed j i)]
                    refine (hslot j i (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
                    have h1 : r ^ (2 * (j + i)) ≤ r ^ (2 * k) :=
                      pow_le_pow_right₀ hr1 (by omega)
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left h1 hK0) hS0
                  · have hfun : (fun q : ℝ × ℝ => ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                        (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0))
                        = fun _ : ℝ × ℝ => (0 : ℝ≥0∞) := by
                      funext q; rw [if_neg hc, ENNReal.ofReal_zero]
                    rw [hfun]
                    simp
              _ = (Finset.range (k + 1)).card • X := Finset.sum_const X
              _ ≤ (7 : ℝ≥0∞) * X := by
                  rw [nsmul_eq_mul, Finset.card_range]
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact_mod_cast (by omega : k + 1 ≤ 7)
        _ = (Finset.range (k + 1)).card • ((7 : ℝ≥0∞) * X) := Finset.sum_const _
        _ ≤ (7 : ℝ≥0∞) * ((7 : ℝ≥0∞) * X) := by
            rw [nsmul_eq_mul, Finset.card_range]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast (by omega : k + 1 ≤ 7)
        _ = (49 : ℝ≥0∞) * X := by rw [← mul_assoc]; norm_num
    calc (∫⁻ q, ∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
            ((Work.Spaces.DzIter a hh q.1 q.2 * epsW α q.1 q.2) ^ 2) ∂nu)
          + (∫⁻ q, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i hh q.1 q.2 * epsW α q.1 q.2) ^ 2 else 0) ∂nu)
        ≤ (7 : ℝ≥0∞) * X + (49 : ℝ≥0∞) * X := add_le_add hZ hM
      _ = (56 : ℝ≥0∞) * X := by rw [← add_mul]; norm_num
  -- the bump integral
  have hBint : (∫⁻ q, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
      ≤ ENNReal.ofReal (B ^ 2) := by
    rw [← ofReal_HkSq_eq_nuLint (Work.FTS.StrongEps.PZeroAux.hkMem_bump α k) hsmb]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hB α hα k hk
    rw [Work.Spaces.HkNorm] at h1
    have h2 : 0 ≤ Work.Spaces.HkSq α k Work.FTS.StrongEps.bump :=
      Work.Spaces.HkSq_nonneg α k _
    have h3 : (Real.sqrt (Work.Spaces.HkSq α k Work.FTS.StrongEps.bump)) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt h2] at h3
  -- the coefficient bound
  have hSe : Work.FTS.StrongEps.EpsSq α hh ≤ max C₀ 1 * S := by
    have h00 := hslot 0 0 (by norm_num : (0 : ℕ) + 0 ≤ 6)
    have h2 := ofReal_EpsSq_le_iter α hh
    have h3 : ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α hh)
        ≤ ENNReal.ofReal (max C₀ 1 * r ^ (2 * 0) * S) := h2.trans h00
    have h4 := (ENNReal.ofReal_le_ofReal_iff
      (by positivity : (0 : ℝ) ≤ max C₀ 1 * r ^ (2 * 0) * S)).mp h3
    simpa using h4
  have hcc : cc ^ 2 ≤ Kc * S := by
    have hl := hC₁ α hα hh hEpsMem
    have hl2 : (Work.Construction.L12 hh 0) ^ 2
        ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α hh)) ^ 2 := by
      nlinarith [hl, neg_abs_le (Work.Construction.L12 hh 0),
        le_abs_self (Work.Construction.L12 hh 0)]
    calc cc ^ 2
        = (Work.Construction.L12 hh 0) ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 := by
          dsimp only [cc]; rw [div_pow]
      _ ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α hh)) ^ 2
            / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right hl2 (by positivity)
      _ = C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α hh / Work.FTS.StrongEps.pzNorm ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Work.FTS.StrongEps.EpsSq_nonneg α hh)]
      _ ≤ C₁ ^ 2 * (max C₀ 1 * S) / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSe (sq_nonneg C₁))
            (by positivity)
      _ = Kc * S := by dsimp only [Kc]; ring
  -- smoothness of the projection
  have heqPz : Work.FTS.StrongEps.Pz hh
      = fun z θ => hh z θ + (-cc) * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    dsimp only [cc]
    ring
  have hsoPz : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Pz hh) := by
    rw [heqPz]
    exact Work.FTS.EllipticEst.smoothOpen_add hso_h
      (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-cc)
        Work.FTS.StrongEps.smoothOpen_bump)
  have hsmPz : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.Pz hh)) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoPz
  let gr : ℝ → ℝ → ℝ := fun z θ => (-cc) * Work.FTS.StrongEps.bump z θ
  have hsmgr : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry gr) Quad := by
    intro n
    have hfun : Function.uncurry gr
        = fun q : ℝ × ℝ => (-cc) * Work.FTS.StrongEps.bump q.1 q.2 := by
      funext q; rcases q with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (contDiffOn_const (c := -cc) (s := Quad)).mul (hsmb n)
  have hPzeq' : (fun z θ => hh z θ + gr z θ) = Work.FTS.StrongEps.Pz hh := by
    funext z θ
    show hh z θ + (-cc) * Work.FTS.StrongEps.bump z θ = Work.FTS.StrongEps.Pz hh z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    dsimp only [cc]
    ring
  have hptPz : ∀ q ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2)
        ≤ 2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2)
          + ENNReal.ofReal (2 * cc ^ 2) * ENNReal.ofReal
              (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) := by
    intro q hq
    have hsqrt := Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_sqrt_add_le α k hsmh hsmgr
      q.1 hq.1 q.2 hq.2
    rw [hPzeq'] at hsqrt
    have hA0 : 0 ≤ Work.Spaces.HkIntegrand α k hh q.1 q.2 :=
      Work.Spaces.HkIntegrand_nonneg α k hh q.1 q.2
    have hB0 : 0 ≤ Work.Spaces.HkIntegrand α k gr q.1 q.2 :=
      Work.Spaces.HkIntegrand_nonneg α k gr q.1 q.2
    have hX0 : 0 ≤ Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2 :=
      Work.Spaces.HkIntegrand_nonneg α k (Work.FTS.StrongEps.Pz hh) q.1 q.2
    have hsq : Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2
        ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k hh q.1 q.2)
            + Real.sqrt (Work.Spaces.HkIntegrand α k gr q.1 q.2)) ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
      rwa [Real.sq_sqrt hX0] at h
    have hAB : (Real.sqrt (Work.Spaces.HkIntegrand α k hh q.1 q.2)
          + Real.sqrt (Work.Spaces.HkIntegrand α k gr q.1 q.2)) ^ 2
        ≤ 2 * Work.Spaces.HkIntegrand α k hh q.1 q.2
          + 2 * Work.Spaces.HkIntegrand α k gr q.1 q.2 := by
      rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
      nlinarith [sq_nonneg (Real.sqrt (Work.Spaces.HkIntegrand α k hh q.1 q.2)
        - Real.sqrt (Work.Spaces.HkIntegrand α k gr q.1 q.2)), Real.sq_sqrt hA0,
        Real.sq_sqrt hB0]
    have hgr : Work.Spaces.HkIntegrand α k gr q.1 q.2
        = cc ^ 2 * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2 := by
      have h := Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k (-cc)
        Work.FTS.StrongEps.bump q.1 q.2
      rw [h]; ring
    have hreal : Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2
        ≤ 2 * Work.Spaces.HkIntegrand α k hh q.1 q.2
          + 2 * cc ^ 2 * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2 := by
      refine hsq.trans (hAB.trans (le_of_eq ?_))
      rw [hgr]; ring
    calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2)
        ≤ ENNReal.ofReal (2 * Work.Spaces.HkIntegrand α k hh q.1 q.2
            + 2 * cc ^ 2 * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 * Work.Spaces.HkIntegrand α k hh q.1 q.2)
            + ENNReal.ofReal (2 * cc ^ 2
                * Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) :=
          ENNReal.ofReal_add
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
              (Work.Spaces.HkIntegrand_nonneg α k hh q.1 q.2))
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg cc))
              (Work.Spaces.HkIntegrand_nonneg α k Work.FTS.StrongEps.bump q.1 q.2))
      _ = 2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2)
            + ENNReal.ofReal (2 * cc ^ 2)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * cc ^ 2),
            show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  -- the integral level split
  have hAeA : AEMeasurable (fun q : ℝ × ℝ =>
      2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2)) nu :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (aesm_HkIntegrand_nu hsmh).aemeasurable).const_mul 2
  have hAeA' : AEMeasurable (fun q : ℝ × ℝ =>
      2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2))
      ((volume.prod volume).restrict (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (π / 2))) := by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume)
      (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) (π / 2))]
    exact hAeA
  have hPzsplit : (∫⁻ q, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Pz hh) q.1 q.2) ∂nu)
      ≤ 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        + ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu) := by
    rw [nu_eq]
    refine (MeasureTheory.setLIntegral_mono' (measurableSet_Ici.prod measurableSet_Icc)
      (fun q hq => hptPz q hq)).trans ?_
    rw [MeasureTheory.lintegral_add_left' hAeA',
      MeasureTheory.lintegral_const_mul' (2 : ℝ≥0∞) _
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
      MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (2 * cc ^ 2)) _
        ENNReal.ofReal_ne_top]
    exact le_rfl
  have hstep : 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        + ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
      ≤ ENNReal.ofReal ((112 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S) := by
    have h1 : 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
        ≤ 2 * ((56 : ℝ≥0∞) * X) := mul_le_mul_of_nonneg_left hA (by norm_num)
    have h112 : 2 * ((56 : ℝ≥0∞) * X) = (112 : ℝ≥0∞) * X := by
      rw [← mul_assoc]; norm_num
    have h2 : ENNReal.ofReal (2 * cc ^ 2) ≤ ENNReal.ofReal (2 * Kc * S) :=
      ENNReal.ofReal_le_ofReal (by linarith [hcc])
    have h3 : ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
          (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
        ≤ ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2) :=
      mul_le_mul h2 hBint (zero_le) (by positivity)
    have hXeq : (112 : ℝ≥0∞) * X = ENNReal.ofReal (112 * (max C₀ 1 * r ^ (2 * k) * S)) := by
      dsimp only [X]
      rw [show (112 : ℝ≥0∞) = ENNReal.ofReal (112 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 112)]
    have hBeq : ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2)
        = ENNReal.ofReal (2 * Kc * S * B ^ 2) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    have hrpow : 1 ≤ r ^ (2 * k) := one_le_pow₀ hr1
    have hkey : 2 * Kc * S * B ^ 2 ≤ 2 * Kc * B ^ 2 * r ^ (2 * k) * S := by
      have h0 : 0 ≤ 2 * Kc * B ^ 2 * S := by positivity
      calc 2 * Kc * S * B ^ 2 = (2 * Kc * B ^ 2 * S) * 1 := by ring
        _ ≤ (2 * Kc * B ^ 2 * S) * r ^ (2 * k) := mul_le_mul_of_nonneg_left hrpow h0
        _ = 2 * Kc * B ^ 2 * r ^ (2 * k) * S := by ring
    have hfinal2 : 112 * (max C₀ 1 * r ^ (2 * k) * S) + 2 * Kc * S * B ^ 2
        ≤ (112 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S := by
      have hexp : (112 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S
          = 112 * (max C₀ 1 * r ^ (2 * k) * S) + 2 * Kc * B ^ 2 * r ^ (2 * k) * S := by
        ring
      rw [hexp]
      linarith [hkey]
    calc 2 * (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k hh q.1 q.2) ∂nu)
          + ENNReal.ofReal (2 * cc ^ 2) * (∫⁻ q, ENNReal.ofReal
              (Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump q.1 q.2) ∂nu)
        ≤ 2 * ((56 : ℝ≥0∞) * X) + ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2) :=
          add_le_add h1 h3
      _ = (112 : ℝ≥0∞) * X + ENNReal.ofReal (2 * Kc * S) * ENNReal.ofReal (B ^ 2) := by
          rw [h112]
      _ = ENNReal.ofReal (112 * (max C₀ 1 * r ^ (2 * k) * S))
            + ENNReal.ofReal (2 * Kc * S * B ^ 2) := by rw [hXeq, hBeq]
      _ = ENNReal.ofReal (112 * (max C₀ 1 * r ^ (2 * k) * S) + 2 * Kc * S * B ^ 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ((112 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) * S) :=
          ENNReal.ofReal_le_ofReal hfinal2
  have hfin : ENNReal.ofReal (Work.Spaces.HkSq α k (Work.FTS.StrongEps.Pz hh))
      ≤ ENNReal.ofReal (Cfin * (Cfin / ε) ^ (2 * k) * S) := by
    refine (ofReal_HkSq_le_nuLint hsmPz).trans (hPzsplit.trans (hstep.trans ?_))
    refine ENNReal.ofReal_le_ofReal ?_
    have hrle : r ≤ Cfin / ε := by
      dsimp only [r]
      exact div_le_div_of_nonneg_right hCfinK hε0.le
    have h2 : r ^ (2 * k) ≤ (Cfin / ε) ^ (2 * k) := pow_le_pow_left₀ hr0 hrle _
    have h3 : (112 * max C₀ 1 + 2 * Kc * B ^ 2) * r ^ (2 * k) ≤ Cfin * (Cfin / ε) ^ (2 * k) :=
      mul_le_mul hCfinbig h2 (by positivity) hCfinpos.le
    exact mul_le_mul_of_nonneg_right h3 hS0
  exact (ENNReal.ofReal_le_ofReal_iff
    (by positivity : (0 : ℝ) ≤ Cfin * (Cfin / ε) ^ (2 * k) * S)).mp hfin

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.Min.L12Cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The `L₁₂`-facts of the open-quadrant finite-order class

This module assembles, for a datum `f` which is `ContDiffOn ℝ 4` on the open quadrant and lies
in `ℋ⁴`: integrability of the `L₁₂`-density on `(0,∞)`, integrability of the angular slice
`θ ↦ K θ f z θ / z` on `Iθ` for `z > 0`, and continuity of the `L₁₂`-density at every `z > 0`.

The last one is the only non-trivial part: `L12dens K f s = 3·F_*(f)(s)/s`
(`HardyAlt.L12dens_eq_three_Fstar`), so it suffices to prove the continuity of the angular moment
`F_*(f)`.  The latter is `Fstar_continuousAt_of_chain`, applied to the four analytic inputs of
the sibling `Pieces` modules: the chain relation `Pieces.moment_relation_of_contDiffOn_four`, the
box integrability `Pieces.pzSqSeta_box_integrable_of_contDiffOn_four`, the slice integrability
`Pieces.slice_sinCos2_integrable_of_contDiffOn_four` and the moment bound
`Pieces.pzMoment_le_sqrt_of_contDiffOn_four`.
-/

/-- Integrability of the `L₁₂`-density of a continuous datum of `ℋ⁴`. -/
theorem L12dens_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
  Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hC hmem

/-- Integrability of the angular slice `θ ↦ K θ f z θ / z` of a continuous datum of `ℋ⁴`. -/
theorem sliceK_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
  Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hC hmem

/-- Continuity of the `L₁₂`-density of a `C⁴`-datum of `ℋ⁴`. -/
theorem L12dens_continuousAt_of_contDiffOn_four (α : ℝ) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hC : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z := by
  have hbox := Work.FTS.MeridianDyn.Bridge.Pieces.pzSqSeta_box_integrable_of_contDiffOn_four
    α hC hmem
  have hsl := Work.FTS.MeridianDyn.Bridge.Pieces.slice_sinCos2_integrable_of_contDiffOn_four
    hC hmem
  have hmom := Work.FTS.MeridianDyn.Bridge.Pieces.pzMoment_le_sqrt_of_contDiffOn_four
    α hC hmem
  have hchain : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b = Work.Elliptic.Fstar f a
        + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ) :=
    fun a b ha hab =>
      Work.FTS.MeridianDyn.Bridge.Pieces.moment_relation_of_contDiffOn_four f hC hbox hsl ha hab
  have hF : ContinuousAt (Work.Elliptic.Fstar f) z :=
    Fstar_continuousAt_of_chain α hz hchain hsl hmem.2 hmom
  have hdiv : ContinuousAt (fun s : ℝ => 3 * Work.Elliptic.Fstar f s / s) z :=
    (hF.const_mul 3).div continuousAt_id (ne_of_gt hz)
  exact hdiv.congr (Filter.Eventually.of_forall fun s =>
    (Work.FTS.CoercivityFix.Coer1T.HardyAlt.L12dens_eq_three_Fstar f s).symm)

end Work.FTS_FinalLeaves.Min
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## `fsm`: the angular moment of the log-mollified datum -/

/-- The `fsm` clause of `ClassC` for the localised datum: `F_*(J_ε (locG6 α L β))` is `C^∞` on
`(0,∞)`.  This is the separable form of `contDiffOn_Fstar_Jeps_sep`, read through
`locG6 α L β = locR α L β · Γ`. -/
theorem contDiffOn_Fstar_Jeps_locG6 {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {α L β : ℝ}
    (hα : 0 < α) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε (locG6 α L β))) (Set.Ioi 0) := by
  have h : locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  rw [h]
  exact contDiffOn_Fstar_Jeps_sep (α := α) (a := Work.FTS.LocDataExt.locR α L β)
    hρ hε hα ((Work.FTS.LocDataExt.contDiffOn_locR α L β).mono
      (Set.Ioi_subset_Ioi (by norm_num)))

/-! ## The source class `ClassC` -/

/-- **The localised datum with the mollifier applied is in the elliptic source class**:
`ClassC α (J_ε (locG6 α L β))`. -/
theorem classC_Jeps_locG6 {α L β : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (h12 : Work.Construction.L12 (locG6 α L β) 0 = 0) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Jeps ρ ε (locG6 α L β)) := by
  obtain ⟨hbdd, hz0, hzin, ht0, ht1⟩ := BdryTraces_data_locG6 α L β hα hα1 hL
  have hsoft : Work.FTS.StrongEps.SoftClass α (Work.FTS.StrongEps.Jeps ρ ε (locG6 α L β)) :=
    Work.FTS.StrongEps.softClass_Jeps hρ ⟨hα, hα1⟩ hε
      (forall_contDiffOn_locG6 α L β) (HkMem_locG8 α L β hα hα1 hL)
      hbdd hz0 hzin ht0 ht1 (hax_locG6_eps α L β hL) (locallyIntegrable_logPull_locG6 α L β)
  exact
    { norm := hsoft.norm
      reg := hsoft.reg
      mem := Work.FTS.OpenPkg.HkMem_mono_open hsoft.reg 7 (by norm_num) hsoft.mem8
      mem8 := hsoft.mem8
      mem10 := hsoft.mem10
      tr := Work.FTS.ClassC.bdryTraces_mono (by norm_num : 6 ≤ 7) hsoft.tr7
      tr7 := hsoft.tr7
      fsm := contDiffOn_Fstar_Jeps_locG6 hρ hε hα
      axis := hsoft.axis
      l12 := L12_Jeps_locG6 α L β hα hα1 hL hρ hε h12
      thTr := hsoft.thTr }

/-! ## The deliverable -/

/-- **(3a′) — the localised order-`6` datum is regular data of the `ε`-scheme.**  For
`0 < α ≤ 1`, `1 ≤ L`, an `L₁₂`-orthogonal datum (`L₁₂ (locG6 α L β) 0 = 0`, which the producer
`Work.FTS.LocData6.locG6_data` supplies), a smooth mollifier kernel `ρ` and `ε > 0`,

  `EpsDatum α ρ ε (locG6 α L β) = SmoothOpen ∧ HkMem α 6 ∧ ClassC α (J_ε (locG6 α L β))`. -/
theorem locG6_epsDatum (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (h12 : Work.Construction.L12 (locG6 α L β) 0 = 0)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    Work.FTS.StrongEps.EpsDatum α ρ ε (locG6 α L β) :=
  ⟨smoothOpen_locG6 α L β,
    (Work.FTS.LocData6.regQ_locG6_uncond α L β hα hα1 hL).2.1,
    classC_Jeps_locG6 hα hα1 hL hρ hε h12⟩


/-- **(3a′) in the shape of the core field** of `Submission/Work/FTS/Final/Assembly.lean`: the
same statement at `pExp α = 3α`, with the (unused) hypothesis `RegQ (pExp α) 6 (locG6 …)` of the
interface carried along. -/
theorem core3a'_of_locG6 {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ L β : ℝ, 1 ≤ L → Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 6
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) →
      Work.Construction.L12 (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) 0 = 0 →
      ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (Work.FTS.Regularity.pExp α) ρ ε
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) :=
  fun L β hL _ h12 ε hε =>
    locG6_epsDatum _ L β (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13) hL h12 hρ hε

end Work.FTS_LocDatum3a
end
end
