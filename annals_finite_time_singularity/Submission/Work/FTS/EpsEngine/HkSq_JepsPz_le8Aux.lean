/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkSq_JepsPz_le8Aux.lean`

**The order-`8` assembly `Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le8_of_slot`.**

This is the proof of `Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le` (the `k ≤ 6` counterflow
estimate of `Submission/Work/FTS/StrongEps/EpsSqTools/HkSq_JepsPz_le.lean`), run with

* a level-zero slot bound for `J_ε f` at order `8` (supplied as a hypothesis, since the
  `k ≤ 8` slot estimate is `Work.FTS.EpsEngine.EpsSqIter_mixed_Jeps_le_gen ρ hρ 8`),
* the order-`8` bump bound `Work.FTS.EpsEngine.exists_HkNorm_bump_le8`, and
* the cardinal constant `k + 1 ≤ 9` (`9 = 8 + 1`) for the two slot sums,

so that the constants `7`, `49`, `56`, `112` of the `k ≤ 6` assembly become `9`, `81`, `90`, `180`.

Consumed by `Submission/Work/FTS/EpsEngine/HkSq_JepsPz_le8.lean`, which supplies the slot bound.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSqJepsPzPre
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8Bump

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
