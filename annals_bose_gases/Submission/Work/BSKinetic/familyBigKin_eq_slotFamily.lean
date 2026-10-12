import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq
import Submission.Work.BSKinetic.integral_bsWin_deriv_sq
import Submission.Work.BSKinetic.kinFT_energy_sum
import Submission.Work.BSKinetic.peel_tBamp_gen
import Submission.Work.BSKinetic.plancherel_pconv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

/-! ## A. The moving box and its window -/

lemma famKin_chiBig_eq_bsWin (ℓ : ℝ) (u : ℝ³) :
    Work.UBBInputs9.chiBig ℓ u = Work.BSKinetic.bsWin ℓ u := rfl

lemma famKin_chiBig_eq_zero_of_not_mem {ℓ : ℝ} (hℓ : 0 < ℓ) (u z : ℝ³)
    (hz : z ∉ Work.UBBInputs9.bigBox ℓ u) : Work.UBBInputs9.chiBig ℓ u z = 0 := by
  by_contra h
  exact hz (Submission.BoseGases.chiScale_mem_acube hℓ h)

lemma famKin_isCompact_bigBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    IsCompact (Work.UBBInputs9.bigBox ℓ u) := by
  have h : Work.UBBInputs9.bigBox ℓ u
      = (fun w : ℝ³ => w + ℓ • u) '' Submission.BoseGases.acube ℓ := by
    ext x
    constructor
    · intro hx
      exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨w, hw, rfl⟩
      show w + ℓ • u - ℓ • u ∈ Submission.BoseGases.acube ℓ
      simpa only [add_sub_cancel_right] using hw
  rw [h]
  exact (Submission.BoseGases.acube_compact hℓ).image (continuous_id.add continuous_const)

lemma famKin_continuous_chiBig {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    Continuous (Work.UBBInputs9.chiBig ℓ u) := by
  have h : Work.UBBInputs9.chiBig ℓ u
      = fun x : ℝ³ => Submission.BoseGases.chiScale ℓ (x - ℓ • u) := rfl
  rw [h]
  exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
    (continuous_id.sub continuous_const)

lemma famKin_setIntegral_bigBox_eq_add (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    ∫ z in Work.UBBInputs9.bigBox ℓ u, ψ z
      = ∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z) := by
  classical
  have hmeasB : MeasurableSet (Work.UBBInputs9.bigBox ℓ u) := by
    have h : Work.UBBInputs9.bigBox ℓ u
        = (fun x : ℝ³ => x - ℓ • u) ⁻¹' Submission.BoseGases.acube ℓ := rfl
    rw [h]
    exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)
  rw [← integral_indicator hmeasB,
      ← integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  rw [← Submission.BoseGases.integral_comp_add_left
        ((Work.UBBInputs9.bigBox ℓ u).indicator ψ) (ℓ • u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · have hz' : ℓ • u + z ∈ Work.UBBInputs9.bigBox ℓ u := by
      show ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ
      rwa [add_sub_cancel_left]
    rw [if_pos hz', if_pos hz]
  · have hz' : ℓ • u + z ∉ Work.UBBInputs9.bigBox ℓ u := by
      show ¬ (ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ)
      rwa [add_sub_cancel_left]
    rw [if_neg hz', if_neg hz]

/-! ## B. The moving-box projection on the inserted configuration -/

lemma famKin_boxQ_kcInsN_eq_bsQ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) (z : ℝ³) (r : X n) :
    Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ
        (Submission.BoseGases.kcInsN n i (z, r))
      = Work.BSKinetic.bsQ ℓ u
          (fun z' : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z', r))) z := by
  simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean]
  have hI : (∫ a in Work.UBBInputs9.bigBox ℓ u,
        Φ (Function.update (Submission.BoseGases.kcInsN n i (z, r)) i a))
      = ∫ a in Work.UBBInputs9.bigBox ℓ u,
          Φ (Submission.BoseGases.kcInsN n i (a, r)) := by
    apply integral_congr_ae
    filter_upwards with a
    rw [Work.SmallBoxBridge.Fourier.update_kcInsN]
  rw [hI, famKin_setIntegral_bigBox_eq_add ℓ u
    (fun z' : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z', r)))]
  ring

/-! ## C. The pointwise amplitude identity -/

lemma famKin_tBamp_chiBig_boxQ_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) (r : X n) (p : ℝ³) :
    Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
        (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
        (Submission.BoseGases.kcInsN n i (0, r))
      = kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
            (Work.BSKinetic.bsQ ℓ u
              (fun z' : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z', r))) z : ℂ)) p := by
  rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]
  congr 1
  funext z
  rw [famKin_chiBig_eq_bsWin, famKin_boxQ_kcInsN_eq_bsQ hℓ u Φ i z r]


/-! ## D. The `p ↔ abox` Fubini exchange at fixed `u` -/

lemma famKin_fsKinCoeff_le_bound (c r : ℝ) (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ 2 * (1 + c ^ 2) * (1 + r ^ 2) := by
  rw [Submission.BoseGases.fsKinCoeff]
  have hnn : 0 ≤ max (r - c) 0 := le_max_right _ _
  have h1 : max (r - c) 0 ≤ r + |c| := by
    apply max_le
    · linarith [neg_le_abs c]
    · positivity
  have h3 : (max (r - c) 0) ^ 2 ≤ (r + |c|) ^ 2 := pow_le_pow_left₀ hnn h1 2
  have h4 : (r + |c|) ^ 2 ≤ 2 * (1 + c ^ 2) * (1 + r ^ 2) := by
    have hs : |c| ^ 2 = c ^ 2 := sq_abs c
    nlinarith [sq_nonneg (r - |c|), sq_nonneg r, sq_nonneg c, abs_nonneg c, sq_nonneg (c * r)]
  linarith

lemma famKin_continuous_fsKinCoeff_norm (c : ℝ) :
    Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
  have hc : Continuous fun r : ℝ => Submission.BoseGases.fsKinCoeff c r := by
    have hfun : (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r)
        = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
    rw [hfun]
    have hsub : Continuous fun r : ℝ => r - c := continuous_id.sub continuous_const
    have hmax : Continuous fun r : ℝ => max (r - c) 0 :=
      hsub.max (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
    exact hmax.pow 2
  exact hc.comp continuous_norm

lemma famKin_chiBig_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    ContDiff ℝ (⊤ : ENat) (Work.UBBInputs9.chiBig ℓ u) := by
  have h : Work.UBBInputs9.chiBig ℓ u
      = fun x : ℝ³ => Submission.BoseGases.chiScale ℓ (x - ℓ • u) := rfl
  rw [h]
  exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp
    (contDiff_id.sub contDiff_const)

lemma famKin_chiBig_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (Work.UBBInputs9.chiBig ℓ u) := by
  have hcomp : IsCompact (Work.UBBInputs9.bigBox ℓ u) := famKin_isCompact_bigBox hℓ u
  have hsub : Function.support (Work.UBBInputs9.chiBig ℓ u) ⊆ Work.UBBInputs9.bigBox ℓ u := by
    intro z hz
    by_contra hcon
    exact hz (famKin_chiBig_eq_zero_of_not_mem hℓ u z hcon)
  exact IsCompact.of_isClosed_subset hcomp (isClosed_tsupport (Work.UBBInputs9.chiBig ℓ u))
    (closure_minimal hsub hcomp.isClosed)

lemma famKin_mem_abox_kcInsN_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {r : X n}
    (hr : r ∈ Submission.BoseGases.abox n ℓ) :
    Submission.BoseGases.kcInsN n i (0, r) ∈ Submission.BoseGases.abox (n + 1) ℓ := by
  intro j
  by_cases hj : j = i
  · rw [hj, Submission.BoseGases.kc_insN_apply_same]
    intro m
    have h0 : (0 : ℝ³) m = 0 := by simp
    rw [h0]
    exact ⟨by linarith [hℓ], by linarith [hℓ]⟩
  · rcases Fin.exists_succAbove_eq hj with ⟨j', hj'⟩
    rw [← hj', Submission.BoseGases.kc_insN_apply_succ]
    exact hr j'

lemma famKin_continuous_tBamp_pair {n : ℕ} {K : Set ℝ³} {W : ℝ³ → ℝ} (hK : IsCompact K)
    (hW : Continuous W) (hWs : ∀ z, z ∉ K → W z = 0)
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    Continuous (fun q : ℝ³ × X (n + 1) => Work.SmallBoxTBWord.tBamp W q.1 Φ i q.2) := by
  have hF : Continuous (Function.uncurry (fun (q : ℝ³ × X (n + 1)) (z : ℝ³) =>
      (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
        (Φ (Function.update q.2 i z) : ℂ))) := by
    rw [show (Function.uncurry (fun (q : ℝ³ × X (n + 1)) (z : ℝ³) =>
        (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          (Φ (Function.update q.2 i z) : ℂ)))
        = fun w : (ℝ³ × X (n + 1)) × ℝ³ =>
            (W w.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ))) *
              (Φ (Function.update w.1.2 i w.2) : ℂ) from rfl]
    have h1 : Continuous (fun w : (ℝ³ × X (n + 1)) × ℝ³ => (W w.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hW.comp continuous_snd)
    have h2 : Continuous (fun w : (ℝ³ × X (n + 1)) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_fst.fst.prodMk continuous_snd)))).neg)
    have h3 : Continuous (fun w : (ℝ³ × X (n + 1)) × ℝ³ =>
        (Φ (Function.update w.1.2 i w.2) : ℂ)) :=
      Complex.continuous_ofReal.comp (hΦ.comp ((continuous_update i).comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    exact (h1.mul h2).mul h3
  have hcont : Continuous (fun q : ℝ³ × X (n + 1) => ∫ z in K,
      (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
        (Φ (Function.update q.2 i z) : ℂ)) :=
    Commons.Analysis.Calculus.continuous_setIntegral_isCompact hK hF
  refine hcont.congr (fun q => ?_)
  exact (Work.BSKinetic.tBamp_eq_setIntegral_of_support hWs i q.1 q.2).symm

theorem famKin_swap_p_abox_tBamp {n : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        (∫ r in abox n ℓ, ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
            (kcInsN n i (0, r))‖ ^ 2))
      = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
            (kcInsN n i (0, r))‖ ^ 2 := by
  classical
  set A : ℝ := ((2 * Real.pi) ^ 3)⁻¹ with hA
  set Φ' : X (n + 1) → ℝ :=
    Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ with hΦ'def
  have hΦ'cd : ContDiff ℝ (⊤ : ENat) Φ' := by
    rw [hΦ'def]
    exact Work.SmallBoxTBWord.boxQ_contDiff_of_compact (famKin_isCompact_bigBox hℓ u) (ℓ ^ 3) i hΦ
  set ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ) with hν
  let f : ℝ³ → X n → ℝ := fun p r =>
    fsKinCoeff c ‖p‖ * ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
      (kcInsN n i (0, r))‖ ^ 2
  have hf_nonneg : ∀ p r, 0 ≤ f p r := fun p r =>
    mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)
  obtain ⟨C, hC0, hCdec⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n + 1) hℓ
    (famKin_chiBig_contDiff hℓ u) (famKin_chiBig_hasCompactSupport hℓ u) hΦ'cd
  have hbd : ∀ r ∈ abox n ℓ, ∀ p : ℝ³,
      f p r ≤ (2 * (1 + c ^ 2) * C ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
    intro r hr p
    have hx : kcInsN n i (0, r) ∈ abox (n + 1) ℓ := famKin_mem_abox_kcInsN_zero hℓ i hr
    have h1 : ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
        (kcInsN n i (0, r))‖ ≤ C / (1 + ‖p‖) ^ 3 := hCdec _ hx i p
    have h2 : ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
        (kcInsN n i (0, r))‖ ^ 2 ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : fsKinCoeff c ‖p‖ ≤ 2 * (1 + c ^ 2) * (1 + ‖p‖ ^ 2) :=
      famKin_fsKinCoeff_le_bound c ‖p‖ (norm_nonneg p)
    have h6 : (0 : ℝ) < 1 + ‖p‖ := by positivity
    have hkey : (1 + ‖p‖) ^ (-(4 : ℝ)) * (1 + ‖p‖) ^ 6 = (1 + ‖p‖) ^ 2 := by
      rw [show (1 + ‖p‖) ^ 6 = (1 + ‖p‖) ^ (((6 : ℕ) : ℝ)) by rw [Real.rpow_natCast],
        ← Real.rpow_add h6]
      rw [show -(4 : ℝ) + ((6 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h7 : (1 + ‖p‖ ^ 2) ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
    have h8 : (1 + ‖p‖ ^ 2) / (1 + ‖p‖) ^ 6 ≤ (1 + ‖p‖) ^ (-(4 : ℝ)) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ 6), hkey]
      exact h7
    have hC2 : (0 : ℝ) ≤ 2 * (1 + c ^ 2) * C ^ 2 := by positivity
    calc f p r
        = fsKinCoeff c ‖p‖ * ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
            (kcInsN n i (0, r))‖ ^ 2 := rfl
      _ ≤ (2 * (1 + c ^ 2) * (1 + ‖p‖ ^ 2)) * (C / (1 + ‖p‖) ^ 3) ^ 2 := by
          apply mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = (2 * (1 + c ^ 2) * C ^ 2) * ((1 + ‖p‖ ^ 2) / (1 + ‖p‖) ^ 6) := by
          field_simp
      _ ≤ (2 * (1 + c ^ 2) * C ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) :=
          mul_le_mul_of_nonneg_left h8 hC2
  have hIntDom : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4 : ℝ))) := by
    have h := integrable_one_add_norm (μ := volume) (E := ℝ³) (r := (4 : ℝ)) ?_
    · simpa using h
    · have hfr : (Module.finrank ℝ ℝ³ : ℝ) = 3 := by
        rw [finrank_euclideanSpace_fin]; norm_num
      rw [hfr]; norm_num
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    have htb : Continuous (fun q : ℝ³ × X (n + 1) =>
        Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) q.1 Φ' i q.2) :=
      famKin_continuous_tBamp_pair (famKin_isCompact_bigBox hℓ u) (famKin_continuous_chiBig hℓ u)
        (fun z hz => famKin_chiBig_eq_zero_of_not_mem hℓ u z hz) hΦ'cd.continuous i
    have hq : Continuous (fun q : ℝ³ × X n => (q.1, kcInsN n i (0, q.2))) :=
      continuous_fst.prodMk ((Submission.BoseGases.kcInsN_cont i).comp
        (continuous_const.prodMk continuous_snd))
    have hcont : Continuous (fun q : ℝ³ × X n =>
        fsKinCoeff c ‖q.1‖ * ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u)
          q.1 Φ' i (kcInsN n i (0, q.2))‖ ^ 2) :=
      ((famKin_continuous_fsKinCoeff_norm c).comp continuous_fst).mul (((htb.comp hq).norm).pow 2)
    have hcont' : Continuous (fun q : ℝ³ × X n => f q.1 q.2) := hcont
    exact hcont'.aestronglyMeasurable
  have hbm : ∀ᵐ r ∂ν, (∫⁻ p, ENNReal.ofReal ‖f p r‖ ∂volume) ≤
      ENNReal.ofReal (2 * (1 + c ^ 2) * C ^ 2 * ∫ p : ℝ³, (1 + ‖p‖) ^ (-(4 : ℝ))) := by
    filter_upwards [ae_restrict_mem (abox_measurable n ℓ)] with r hr
    have hpoint : ∀ p : ℝ³, ENNReal.ofReal ‖f p r‖ ≤
        ENNReal.ofReal ((2 * (1 + c ^ 2) * C ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) := by
      intro p
      rw [Real.norm_of_nonneg (hf_nonneg p r)]
      exact ENNReal.ofReal_le_ofReal (hbd r hr p)
    calc (∫⁻ p, ENNReal.ofReal ‖f p r‖ ∂volume)
        ≤ ∫⁻ p, ENNReal.ofReal ((2 * (1 + c ^ 2) * C ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) ∂volume :=
          lintegral_mono hpoint
      _ = ENNReal.ofReal (2 * (1 + c ^ 2) * C ^ 2) *
            ∫⁻ p, ENNReal.ofReal ((1 + ‖p‖) ^ (-(4 : ℝ))) ∂volume := by
          rw [lintegral_congr (fun p => ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ _))]
          rw [MeasureTheory.lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 * (1 + c ^ 2) * C ^ 2) *
            ENNReal.ofReal (∫ p : ℝ³, (1 + ‖p‖) ^ (-(4 : ℝ))) := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntDom
            (ae_of_all _ (fun p => Real.rpow_nonneg (by positivity) _))]
      _ = ENNReal.ofReal (2 * (1 + c ^ 2) * C ^ 2 *
            ∫ p : ℝ³, (1 + ‖p‖) ^ (-(4 : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (1 + c ^ 2) * C ^ 2)]
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
      (μ := volume) (ν := ν)
      (f := f) (g := fun _ => ENNReal.ofReal (2 * (1 + c ^ 2) * C ^ 2 *
        ∫ p : ℝ³, (1 + ‖p‖) ^ (-(4 : ℝ)))) hmeas ?_ hbm
    rw [MeasureTheory.lintegral_const]
    have hfin : ν Set.univ < ⊤ := by
      rw [hν, MeasureTheory.Measure.restrict_apply_univ]
      exact abox_lt_top n ℓ hℓ.le
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
  have hFub : (∫ p : ℝ³, ∫ r : X n, f p r ∂ν ∂volume) =
      ∫ r : X n, ∫ p : ℝ³, f p r ∂volume ∂ν :=
    MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) hint
  have hL : (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        (∫ r in abox n ℓ, ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
          (kcInsN n i (0, r))‖ ^ 2))
      = ∫ p : ℝ³, ∫ r : X n, f p r ∂ν := by
    apply integral_congr_ae
    filter_upwards with p
    simp only [f]
    rw [← MeasureTheory.integral_const_mul]
  calc A * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        (∫ r in abox n ℓ, ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
          (kcInsN n i (0, r))‖ ^ 2))
      = A * (∫ p : ℝ³, ∫ r : X n, f p r ∂ν) := by rw [hL]
    _ = A * (∫ r : X n, ∫ p : ℝ³, f p r ∂volume ∂ν) := by rw [hFub]
    _ = ∫ r : X n, A * (∫ p : ℝ³, f p r ∂volume) ∂ν :=
        (MeasureTheory.integral_const_mul A _).symm
    _ = ∫ r in abox n ℓ, A * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p Φ' i
            (kcInsN n i (0, r))‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with r
        simp only [f]

/-! ## E. The slot decomposition -/

lemma famKin_slot_step {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (u : ℝ³)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i x‖ ^ 2))
      = ∫ r in abox n ℓ, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  have hΦ' : ContDiff ℝ (⊤ : ENat)
      (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact (famKin_isCompact_bigBox hℓ u) (ℓ ^ 3) i hΦ
  have hpeel : ∀ p : ℝ³,
      (ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i x‖ ^ 2
        = ∫ r in abox n ℓ,
            ‖kinFT (fun z : ℝ³ => (Work.UBBInputs9.chiBig ℓ u z : ℂ) *
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ
                (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 :=
    fun p => peel_tBamp_gen hℓ (famKin_isCompact_bigBox hℓ u) (famKin_continuous_chiBig hℓ u)
      (fun z hz => famKin_chiBig_eq_zero_of_not_mem hℓ u z hz) hΦ'.continuous i p
  calc (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i x‖ ^ 2))
      = (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ,
            ‖kinFT (fun z : ℝ³ => (Work.UBBInputs9.chiBig ℓ u z : ℂ) *
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ
                (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [hpeel p]
    _ = (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
              (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        congr 1
        apply integral_congr_ae
        filter_upwards with r
        rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]
    _ = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
            (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 :=
        famKin_swap_p_abox_tBamp hℓ u Φ hΦ i
    _ = ∫ r in abox n ℓ, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
        apply integral_congr_ae
        filter_upwards with r
        rw [Work.BSKinetic.bsOneBody]
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [famKin_tBamp_chiBig_boxQ_eq hℓ u Φ i r p]

theorem famKin_tBwordKinBigU_eq_slotSum {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (u : ℝ³) (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ
      = ∑ i : Fin (n + 1), ∫ r in abox n ℓ,
          bsOneBody ℓ (fsKinCoeff c) u
            (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  rw [Work.UBBInputs9.tBwordKinBigU, Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (fsKinCoeff c) Φ
      (fun z hz => famKin_chiBig_eq_zero_of_not_mem hℓ u z hz)]
  rw [Work.SmallBoxTBWord.tBdiagForm]
  apply Finset.sum_congr rfl
  intro i _
  exact famKin_slot_step hℓ n u Φ hΦ i


/-! ## F. Support, far vanishing and the pointwise bound -/

lemma famKin_norm_lt_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℝ³} (hz : z ∈ acube ℓ) :
    ‖z‖ < ℓ := by
  have hcomp : ∀ m : Fin 3, ‖z m‖ ≤ ℓ / 2 := by
    intro m
    have h := (Submission.BoseGases.mem_acube_iff ℓ z).mp hz m
    rw [Set.mem_Icc] at h
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hsq : ‖z‖ ^ 2 < ℓ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ < ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]
  have h2 := sq_lt_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (le_of_lt hℓ)] at h2
  exact h2

lemma famKin_mem_abox_kcInsN {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {r : X n}
    (hr : r ∈ abox n ℓ) {z : ℝ³} (hz : z ∈ acube ℓ) :
    Submission.BoseGases.kcInsN n i (z, r) ∈ abox (n + 1) ℓ := by
  intro j
  by_cases hj : j = i
  · rw [hj, Submission.BoseGases.kc_insN_apply_same]; exact hz
  · rcases Fin.exists_succAbove_eq hj with ⟨j', hj'⟩
    rw [← hj', Submission.BoseGases.kc_insN_apply_succ]; exact hr j'

lemma famKin_fib_support {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (Φ : X (n + 1) → ℝ)
    (hsupp : SuppInBox (n + 1) ℓ Φ) (i : Fin (n + 1)) {r : X n} (hr : r ∈ abox n ℓ) :
    ∀ z : ℝ³, z ∉ acube ℓ → Φ (Submission.BoseGases.kcInsN n i (z, r)) = 0 := by
  intro z hz
  exact hsupp _ ⟨i, by rwa [Submission.BoseGases.kc_insN_apply_same]⟩

lemma famKin_fderiv_eq_zero_of_notMem {ℓ : ℝ} {ψ : ℝ³ → ℝ}
    (hsupp : ∀ x : ℝ³, x ∉ acube ℓ → ψ x = 0) {z : ℝ³} (hz : z ∉ acube ℓ) :
    fderiv ℝ ψ z = 0 := by
  have hopen : IsOpen (acube ℓ)ᶜ := (Submission.BoseGases.acube_isClosed ℓ).isOpen_compl
  have hev : ψ =ᶠ[𝓝 z] (fun _ : ℝ³ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds (by simpa using hz)] with w hw
    exact hsupp w (by simpa using hw)
  rw [hev.fderiv_eq, fderiv_const_apply]

lemma famKin_bsMean_eq_zero_of_far {ℓ R : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ∀ x, R ≤ ‖x‖ → ψ x = 0) {u : ℝ³} (hu : R + ℓ ≤ ℓ * ‖u‖) :
    bsMean ℓ u ψ = 0 := by
  unfold bsMean
  have hInt : ∫ z in acube ℓ, ψ (ℓ • u + z) = 0 := by
    have hcong : ∫ z in acube ℓ, ψ (ℓ • u + z) = ∫ z in acube ℓ, (0 : ℝ) := by
      apply setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      intro z hz
      apply hψ
      have hzℓ : ‖z‖ ≤ ℓ := le_of_lt (famKin_norm_lt_of_mem_acube hℓ hz)
      have h1 : ‖ℓ • u‖ = ℓ * ‖u‖ := by
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt hℓ)]
      have h2 : ‖ℓ • u‖ - ‖z‖ ≤ ‖ℓ • u + z‖ := by
        have h := norm_sub_le (ℓ • u + z) z
        simp only [add_sub_cancel_right] at h
        linarith
      calc R ≤ ℓ * ‖u‖ - ℓ := by linarith
        _ = ‖ℓ • u‖ - ℓ := by rw [h1]
        _ ≤ ‖ℓ • u‖ - ‖z‖ := by linarith
        _ ≤ ‖ℓ • u + z‖ := h2
    rw [hcong]; simp
  rw [hInt, mul_zero]

lemma famKin_norm_ge_of_bsWin_ne_zero {ℓ R : ℝ} (hℓ : 0 < ℓ) {u z : ℝ³}
    (hu : R + ℓ ≤ ℓ * ‖u‖) (hz : bsWin ℓ u z ≠ 0) : R ≤ ‖z‖ := by
  have hw : chiScale ℓ (z - ℓ • u) ≠ 0 := hz
  have hsupp : ‖z - ℓ • u‖ ≤ ℓ / 2 := Submission.BoseGases.chiScale_support_le hℓ hw
  have hnormu : ‖ℓ • u‖ = ℓ * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  have htri : ‖ℓ • u‖ ≤ ‖z‖ + ‖z - ℓ • u‖ := by
    have h := norm_add_le z (ℓ • u - z)
    rw [add_sub_cancel] at h
    rwa [norm_sub_rev (ℓ • u) z] at h
  have hzlb : ℓ * ‖u‖ - ℓ / 2 ≤ ‖z‖ := by
    have := htri
    rw [hnormu] at this
    linarith
  have hu' : R ≤ ℓ * ‖u‖ - ℓ := by linarith
  linarith

lemma famKin_bsOneBody_eq_zero_of_far {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hsupp : SuppInBox (n + 1) ℓ Φ) (i : Fin (n + 1)) {r : X n}
    (hr : r ∈ abox n ℓ) {u : ℝ³} (hu : 2 ≤ ‖u‖) :
    bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))
      = 0 := by
  have hψ : ∀ z : ℝ³, z ∉ acube ℓ → Φ (Submission.BoseGases.kcInsN n i (z, r)) = 0 :=
    famKin_fib_support hℓ n Φ hsupp i hr
  have hψfar : ∀ z : ℝ³, ℓ ≤ ‖z‖ →
      Φ (Submission.BoseGases.kcInsN n i (z, r)) = 0 := by
    intro z hz
    exact hψ z (fun hcon => absurd hz (not_le.mpr (famKin_norm_lt_of_mem_acube hℓ hcon)))
  have hℓu : ℓ + ℓ ≤ ℓ * ‖u‖ := by
    have : ℓ * 2 ≤ ℓ * ‖u‖ := mul_le_mul_of_nonneg_left hu hℓ.le
    linarith
  have hprod : (fun z : ℝ³ => (bsWin ℓ u z : ℂ) *
      (bsQ ℓ u (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) z : ℂ))
      = fun _ => 0 := by
    funext z
    by_cases hz : bsWin ℓ u z = 0
    · rw [hz]; simp
    · have hznorm : ℓ ≤ ‖z‖ := famKin_norm_ge_of_bsWin_ne_zero hℓ hℓu hz
      have hψz : Φ (Submission.BoseGases.kcInsN n i (z, r)) = 0 := hψfar z hznorm
      have hm : bsMean ℓ u (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) = 0 :=
        famKin_bsMean_eq_zero_of_far hℓ hψfar hℓu
      simp [bsQ, hψz, hm]
  rw [bsOneBody, hprod]
  simp [kinFT]

/-! ## G. The Dirichlet domination and the uniform bound -/

lemma famKin_bsOneBody_le_weighted {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    bsOneBody ℓ (fsKinCoeff c) u ψ
      ≤ 2 * (1 + c ^ 2) *
          ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
            + ∑ k : Fin 3, (∫ z : ℝ³,
                (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
                  (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
  set h : ℝ³ → ℝ := fun z => bsWin ℓ u z * bsQ ℓ u ψ z with hh
  have hbsQ : ContDiff ℝ (⊤ : ENat) (bsQ ℓ u ψ) := by
    have h : bsQ ℓ u ψ = fun z : ℝ³ => ψ z - bsMean ℓ u ψ := rfl
    rw [h]; exact hψ.sub contDiff_const
  have hbsWin : ContDiff ℝ (⊤ : ENat) (bsWin ℓ u) := by
    have h : bsWin ℓ u = fun z : ℝ³ => chiScale ℓ (z - ℓ • u) := rfl
    rw [h]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp
      (contDiff_id.sub contDiff_const)
  have hcd : ContDiff ℝ (⊤ : ENat) h := by rw [hh]; exact hbsWin.mul hbsQ
  have hcs' : HasCompactSupport h := by
    rw [hh]
    exact HasCompactSupport.mul_right
      (by simpa only [famKin_chiBig_eq_bsWin] using famKin_chiBig_hasCompactSupport hℓ u)
  have hcomplex : (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ))
      = fun z => (h z : ℂ) := by
    funext z; rw [hh, Complex.ofReal_mul]
  have h1 := plancherel_pconv h hcd hcs'
  have h2 := kinFT_energy_sum h hcd hcs'
  have hI1 : Integrable (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    integrable_kinFT_sq h hcd hcs'
  have hI2 : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    Work.SmallBoxTBWord.kinFT_energy_integrable h hcd hcs'
  have hIg : Integrable (fun p : ℝ³ => 2 * (1 + c ^ 2) *
      (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
        + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)) :=
    (hI1.add hI2).const_mul _
  have hpt : ∀ p : ℝ³, fsKinCoeff c ‖p‖ * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
      ≤ 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
    intro p
    have hb := famKin_fsKinCoeff_le_bound c ‖p‖ (norm_nonneg p)
    have hp : 0 ≤ ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := sq_nonneg _
    have hp2 : 0 ≤ ‖p‖ ^ 2 := sq_nonneg _
    nlinarith [hb, hp, hp2]
  have hmono : (∫ p : ℝ³, fsKinCoeff c ‖p‖ * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      ≤ ∫ p : ℝ³, 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    integral_mono_of_nonneg
      (Eventually.of_forall (fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)))
      hIg (Eventually.of_forall hpt)
  have hmain : ((2 * Real.pi) ^ 3)⁻¹ *
      (∫ p : ℝ³, (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      = (∫ z : ℝ³, (h z) ^ 2)
        + ∑ k : Fin 3, (∫ z : ℝ³, (fderiv ℝ h z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    have hsplit : (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
        = fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
            + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by
      funext p; ring
    rw [hsplit, integral_add hI1 hI2, mul_add, h1, h2]
  have hIntW : Integrable (fun p : ℝ³ =>
      (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
    have hsplit : (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
        = fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
            + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by
      funext p; ring
    rw [hsplit]; exact hI1.add hI2
  have hstep : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : ℝ³, 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2))
      = 2 * (1 + c ^ 2) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
    have hsplit : (fun p : ℝ³ => 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2))
        = fun p : ℝ³ => 2 * (1 + c ^ 2) *
            ((1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
      funext p; ring
    rw [hsplit, integral_const_mul]
    ring
  rw [bsOneBody, hcomplex]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³,
        fsKinCoeff c ‖p‖ * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (h z) ^ 2)
        + ∑ k : Fin 3, (∫ z : ℝ³, (fderiv ℝ h z (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
        rw [hstep, hmain]
    _ = 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
        + ∑ k : Fin 3, (∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2)) := rfl

lemma famKin_hasCompactSupport_sq {f : ℝ³ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun z : ℝ³ => (f z) ^ 2) := by
  refine IsCompact.of_isClosed_subset hf (isClosed_tsupport _) (closure_mono ?_)
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro h
  exact hz (by rw [h]; ring)

lemma famKin_fderiv_bsQ {ℓ : ℝ} (u z : ℝ³) (k : Fin 3) {ψ : ℝ³ → ℝ}
    (hψ : DifferentiableAt ℝ ψ z) :
    fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z (Submission.BoseGases.kcStdBasis k)
      = bsWin ℓ u z * fderiv ℝ (bsQ ℓ u ψ) z (Submission.BoseGases.kcStdBasis k)
        + bsQ ℓ u ψ z * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
            (Submission.BoseGases.kcStdBasis k)) := by
  have hbsQ : bsQ ℓ u ψ = fun y : ℝ³ => ψ y - bsMean ℓ u ψ := rfl
  have hdiff : DifferentiableAt ℝ (bsQ ℓ u ψ) z := by
    rw [hbsQ]; exact hψ.sub_const _
  exact Work.BSKinetic.fderiv_bsWin_mul_apply (ℓ := ℓ) (ψ := bsQ ℓ u ψ) u z
    (Submission.BoseGases.kcStdBasis k) hdiff

lemma famKin_bsOneBody_le {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hsupp : SuppInBox (n + 1) ℓ Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ³) (i : Fin (n + 1)) (r : X n), r ∈ abox n ℓ →
      bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))
        ≤ C := by
  obtain ⟨S0, hS00, hS0⟩ : ∃ S0 : ℝ, 0 ≤ S0 ∧ ∀ x ∈ abox (n + 1) ℓ, |Φ x| ≤ S0 := by
    obtain ⟨C, hC⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
      hΦ.continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  obtain ⟨S1, hS10, hS1⟩ : ∃ S1 : ℝ, 0 ≤ S1 ∧ ∀ x ∈ abox (n + 1) ℓ, ‖fderiv ℝ Φ x‖ ≤ S1 := by
    obtain ⟨C, hC⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
      (hΦ.continuous_fderiv (by simp)).norm.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact le_trans h (le_max_left _ _)
  set E0 : ℝ := ∫ z : ℝ³, (chiScale ℓ z) ^ 2 with hE0
  set Dk : Fin 3 → ℝ :=
    fun k => ∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (Submission.BoseGases.kcStdBasis k)) ^ 2
    with hDk
  refine ⟨max (2 * (1 + c ^ 2) * (4 * S0 ^ 2 * E0
      + ∑ k : Fin 3, (8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0))) 0, le_max_right _ _, ?_⟩
  intro u i r hr
  set ψ : ℝ³ → ℝ := fun z => Φ (Submission.BoseGases.kcInsN n i (z, r)) with hψdef
  have hψcd : ContDiff ℝ (⊤ : ENat) ψ := by
    rw [hψdef]
    exact hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  have hψsupp : ∀ z : ℝ³, z ∉ acube ℓ → ψ z = 0 := famKin_fib_support hℓ n Φ hsupp i hr
  have hψcs : HasCompactSupport ψ := by
    rw [hψdef]
    refine IsCompact.of_isClosed_subset (Submission.BoseGases.acube_compact hℓ)
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (Submission.BoseGases.acube_isClosed ℓ)
    intro z hz
    by_contra hcon
    exact hz (hψsupp z hcon)
  have hψ_abs : ∀ w : ℝ³, |ψ w| ≤ S0 := by
    intro w
    by_cases hw : w ∈ acube ℓ
    · rw [hψdef]
      exact hS0 _ (famKin_mem_abox_kcInsN hℓ i hr hw)
    · rw [hψsupp w hw]; simp [hS00]
  have hvolreal : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  -- the bound on the box mean
  have hm_bound : (bsMean ℓ u ψ) ^ 2 ≤ S0 ^ 2 := by
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [bsMean]
    have hIntAbs : ∫ z in acube ℓ, |ψ (ℓ • u + z)| ≤ ∫ z in acube ℓ, S0 := by
      have h1int : IntegrableOn (fun z : ℝ³ => |ψ (ℓ • u + z)|) (acube ℓ) volume :=
        ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
          ((continuous_abs.comp hψcd.continuous).comp
            (continuous_const.add continuous_id)).continuousOn
      have h2int : IntegrableOn (fun _ : ℝ³ => S0) (acube ℓ) volume := by
        refine integrableOn_const ?_
        rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
        exact ENNReal.ofReal_lt_top.ne
      exact setIntegral_mono_on h1int h2int (Submission.BoseGases.acube_measurable ℓ)
        (fun z _ => hψ_abs (ℓ • u + z))
    calc |(ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (ℓ • u + z)|
        = (ℓ ^ 3)⁻¹ * |∫ z in acube ℓ, ψ (ℓ • u + z)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ℓ ^ 3)⁻¹)]
      _ ≤ (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, |ψ (ℓ • u + z)| :=
          mul_le_mul_of_nonneg_left (MeasureTheory.abs_integral_le_integral_abs)
            (by positivity)
      _ ≤ (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, S0 :=
          mul_le_mul_of_nonneg_left hIntAbs (by positivity)
      _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * S0) := by
          rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
      _ = S0 := by field_simp
  have hm_abs : |bsMean ℓ u ψ| ≤ S0 := by
    rw [abs_le]
    constructor <;>
      nlinarith [hm_bound, hS00, sq_abs (bsMean ℓ u ψ), abs_nonneg (bsMean ℓ u ψ),
        sq_nonneg (|bsMean ℓ u ψ| + S0), sq_nonneg (|bsMean ℓ u ψ| - S0)]
  have hbsQ_bound : ∀ z : ℝ³, (bsQ ℓ u ψ z) ^ 2 ≤ 4 * S0 ^ 2 := by
    intro z
    have hbsQ : bsQ ℓ u ψ z = ψ z - bsMean ℓ u ψ := rfl
    rw [hbsQ, ← sq_abs]
    calc |ψ z - bsMean ℓ u ψ| ^ 2 ≤ (|ψ z| + |bsMean ℓ u ψ|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) 2
      _ ≤ (S0 + S0) ^ 2 :=
          pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
            (add_le_add (hψ_abs z) hm_abs) 2
      _ = 4 * S0 ^ 2 := by ring
  -- L2 bound
  have hL2 : ∫ z : ℝ³, (ψ z) ^ 2 ≤ S0 ^ 2 * ℓ ^ 3 := by
    have h1 : ∫ z : ℝ³, (ψ z) ^ 2 = ∫ z in acube ℓ, (ψ z) ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by rw [hψsupp z hz]; simp)).symm
    rw [h1]
    calc ∫ z in acube ℓ, (ψ z) ^ 2 ≤ ∫ z in acube ℓ, S0 ^ 2 := by
          apply setIntegral_mono_on
          · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
              (hψcd.continuous.pow 2).continuousOn
          · refine integrableOn_const ?_
            rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
            exact ENNReal.ofReal_lt_top.ne
          · exact Submission.BoseGases.acube_measurable ℓ
          · intro z hz
            have : |ψ z| ≤ S0 := hψ_abs z
            nlinarith [sq_abs (ψ z), abs_nonneg (ψ z), hS00]
      _ = S0 ^ 2 * ℓ ^ 3 := by
          rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul, mul_comm]
  -- the derivative bound
  have hψS1 : ∀ k : Fin 3, ∀ z : ℝ³,
      (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ S1 ^ 2 := by
    intro k z
    rw [← sq_abs]
    by_cases hz : z ∈ acube ℓ
    · have hmem := famKin_mem_abox_kcInsN hℓ i hr hz
      have hd : fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)
          = fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Submission.BoseGases.kcDir (n + 1) i k) := by
        rw [hψdef]
        exact Submission.BoseGases.fiber_fderiv_kcDir i hΦ r z k
      rw [hd]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Submission.BoseGases.kcDir (n + 1) i k)|
          = ‖(fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r)))
              (Submission.BoseGases.kcDir (n + 1) i k)‖ := Real.norm_eq_abs _
        _ ≤ ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))‖
              * ‖Submission.BoseGases.kcDir (n + 1) i k‖ :=
              (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))).le_opNorm _
        _ = ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))‖ := by
              rw [Submission.BoseGases.kc_norm_dir, mul_one]
        _ ≤ S1 := hS1 _ hmem
    · rw [famKin_fderiv_eq_zero_of_notMem hψsupp hz]
      simp [hS10]
  have hDir : ∀ k : Fin 3,
      ∫ z : ℝ³, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ S1 ^ 2 * ℓ ^ 3 := by
    intro k
    have h1 : ∫ z : ℝ³, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
        = ∫ z in acube ℓ, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by rw [famKin_fderiv_eq_zero_of_notMem hψsupp hz]; simp)).symm
    rw [h1]
    calc ∫ z in acube ℓ, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ ∫ z in acube ℓ, S1 ^ 2 := by
          apply setIntegral_mono_on
          · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
              (((hψcd.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).continuousOn
          · refine integrableOn_const ?_
            rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
            exact ENNReal.ofReal_lt_top.ne
          · exact Submission.BoseGases.acube_measurable ℓ
          · intro z hz; exact hψS1 k z
      _ = S1 ^ 2 * ℓ ^ 3 := by
          rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul, mul_comm]
  -- L2 and Dirichlet bounds of `h`
  have htrans2 : ∫ z : ℝ³, (bsWin ℓ u z) ^ 2 = E0 := by
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ³))
      (fun y : ℝ³ => (chiScale ℓ y) ^ 2) (-(ℓ • u))
    have hgoal : (fun z : ℝ³ => (bsWin ℓ u z) ^ 2)
        = fun z : ℝ³ => (chiScale ℓ (z + -(ℓ • u))) ^ 2 := by
      funext z
      show (chiScale ℓ (z - ℓ • u)) ^ 2 = (chiScale ℓ (z + -(ℓ • u))) ^ 2
      rw [sub_eq_add_neg]
    rw [hgoal, h, hE0]
  have htransD : ∀ k : Fin 3,
      ∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k)) ^ 2 = Dk k := by
    intro k
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ³))
      (fun y : ℝ³ => (fderiv ℝ (chiScale ℓ) y (Submission.BoseGases.kcStdBasis k)) ^ 2)
      (-(ℓ • u))
    have hgoal : (fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z + -(ℓ • u))
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
      funext z; rw [sub_eq_add_neg]
    rw [hgoal, h, hDk]
  have hbsWincs : HasCompactSupport (bsWin ℓ u) :=
    by simpa only [famKin_chiBig_eq_bsWin] using famKin_chiBig_hasCompactSupport hℓ u
  have hbsWincont : Continuous (bsWin ℓ u) := by
    have hh' : bsWin ℓ u = fun z : ℝ³ => chiScale ℓ (z - ℓ • u) := rfl
    rw [hh']
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
      (continuous_id.sub continuous_const)
  have hL2h : ∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2 ≤ 4 * S0 ^ 2 * E0 := by
    have hpt : ∀ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2
        ≤ (4 * S0 ^ 2) * (bsWin ℓ u z) ^ 2 := by
      intro z
      have h1 : (bsQ ℓ u ψ z) ^ 2 ≤ 4 * S0 ^ 2 := hbsQ_bound z
      nlinarith [h1, sq_nonneg (bsWin ℓ u z)]
    have hint : Integrable (fun z : ℝ³ => (4 * S0 ^ 2) * (bsWin ℓ u z) ^ 2) :=
      ((hbsWincont.pow 2).integrable_of_hasCompactSupport
        (famKin_hasCompactSupport_sq hbsWincs)).const_mul _
    calc ∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2
        ≤ ∫ z : ℝ³, (4 * S0 ^ 2) * (bsWin ℓ u z) ^ 2 :=
          integral_mono_of_nonneg (Eventually.of_forall (fun z => sq_nonneg _)) hint
            (Eventually.of_forall hpt)
      _ = 4 * S0 ^ 2 * E0 := by
          rw [MeasureTheory.integral_const_mul, htrans2]
  have hDirh : ∀ k : Fin 3, ∫ z : ℝ³,
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
        (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ 8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0 := by
    intro k
    have hpt : ∀ z : ℝ³,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ 8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
            (Submission.BoseGases.kcStdBasis k)) ^ 2
          + 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2 := by
      intro z
      have hd := famKin_fderiv_bsQ (ℓ := ℓ) (ψ := ψ) u z k
        (hψcd.differentiable (by simp) z)
      have hbsQd : fderiv ℝ (bsQ ℓ u ψ) z (Submission.BoseGases.kcStdBasis k)
          = fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k) := by
        have hbsQeq : bsQ ℓ u ψ = fun y : ℝ³ => ψ y - bsMean ℓ u ψ := rfl
        have hfd : fderiv ℝ (fun y : ℝ³ => ψ y - bsMean ℓ u ψ) z = fderiv ℝ ψ z :=
          ((hψcd.differentiable (by simp) z).hasFDerivAt.sub_const (bsMean ℓ u ψ)).fderiv
        rw [hbsQeq, hfd]
      rw [hd, hbsQd]
      have h1 : ((fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k))
            * bsQ ℓ u ψ z) ^ 2
          ≤ (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k)) ^ 2
              * (4 * S0 ^ 2) := by
        have := hbsQ_bound z
        nlinarith [this, sq_nonneg (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k))]
      have h2 : (bsWin ℓ u z * fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
          ≤ S1 ^ 2 * (bsWin ℓ u z) ^ 2 := by
        have := hψS1 k z
        nlinarith [this, sq_nonneg (bsWin ℓ u z)]
      nlinarith [h1, h2, sq_nonneg ((fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k)) * bsQ ℓ u ψ z
          - bsWin ℓ u z * fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)),
        sq_nonneg (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k))]
    have hcA : Continuous (fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
        (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
      have h1 : Continuous (fun z : ℝ³ =>
          fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k)) :=
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous_fderiv (by simp)).clm_apply
          continuous_const |>.comp (continuous_id.sub continuous_const)
      exact h1.pow 2
    have hDerivCS : HasCompactSupport (fun z : ℝ³ =>
        fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k)) := by
      have h2 : HasCompactSupport (fun z : ℝ³ =>
          fderiv ℝ (bsWin ℓ u) z (Submission.BoseGases.kcStdBasis k)) :=
        hbsWincs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis k)
      have h3 : (fun z : ℝ³ => fderiv ℝ (bsWin ℓ u) z (Submission.BoseGases.kcStdBasis k))
          = fun z : ℝ³ => fderiv ℝ (chiScale ℓ) (z - ℓ • u)
              (Submission.BoseGases.kcStdBasis k) := by
        funext z
        exact Work.BSKinetic.fderiv_comp_sub_const_apply (chiScale ℓ) (ℓ • u) z
          (Submission.BoseGases.kcStdBasis k)
          ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable (by simp)
            (z - ℓ • u))
      rwa [h3] at h2
    have hAcs : HasCompactSupport (fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
        (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
      have hfun : (fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
            (Submission.BoseGases.kcStdBasis k)) ^ 2)
          = (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k))
            * (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) (z - ℓ • u) (Submission.BoseGases.kcStdBasis k)) := by
        funext z; rw [Pi.mul_apply, pow_two]
      rw [hfun]
      exact HasCompactSupport.mul_right hDerivCS
    have hIntA : Integrable (fun z : ℝ³ => 8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
        (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
      (hcA.integrable_of_hasCompactSupport hAcs).const_mul _
    have hIntB : Integrable (fun z : ℝ³ => 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2) :=
      ((hbsWincont.pow 2).integrable_of_hasCompactSupport
        (famKin_hasCompactSupport_sq hbsWincs)).const_mul _
    have hint : Integrable (fun z : ℝ³ => 8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
          (Submission.BoseGases.kcStdBasis k)) ^ 2 + 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2) :=
      hIntA.add hIntB
    calc ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ ∫ z : ℝ³, (8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
              (Submission.BoseGases.kcStdBasis k)) ^ 2 + 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall (fun z => sq_nonneg _)) hint
            (Eventually.of_forall hpt)
      _ = 8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0 := by
          rw [integral_add hIntA hIntB, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul, htransD k, htrans2]
  have hw := famKin_bsOneBody_le_weighted (c := c) hℓ u hψcd hψcs
  have hfin : 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
      + ∑ k : Fin 3, (∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2))
      ≤ 2 * (1 + c ^ 2) * (4 * S0 ^ 2 * E0
          + ∑ k : Fin 3, (8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add hL2h
    exact Finset.sum_le_sum (fun k _ => hDirh k)
  calc bsOneBody ℓ (fsKinCoeff c) u ψ
      ≤ 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
          + ∑ k : Fin 3, (∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2)) := hw
    _ ≤ 2 * (1 + c ^ 2) * (4 * S0 ^ 2 * E0
          + ∑ k : Fin 3, (8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0)) := hfin
    _ ≤ max (2 * (1 + c ^ 2) * (4 * S0 ^ 2 * E0
          + ∑ k : Fin 3, (8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0))) 0 := le_max_left _ _

/-! ## H. Joint measurability of the uncurried slot form -/

lemma famKin_bsMean_pair_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun q : ℝ³ × X n =>
      bsMean ℓ q.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.2)))) := by
  have hcont : Continuous (Function.uncurry (fun (q : ℝ³ × X n) (z : ℝ³) =>
      Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2)))) := by
    refine hΦ.continuous.comp ?_
    refine (Submission.BoseGases.kcInsN_cont i).comp ?_
    exact (((continuous_fst.fst).const_smul ℓ).add continuous_snd).prodMk continuous_fst.snd
  have h := Commons.Analysis.Calculus.continuous_setIntegral_isCompact
    (Submission.BoseGases.acube_compact hℓ) hcont
  have hfun : (fun q : ℝ³ × X n =>
      bsMean ℓ q.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      = fun q : ℝ³ × X n => (ℓ ^ 3)⁻¹ *
          ∫ z in acube ℓ, Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2)) := rfl
  rw [hfun]
  exact h.const_mul _

lemma famKin_uncurry_aemeas {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    AEStronglyMeasurable
      (Function.uncurry (fun (u : ℝ³) (r : X n) =>
        bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))))
      (volume.prod ((volume : Measure (X n)).restrict (abox n ℓ))) := by
  set ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ) with hν
  have hz : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => w.2 - ℓ • w.1.1.1) :=
    continuous_snd.sub (continuous_fst.fst.fst.const_smul ℓ)
  have hW : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => bsWin ℓ w.1.1.1 w.2) := by
    have hfun : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => bsWin ℓ w.1.1.1 w.2)
        = fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => chiScale ℓ (w.2 - ℓ • w.1.1.1) := rfl
    rw [hfun]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp hz
  have hfib : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      Φ (Submission.BoseGases.kcInsN n i (w.2, w.1.1.2))) :=
    hΦ.continuous.comp ((Submission.BoseGases.kcInsN_cont i).comp
      (continuous_snd.prodMk continuous_fst.fst.snd))
  have hmean0 : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      ∫ z in acube ℓ, Φ (Submission.BoseGases.kcInsN n i (ℓ • w.1.1.1 + z, w.1.1.2))) := by
    refine Commons.Analysis.Calculus.continuous_setIntegral_isCompact
      (Submission.BoseGases.acube_compact hℓ) ?_
    have h1 : Continuous (fun p : (((ℝ³ × X n) × ℝ³) × ℝ³) × ℝ³ => ℓ • p.1.1.1.1) :=
      (continuous_fst.fst.fst.fst).const_smul ℓ
    have h2 : Continuous (fun p : (((ℝ³ × X n) × ℝ³) × ℝ³) × ℝ³ => p.2) := continuous_snd
    have h3 : Continuous (fun p : (((ℝ³ × X n) × ℝ³) × ℝ³) × ℝ³ => p.1.1.1.2) :=
      continuous_fst.fst.fst.snd
    refine hΦ.continuous.comp ?_
    refine (Submission.BoseGases.kcInsN_cont i).comp ?_
    exact (h1.add h2).prodMk h3
  have hmean : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      bsMean ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2)))) := by
    have hfun : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
        bsMean ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2))))
        = fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => (ℓ ^ 3)⁻¹ *
            ∫ z in acube ℓ, Φ (Submission.BoseGases.kcInsN n i (ℓ • w.1.1.1 + z, w.1.1.2)) := rfl
    rw [hfun]
    exact hmean0.const_mul _
  have hQ : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2))) w.2) := by
    have hfun : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
        bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2))) w.2)
        = fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
            Φ (Submission.BoseGases.kcInsN n i (w.2, w.1.1.2))
            - bsMean ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2))) := rfl
    rw [hfun]
    exact hfib.sub hmean
  have hExp : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ)))) :=
    Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_fst.snd.prodMk continuous_snd)))).neg)
  have hWc : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => (bsWin ℓ w.1.1.1 w.2 : ℂ)) :=
    Complex.continuous_ofReal.comp hW
  have hQc : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      (bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2))) w.2 : ℂ)) :=
    Complex.continuous_ofReal.comp hQ
  let JJ : ((ℝ³ × X n) × ℝ³) × ℝ³ → ℂ := fun w =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))) *
        ((bsWin ℓ w.1.1.1 w.2 : ℂ) *
          (bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, w.1.1.2))) w.2
            : ℂ))
  have hJ : Continuous JJ := hExp.mul (hWc.mul hQc)
  have hK : AEStronglyMeasurable (fun q : (ℝ³ × X n) × ℝ³ => ∫ z : ℝ³, JJ (q, z))
      ((volume.prod ν).prod volume) :=
    hJ.stronglyMeasurable.aestronglyMeasurable.integral_prod_right'
  have hK2 : AEStronglyMeasurable (fun q : (ℝ³ × X n) × ℝ³ =>
      fsKinCoeff c ‖q.2‖ * ‖(∫ z : ℝ³, JJ (q, z))‖ ^ 2)
      ((volume.prod ν).prod volume) := by
    have hc2 : Continuous (fun q : (ℝ³ × X n) × ℝ³ => fsKinCoeff c ‖q.2‖) :=
      (famKin_continuous_fsKinCoeff_norm c).comp continuous_snd
    have hf : AEStronglyMeasurable (fun q : (ℝ³ × X n) × ℝ³ => fsKinCoeff c ‖q.2‖)
        ((volume.prod ν).prod volume) := hc2.stronglyMeasurable.aestronglyMeasurable
    exact hf.mul ((hK.norm).pow 2)
  have hK3 : AEStronglyMeasurable (fun q : ℝ³ × X n => ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ‖(∫ z : ℝ³, JJ ((q, p), z))‖ ^ 2)
      (volume.prod ν) := by
    have h3 := hK2.integral_prod_right'
    exact h3.const_mul _
  refine hK3.congr ?_
  filter_upwards with q
  show ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
      ‖(∫ z : ℝ³, JJ ((q, p), z))‖ ^ 2
    = bsOneBody ℓ (fsKinCoeff c) q.1
        (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, q.2)))
  rw [bsOneBody]
  rfl


lemma famKin_bsOneBody_nonneg (ℓ c : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    0 ≤ bsOneBody ℓ (fsKinCoeff c) u ψ := by
  rw [bsOneBody]
  exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg (fun p =>
    mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)))

theorem familyBigKin_eq_slotFamily {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BSKinetic.SuppInBox (n + 1) ℓ Φ) :
    Work.BSKinetic.familyBigKin (n + 1) ℓ c Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          Work.BSKinetic.bsFamilyForm ℓ (Submission.BoseGases.fsKinCoeff c)
            (fun z : EuclideanSpace ℝ (Fin 3) =>
              Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  classical
  set ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ) with hν
  obtain ⟨C, hC0, hC⟩ := famKin_bsOneBody_le (c := c) hℓ n Φ hΦ hsupp
  have hInt : ∀ i : Fin (n + 1),
      Integrable (Function.uncurry (fun (u : ℝ³) (r : X n) =>
        bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))))
        (volume.prod ν) := by
    intro i
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
      (μ := volume) (ν := ν)
      (f := fun (u : ℝ³) (r : X n) =>
        bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))))
      (g := fun _ => ENNReal.ofReal C * volume (Metric.ball (0 : ℝ³) 2)) ?_ ?_ ?_
    · exact famKin_uncurry_aemeas (c := c) hℓ n Φ hΦ i
    · rw [MeasureTheory.lintegral_const, hν, MeasureTheory.Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top MeasureTheory.measure_ball_lt_top.ne)
        (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
    · filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ)] with r hr
      calc (∫⁻ u : ℝ³, ENNReal.ofReal ‖bsOneBody ℓ (fsKinCoeff c) u
              (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))‖)
          = ∫⁻ u : ℝ³, ENNReal.ofReal (bsOneBody ℓ (fsKinCoeff c) u
              (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))) := by
            apply lintegral_congr; intro u
            rw [Real.norm_of_nonneg (famKin_bsOneBody_nonneg ℓ c u _)]
        _ ≤ ∫⁻ u : ℝ³, (Metric.ball (0 : ℝ³) 2).indicator (fun _ => ENNReal.ofReal C) u := by
            apply lintegral_mono; intro u
            by_cases hu : u ∈ Metric.ball (0 : ℝ³) 2
            · rw [Set.indicator_of_mem hu]
              exact ENNReal.ofReal_le_ofReal (hC u i r hr)
            · rw [Set.indicator_of_notMem hu]
              have hfar : bsOneBody ℓ (fsKinCoeff c) u
                  (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) = 0 :=
                famKin_bsOneBody_eq_zero_of_far (c := c) hℓ n Φ hsupp i hr
                  (not_lt.mp (by simpa [Metric.mem_ball, dist_eq_norm] using hu))
              simp only [hfar, ENNReal.ofReal_zero]
              exact le_refl _
        _ = ENNReal.ofReal C * volume (Metric.ball (0 : ℝ³) 2) := by
            rw [MeasureTheory.lintegral_indicator measurableSet_ball,
              MeasureTheory.setLIntegral_const]
  have hpt : ∀ u : ℝ³, Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ
      = ∑ i : Fin (n + 1), ∫ r : X n, (bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))) ∂ν := by
    intro u
    rw [famKin_tBwordKinBigU_eq_slotSum (c := c) hℓ n u Φ hΦ]
  trans ∫ u : ℝ³, ∑ i : Fin (n + 1), ∫ r : X n, (bsOneBody ℓ (fsKinCoeff c) u
      (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))) ∂ν
  · rw [show Work.BSKinetic.familyBigKin (n + 1) ℓ c Φ
        = ∫ u : ℝ³, Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ from rfl]
    apply integral_congr_ae
    filter_upwards with u
    exact hpt u
  · rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) (hInt i)]
      rfl
    · intro i _
      exact MeasureTheory.Integrable.integral_prod_left (hInt i)

end Work.BSKinetic
