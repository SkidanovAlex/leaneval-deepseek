/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeS1/SigFirstOrderHon` — the `σ`-weighted slice self-form with the `sec²θ` slot (honest class)

The honest (`C²` on `(0,π/2)`, `C¹` on `[0,π/2]`, vanishing at both endpoints) slicewise
`σ`-weighted upper bound for the `sec²θ`-slot of `Lzero1`:

  `((1-η)/2) ∫_θ (f/cos θ)² σ ≤ ∫_θ (Lzero1 f)·f·σ + K ∫_θ f² σ`,   `σ = sin(2θ)^{-η}`.

It is the strengthening of `Work.FTS.EllipticEst.Honest.HonSliceSigmaLower` obtained by *keeping*
the positive `honCc`-term of `honSliceIdentity` instead of dropping it, i.e. by substituting

  `∫ honCc = ∫ honLz - ∫ honDu + (η+6) ∫ honU2 + 2η(1+η) ∫ honHc`

and bounding `∫ honHc` with the sharp same-weight Hardy inequality; the resulting inequality
`2η(1+η) ∫honHc ≤ ∫honDu + (2η/(1+η))... ` is closed by `2η/(1+η) ≤ 1`, which is `η ≤ 1`.

The proof is a verbatim copy of the proof of `HonSliceSigmaLower` (all of whose ingredients are
reused) up to the final arithmetic, which is redone here.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `σ`-weighted slice self-form of `Lzero1`, with the positive `sec²θ`-slot** (honest
class).  There is `K > 0` such that for every `f` which is `C²` on `(0,π/2)`, `C¹` on `[0,π/2]`,
vanishes at both endpoints, and whose four `σ`-weighted integrands are honest,

  `((1-η)/2) ∫_θ (f/cos θ)² σ ≤ ∫_θ (Lzero1 f)·f·σ + K ∫_θ f² σ`. -/
theorem honSliceSigmaStrong :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContDiffOn ℝ 1 f (Work.Spaces.Iθ) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      ((1 - Work.Spaces.eta) / 2) * (∫ θ in Work.Spaces.Iθ,
          (f θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ)
          + K * (∫ θ in Work.Spaces.Iθ,
              (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨CH, hCH0, hHardyBase⟩ :=
    hardy_shift_two_same_weight Work.Spaces.eta Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
  have hKpos : 0 < Work.Spaces.eta + 6 + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * CH := by
    have h1 : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
    have h2 : (0 : ℝ) < 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
    have h3 : (0 : ℝ) < 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) := mul_pos h2 h1
    have h4 : (0 : ℝ) < 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * CH := mul_pos h3 hCH0
    linarith [h4, Work.Spaces.eta_pos]
  refine ⟨Work.Spaces.eta + 6 + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * CH,
    hKpos, ?_⟩
  intro f hu2 hu1 h0 hπ hint_du hint_ddu hint_u hint_lz
  set η : ℝ := Work.Spaces.eta with hηdef
  have hη0 : 0 ≤ η := by rw [hηdef, Work.Spaces.eta]; norm_num
  have hη1 : η < 1 := by rw [hηdef, Work.Spaces.eta]; norm_num
  obtain ⟨C, hC0, hbdIcc, hbdd⟩ := Work.Elliptic.contDiffOn_one_bounds hu1 h0 hπ
  have hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ := fun θ hθ =>
    le_trans (hbdIcc θ (Ioo_subset_Icc_self hθ))
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hC0)
  have hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ) := fun θ hθ =>
    le_trans (hbdIcc θ (Ioo_subset_Icc_self hθ))
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC0)
  have hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C := fun θ hθ => by
    rw [← Real.norm_eq_abs]
    exact hbdd θ hθ
  have hu_cont : ContinuousOn f Iθo := hu2.continuousOn
  have hlim : HonPrimTendstoProp η f :=
    HonPrimitiveTendsto η hη0 hη1 f C hC0 hb1 hb2 hb3
  obtain ⟨hcc, hhc⟩ := HonAuxIntegrable η hη0 hη1 f C hC0 hu_cont hb1 hb2
  have hfull : IntegrableOn (honFull η f) Iθo :=
    HonFullWeightIntegrable η hη0 hη1 f C hC0 hu_cont hb1 hb2
  have hid := honSliceIdentity η hη0 hη1 f hu2 hlim
    (hint_lz.mono_set Ioo_subset_Icc_self) hint_du hint_u hcc hhc
  -- the sharp Hardy bound on the full weight
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_of_Icc hθ
  have hAeq : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      = ∫ θ in Work.Spaces.Iθ, honDu η f θ := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    simp only [honDu, sig]
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ)]
  have hBeq : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      = ∫ θ in Work.Spaces.Iθ, honU2 η f θ := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    simp only [honU2, sig]
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ)]
  have hHardy' : (∫ θ in Work.Spaces.Iθ, honFull η f θ)
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
        + CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
    have h := hHardyBase f hu1 h0 hπ
    rw [show (1 : ℝ) / (η + 1) ^ 2 = 1 / (1 + η) ^ 2 by ring] at h
    rw [hAeq, hBeq] at h
    exact h
  have hHtG : (∫ θ in Work.Spaces.Iθ, honHc η f θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honFull η f θ) := by
    have hhcI : IntegrableOn (honHc η f) Work.Spaces.Iθ :=
      hhc.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2)).symm
    have hfullI : IntegrableOn (honFull η f) Work.Spaces.Iθ :=
      hfull.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2)).symm
    refine MeasureTheory.integral_mono_of_nonneg ?_ hfullI ?_
    · refine eventually_ae_Iθ_of_Ioo ?_
      intro θ hθ
      have hs := sin_two_pos_of_Iθo hθ
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
    · refine eventually_ae_Iθ_of_Ioo ?_
      intro θ hθ
      exact honHc_le_honFull η f hθ
  have hHtBound : (∫ θ in Work.Spaces.Iθ, honHc η f θ)
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
        + CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := le_trans hHtG hHardy'
  have hH2 : (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honHc η f θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honDu η f θ)
        + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
    have hne : (1 + η) ^ 2 ≠ 0 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hHtBound (by positivity : (0 : ℝ) ≤ (1 + η) ^ 2)
    have he : (1 + η) ^ 2 * (1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
          + CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ))
        = (∫ θ in Work.Spaces.Iθ, honDu η f θ)
          + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
      field_simp
    linarith [h1, he]
  have hDu0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, honDu η f θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos_of_Iθo hθ).le _)
  -- the pointwise identity `honCc = ((1-η)/2)·(f/cos)²σ`
  have honCc_eq_pt : ∀ θ : ℝ,
      honCc η f θ = ((1 - η) / 2) * ((f θ / Real.cos θ) ^ 2 * sig η θ) := by
    intro θ
    rw [honCc]
    by_cases h : Real.cos θ = 0
    · simp [h]
    · have hcos2 : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 h
      rw [div_pow,
        show (1 / 2 * (1 - η) / Real.cos θ ^ 2) = (1 - η) / 2 / Real.cos θ ^ 2 from by ring]
      field_simp
      try ring
  have hCcEq : (∫ θ in Work.Spaces.Iθ, honCc η f θ)
      = ((1 - η) / 2) * (∫ θ in Work.Spaces.Iθ,
          (f θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [show (∫ θ in Work.Spaces.Iθ, honCc η f θ)
        = ∫ θ in Work.Spaces.Iθ, ((1 - η) / 2) * ((f θ / Real.cos θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => honCc_eq_pt θ)]
    exact MeasureTheory.integral_const_mul _ _
  -- the final arithmetic
  have hne1 : (0 : ℝ) < 1 + η := by linarith
  rw [← hCcEq]
  have hgoal : (∫ θ in Work.Spaces.Iθ, honCc η f θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honLz η f θ)
        + (η + 6 + 2 * η * (1 + η) * CH)
          * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
    have hmul : (1 + η) * (∫ θ in Work.Spaces.Iθ, honCc η f θ)
        ≤ (1 + η) * ((∫ θ in Work.Spaces.Iθ, honLz η f θ)
          + (η + 6 + 2 * η * (1 + η) * CH)
            * (∫ θ in Work.Spaces.Iθ, honU2 η f θ)) := by
      have hstep1 : 2 * η * ((1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honHc η f θ))
          ≤ 2 * η * ((∫ θ in Work.Spaces.Iθ, honDu η f θ)
              + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ)) :=
        mul_le_mul_of_nonneg_left hH2 (by linarith)
      have hstep2 : 2 * η * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
          ≤ (1 + η) * (∫ θ in Work.Spaces.Iθ, honDu η f θ) :=
        mul_le_mul_of_nonneg_right (by linarith) hDu0
      nlinarith [hid, hstep1, hstep2]
    exact le_of_mul_le_mul_left hmul hne1
  exact hgoal

end Work.FTS.EllipticEst.Honest
