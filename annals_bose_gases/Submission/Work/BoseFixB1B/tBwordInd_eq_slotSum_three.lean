import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.win.chiSmallB_windowIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.tBwordInd_eq_slotSum_three`

Slot additivity of the FS-faithful small-box word `Work.UBBInputs8.tBwordInd` at a **`C³`
window** `χ` supported in the sliding box `A = dlBox ℓ d u`:

    `tBwordInd ℓ A |A| χ (ℓ d) ε c Φ
       = Σ_i ∫_{r ∈ abox n ℓ} tBwordInd ℓ A |A| χ (ℓ d) ε c (slotState1 i Φ r)`.

The corpus's `Work.BSKinetic.tBwordBInd_eq_slotSum` proves this for the *smooth* sliding window
`chiB ℓ d u` (`ContDiff ℝ ⊤`); the point of the present file is to run the same proof with the
smoothness of the window relaxed to `ContDiff ℝ 3` (the regularity needed by the Fourier-decay
engine `Commons.Analysis.Fourier.fourier_decay_mul_update`), so that the statement can be
instantiated at the cosine-cutoff windows `chiSmallB`/`chiCubeB`, which are *not* smooth.

Both halves of `tBwordInd` decompose slot by slot:

* the FS mean-free count `cnPlusBoxInd` is *window-free*, so the corpus's `cnPlusBoxInd_slotStep`
  applies verbatim;
* the spectral half `tBdiagFormInd` needs the window only through the uniform `(1+‖p‖)⁻³` decay of
  the windowed amplitude (`Work.BoseFixB1S.win.tBamp_decay_three`, the `C³` counterpart of
  `Work.SmallBoxTBWord.tBamp_decay`), which is what makes the `p ↔ abox n ℓ` Fubini exchange
  `swap_p_abox_tBamp_gen_three` legitimate.  Everything else (`peel_tBamp_gen`,
  `boxQInd_oneBody_energy`) already needs only *continuity* of the window.

The two intermediate lemmas are stated separately so that they are reusable.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

-- `ℝ³` is the *global* `notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` of
-- `Submission/Work/BoseKinLoc/Defs.lean`, which is in this file's import cone.

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The `C³` `p ↔ abox` Fubini exchange

This is `Work.BSKinetic.swap_p_abox_tBamp_gen` with the smoothness hypothesis on the window
weakened from `ContDiff ℝ ⊤` to `ContDiff ℝ 3`; the only change in the proof is that the uniform
Fourier decay is supplied by `Work.BoseFixB1S.win.tBamp_decay_three`. -/

theorem swap_p_abox_tBamp_gen_three {n : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ)
    (χ : ℝ³ → ℝ) (hχcd : ContDiff ℝ 3 χ) (hχcs : HasCompactSupport χ)
    (Ψ : X (n + 1) → ℝ) (hΨcd : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    MeasureTheory.Integrable (fun q : ℝ³ × X n =>
        fsKinCoeff c ‖q.1‖ * ‖Work.SmallBoxTBWord.tBamp χ q.1 Ψ i (kcInsN n i (0, q.2))‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict (abox n ℓ)))
    ∧ (((2 * Real.pi) ^ 3)⁻¹) *
        (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2))
      = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2 := by
  classical
  set ν : Measure (X n) :=
    (volume : Measure (X n)).restrict (abox n ℓ) with hν
  set f : ℝ³ → X n → ℝ := fun p r =>
    fsKinCoeff c ‖p‖ *
      ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2 with hf
  -- uniform Fourier decay of the windowed amplitude on the ambient box
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1S.win.tBamp_decay_three (N := n + 1) hℓ hχcd hχcs hΨcd
  -- the slice `kcInsN n i (0, r)` of a box configuration remains in the ambient box
  have h0mem : (0 : ℝ³) ∈ acube ℓ :=
    mem_acube_of_norm_le (le_of_lt hℓ) (by rw [norm_zero]; positivity)
  -- the pointwise domination of the integrand
  have hpt : ∀ p : ℝ³, ∀ r ∈ abox n ℓ,
      f p r ≤ ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4 := by
    intro p r hr
    have hx : kcInsN n i (0, r) ∈ abox (n + 1) ℓ := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [kc_insN_apply_same]; exact h0mem
      · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
        rw [kc_insN_apply_succ]; exact hr j'
    have hb : ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖
        ≤ C / (1 + ‖p‖) ^ 3 := hC _ hx i p
    rw [hf]
    calc fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2
        ≤ fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
            (fsKinCoeff_nonneg c ‖p‖)
      _ ≤ ((1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right (Work.BSKinetic.SwapTBAmp.fsKinCoeff_le (norm_nonneg p))
            (sq_nonneg _)
      _ = ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4 :=
          Work.BSKinetic.SwapTBAmp.fsKinCoeff_algebra c C ‖p‖ (norm_nonneg p)
  -- the dominating function and its integrability
  have hD : MeasureTheory.Integrable
      (fun p : ℝ³ => ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) := by
    refine (Work.BSKinetic.SwapTBAmp.integrable_one_div_pow4.const_mul
      ((1 + |c|) ^ 2 * C ^ 2)).congr (Eventually.of_forall (fun p => ?_))
    change ((1 + |c|) ^ 2 * C ^ 2) * (1 / (1 + ‖p‖) ^ 4)
      = ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4
    rw [mul_one_div]
  have hDnn : ∀ p : ℝ³, 0 ≤ ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4 := by
    intro p; positivity
  have hfnn : ∀ p r, 0 ≤ f p r := by
    intro p r
    rw [hf]
    exact mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)
  -- joint measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    change AEStronglyMeasurable (fun q : ℝ³ × X n =>
      fsKinCoeff c ‖q.1‖ *
        ‖Work.SmallBoxTBWord.tBamp χ q.1 Ψ i (kcInsN n i (0, q.2))‖ ^ 2) (volume.prod ν)
    refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
    · have hfs : Continuous (fun r : ℝ => fsKinCoeff c r) := by
        rw [show fsKinCoeff c = fun r : ℝ => (max (r - c) 0) ^ 2 from rfl]
        exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
      exact hfs.comp (continuous_norm.comp continuous_fst)
    · exact ((Work.SmallBoxTBWord.continuous_tBamp_pair hχcd.continuous hχcs
        hΨcd.continuous i).comp
        (continuous_fst.prodMk ((kcInsN_cont i).comp
          (continuous_const.prodMk continuous_snd)))).norm.pow 2
  -- the iterated-lintegral bound along the fibres
  have hbm : ∀ᵐ r ∂ν, (∫⁻ p : ℝ³, ENNReal.ofReal ‖f p r‖) ≤
      ENNReal.ofReal (∫ p : ℝ³, ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) := by
    rw [hν, ae_restrict_iff' (abox_measurable n ℓ)]
    filter_upwards with r hr
    calc (∫⁻ p : ℝ³, ENNReal.ofReal ‖f p r‖)
        = ∫⁻ p : ℝ³, ENNReal.ofReal (f p r) := by
          apply lintegral_congr; intro p; rw [Real.norm_of_nonneg (hfnn p r)]
      _ ≤ ∫⁻ p : ℝ³, ENNReal.ofReal (((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) := by
          apply lintegral_mono; intro p
          exact ENNReal.ofReal_le_ofReal (hpt p r hr)
      _ = ENNReal.ofReal (∫ p : ℝ³, ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) :=
          (ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall hDnn)).symm
  have hg : (∫⁻ r : X n,
      ENNReal.ofReal (∫ p : ℝ³, ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) ∂ν) ≠ ⊤ := by
    rw [hν, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (abox_lt_top n ℓ hℓ.le).ne
  have hInt : MeasureTheory.Integrable (Function.uncurry f) (volume.prod ν) :=
    Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite hmeas hg hbm
  -- the Fubini exchange
  have hswap := MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) hInt
  have hL : (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        (∫ r in abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2))
      = ∫ p : ℝ³, ∫ r : X n, f p r ∂ν := by
    apply integral_congr_ae; filter_upwards with p
    rw [hf]
    rw [integral_const_mul]
  have hR : (∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
        ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2)
      = (((2 * Real.pi) ^ 3)⁻¹) * (∫ r : X n,
          ∫ p : ℝ³, f p r ∂volume ∂ν) := by
    rw [← integral_const_mul]
  refine ⟨?_, ?_⟩
  · exact hInt
  · calc (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        (∫ r in abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2))
        = (((2 * Real.pi) ^ 3)⁻¹) *
            (∫ p : ℝ³, ∫ r : X n, f p r ∂ν) := by rw [hL]
      _ = (((2 * Real.pi) ^ 3)⁻¹) *
            (∫ r : X n, ∫ p : ℝ³, f p r ∂volume ∂ν) := by rw [hswap]
      _ = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
            ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
              ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2 :=
          hR.symm

/-! ## 2. The spectral slot step at a `C³` window -/

theorem tBdiagFormInd_slotStep_three {n : ℕ} {ℓ c volA : ℝ} (hℓ : 0 < ℓ)
    (χ : ℝ³ → ℝ) (hχcd : ContDiff ℝ 3 χ) (hχcs : HasCompactSupport χ)
    {A : Set ℝ³} (hχsupp : ∀ z, z ∉ A → χ z = 0) (hAc : IsCompact A)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in abox 1 ℓ,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2) := by
  set Ψ : X (n + 1) → ℝ := Work.SmallBoxTBWord.boxQ volA A i Φ with hΨdef
  have hΨcd : ContDiff ℝ (⊤ : ENat) Ψ :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAc volA i hΦ
  have henergy : ∀ (r : X n) (p : ℝ³),
      (ℓ ^ 3)⁻¹ * ∫ x in abox 1 ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2
        = ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2 := by
    intro r p
    rw [Work.BSKinetic.boxQInd_oneBody_energy hℓ χ hχsupp Φ i r p]
  have hpeel : ∀ p : ℝ³, (ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2
      = ∫ r in abox n ℓ, ‖kinFT (fun z : ℝ³ => (χ z : ℂ) *
          (Ψ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
    intro p
    refine Work.BSKinetic.peel_tBamp_gen hℓ hχcs hχcd.continuous ?_ hΨcd.continuous i p
    intro z hz
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  have hbq : ∀ p : ℝ³, (ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
      = (ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2 := by
    intro p; congr 1; apply integral_congr_ae; filter_upwards with x
    rw [Work.UBBInputs9.A.tBamp_boxQInd hχsupp]
  have hL1 : (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = ∫ r in abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2 := by
    rw [show (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
        = ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2) from by
      apply integral_congr_ae; filter_upwards with p; rw [hbq p]]
    rw [show (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2))
        = ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ, ‖kinFT (fun z : ℝ³ => (χ z : ℂ) *
            (Ψ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2) from by
      apply integral_congr_ae; filter_upwards with p; rw [hpeel p]]
    rw [show (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ, ‖kinFT (fun z : ℝ³ => (χ z : ℂ) *
            (Ψ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2))
        = ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (kcInsN n i (0, r))‖ ^ 2) from by
      apply integral_congr_ae; filter_upwards with p; congr 1
      apply integral_congr_ae; filter_upwards with r
      rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]]
    rw [(Work.BoseFixB1B.swap_p_abox_tBamp_gen_three hℓ χ hχcd hχcs Ψ hΨcd i).2]
  rw [hL1]
  apply integral_congr_ae
  filter_upwards with r
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [henergy r p]

/-! ## 3. The target -/

theorem tBwordInd_eq_slotSum_three {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχcs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Submission.BoseGases.dlBox ℓ d u → χ z = 0)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) χ (ℓ * d) ε c Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) χ (ℓ * d) ε c
            (Work.BSKinetic.slotState1 i Φ r) := by
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  have hAmeas : MeasurableSet A := Work.BSKinetic.measurableSet_dlBox u
  have hAc : IsCompact A := Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u
  have hχsuppA : ∀ z, z ∉ A → χ z = 0 := fun z hz => hχsupp z (by simpa only [hAdef] using hz)
  have hstep : ∀ i : Fin (n + 1),
      (∫ r in Submission.BoseGases.abox n ℓ,
        (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
            (∫ x in Submission.BoseGases.abox 1 ℓ,
              (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x) ^ 2)
          + (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd volA A 0
                    (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)))
        = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
            (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          + (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2) := by
    intro i
    have hGint : MeasureTheory.Integrable (fun r : X n =>
        ∫ x in Submission.BoseGases.abox 1 ℓ,
          (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x) ^ 2)
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
      have hF : IntegrableOn
          (fun x : X (n + 1) => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          (Submission.BoseGases.abox (n + 1) ℓ) volume :=
        Work.BSKinetic.integrableOn_boxQInd_sq hℓ hAmeas hAc Φ hΦ i
      have hpeel_int := Submission.BoseGases.abox_peel_inner_integrable i
        (fun x : X (n + 1) => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) hF
      refine hpeel_int.congr ?_
      filter_upwards with r
      rw [Work.BSKinetic.integral_abox_one_eq_acube ℓ (fun x : X 1 =>
        (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x) ^ 2)]
      apply integral_congr_ae; filter_upwards with y
      rw [Work.BSKinetic.boxQInd_slotState1]
    have hKint : MeasureTheory.Integrable (fun r : X n =>
        (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A 0
                (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2))
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
      have hΨcd : ContDiff ℝ (⊤ : ENat) (Work.SmallBoxTBWord.boxQ volA A i Φ) :=
        Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAc volA i hΦ
      have hprod := (swap_p_abox_tBamp_gen_three (ℓ := ℓ) (c := c) hℓ χ hχ hχcs
        (Work.SmallBoxTBWord.boxQ volA A i Φ) hΨcd i).1.integral_prod_right
      refine (hprod.const_mul (((2 * Real.pi) ^ 3)⁻¹)).congr ?_
      filter_upwards with r
      congr 1
      apply integral_congr_ae; filter_upwards with p
      rw [Work.BSKinetic.boxQInd_oneBody_energy hℓ χ hχsuppA Φ i r p]
    rw [MeasureTheory.integral_add (hGint.const_mul _) hKint, MeasureTheory.integral_const_mul,
      ← Work.BSKinetic.cnPlusBoxInd_slotStep hℓ hAmeas hAc n Φ hΦ i,
      ← tBdiagFormInd_slotStep_three hℓ χ hχ hχcs hχsuppA hAc Φ hΦ i]
  simp only [Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.tBdiagFormInd, Fin.sum_univ_one]
  symm
  rw [show (∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
        (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
            (∫ x in Submission.BoseGases.abox 1 ℓ,
              (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x) ^ 2)
          + (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd volA A 0
                    (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)))
      = ∑ i : Fin (n + 1),
          (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
              (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            + (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
                ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  ‖Work.SmallBoxTBWord.tBamp χ p
                    (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      from Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end Work.BoseFixB1B
