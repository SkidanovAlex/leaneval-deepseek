import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.swap_p_abox_tBamp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.swap_p_abox_tBamp_gen` — the `p ↔ abox` Fubini exchange, general window

This is the general form of `Work.BSKinetic.swap_p_abox_tBamp`: the window `χ` and the
`(n+1)`-particle state `Ψ` are *free* parameters (smooth, `χ` of compact support) rather than
the concrete big-box data `chiBig ℓ u` / `boxQ (ℓ³) (bigBox ℓ u) i Φ`.

Both halves of the conclusion are *integrability* statements about the same integrand

    `(p, r) ↦ fsKinCoeff c ‖p‖ · ‖tBamp χ p Ψ i (kcInsN n i (0, r))‖²`   on `ℝ³ × abox n ℓ`

(Tonelli/Fubini for a nonnegative integrand plus the linearity of the integral in the two
constant prefactors).  The only substantive input is the uniform Fourier decay of the windowed
amplitude (`Work.SmallBoxTBWord.tBamp_decay`): on the ambient box `abox (n+1) ℓ`, which contains
every slice `kcInsN n i (0, r)` with `r ∈ abox n ℓ`, the amplitude is bounded by `C(1+‖p‖)⁻³`,
so the integrand is dominated by `(1+|c|)²C²·(1+‖p‖)⁻⁴` — integrable in dimension three.  The
iterated-lintegral criterion `integrable_uncurry_of_lintegral_le_sfinite` then gives joint
integrability, and `integral_integral_swap` gives the exchange.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

theorem swap_p_abox_tBamp_gen {n : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (hχcd : ContDiff ℝ (⊤ : ENat) χ)
    (hχcs : HasCompactSupport χ)
    (Ψ : Submission.BoseGases.X (n + 1) → ℝ) (hΨcd : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ‖Work.SmallBoxTBWord.tBamp χ q.1 Ψ i (Submission.BoseGases.kcInsN n i (0, q.2))‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
    ∧ (((2 * Real.pi) ^ 3)⁻¹) *
        (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          (∫ r in Submission.BoseGases.abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2))
      = ∫ r in Submission.BoseGases.abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 := by
  classical
  set ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ) with hν
  set f : ℝ³ → Submission.BoseGases.X n → ℝ := fun p r =>
    Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 with hf
  -- uniform Fourier decay of the windowed amplitude on the ambient box
  obtain ⟨C, hC0, hC⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n + 1) hℓ hχcd hχcs hΨcd
  -- the slice `kcInsN n i (0, r)` of a box configuration remains in the ambient box
  have h0mem : (0 : ℝ³) ∈ Submission.BoseGases.acube ℓ :=
    Submission.BoseGases.mem_acube_of_norm_le (le_of_lt hℓ) (by rw [norm_zero]; positivity)
  -- the pointwise domination of the integrand
  have hpt : ∀ p : ℝ³, ∀ r ∈ Submission.BoseGases.abox n ℓ,
      f p r ≤ ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4 := by
    intro p r hr
    have hx : Submission.BoseGases.kcInsN n i (0, r) ∈ Submission.BoseGases.abox (n + 1) ℓ := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [Submission.BoseGases.kc_insN_apply_same]; exact h0mem
      · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
        rw [Submission.BoseGases.kc_insN_apply_succ]; exact hr j'
    have hb : ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖
        ≤ C / (1 + ‖p‖) ^ 3 := hC _ hx i p
    rw [hf]
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
            (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
      _ ≤ ((1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right (SwapTBAmp.fsKinCoeff_le (norm_nonneg p)) (sq_nonneg _)
      _ = ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4 :=
          SwapTBAmp.fsKinCoeff_algebra c C ‖p‖ (norm_nonneg p)
  -- the dominating function and its integrability
  have hD : MeasureTheory.Integrable
      (fun p : ℝ³ => ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) := by
    refine (SwapTBAmp.integrable_one_div_pow4.const_mul ((1 + |c|) ^ 2 * C ^ 2)).congr
      (Eventually.of_forall (fun p => ?_))
    change ((1 + |c|) ^ 2 * C ^ 2) * (1 / (1 + ‖p‖) ^ 4)
      = ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4
    rw [mul_one_div]
  have hDnn : ∀ p : ℝ³, 0 ≤ ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4 := by
    intro p; positivity
  have hfnn : ∀ p r, 0 ≤ f p r := by
    intro p r
    rw [hf]
    exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)
  -- joint measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    change AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
        ‖Work.SmallBoxTBWord.tBamp χ q.1 Ψ i (Submission.BoseGases.kcInsN n i (0, q.2))‖ ^ 2)
      (volume.prod ν)
    refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
    · have hfs : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
        rw [show Submission.BoseGases.fsKinCoeff c
            = fun r : ℝ => (max (r - c) 0) ^ 2 from rfl]
        exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
      exact hfs.comp (continuous_norm.comp continuous_fst)
    · exact ((Work.SmallBoxTBWord.continuous_tBamp_pair hχcd.continuous hχcs hΨcd.continuous i).comp
        (continuous_fst.prodMk ((Submission.BoseGases.kcInsN_cont i).comp
          (continuous_const.prodMk continuous_snd)))).norm.pow 2
  -- the iterated-lintegral bound along the fibres
  have hbm : ∀ᵐ r ∂ν, (∫⁻ p : ℝ³, ENNReal.ofReal ‖f p r‖) ≤
      ENNReal.ofReal (∫ p : ℝ³, ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) := by
    rw [hν, ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    filter_upwards with r hr
    calc (∫⁻ p : ℝ³, ENNReal.ofReal ‖f p r‖)
        = ∫⁻ p : ℝ³, ENNReal.ofReal (f p r) := by
          apply lintegral_congr; intro p; rw [Real.norm_of_nonneg (hfnn p r)]
      _ ≤ ∫⁻ p : ℝ³, ENNReal.ofReal (((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) := by
          apply lintegral_mono; intro p
          exact ENNReal.ofReal_le_ofReal (hpt p r hr)
      _ = ENNReal.ofReal (∫ p : ℝ³, ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) :=
          (ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall hDnn)).symm
  have hg : (∫⁻ r : Submission.BoseGases.X n,
      ENNReal.ofReal (∫ p : ℝ³, ((1 + |c|) ^ 2 * C ^ 2) / (1 + ‖p‖) ^ 4) ∂ν) ≠ ⊤ := by
    rw [hν, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
  have hInt : MeasureTheory.Integrable (Function.uncurry f) (volume.prod ν) :=
    Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite hmeas hg hbm
  -- the Fubini exchange
  have hswap := MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) hInt
  have hL : (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        (∫ r in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2))
      = ∫ p : ℝ³, ∫ r : Submission.BoseGases.X n, f p r ∂ν := by
    apply integral_congr_ae; filter_upwards with p
    rw [hf]
    rw [integral_const_mul]
  have hR : (∫ r in Submission.BoseGases.abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
        ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2)
      = (((2 * Real.pi) ^ 3)⁻¹) * (∫ r : Submission.BoseGases.X n,
          ∫ p : ℝ³, f p r ∂volume ∂ν) := by
    rw [← integral_const_mul]
  refine ⟨?_, ?_⟩
  · exact hInt
  · calc (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        (∫ r in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2))
        = (((2 * Real.pi) ^ 3)⁻¹) *
            (∫ p : ℝ³, ∫ r : Submission.BoseGases.X n, f p r ∂ν) := by rw [hL]
      _ = (((2 * Real.pi) ^ 3)⁻¹) *
            (∫ r : Submission.BoseGases.X n, ∫ p : ℝ³, f p r ∂volume ∂ν) := by rw [hswap]
      _ = ∫ r in Submission.BoseGases.abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
            ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 :=
          hR.symm

end Work.BSKinetic
