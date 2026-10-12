import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.swap_p_abox_tBamp` — the `p ↔ abox` Fubini exchange

The one-body kinetic content of the big-box word `tBwordKinBigU` is written as a `p`-integral of
the windowed amplitude `tBamp (chiBig ℓ u) p (Q_{Λ(u)}Φ) i` evaluated on the slice
`kcInsN n i (0, r)`; taking the `r`-average over the configuration box `abox n ℓ` (which is what
the fibre form `bsOneBody` does) requires exchanging the `p`-integral with that `r`-integral.

The statement is a Fubini exchange of a *nonnegative* integrand, so the only real content is
joint integrability, and that is supplied by the uniform Fourier decay of the windowed amplitude
(`tBamp_decay`): the state `Ψ = boxQ (ℓ³) (bigBox ℓ u) i Φ` is smooth (the big box is compact,
so `boxQ_contDiff_of_compact` applies) and the decay is uniform on the box `abox (n+1) ℓ`, which
contains every slice `kcInsN n i (0, r)` with `r ∈ abox n ℓ`.  Hence the `(p,r)`-integrand is
dominated by `(1+|c|)²C²·(1+‖p‖)⁻⁴` — integrable in dimension three — and the standard
iterated-lintegral criterion (`integrable_uncurry_of_lintegral_le_sfinite`) yields joint
integrability.  The exchange itself is then `integral_integral_swap`, and the remaining steps are
the (unconditional) linearity of the integral in the constant prefactors.
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

namespace SwapTBAmp

/-- **The moving big box `Λ(u) = ℓu + acube ℓ` is compact.**  It is the image of the compact
centred cube `acube ℓ` under the translation `w ↦ w + ℓ•u`. -/
lemma isCompact_bigBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    IsCompact (Work.UBBInputs9.bigBox ℓ u) := by
  have h : Work.UBBInputs9.bigBox ℓ u
      = (fun w : ℝ³ => w + ℓ • u) '' Submission.BoseGases.acube ℓ := by
    ext x
    constructor
    · intro hx
      exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨w, hw, rfl⟩
      show w + ℓ • u - ℓ • u ∈ Submission.BoseGases.acube ℓ
      simpa using hw
  rw [h]
  exact (Submission.BoseGases.acube_compact hℓ).image (continuous_id.add continuous_const)

/-- The big-box window `chiBig ℓ u = chiScale ℓ (· − ℓ•u)` is a translate of the scaled bump,
hence compactly supported. -/
lemma hasCompactSupport_chiBig {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    HasCompactSupport (Work.UBBInputs9.chiBig ℓ u) := by
  have h : Work.UBBInputs9.chiBig ℓ u
      = Submission.BoseGases.chiScale ℓ ∘ ⇑(Homeomorph.subRight (ℓ • u)) := rfl
  rw [h]
  exact (Submission.BoseGases.chiScale_hasCompactSupport hℓ).comp_homeomorph _

/-- The big-box window is smooth. -/
lemma contDiff_chiBig {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    ContDiff ℝ (⊤ : ENat) (Work.UBBInputs9.chiBig ℓ u) := by
  have h : Work.UBBInputs9.chiBig ℓ u
      = fun x : ℝ³ => Submission.BoseGases.chiScale ℓ (x - ℓ • u) := rfl
  rw [h]
  exact (Submission.BoseGases.chiScale_contDiff hℓ).comp (contDiff_id.sub contDiff_const)

/-- **The symbol `fsKinCoeff c` grows at most quadratically**: `[t−c]₊² ≤ (1+|c|)²(1+t)²` for
`t ≥ 0`. -/
lemma fsKinCoeff_le {c t : ℝ} (ht : 0 ≤ t) :
    Submission.BoseGases.fsKinCoeff c t ≤ (1 + |c|) ^ 2 * (1 + t) ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have h1 : max (t - c) 0 ≤ (1 + |c|) * (1 + t) := by
    apply max_le
    · have hlt : t - c ≤ t + |c| := by linarith [neg_le_abs c]
      have h2 : t + |c| ≤ (1 + |c|) * (1 + t) := by nlinarith [abs_nonneg c, ht]
      linarith
    · positivity
  simpa [mul_pow] using pow_le_pow_left₀ (le_max_right (t - c) 0) h1 2

/-- The elementary algebra collapsing the decay bound: for `t ≥ 0`,
`(1+|c|)²(1+t)²·(C/(1+t)³)² = (1+|c|)²C²/(1+t)⁴`. -/
lemma fsKinCoeff_algebra (c C t : ℝ) (ht : 0 ≤ t) :
    ((1 + |c|) ^ 2 * (1 + t) ^ 2) * (C / (1 + t) ^ 3) ^ 2
      = ((1 + |c|) ^ 2 * C ^ 2) / (1 + t) ^ 4 := by
  have ht1 : (0 : ℝ) < 1 + t := by linarith
  rw [div_pow, div_eq_mul_inv, div_eq_mul_inv, ← pow_mul]
  field_simp
  ring

/-- `p ↦ 1/(1+‖p‖)⁴` is integrable on `ℝ³` (the model decay of the `(1+‖p‖)⁻³` amplitude). -/
lemma integrable_one_div_pow4 :
    MeasureTheory.Integrable (fun p : ℝ³ => 1 / (1 + ‖p‖) ^ 4) := by
  have hbase : MeasureTheory.Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4 : ℝ))) := by
    have h := integrable_one_add_norm (μ := volume) (E := ℝ³) (r := (4 : ℝ)) ?_
    · simpa using h
    · have : (Module.finrank ℝ ℝ³ : ℝ) = 3 := by
        rw [finrank_euclideanSpace_fin]; norm_num
      rw [this]; norm_num
  refine hbase.congr (Eventually.of_forall (fun p => ?_))
  change (1 + ‖p‖) ^ (-(4 : ℝ)) = 1 / (1 + ‖p‖) ^ 4
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  norm_num

end SwapTBAmp

theorem swap_p_abox_tBamp {n : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
          (∫ r in Submission.BoseGases.abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
              (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2))
      = ∫ r in Submission.BoseGases.abox n ℓ, (((2 * Real.pi) ^ 3)⁻¹) *
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
              (Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ) i
              (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 := by
  classical
  set χ : ℝ³ → ℝ := Work.UBBInputs9.chiBig ℓ u with hχ
  set Ψ : Submission.BoseGases.X (n + 1) → ℝ :=
    Work.SmallBoxTBWord.boxQ (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) i Φ with hΨ
  set ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ) with hν
  set f : ℝ³ → Submission.BoseGases.X n → ℝ := fun p r =>
    Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖ ^ 2 with hf
  -- smoothness and compact support of the window, smoothness of the projected state
  have hχcd : ContDiff ℝ (⊤ : ENat) χ := SwapTBAmp.contDiff_chiBig (ne_of_gt hℓ) u
  have hχcs : HasCompactSupport χ := SwapTBAmp.hasCompactSupport_chiBig (ne_of_gt hℓ) u
  have hΨcd : ContDiff ℝ (⊤ : ENat) Ψ :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact (SwapTBAmp.isCompact_bigBox hℓ u) (ℓ ^ 3) i hΦ
  obtain ⟨C, _hC0, hC⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n + 1) hℓ hχcd hχcs hΨcd
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
  calc (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
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
