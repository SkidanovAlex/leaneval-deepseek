import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.integrable_fsKinCoeff_mul_kinFT_sq
import Submission.Work.BoseBoxFock.FRK.labN_sum_le_tsum_of_growth
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseBoxFock.kinRow_lattice_tauPhi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.tauRow_window_of_valid_W3` — the R-τ leaf from a **well-posed** W3

`Submission/Work/BoseBoxFock/FRK/tauRow_window_of_pieces.lean` states the leaf R-τ *conditionally*
on the analytic crux W3.  In that file the W3 hypothesis is written

```
  (∑' n, …) ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
      σ p * ‖…p‖ ^ 2
    + K * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹ * gapBare ℓ 0 ψ
```

Because the integral notation swallows the rest of the term, Lean reads the whole tail
`σ p * ‖…‖ ^ 2 + K * (…) * …` as the **body of the integral**, i.e. the reserve
`K·‖D⁶σ‖₁·ℓ⁻³·gapBare` — which does not depend on `p` — is placed *inside* an integral over the
infinite measure space `ℝ³`.  Then that integral is the integral of a non-integrable function and
equals `0` (`MeasureTheory.integral_undef`), so the hypothesis degenerates to `∑' ≤ 0` whenever
the reserve is nonzero; it is **unsatisfiable** and the file's theorem is vacuous.

The statement *intended* by the design (`LEAD_DESIGN_formrowkin.md` §3, W3 `windowAlias_le`) has the
reserve **added outside** the integral; the only missing ingredient in the file
`tauRow_window_of_pieces.lean` is a pair of parentheses:

```
  (∑' n, …) ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
                              σ p * ‖…p‖ ^ 2)
      + K * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹ *
          Work.BoseKinLoc.gapBare ℓ 0 ψ
```

This module states R-τ against that **valid** W3 (reserve outside the integral) and proves it.
Nothing else changes: `hW4` and the conclusion are verbatim those of `tauRow_window_of_pieces`.
The proof is the one designed in `LEAD_DESIGN_formrowkin.md`: the `Lab N` sum is dominated by the
full lattice series (child lemma `labN_sum_le_tsum_of_growth`), W3 handles the series, the
continuum piece is identified with `mainWord` through the pointwise
`c²τ(‖p‖/c) ≤ fsKinCoeff c ‖p‖` (with the child lemma `integrable_fsKinCoeff_mul_kinFT_sq` for
integrability), and the reserve row `K·‖D⁶τ̃‖₁·ℓ⁻³·gapBare ≤ 2KK₆·s·ℓ⁻²·gapBare` is the W4 bound.
-/

noncomputable section
open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The pointwise pin of the smoothed symbol -/

/-- `fsKinCoeff c x = (max 0 (x - c))²`. -/
private lemma fsKinCoeff_eq_max (c x : ℝ) :
    Submission.BoseGases.fsKinCoeff c x = (max 0 (x - c)) ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff, max_comm]

/-- The one-variable core: since `τ ≤ (max 0 (·−1))²`, the rescaled smoothed term at threshold
`c > 0` is dominated by the square of the positive part of `x − c`. -/
private lemma sq_mul_tauProf_le {c x : ℝ} (hc : 0 < c) :
    c ^ 2 * Work.BoseBoxFock.tauProf (x / c) ≤ (max 0 (x - c)) ^ 2 := by
  have h := Work.BoseBoxFock.tauProf_spec.2.2.2.1 (x / c)
  have hcm : c * max 0 (x / c - 1) = max 0 (x - c) := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero, mul_sub, mul_one,
      mul_div_cancel₀ x (ne_of_gt hc)]
  calc c ^ 2 * Work.BoseBoxFock.tauProf (x / c)
      ≤ c ^ 2 * (max 0 (x / c - 1)) ^ 2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    _ = (c * max 0 (x / c - 1)) ^ 2 := by rw [mul_pow]
    _ = (max 0 (x - c)) ^ 2 := by rw [hcm]

/-- **Pointwise dominance of the smoothed symbol by the two FS kinks.** -/
private lemma tauSm_le_fsKinCoeff_add {eT s d ℓ : ℝ} (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (k : E3) :
    Work.BoseBoxFock.tauSm eT s d ℓ k ≤
      (1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖k‖ +
        eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖k‖ := by
  have hc1 : 0 < (2 * (s * ℓ))⁻¹ := by positivity
  have hc2 : 0 < (2 * (d * s * ℓ))⁻¹ := by positivity
  have key : Work.BoseBoxFock.tauSm eT s d ℓ k =
      (1 - eT) * ((2 * (s * ℓ))⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * (s * ℓ))⁻¹)
      + eT * ((2 * (d * s * ℓ))⁻¹) ^ 2 *
          Work.BoseBoxFock.tauProf (‖k‖ / (2 * (d * s * ℓ))⁻¹) := by
    simp only [Work.BoseBoxFock.tauSm, show (2 : ℝ) * s * ℓ = 2 * (s * ℓ) by ring,
      show (2 : ℝ) * d * s * ℓ = 2 * (d * s * ℓ) by ring]
  rw [key, fsKinCoeff_eq_max, fsKinCoeff_eq_max]
  have hA := sq_mul_tauProf_le (x := ‖k‖) hc1
  have hB := sq_mul_tauProf_le (x := ‖k‖) hc2
  have h1 : (1 - eT) * ((2 * (s * ℓ))⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * (s * ℓ))⁻¹)
      = (1 - eT) * (((2 * (s * ℓ))⁻¹) ^ 2 *
          Work.BoseBoxFock.tauProf (‖k‖ / (2 * (s * ℓ))⁻¹)) := by ring
  have h2 : eT * ((2 * (d * s * ℓ))⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * (d * s * ℓ))⁻¹)
      = eT * (((2 * (d * s * ℓ))⁻¹) ^ 2 *
          Work.BoseBoxFock.tauProf (‖k‖ / (2 * (d * s * ℓ))⁻¹)) := by ring
  rw [h1, h2]
  have h3 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 1 - eT)
  have h4 := mul_le_mul_of_nonneg_left hB heT0
  linarith

/-- **The continuum comparison**: a symbol `τ` pointwise below the two FS kinks has its
`kinFT`-weighted integral below the two-kink continuum word. -/
private lemma integral_le_two {eT s d ℓ : ℝ} (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ)
    {τ : E3 → ℝ} {g : E3 → ℂ}
    (hτnn : ∀ p, 0 ≤ τ p)
    (hτle : ∀ p, τ p ≤ (1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ +
      eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, τ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ≤ (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : E3, Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
              ‖Submission.BoseGases.kinFT g p‖ ^ 2))
        + eT * (((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : E3, Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
              ‖Submission.BoseGases.kinFT g p‖ ^ 2)) := by
  have hc1 : (0 : ℝ) ≤ (2 * (s * ℓ))⁻¹ := by positivity
  have hc2 : (0 : ℝ) ≤ (2 * (d * s * ℓ))⁻¹ := by positivity
  set IA : ℝ := ∫ p : E3, Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
      ‖Submission.BoseGases.kinFT g p‖ ^ 2 with hIA
  set IB : ℝ := ∫ p : E3, Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
      ‖Submission.BoseGases.kinFT g p‖ ^ 2 with hIB
  have hAint : Integrable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    integrable_fsKinCoeff_mul_kinFT_sq hc1 hg hgc
  have hBint : Integrable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    integrable_fsKinCoeff_mul_kinFT_sq hc2 hg hgc
  have hmaj : Integrable (fun p : E3 =>
      (1 - eT) * (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      + eT * (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :=
    (hAint.const_mul (1 - eT)).add (hBint.const_mul eT)
  have hpt : ∀ p : E3, τ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤
      (1 - eT) * (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      + eT * (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    intro p
    have hG : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right (hτle p) hG
    nlinarith [h]
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := (volume : Measure E3))
    (Filter.Eventually.of_forall (fun p => mul_nonneg (hτnn p) (by positivity)))
    hmaj (Filter.Eventually.of_forall hpt)
  have hsplit : (∫ p : E3, ((1 - eT) * (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      + eT * (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2))) = (1 - eT) * IA + eT * IB := by
    rw [MeasureTheory.integral_add (hAint.const_mul (1 - eT)) (hBint.const_mul eT),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hring : ((2 * Real.pi) ^ 3)⁻¹ * ((1 - eT) * IA + eT * IB)
      = (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ * IA) + eT * (((2 * Real.pi) ^ 3)⁻¹ * IB) := by ring
  have step1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, τ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((1 - eT) * IA + eT * IB) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  rw [hIA, hIB] at hring
  rw [hIA, hIB]
  linarith [step1, hring]

/-- The reserve row: the `W4` bound on `‖D⁶τ̃‖₁` transfers the `(ℓ³)⁻¹`-row to the `s ℓ⁻²`-row. -/
private lemma gap_term_le {K K₆ ℓ s I g : ℝ} (hK : 0 ≤ K) (hK₆ : 0 ≤ K₆) (hℓ : 0 < ℓ)
    (hs : 0 < s) (hI : I ≤ K₆ * (2 * s * ℓ)) (hg : 0 ≤ g) :
    K * I * (ℓ ^ 3)⁻¹ * g ≤ (2 * K * K₆) * s * (ℓ ^ 2)⁻¹ * g := by
  have h1 : K * I * (ℓ ^ 3)⁻¹ ≤ 2 * K * K₆ * s * (ℓ ^ 2)⁻¹ := by
    have h2 : K * I ≤ K * (K₆ * (2 * s * ℓ)) := by
      have := mul_le_mul_of_nonneg_left hI hK
      linarith [this]
    calc K * I * (ℓ ^ 3)⁻¹ ≤ K * (K₆ * (2 * s * ℓ)) * (ℓ ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * K * K₆ * s * (ℓ ^ 2)⁻¹ := by field_simp
  exact mul_le_mul_of_nonneg_right h1 hg

/-! ## 2. R-τ from the valid W3 -/

/-- **The R-τ leaf `tauRow_window` from the well-posed W3** (the reserve added *outside* the
continuum integral — the statement of `LEAD_DESIGN_formrowkin.md` §3, W3 `windowAlias_le`).
Identical to `Work.BoseBoxFock.FRK.tauRow_window_of_pieces` except that the `hW3` hypothesis has
the integral parenthesised, which is the only difference between the intended statement and the
one formalised in that file. -/
theorem tauRow_window_of_valid_W3
    (hW3 : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) σ → (∀ p, 0 ≤ σ p) →
      (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖) →
      ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
          ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
            σ p * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2)
          + K * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 σ p‖) *
              (ℓ ^ 3)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ)
    (hW4 : ∃ K₆ : ℝ, 0 ≤ K₆ ∧ ∀ {eT s d ℓ : ℝ}, 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 → 0 < ℓ →
      ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.tauSm eT s d ℓ) ∧
      (∀ p, 0 ≤ Work.BoseBoxFock.tauSm eT s d ℓ p) ∧
      (∃ A : ℝ, ∀ p, |Work.BoseBoxFock.tauSm eT s d ℓ p| ≤ A * (1 + ‖p‖) ^ 2) ∧
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖iteratedFDeriv ℝ 6 (Work.BoseBoxFock.tauSm eT s d ℓ) p‖) ∧
      (∫ p : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ 6 (Work.BoseBoxFock.tauSm eT s d ℓ) p‖) ≤ K₆ * (2 * s * ℓ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ s d eT : ℝ}, 0 < ℓ → 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 →
      ∀ (N : ℕ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.tauSm eT s d ℓ
          (Work.BoseBoxFock.kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
            (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
        ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
          + K * s * (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  obtain ⟨K, hK0, hW3'⟩ := hW3
  obtain ⟨K₆, hK₆0, hW4'⟩ := hW4
  refine ⟨2 * K * K₆, by positivity, ?_⟩
  intro ℓ s d eT hℓ hs hd hd1 heT0 heT1 N ψ hψ
  obtain ⟨hτcd, hτnn, hτgr, hτint, hτl1⟩ := hW4' hs hd hd1 heT0 heT1 hℓ
  have hrow := hW3' hℓ (Work.BoseBoxFock.tauSm eT s d ℓ) hτcd hτnn hτgr hτint ψ hψ
  -- (1) the finite `Lab N` sum is a sub-sum of the full lattice series
  have hsub := labN_sum_le_tsum_of_growth hℓ hτnn hτgr
    (Work.BoseBoxFock.winState_contDiff hℓ hψ)
    (Work.BoseBoxFock.winState_hasCompactSupport hℓ ψ) N
  -- (2) the continuum piece is dominated by `mainWord`
  have hint : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Work.BoseBoxFock.tauSm eT s d ℓ p *
        ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ) p‖ ^ 2)
      ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
    rw [Work.BoseBoxFock.mainWord_eq_winState]
    exact integral_le_two hs hd hℓ hτnn
      (fun p => tauSm_le_fsKinCoeff_add hs hd hℓ heT0 heT1 p)
      (Work.BoseBoxFock.winState_contDiff hℓ hψ)
      (Work.BoseBoxFock.winState_hasCompactSupport hℓ ψ)
  -- (3) the reserve row
  have hgap : K * (∫ p : E3, ‖iteratedFDeriv ℝ 6 (Work.BoseBoxFock.tauSm eT s d ℓ) p‖) *
        (ℓ ^ 3)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ
      ≤ (2 * K * K₆) * s * (ℓ ^ 2)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ :=
    gap_term_le hK0 hK₆0 hℓ hs hτl1 (gapBare_nonneg ℓ ψ)
  have hL : (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.tauSm eT s d ℓ
          (Work.BoseBoxFock.kmomLab ℓ N k) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
            (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
      = ∑ k : Work.BoseBoxFock.Lab N, (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauSm eT s d ℓ
          (Work.BoseBoxFock.kmomLab ℓ N k) *
          ‖Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ ψ)
            (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hL]
  linarith [hsub, hrow, hint, hgap]

end Work.BoseBoxFock.FRK
