import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseFixB1B.pairRung.integralAddLe
import Submission.Work.BoseFixB1B.pairRung.term1Final
import Submission.Work.BoseFixB1B.pairRung.term1PointwiseBall
import Submission.Work.BoseFixB1B.pairRung.term1PointwiseCompl
import Submission.Work.BoseFixB1B.pairRung.term1SetLinBall
import Submission.Work.BoseFixB1B.pairRung.term1SqDivLeCG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.term1` — the credit (Term 1) of the pairing rung

This is the `S·X·(2π)⁻³∫ℬ²/(2𝒜)` row of the chain
(`FINDING_pairingRungBox_chainRoute.md` §1, step 4(a)), with

* `ℬ(q) = pairW 𝒲(q)/V`,
* `𝒜(q) = [1/(N+1)]·fsKinCoeff c ‖q‖ + 2K_s(a)/V`,

and the "M1/Newtonian" inputs `|pairW 𝒲| ≤ K_s a` and `(2π)⁻³∫pairW 𝒲²/‖q‖² ≤ 2K_s·PM`.

The proof is the standard low/high momentum split at the radius `2c`:

* on `‖q‖ ≤ 2c` the whole integrand is at most `K_s a/(4V)` (the denominator is at least
  `4VK_s a`), contributing `K_s a/(4V)·vol(B_{2c}) = 8πc³K_s a/(3V)`;
* on `‖q‖ ≥ 2c` one has `fsKinCoeff c ‖q‖ ≥ ‖q‖²/4`, so the integrand is at most
  `2(N+1)V⁻²·(pairW 𝒲 q)²/‖q‖²`, contributing `(2(N+1)/V²)·(2π)³·2K_s PM`.

Multiplying by `(2π)⁻³` gives `c³K_s a/(3π²V) + 4(N+1)K_s PM/V²`, and the hypothesis on `δ`
(`8K_s + 2K_s a Kc/(3π²PM) ≤ 1+δ` with `c³V ≤ Kc`) pays for it (pure arithmetic).

The measure-theoretic care is concentrated in two places: the two summands are nonnegative but
not known to be integrable, so the comparison `∫G ≤ ∫F₁ + ∫F₂` goes through the `∫⁻`-route (as in
`pairRung/integralAddLe.lean`), and the (possibly junk) Bochner integral `∫ g²/‖q‖²` is only used
after the honest case `Integrable G` is separated out.

## The pieces (delegated, verified in this directory)

* `term1PointwiseBall`, `term1PointwiseCompl` — the two pointwise bounds of the integrand;
* `term1SqDivLeCG` — the off-ball domination `g²/‖q‖² ≤ C·G` with the explicit constant
  `C = 2V²/(N+1) + K_s a V/c²`, which is what makes the complement part of `∫⁻ g²/‖q‖²` finite;
* `term1InvNormSqBall`, `term1SetLinBall` — `1/‖q‖²` is integrable on a ball of `ℝ³`, hence the
  ball part of `∫⁻ g²/‖q‖²` is finite;
* `term1Final` — the pure arithmetic of the final reduction.

What is proved *here* is the assembly: the pointwise split `G ≤ F₁ + F₂`, the `∫⁻`-comparison
`∫G ≤ ∫F₁ + ∫F₂`, the honest/junk case split on `Integrable G` (in the junk case `∫G = 0`), and
the reduction of the `S·X·∫` row of the target to `term1Final`'s hypothesis `I ≤ c³K_s a/(3π²V) +
4(N+1)K_s PM/V²`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1 Elementary facts about the integrand -/

/-- The denominator `V²·2·([1/(N+1)]·fsKinCoeff c ‖q‖ + 2K_s a/V)` is positive. -/
lemma term1Den_pos {N : ℕ} {Ks a c V : ℝ} (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < a)
    (q : E3) :
    0 < V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
      + 2 * Ks * a / V) := by
  have h1 : 0 ≤ 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
    mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
  have h2 : 0 < 2 * Ks * a / V := by positivity
  exact mul_pos (by positivity) (by linarith)

/-- `q ∉ ball 0 (2c)` implies `‖q‖ ≥ 2c` (for `c > 0` this is the far region). -/
lemma two_mul_c_le_norm_of_not_mem_ball {c : ℝ} {q : E3}
    (hq : q ∉ Metric.ball (0 : E3) (2 * c)) : 2 * c ≤ ‖q‖ := by
  have h : ¬ (dist q 0 < 2 * c) := fun hlt => hq (Metric.mem_ball.mpr hlt)
  rw [dist_eq_norm, sub_zero] at h
  linarith

/-! ## 2 The integral bound -/

/-- **The integral core of `term1`.**  With `|g| ≤ K_s a` and `(2π)⁻³∫g²/‖q‖² ≤ 2K_s PM`, the
`𝒜`-normalised spectral integral is at most `c³K_s a/(3π²V) + 4(N+1)K_s PM/V²`. -/
theorem term1IntegralBound {N : ℕ} {Ks a c V PM : ℝ} {g : E3 → ℝ}
    (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks) (ha : 0 < a)
    (hsup : ∀ q, |g q| ≤ Ks * a)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) ≤ 2 * Ks * PM) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
        Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)))
      ≤ c ^ 3 * Ks * a / (3 * Real.pi ^ 2 * V) + 4 * ((N : ℝ) + 1) * Ks * PM / V ^ 2 := by
  have hKsa : 0 < Ks * a := mul_pos hKs ha
  have hPM0 : 0 ≤ PM := by
    have h0 : 0 ≤ ∫ q : E3, g q ^ 2 / ‖q‖ ^ 2 :=
      integral_nonneg (fun q => div_nonneg (sq_nonneg _) (sq_nonneg _))
    have h1 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have h2 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) := mul_nonneg h1 h0
    have h3 : 0 ≤ 2 * Ks * PM := le_trans h2 hM1
    nlinarith [h3, hKs]
  set G : E3 → ℝ := fun q => g q ^ 2 / (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
      Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)) with hGdef
  have hGnn : ∀ q, 0 ≤ G q := by
    intro q
    rw [hGdef]
    exact div_nonneg (sq_nonneg _) (le_of_lt (term1Den_pos hV hKs ha q))
  set B : Set E3 := Metric.ball (0 : E3) (2 * c) with hBdef
  have hBmeas : MeasurableSet B := by rw [hBdef]; exact measurableSet_ball
  have hBcmeas : MeasurableSet Bᶜ := hBmeas.compl
  set F1 : E3 → ℝ := B.indicator (fun _ => Ks * a / (4 * V)) with hF1def
  set F2 : E3 → ℝ := Bᶜ.indicator (fun q => 2 * ((N : ℝ) + 1) / V ^ 2 * (g q ^ 2 / ‖q‖ ^ 2))
    with hF2def
  have hF1meas : Measurable F1 := by
    rw [hF1def]; exact Measurable.indicator measurable_const hBmeas
  have hF1nn : ∀ q, 0 ≤ F1 q := by
    intro q
    rw [hF1def]
    by_cases hq : q ∈ B
    · rw [Set.indicator_of_mem hq]; positivity
    · rw [Set.indicator_of_notMem hq]
  have hF2nn : ∀ q, 0 ≤ F2 q := by
    intro q
    rw [hF2def]
    by_cases hq : q ∈ Bᶜ
    · rw [Set.indicator_of_mem hq]; positivity
    · rw [Set.indicator_of_notMem hq]
  have hpt : ∀ q, G q ≤ F1 q + F2 q := by
    intro q
    by_cases hq : q ∈ B
    · have h1 : G q ≤ Ks * a / (4 * V) := by
        have hq' : q ∈ Metric.ball (0 : E3) (2 * c) := by rw [← hBdef]; exact hq
        rw [hGdef]
        exact term1PointwiseBall (N := N) hV hKs ha g hsup hq'
      have h2 : F1 q = Ks * a / (4 * V) := by rw [hF1def, Set.indicator_of_mem hq]
      have h3 : F2 q = 0 := by
        rw [hF2def, Set.indicator_of_notMem (by simpa using hq)]
      linarith
    · have hq' : q ∉ Metric.ball (0 : E3) (2 * c) := by rw [← hBdef]; exact hq
      have h1 : G q ≤ 2 * ((N : ℝ) + 1) / V ^ 2 * (g q ^ 2 / ‖q‖ ^ 2) := by
        rw [hGdef]
        exact term1PointwiseCompl (N := N) hV hc hKs ha g hq'
      have h2 : F1 q = 0 := by rw [hF1def, Set.indicator_of_notMem hq]
      have h3 : F2 q = 2 * ((N : ℝ) + 1) / V ^ 2 * (g q ^ 2 / ‖q‖ ^ 2) := by
        rw [hF2def, Set.indicator_of_mem (by simpa using hq)]
      linarith
  have hvolBlt : (volume : Measure E3) B < ⊤ := by
    rw [hBdef]; exact MeasureTheory.measure_ball_lt_top
  -- the two partial integrals, explicitly
  have hF1lin : (∫⁻ q, ENNReal.ofReal (F1 q))
      = ENNReal.ofReal (Ks * a / (4 * V)) * (volume B) := by
    rw [hF1def]
    have heq : (fun q : E3 => ENNReal.ofReal (B.indicator (fun _ => Ks * a / (4 * V)) q))
        = B.indicator (fun _ => ENNReal.ofReal (Ks * a / (4 * V))) := by
      funext q
      by_cases hq : q ∈ B
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]; simp
    rw [heq, lintegral_indicator hBmeas, setLIntegral_const]
  have hF1lt : (∫⁻ q, ENNReal.ofReal (F1 q)) < ⊤ := by
    rw [hF1lin]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvolBlt
  have hF1toReal : (∫⁻ q, ENNReal.ofReal (F1 q)).toReal
      = Ks * a / (4 * V) * ((2 * c) ^ 3 * (Real.pi * 4 / 3)) := by
    rw [hF1lin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hBdef,
      EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by positivity)]
  have hF2lin : (∫⁻ q, ENNReal.ofReal (F2 q))
      = ENNReal.ofReal (2 * ((N : ℝ) + 1) / V ^ 2) *
          (∫⁻ q in Bᶜ, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) := by
    rw [hF2def]
    have heq : (fun q : E3 => ENNReal.ofReal (Bᶜ.indicator (fun q =>
          2 * ((N : ℝ) + 1) / V ^ 2 * (g q ^ 2 / ‖q‖ ^ 2)) q))
        = Bᶜ.indicator (fun q => ENNReal.ofReal (2 * ((N : ℝ) + 1) / V ^ 2) *
            ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) := by
      funext q
      by_cases hq : q ∈ Bᶜ
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.ofReal_mul (by positivity)]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]; simp
    rw [heq, lintegral_indicator hBcmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the ball part of `∫⁻ g²/‖q‖²` is finite
  have hball_lt : (∫⁻ q in B, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) < ⊤ := by
    have h := term1SetLinBall (g := g) (C := Ks * a) (R := 2 * c)
      (le_of_lt hKsa) hsup
    rwa [hBdef]
  by_cases hGint : Integrable G volume
  · -- ## the honest case: everything is an honest integral
    have hGmeas : AEStronglyMeasurable G volume := hGint.1
    have hGlt : (∫⁻ q, ENNReal.ofReal (G q)) < ⊤ := hGint.lintegral_lt_top
    -- measurability of `g²/‖q‖²` (only needed here, where `G` is measurable)
    have hDmeas : AEStronglyMeasurable (fun q : E3 => V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
        Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)) volume := by
      have heq : (fun q : E3 => V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
          Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V))
          = fun q : E3 => V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * (max (‖q‖ - c) 0) ^ 2
              + 2 * Ks * a / V) := by
        funext q
        rw [Submission.BoseGases.fsKinCoeff]
      rw [heq]
      fun_prop
    have hg2meas : AEStronglyMeasurable (fun q : E3 => g q ^ 2) volume := by
      have heq : (fun q : E3 => g q ^ 2) = fun q : E3 => G q * (V ^ 2 * 2 *
          (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)) := by
        funext q
        rw [hGdef, div_mul_cancel₀ _ (ne_of_gt (term1Den_pos hV hKs ha q))]
      rw [heq]
      exact hGmeas.mul hDmeas
    have hinvmeas : AEStronglyMeasurable (fun q : E3 => (‖q‖ ^ 2)⁻¹) volume := by fun_prop
    have hhmeas : AEStronglyMeasurable (fun q : E3 => g q ^ 2 / ‖q‖ ^ 2) volume := by
      have hcon : (fun q : E3 => g q ^ 2 / ‖q‖ ^ 2) = fun q : E3 => g q ^ 2 * (‖q‖ ^ 2)⁻¹ := rfl
      rw [hcon]
      exact hg2meas.mul hinvmeas
    have hhInt : (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) ≤ (2 * Real.pi) ^ 3 * (2 * Ks * PM) := by
      have hπ : 0 < (2 * Real.pi) ^ 3 := by positivity
      have h := hM1
      rw [inv_mul_le_iff₀ hπ] at h
      exact h
    -- the complement part of `∫⁻ g²/‖q‖²` is finite: `g²/‖q‖² ≲ G` off the ball
    have hc0lt : (∫⁻ q in Bᶜ, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) < ⊤ := by
      have hstep1 : (∫⁻ q in Bᶜ, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2))
          ≤ ∫⁻ q in Bᶜ, ENNReal.ofReal ((2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2)
              * G q) := by
        refine setLIntegral_mono' hBcmeas ?_
        intro q hq
        have hq' : q ∉ Metric.ball (0 : E3) (2 * c) := by
          rw [hBdef] at hq
          exact hq
        have h1 : g q ^ 2 / ‖q‖ ^ 2 ≤ (2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2) * G q := by
          rw [hGdef]
          exact term1SqDivLeCG (N := N) hV hc hKs ha g hq'
        exact ENNReal.ofReal_le_ofReal h1
      have hstep2 : (∫⁻ q in Bᶜ, ENNReal.ofReal ((2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2)
              * G q))
          = ENNReal.ofReal (2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2) *
              (∫⁻ q in Bᶜ, ENNReal.ofReal (G q)) := by
        have heq : (fun q : E3 => ENNReal.ofReal ((2 * V ^ 2 / ((N : ℝ) + 1)
            + Ks * a * V / c ^ 2) * G q))
            = fun q : E3 => ENNReal.ofReal (2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2) *
                ENNReal.ofReal (G q) := by
          funext q; exact ENNReal.ofReal_mul (by positivity)
        rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lt_of_le_of_lt (le_trans hstep1 (le_of_eq hstep2)) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hGlt)
    have hF2lt : (∫⁻ q, ENNReal.ofReal (F2 q)) < ⊤ := by
      rw [hF2lin]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc0lt
    have hF2toReal : (∫⁻ q, ENNReal.ofReal (F2 q)).toReal
        ≤ 2 * ((N : ℝ) + 1) / V ^ 2 * ((2 * Real.pi) ^ 3 * (2 * Ks * PM)) := by
      rw [hF2lin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsplit : (∫⁻ q in B, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2))
          + (∫⁻ q in Bᶜ, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2))
          = (∫⁻ q, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) :=
        lintegral_add_compl (fun q : E3 => ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) hBmeas
      have htot_lt : (∫⁻ q, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) < ⊤ := by
        rw [← hsplit]
        exact ENNReal.add_lt_top.mpr ⟨hball_lt, hc0lt⟩
      calc (∫⁻ q in Bᶜ, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)).toReal
          ≤ (∫⁻ q, ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)).toReal := by
            refine ENNReal.toReal_mono htot_lt.ne ?_
            rw [← hsplit]
            exact le_add_left le_rfl
        _ = (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) := by
            rw [integral_eq_lintegral_of_nonneg_ae
              (Filter.Eventually.of_forall fun q => div_nonneg (sq_nonneg _) (sq_nonneg _)) hhmeas]
        _ ≤ (2 * Real.pi) ^ 3 * (2 * Ks * PM) := hhInt
    -- the `∫⁻` comparison
    have h1 : (∫⁻ q, ENNReal.ofReal (G q))
        ≤ (∫⁻ q, ENNReal.ofReal (F1 q)) + (∫⁻ q, ENNReal.ofReal (F2 q)) := by
      refine le_trans (lintegral_mono (fun q => ENNReal.ofReal_le_ofReal (hpt q))) ?_
      rw [show (fun q : E3 => ENNReal.ofReal (F1 q + F2 q))
          = fun q : E3 => ENNReal.ofReal (F1 q) + ENNReal.ofReal (F2 q) from
            funext fun q => ENNReal.ofReal_add (hF1nn q) (hF2nn q)]
      exact le_of_eq (lintegral_add_left' (ENNReal.measurable_ofReal.comp hF1meas).aemeasurable _)
    have h2 : (∫⁻ q, ENNReal.ofReal (G q)).toReal
        ≤ Ks * a / (4 * V) * ((2 * c) ^ 3 * (Real.pi * 4 / 3))
          + 2 * ((N : ℝ) + 1) / V ^ 2 * ((2 * Real.pi) ^ 3 * (2 * Ks * PM)) := by
      calc (∫⁻ q, ENNReal.ofReal (G q)).toReal
          ≤ ((∫⁻ q, ENNReal.ofReal (F1 q)) + (∫⁻ q, ENNReal.ofReal (F2 q))).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hF1lt.ne, hF2lt.ne⟩) h1
        _ = (∫⁻ q, ENNReal.ofReal (F1 q)).toReal + (∫⁻ q, ENNReal.ofReal (F2 q)).toReal :=
            ENNReal.toReal_add hF1lt.ne hF2lt.ne
        _ ≤ Ks * a / (4 * V) * ((2 * c) ^ 3 * (Real.pi * 4 / 3))
              + 2 * ((N : ℝ) + 1) / V ^ 2 * ((2 * Real.pi) ^ 3 * (2 * Ks * PM)) :=
            add_le_add (le_of_eq hF1toReal) hF2toReal
    have h3 : (∫ q : E3, G q)
        ≤ Ks * a / (4 * V) * ((2 * c) ^ 3 * (Real.pi * 4 / 3))
          + 2 * ((N : ℝ) + 1) / V ^ 2 * ((2 * Real.pi) ^ 3 * (2 * Ks * PM)) := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hGnn) hGmeas]
      exact h2
    have hπ3 : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left h3 (le_of_lt (inv_pos.mpr hπ3))
    have hsimp : ((2 * Real.pi) ^ 3)⁻¹ * (Ks * a / (4 * V) * ((2 * c) ^ 3 * (Real.pi * 4 / 3))
          + 2 * ((N : ℝ) + 1) / V ^ 2 * ((2 * Real.pi) ^ 3 * (2 * Ks * PM)))
        = c ^ 3 * Ks * a / (3 * Real.pi ^ 2 * V) + 4 * ((N : ℝ) + 1) * Ks * PM / V ^ 2 := by
      have hπ0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hV0 : V ≠ 0 := ne_of_gt hV
      field_simp
      ring
    rw [hsimp] at hmul
    exact hmul
  · -- ## the junk case: `∫ G = 0`
    rw [integral_undef hGint, mul_zero]
    have hb : 0 ≤ c ^ 3 * Ks * a / (3 * Real.pi ^ 2 * V)
        + 4 * ((N : ℝ) + 1) * Ks * PM / V ^ 2 := by positivity
    linarith

/-! ## 3 The target (assembled with `term1Final`) -/

theorem term1 {N : ℕ} {Ks a PM X S c V Kc δ : ℝ}
    {𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks) (ha : 0 < a) (hPM : 0 < PM) (hX : 0 ≤ X)
    (hS : S ≤ (N : ℝ)) (hS0 : 0 ≤ S) (hc3 : c ^ 3 * V ≤ Kc) (hKc : 0 ≤ Kc)
    (hsup : ∀ q : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.pairW 𝒲 q| ≤ Ks * a)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2 ≤ 2 * Ks * PM)
    (hδ : 8 * Ks + 2 * Ks * a * Kc / (3 * Real.pi ^ 2 * PM) ≤ 1 + δ) :
    S * X * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
          Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)))
      ≤ (1 / 2) * (1 + δ) * PM * (((N : ℝ) + 1) * (N : ℝ) / V ^ 2) * X := by
  have hI : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.pairW 𝒲 q ^ 2 /
      (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)))
      ≤ c ^ 3 * Ks * a / (3 * Real.pi ^ 2 * V) + 4 * ((N : ℝ) + 1) * Ks * PM / V ^ 2 :=
    term1IntegralBound (g := fun q => Submission.BoseGases.pairW 𝒲 q) hV hc hKs ha hsup hM1
  have hI0 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.pairW 𝒲 q ^ 2 /
      (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * a / V))) := by
    have h1 : 0 < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have h2 : 0 ≤ (∫ q : E3, Submission.BoseGases.pairW 𝒲 q ^ 2 /
        (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * a / V))) :=
      integral_nonneg (fun q => div_nonneg (sq_nonneg _) (le_of_lt (term1Den_pos hV hKs ha q)))
    exact mul_nonneg h1.le h2
  exact term1Final hV hc hKs ha hPM hX hI0 hS hS0 hc3 hKc hδ hI

end Work.BoseFixB1B.pairRung
