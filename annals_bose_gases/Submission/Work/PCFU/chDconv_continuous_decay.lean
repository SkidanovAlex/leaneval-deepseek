import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
import Submission.Work.BoseBoxFock.chiLam_conv_flat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.chDconv_continuous_decay`

The `(D)`-channel kernel `KχfrU` is the periodisation `Σ'_d (χ_ℓ ⋆ ψ)(z + ℓ•d)` of the
`χ_ℓ`-convolution of the smoothed weight `ψ = uvSmear fu Λ (W1fun v h ℓ)`
(`ChDKernelDefs.lean`).  The Poisson/aliasing analysis of that channel only needs the
elementary regularity of the single term: it must be **continuous** and **rapidly decreasing**.

That is the content of this module, and it is an instance of the general principle

> the convolution of a compactly supported continuous function with a rapidly decreasing
> continuous function is again continuous and rapidly decreasing.

Here the compactly supported factor is the box localisation function
`χ_ℓ = chiLam ℓ` (support in the ball of radius `ℓ/2`, `norm_lt_half_of_chiLam_ne_zero`),
and the rapidly decreasing factor is `ψ = uvSmear fu Λ (W1fun v h ℓ)`, whose continuity and
rapid decay are supplied by `Work.BoseBoxFock.uvSmear_continuous_decay` from the two
hypotheses of the statement (`Integrable W1fun`, `HasCompactSupport W1fun`).

## Route

* `zpow_one_add_norm_sub_le` — the elementary real inequality converting the decay factor
  centred at `y - w` into one centred at `y`, for `‖w‖ ≤ ℓ`
  (`1 + ‖y‖ ≤ (1+ℓ)(1+‖y-w‖)`, monotonicity of `x ↦ x^n`, then inversion);
* `chiLam_conv_continuous_rapidDecay` — the general statement, proved exactly in the pattern
  of `uvSmear_continuous`/`uvSmear_rapidDecay` of
  `Submission/Work/BoseBoxFock/uvSmear_continuous_decay.lean`, with the roles of the two
  factors exchanged:
  - continuity by `continuous_of_dominated`, with the *`y`-independent* dominating function
    `M·χ_ℓ` (`M` the sup-bound on `ψ` coming from the `n = 0` decay), which is integrable
    because `χ_ℓ` is continuous with compact support;
  - decay by `integral_mono_of_nonneg` against the single integrable majorant
    `K(y)·χ_ℓ`, `K(y) := Cψ (1+ℓ)^n (1+‖y‖)^{-n}`, the pointwise comparison being the
    support bound `‖w‖ < ℓ/2` together with `zpow_one_add_norm_sub_le`.
-/

noncomputable section

open MeasureTheory

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The translation of the decay factor -/

/-- **Shifting the decay factor.**  If `‖w‖ ≤ ℓ` then the rapid-decay factor centred at `y - w`
is bounded by the one centred at `y`, at the cost of the fixed factor `(1 + ℓ) ^ n`. -/
lemma zpow_one_add_norm_sub_le {ℓ : ℝ} {n : ℕ} {y w : E3} (hw : ‖w‖ ≤ ℓ) :
    (1 + ‖y - w‖) ^ (-(n : ℤ)) ≤ (1 + ℓ) ^ n * (1 + ‖y‖) ^ (-(n : ℤ)) := by
  have hℓ0 : 0 ≤ ℓ := (norm_nonneg w).trans hw
  -- `1 + ‖y‖ ≤ (1 + ℓ) * (1 + ‖y - w‖)`
  have h1 : 1 + ‖y‖ ≤ (1 + ℓ) * (1 + ‖y - w‖) := by
    have h2 : ‖y‖ ≤ ‖y - w‖ + ‖w‖ := by
      have h := norm_add_le (y - w) w
      rwa [sub_add_cancel] at h
    nlinarith [hw, h2, norm_nonneg (y - w)]
  -- raise to the `n`-th power
  have h2 : (1 + ‖y‖) ^ n ≤ (1 + ℓ) ^ n * (1 + ‖y - w‖) ^ n := by
    calc (1 + ‖y‖) ^ n ≤ ((1 + ℓ) * (1 + ‖y - w‖)) ^ n :=
          pow_le_pow_left₀ (by positivity) h1 n
      _ = (1 + ℓ) ^ n * (1 + ‖y - w‖) ^ n := by rw [mul_pow]
  -- invert
  have hv : 0 < (1 + ‖y - w‖) ^ n := pow_pos (by positivity) n
  have hu : 0 < (1 + ‖y‖) ^ n := pow_pos (by positivity) n
  have h3 : ((1 + ‖y - w‖) ^ n)⁻¹ ≤ (1 + ℓ) ^ n * ((1 + ‖y‖) ^ n)⁻¹ := by
    rw [← div_eq_mul_inv]
    rw [show ((1 + ‖y - w‖) ^ n)⁻¹ = 1 / (1 + ‖y - w‖) ^ n from (one_div _).symm]
    rw [div_le_div_iff₀ hv hu]
    simpa using h2
  simpa only [zpow_neg, zpow_natCast] using h3

/-! ## 2. The convolution of `χ_ℓ` with a continuous rapidly decreasing function -/

/-- **The `χ_ℓ`-convolution of a continuous rapidly decreasing function is continuous and
rapidly decreasing.** -/
lemma chiLam_conv_continuous_rapidDecay {ℓ : ℝ} (hℓ : 0 < ℓ) {s : E3 → ℝ}
    (hsc : Continuous s)
    (hsd : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, |s x| ≤ C * (1 + ‖x‖) ^ (-(n : ℤ))) :
    Continuous (fun y : E3 => ∫ w : E3,
        Work.BoseK15.corpusBox.chiLam ℓ w * s (y - w))
      ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3,
          |∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * s (y - w)|
            ≤ C * (1 + ‖y‖) ^ (-(n : ℤ)) := by
  have hchi_cont : Continuous (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w) :=
    Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ
  have hchi_nn : ∀ w : E3, 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ w :=
    fun w => Work.BoseB4.BoxData.chiLam_nonneg Work.BoseK15.corpusBox ℓ w
  have hchi_cs : HasCompactSupport (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).of_isClosed_subset
      (isClosed_tsupport _)
      (Work.BoseB4.BoxData.tsupport_chiLam_subset Work.BoseK15.corpusBox hℓ)
  have hchi_int : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w) :=
    hchi_cont.integrable_of_hasCompactSupport hchi_cs
  refine ⟨?_, ?_⟩
  · -- continuity: dominated convergence with the `y`-independent majorant `M * χ_ℓ`
    obtain ⟨M, hMnn, hM⟩ := hsd 0
    have hM' : ∀ x : E3, |s x| ≤ M := by
      intro x
      simpa using hM x
    refine continuous_of_dominated
      (F := fun y w => Work.BoseK15.corpusBox.chiLam ℓ w * s (y - w))
      (bound := fun w => M * Work.BoseK15.corpusBox.chiLam ℓ w) ?_ ?_ ?_ ?_
    · intro y
      exact ((hchi_cont.mul (hsc.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
    · intro y
      filter_upwards with w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hchi_nn w)]
      have hle := mul_le_mul_of_nonneg_left (hM' (y - w)) (hchi_nn w)
      calc Work.BoseK15.corpusBox.chiLam ℓ w * |s (y - w)|
          ≤ Work.BoseK15.corpusBox.chiLam ℓ w * M := hle
        _ = M * Work.BoseK15.corpusBox.chiLam ℓ w := by ring
    · exact hchi_int.const_mul M
    · filter_upwards with w
      exact continuous_const.mul (hsc.comp (continuous_id.sub continuous_const))
  · -- decay
    intro n
    obtain ⟨Cs, hCsnn, hCs⟩ := hsd n
    have hInt0 : 0 ≤ ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w := integral_nonneg hchi_nn
    refine ⟨(∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w) * Cs * (1 + ℓ) ^ n,
      mul_nonneg (mul_nonneg hInt0 hCsnn) (pow_nonneg (by linarith) n), ?_⟩
    intro y
    set K : ℝ := Cs * (1 + ℓ) ^ n * (1 + ‖y‖) ^ (-(n : ℤ)) with hK
    -- step 1: pull the absolute value inside
    have step1 : |∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * s (y - w)|
        ≤ ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * |s (y - w)| := by
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with w
      rw [abs_mul, abs_of_nonneg (hchi_nn w)]
    -- step 2: the majorant `K * χ_ℓ` is integrable and dominates the integrand
    have step2 : (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * |s (y - w)|)
        ≤ K * ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w := by
      have hKint : (∫ w : E3, K * Work.BoseK15.corpusBox.chiLam ℓ w)
          = K * ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w :=
        integral_const_mul K _
      rw [← hKint]
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun w => mul_nonneg (hchi_nn w) (abs_nonneg _))
        (hchi_int.const_mul K) (Filter.Eventually.of_forall fun w => ?_)
      change Work.BoseK15.corpusBox.chiLam ℓ w * |s (y - w)|
          ≤ K * Work.BoseK15.corpusBox.chiLam ℓ w
      by_cases hw : Work.BoseK15.corpusBox.chiLam ℓ w = 0
      · rw [hw]; simp
      · have hwn : ‖w‖ < ℓ / 2 := Work.BoseBoxFock.norm_lt_half_of_chiLam_ne_zero hℓ hw
        have hwle : ‖w‖ ≤ ℓ := by linarith
        have hshift := zpow_one_add_norm_sub_le (ℓ := ℓ) (n := n) (y := y) (w := w) hwle
        have hcs' : Cs * (1 + ‖y - w‖) ^ (-(n : ℤ))
            ≤ Cs * (1 + ℓ) ^ n * (1 + ‖y‖) ^ (-(n : ℤ)) := by
          have := mul_le_mul_of_nonneg_left hshift hCsnn
          simpa only [mul_assoc] using this
        calc Work.BoseK15.corpusBox.chiLam ℓ w * |s (y - w)|
            ≤ Work.BoseK15.corpusBox.chiLam ℓ w * (Cs * (1 + ‖y - w‖) ^ (-(n : ℤ))) :=
              mul_le_mul_of_nonneg_left (hCs (y - w)) (hchi_nn w)
          _ ≤ Work.BoseK15.corpusBox.chiLam ℓ w
                * (Cs * (1 + ℓ) ^ n * (1 + ‖y‖) ^ (-(n : ℤ))) :=
              mul_le_mul_of_nonneg_left hcs' (hchi_nn w)
          _ = K * Work.BoseK15.corpusBox.chiLam ℓ w := by rw [hK]; ring
    calc |∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * s (y - w)|
        ≤ ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * |s (y - w)| := step1
      _ ≤ K * ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w := step2
      _ = (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w) * Cs * (1 + ℓ) ^ n
            * (1 + ‖y‖) ^ (-(n : ℤ)) := by rw [hK]; ring

/-! ## 3. The target -/

theorem chDconv_continuous_decay {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ)) :
    Continuous (fun y : EuclideanSpace ℝ (Fin 3) => ∫ w : EuclideanSpace ℝ (Fin 3),
        Work.BoseK15.corpusBox.chiLam ℓ w
          * Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (y - w))
      ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclideanSpace ℝ (Fin 3),
          |∫ w : EuclideanSpace ℝ (Fin 3),
              Work.BoseK15.corpusBox.chiLam ℓ w
                * Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (y - w)|
            ≤ C * (1 + ‖y‖) ^ (-(n : ℤ)) := by
  obtain ⟨hc, hd⟩ := Work.BoseBoxFock.uvSmear_continuous_decay fu hΛ hI hcs
  exact chiLam_conv_continuous_rapidDecay hℓ hc hd

end Work.PCFU
