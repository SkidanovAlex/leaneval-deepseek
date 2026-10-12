import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBox.q3kinDiagCore` — the junk-robust core of the kinetic bridge

This module contains the MEASURE-THEORETIC CORE of `Work.BoseBox.q3kinDiagBridge`, isolated
from the corpus's words so that it can be proved in one piece:

* `bOKT` / `fibKT` — the **square of the windowed Fourier transform** of the mean-free state
  (`bOKT ℓ ψ p = ‖kinFT (χ_ℓ · bsQ_ℓ ψ) p‖²`), which is *definitionally* the `p`-integrand of
  `bsOneBody ℓ F 0 ψ`; `fibKT` is its instance at the slot-`i` fibre of an `(m+1)`-body state.
* `fsKinCoeff_antitone`, `fsKinCoeff_combo`, `fsKinCoeff_le_const_add` — the three pointwise
  facts about the symbol `[r−c]₊²` that carry the whole comparison:
  `[·−c₀]₊² ≤ (1−ε)[·−c₁]₊² + ε[·−c₂]₊²` for `c₁,c₂ ≤ c₀` and `ε ∈ [0,1]` (the τ-symbol
  dominating the Bogoliubov cutoff), and the domination `[·−c]₊² ≤ 2[·−c₀]₊² + 2(c₀−c)²`
  which converts *finiteness* of one weighted `p`-lintegral into finiteness of the others.
* `lintegral_step` — the **Bochner/lintegral/Tonelli rewrite**: for a nonnegative `p`-density
  `A` presented as the `r`-integral of a nonnegative jointly measurable kernel `U`, the
  `p`-lintegral of `F(‖p‖)·A(p)` is the double `r`-`p` lintegral of `F(‖p‖)U r p`.
* `coreA` — the **junk-robust symbol comparison**: the `p`-integral of `[‖·‖−c₀]₊²·u` is
  dominated by the `(1−ε)/(ε)`-weighted combination of the `p`-integrals of
  `[‖·‖−c₁]₊²·u` and `[‖·‖−c₂]₊²·u`, *in the Bochner-integral convention* — i.e. the junk
  value `0` of a divergent `p`-integral on the left is handled (it is then `≤` the right side,
  which is a nonnegative combination of Bochner integrals).
* `coreB` — the **lintegral transfer**: if `h ≥ 0` is bounded by `C` on a finite-measure set
  `s` (and by `0` off it), then `(∫⁻ ofReal m).toReal ≤ (∫⁻ ofReal (m + h)).toReal`; this is
  the step that lets the three *bounded* pieces of `fsT` be upgraded to a bound for the whole
  `fsT` without any a.e.-measurability hypothesis on `fsT` itself.

Every statement here is quantified over an abstract measure space
`EuclideanSpace ℝ (Fin 3)` (= `ℝ³`) and the volume measure: no corpus word appears, so the
mathematics is self-contained.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Real BigOperators

namespace Work.BoseBox

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. The `p`-integrand of `bsOneBody`: the windowed Fourier energy of the mean-free state -/

/-- The **square of the windowed `p`-Fourier transform of the mean-free state**:
`bOKT ℓ ψ p = ‖kinFT (χ_ℓ · bsQ ℓ 0 ψ) p‖²`.  This is *definitionally* the `p`-integrand of
`bsOneBody ℓ F 0 ψ` (`bsOneBody ℓ F 0 ψ = (2π)⁻³∫_p F(‖p‖)·bOKT ℓ ψ p`). -/
def bOKT (ℓ : ℝ) (ψ : ℝ³ → ℝ) (p : ℝ³) : ℝ :=
  ‖Submission.BoseGases.kinFT
      (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ)) p‖ ^ 2

/-- The same integrand at the slot-`i` **fibre** `z ↦ Φ (kcInsN m i (z, r))` of an `(m+1)`-body
state `Φ`. -/
def fibKT (ℓ : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) (p : ℝ³) : ℝ :=
  bOKT ℓ (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r))) p

/-- `bsOneBody ℓ F 0 ψ` is the `(2π)⁻³`-normalised `p`-integral of `F(‖p‖)` against `bOKT`. -/
lemma bsOneBody_eq_integral_bOKT (ℓ : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) :
    Work.BSKinetic.bsOneBody ℓ F 0 ψ
      = (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³, F ‖p‖ * bOKT ℓ ψ p := rfl

/-- `fibKT` is nonnegative. -/
lemma fibKT_nonneg (ℓ : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ)
    (i : Fin (m + 1)) (r : Submission.BoseGases.X m) (p : ℝ³) : 0 ≤ fibKT ℓ Φ i r p :=
  sq_nonneg _


/-! ## 1b. Vanishing on the box: the support facts used by every downstream argument -/

/-- `bsQ ℓ 0 ψ` is `ψ` itself when `ψ` vanishes on the anchored box: the box mean is `0`. -/
lemma bsQ_eq_self_of_eq_zero_on {ℓ : ℝ} {ψ : ℝ³ → ℝ} (h : ∀ z ∈ acube ℓ, ψ z = 0) :
    Work.BSKinetic.bsQ ℓ 0 ψ = ψ := by
  have hzero : (∫ z in acube ℓ, ψ z) = 0 := by
    rw [show (∫ z in acube ℓ, ψ z) = ∫ z in acube ℓ, (0 : ℝ) from
      setIntegral_congr_fun (acube_measurable ℓ) (fun z hz => h z hz)]
    simp
  have hmean : Work.BSKinetic.bsMean ℓ 0 ψ = 0 := by
    simp only [Work.BSKinetic.bsMean, smul_zero, zero_add, hzero, mul_zero]
  ext z
  simp only [Work.BSKinetic.bsQ, hmean, sub_zero]

/-- `bsOneBody ℓ F 0 ψ = 0` when `ψ` vanishes on the anchored box `acube ℓ`. -/
lemma bsOneBody_eq_zero_of_eq_zero_on {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) {ψ : ℝ³ → ℝ}
    (h : ∀ z ∈ acube ℓ, ψ z = 0) : Work.BSKinetic.bsOneBody ℓ F 0 ψ = 0 := by
  have hfun : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ 0 z : ℂ)
      * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ)) = fun _ => (0 : ℂ) := by
    funext z
    rw [bsQ_eq_self_of_eq_zero_on h]
    by_cases hz : z ∈ acube ℓ
    · rw [h z hz]; simp
    · have h0 : Work.BSKinetic.bsWin ℓ 0 z = 0 := by
        simp only [Work.BSKinetic.bsWin, smul_zero, sub_zero]
        by_contra hc
        exact hz (chiScale_mem_acube hℓ hc)
      rw [h0]; simp
  unfold Work.BSKinetic.bsOneBody
  rw [hfun]
  simp [kinFT]

/-- `fibKT` vanishes when the slot-`i` fibre vanishes on the anchored box `acube ℓ`. -/
lemma fibKT_eq_zero_of_fibre_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (i : Fin (m + 1)) {r : Submission.BoseGases.X m}
    (h : ∀ z ∈ acube ℓ, Φ (Submission.BoseGases.kcInsN m i (z, r)) = 0) (p : ℝ³) :
    fibKT ℓ Φ i r p = 0 := by
  unfold fibKT bOKT
  rw [show (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ 0 z : ℂ)
      * (Work.BSKinetic.bsQ ℓ 0 (fun z => Φ (Submission.BoseGases.kcInsN m i (z, r))) z : ℂ))
      = fun _ => (0 : ℂ) from by
    funext z
    rw [bsQ_eq_self_of_eq_zero_on h]
    by_cases hz : z ∈ acube ℓ
    · simp only [h z hz, Complex.ofReal_zero, mul_zero]
    · have h0 : Work.BSKinetic.bsWin ℓ 0 z = 0 := by
        simp only [Work.BSKinetic.bsWin, smul_zero, sub_zero]
        by_contra hc
        exact hz (chiScale_mem_acube hℓ hc)
      rw [h0]; simp]
  simp [kinFT]

/-! ## 2. The symbol facts -/

/-- `[r−c]₊²` is **antitone in the cutoff**: for `c ≤ c'`, `[r−c']₊² ≤ [r−c]₊²`. -/
lemma fsKinCoeff_antitone {c c' r : ℝ} (h : c ≤ c') :
    Submission.BoseGases.fsKinCoeff c' r ≤ Submission.BoseGases.fsKinCoeff c r := by
  unfold Submission.BoseGases.fsKinCoeff
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith) le_rfl) 2

/-- **The τ-symbol dominates the Bogoliubov cutoff**: for cutoffs `c₁, c₂ ≤ c₀` and a weight
`eT ∈ [0,1]`, `[r−c₀]₊² ≤ (1−eT)[r−c₁]₊² + eT[r−c₂]₊²` for every real `r`. -/
lemma fsKinCoeff_combo {c₀ c₁ c₂ eT r : ℝ} (h₁ : c₁ ≤ c₀) (h₂ : c₂ ≤ c₀)
    (he0 : 0 ≤ eT) (he1 : eT ≤ 1) :
    Submission.BoseGases.fsKinCoeff c₀ r
      ≤ (1 - eT) * Submission.BoseGases.fsKinCoeff c₁ r
        + eT * Submission.BoseGases.fsKinCoeff c₂ r := by
  have h1 : Submission.BoseGases.fsKinCoeff c₀ r ≤ Submission.BoseGases.fsKinCoeff c₁ r :=
    fsKinCoeff_antitone h₁
  have h2 : Submission.BoseGases.fsKinCoeff c₀ r ≤ Submission.BoseGases.fsKinCoeff c₂ r :=
    fsKinCoeff_antitone h₂
  nlinarith

/-- **Domination of the cutoffs**: `[r−c]₊² ≤ 2[r−c₀]₊² + 2(c₀−c)²` for `c ≤ c₀`. -/
lemma fsKinCoeff_le_const_add {c₀ c r : ℝ} (h : c ≤ c₀) :
    Submission.BoseGases.fsKinCoeff c r
      ≤ 2 * Submission.BoseGases.fsKinCoeff c₀ r + 2 * (c₀ - c) ^ 2 := by
  have hle : max (r - c) 0 ≤ max (r - c₀) 0 + (c₀ - c) := by
    rcases lt_or_ge (r - c) 0 with h' | h'
    · rw [max_eq_right h'.le]
      have := le_max_right (r - c₀) 0
      linarith
    · rw [max_eq_left h']
      have h2 : r - c₀ ≤ max (r - c₀) 0 := le_max_left _ _
      linarith
  have hsq : (max (r - c) 0) ^ 2 ≤ (max (r - c₀) 0 + (c₀ - c)) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) hle 2
  have h2 : (max (r - c₀) 0 + (c₀ - c)) ^ 2 ≤ 2 * (max (r - c₀) 0) ^ 2 + 2 * (c₀ - c) ^ 2 := by
    nlinarith [sq_nonneg (max (r - c₀) 0 - (c₀ - c))]
  simpa [Submission.BoseGases.fsKinCoeff, mul_comm, mul_left_comm, mul_assoc] using le_trans hsq h2

/-- `p ↦ [‖p‖−c]₊²` is continuous. -/
lemma continuous_fsKinCoeff_norm (c : ℝ) :
    Continuous fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ := by
  unfold Submission.BoseGases.fsKinCoeff
  fun_prop

/-! ## 3. The Bochner/lintegral/Tonelli rewrite -/

/-- **The `p`-density as an `r`-integral: the lintegral/Tonelli rewrite.**

Let `A p = ∫_r U r p` be a nonnegative `p`-density presented as the `r`-integral of a
nonnegative jointly measurable kernel `U` whose `r`-lintegral is finite for every `p`.  Then for
any nonnegative symbol `F` the `p`-lintegral of `ofReal (F(‖p‖)·A p)` equals the double
`r`-`p` lintegral of `ofReal (F(‖p‖)·U r p)`. -/
theorem lintegral_step {m : ℕ} {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (hFmeas : Measurable F)
    {A : ℝ³ → ℝ}
    (hA : ∀ p, 0 ≤ A p)
    {U : Submission.BoseGases.X m → ℝ³ → ℝ} (hU : ∀ r p, 0 ≤ U r p)
    (hUmeas : Measurable (Function.uncurry U))
    (hAeq : ∀ p, A p = ∫ r : Submission.BoseGases.X m, U r p)
    (hfin : ∀ p, ∫⁻ r : Submission.BoseGases.X m, ENNReal.ofReal (U r p) < ⊤) :
    ∫⁻ p : ℝ³, ENNReal.ofReal (F ‖p‖ * A p) ∂volume
      = ∫⁻ r : Submission.BoseGases.X m, ∫⁻ p : ℝ³, ENNReal.ofReal (F ‖p‖ * U r p) ∂volume
        ∂(volume : Measure (Submission.BoseGases.X m)) := by
  have hslice : ∀ p : ℝ³, Measurable (fun r : Submission.BoseGases.X m => U r p) := fun p =>
    hUmeas.comp (Measurable.prodMk measurable_id measurable_const)
  have hpt : ∀ p : ℝ³, ENNReal.ofReal (F ‖p‖ * A p)
      = ENNReal.ofReal (F ‖p‖) * ∫⁻ r : Submission.BoseGases.X m, ENNReal.ofReal (U r p) := by
    intro p
    have h1 : A p = (∫⁻ r : Submission.BoseGases.X m, ENNReal.ofReal (U r p)).toReal := by
      rw [hAeq p]
      exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun r => hU r p))
        (hslice p).aestronglyMeasurable)
    rw [h1, ENNReal.ofReal_mul (hF ‖p‖), ENNReal.ofReal_toReal (hfin p).ne, mul_comm]
  calc ∫⁻ p : ℝ³, ENNReal.ofReal (F ‖p‖ * A p) ∂volume
      = ∫⁻ p : ℝ³, ENNReal.ofReal (F ‖p‖)
          * (∫⁻ r : Submission.BoseGases.X m, ENNReal.ofReal (U r p)) ∂volume := by
        exact lintegral_congr hpt
    _ = ∫⁻ p : ℝ³, ∫⁻ r : Submission.BoseGases.X m,
          ENNReal.ofReal (F ‖p‖) * ENNReal.ofReal (U r p) ∂volume ∂volume := by
        refine lintegral_congr (fun p => ?_)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ p : ℝ³, ∫⁻ r : Submission.BoseGases.X m,
          ENNReal.ofReal (F ‖p‖ * U r p) ∂volume ∂volume := by
        refine lintegral_congr (fun p => lintegral_congr (fun r => ?_))
        rw [ENNReal.ofReal_mul (hF ‖p‖)]
    _ = ∫⁻ r : Submission.BoseGases.X m, ∫⁻ p : ℝ³,
          ENNReal.ofReal (F ‖p‖ * U r p) ∂volume ∂(volume : Measure (Submission.BoseGases.X m)) := by
        refine lintegral_lintegral_swap ?_
        refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
        refine (hFmeas.comp (continuous_norm.measurable.comp measurable_fst)).mul ?_
        exact hUmeas.comp (Measurable.prodMk measurable_snd measurable_fst)

/-! ## 4. `coreA` — the junk-robust symbol comparison -/

/-- **The junk-robust symbol comparison.**  For cutoffs `c₁, c₂ ≤ c₀`, a weight `eT ∈ [0,1]`, a
nonnegative a.e.-measurable density `u` with finite `L¹`-mass (i.e. `∫⁻ ofReal u < ∞`, which is
the `L²`-mass of the windowed state in the application),

`(2π)⁻³·(∫⁻_p ofReal ([‖p‖−c₀]₊²·u p)).toReal
    ≤ (1−eT)·(2π)⁻³∫_p [‖p‖−c₁]₊²·u p + eT·(2π)⁻³∫_p [‖p‖−c₂]₊²·u p`.

The point of the statement is that it is **junk-robust**: when the left `p`-integral diverges
(the fibre fails to be in `H¹`), its Bochner value is `0` and the inequality is trivial. -/
theorem coreA {c₀ c₁ c₂ eT : ℝ} (h₁ : c₁ ≤ c₀) (h₂ : c₂ ≤ c₀) (he0 : 0 ≤ eT) (he1 : eT ≤ 1)
    {u : ℝ³ → ℝ} (hu : ∀ p, 0 ≤ u p) (humeas : AEMeasurable u volume)
    (hufin : ∫⁻ p, ENNReal.ofReal (u p) ∂volume < ⊤) :
    (((2 * Real.pi) ^ 3)⁻¹) *
        ((∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume).toReal)
      ≤ (1 - eT) * ((((2 * Real.pi) ^ 3)⁻¹)
            * ∫ p, Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p ∂volume)
        + eT * ((((2 * Real.pi) ^ 3)⁻¹)
            * ∫ p, Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p ∂volume) := by
  have hsym : ∀ p : ℝ³, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ ≤
      (1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
        + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖ :=
    fun p => fsKinCoeff_combo h₁ h₂ he0 he1
  have hmeas_raw : ∀ c : ℝ,
      AEMeasurable (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ * u p) volume :=
    fun c => (continuous_fsKinCoeff_norm c).measurable.aemeasurable.mul humeas
  have hmeasF : ∀ c : ℝ, AEMeasurable (fun p : ℝ³ =>
      ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * u p)) volume :=
    fun c => ENNReal.measurable_ofReal.comp_aemeasurable (hmeas_raw c)
  have hgnn : ∀ p : ℝ³, (0 : ℝ) ≤ ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
      + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p := by
    intro p
    have hreal : ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
          + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p
        = (1 - eT) * (Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p)
          + eT * (Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p) := by ring
    rw [hreal]
    exact add_nonneg
      (mul_nonneg (by linarith) (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p)))
      (mul_nonneg he0 (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p)))
  have hgmeas : AEMeasurable (fun p : ℝ³ => ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
      + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p) volume :=
    ((continuous_fsKinCoeff_norm c₁).measurable.const_mul (1 - eT) |>.add
      ((continuous_fsKinCoeff_norm c₂).measurable.const_mul eT)).aemeasurable.mul humeas
  have hbound : ∀ {c : ℝ}, c ≤ c₀ →
      ∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * u p) ∂volume
      ≤ (2 : ℝ≥0∞) * (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume)
        + ENNReal.ofReal (2 * (c₀ - c) ^ 2) * (∫⁻ p, ENNReal.ofReal (u p) ∂volume) := by
    intro c hc
    have hpt : ∀ p : ℝ³, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * u p)
        ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p)
          + ENNReal.ofReal (2 * (c₀ - c) ^ 2) * ENNReal.ofReal (u p) := by
      intro p
      have hcu : (0 : ℝ) ≤ 2 * (c₀ - c) ^ 2 := by nlinarith [sq_nonneg (c₀ - c)]
      have hreal : Submission.BoseGases.fsKinCoeff c ‖p‖ * u p
          ≤ 2 * (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) + 2 * (c₀ - c) ^ 2 * u p := by
        have h0 := fsKinCoeff_le_const_add (c₀ := c₀) (c := c) hc (r := ‖p‖)
        nlinarith [h0, hu p]
      have hnn1 : (0 : ℝ) ≤ 2 * (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p))
      calc ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * u p)
          ≤ ENNReal.ofReal (2 * (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p)
              + 2 * (c₀ - c) ^ 2 * u p) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (2 * (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p))
              + ENNReal.ofReal (2 * (c₀ - c) ^ 2 * u p) :=
              ENNReal.ofReal_add hnn1 (by nlinarith [hcu, hu p])
        _ = (2 : ℝ≥0∞) * ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p)
              + ENNReal.ofReal (2 * (c₀ - c) ^ 2) * ENNReal.ofReal (u p) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul hcu, ENNReal.ofReal_ofNat]
    calc ∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * u p) ∂volume
        ≤ ∫⁻ p, ((2 : ℝ≥0∞) * ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p)
            + ENNReal.ofReal (2 * (c₀ - c) ^ 2) * ENNReal.ofReal (u p)) ∂volume :=
          lintegral_mono hpt
      _ = (2 : ℝ≥0∞) * (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume)
            + ENNReal.ofReal (2 * (c₀ - c) ^ 2) * (∫⁻ p, ENNReal.ofReal (u p) ∂volume) := by
          rw [lintegral_add_left' ((hmeasF c₀).const_mul 2),
            lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  by_cases hX : (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume) = ⊤
  · rw [hX, ENNReal.toReal_top, mul_zero]
    have hb1 : 0 ≤ (((2 * Real.pi) ^ 3)⁻¹)
        * ∫ p, Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p ∂volume :=
      mul_nonneg (by positivity) (integral_nonneg
        (fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p)))
    have hb2 : 0 ≤ (((2 * Real.pi) ^ 3)⁻¹)
        * ∫ p, Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p ∂volume :=
      mul_nonneg (by positivity) (integral_nonneg
        (fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p)))
    nlinarith [he0, he1, hb1, hb2]
  · have hXlt : (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume) < ⊤ :=
      lt_top_iff_ne_top.mpr hX
    have hfin : ∀ {c : ℝ}, c ≤ c₀ →
        ∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * u p) ∂volume < ⊤ := by
      intro c hc
      refine lt_of_le_of_lt (hbound hc) ?_
      exact ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top (by norm_num) hXlt, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hufin⟩
    have hint : ∀ {c : ℝ}, c ≤ c₀ → Integrable (fun p : ℝ³ =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ * u p) volume := by
      intro c hc
      refine ⟨(hmeas_raw c).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
        (fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p)))]
      exact hfin hc
    have hcombo : ∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume
        ≤ ∫⁻ p, ENNReal.ofReal (((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p) ∂volume :=
      lintegral_mono (fun p => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hsym p) (hu p)))
    have hcombo_fin : ∫⁻ p, ENNReal.ofReal (((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
        + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p) ∂volume < ⊤ := by
      have hpt : ∀ p : ℝ³, ENNReal.ofReal (((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
          + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p)
          ≤ ENNReal.ofReal (1 - eT) * ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p)
            + ENNReal.ofReal eT * ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p) := by
        intro p
        have hreal : ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
              + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p
            = (1 - eT) * (Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p)
              + eT * (Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p) := by ring
        rw [hreal, ENNReal.ofReal_add
            (mul_nonneg (by linarith)
              (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p)))
            (mul_nonneg he0 (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (hu p))),
          ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - eT), ENNReal.ofReal_mul he0]
      refine lt_of_le_of_lt (lintegral_mono hpt) ?_
      rw [lintegral_add_left' ((hmeasF c₁).const_mul (ENNReal.ofReal (1 - eT))),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin h₁),
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin h₂)⟩
    have hstep1 : (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume).toReal
        ≤ (∫⁻ p, ENNReal.ofReal (((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p) ∂volume).toReal :=
      ENNReal.toReal_mono hcombo_fin.ne hcombo
    have hstep2 : (∫⁻ p, ENNReal.ofReal (((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p) ∂volume).toReal
        = ∫ p, ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p ∂volume :=
      (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgnn)
        hgmeas.aestronglyMeasurable).symm
    have hsplit : ∫ p, ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
          + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p ∂volume
        = (1 - eT) * ∫ p, Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p ∂volume
          + eT * ∫ p, Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p ∂volume := by
      have h1 : (fun p : ℝ³ => ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p)
          = fun p => (1 - eT) * (Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p)
              + eT * (Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p) := by
        funext p; ring
      rw [h1, integral_add ((hint h₁).const_mul (1 - eT)) ((hint h₂).const_mul eT),
        integral_const_mul, integral_const_mul]
    calc (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ p, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * u p) ∂volume).toReal
        ≤ (((2 * Real.pi) ^ 3)⁻¹) * (∫⁻ p, ENNReal.ofReal (((1 - eT)
            * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p) ∂volume).toReal :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ = (((2 * Real.pi) ^ 3)⁻¹) * (∫ p, ((1 - eT) * Submission.BoseGases.fsKinCoeff c₁ ‖p‖
            + eT * Submission.BoseGases.fsKinCoeff c₂ ‖p‖) * u p ∂volume) := by rw [hstep2]
      _ = (1 - eT) * ((((2 * Real.pi) ^ 3)⁻¹)
            * ∫ p, Submission.BoseGases.fsKinCoeff c₁ ‖p‖ * u p ∂volume)
          + eT * ((((2 * Real.pi) ^ 3)⁻¹)
            * ∫ p, Submission.BoseGases.fsKinCoeff c₂ ‖p‖ * u p ∂volume) := by
          rw [hsplit]; ring

/-! ## 5. `coreB` — the lintegral transfer from the bounded pieces to the whole `fsT` -/

/-- **The lintegral transfer.**  Let `s` be a finite-measure measurable set, `C ≥ 0`, and
`m, h : ℝ³ → ℝ` nonnegative with `h r ≤ C·1_s(r)`.  Then

`(∫⁻ ofReal m).toReal ≤ (∫⁻ ofReal (m + h)).toReal`.

This is the junk-robust step: `m ↦ m + h` changes the lintegral by at most `C·|s| < ∞`, so
either both lintegrals are `⊤` (both `toReal` are `0`), or both are finite and monotonicity
applies. -/
theorem coreB {s : Set ℝ³} (hs : MeasurableSet s) (hvol : volume s < ⊤) {C : ℝ} (hC : 0 ≤ C)
    {m h : ℝ³ → ℝ} (hm : ∀ r, 0 ≤ m r) (hh : ∀ r, 0 ≤ h r)
    (hb : ∀ r, h r ≤ C * s.indicator (fun _ => (1 : ℝ)) r) :
    (∫⁻ r, ENNReal.ofReal (m r) ∂volume).toReal
      ≤ (∫⁻ r, ENNReal.ofReal (m r + h r) ∂volume).toReal := by
  have hpt : ∀ r : ℝ³, ENNReal.ofReal (m r + h r)
      ≤ ENNReal.ofReal (m r) + ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r) := by
    intro r
    calc ENNReal.ofReal (m r + h r) = ENNReal.ofReal (m r) + ENNReal.ofReal (h r) :=
          ENNReal.ofReal_add (hm r) (hh r)
      _ ≤ ENNReal.ofReal (m r)
            + ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r) :=
          add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal (hb r))
  have hmeasχ : Measurable (fun r : ℝ³ => ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.indicator hs).const_mul (C : ℝ))
  have hM : ∫⁻ r : ℝ³, ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r) ∂volume < ⊤ := by
    have h1 : ∀ r : ℝ³, ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r)
        = ENNReal.ofReal C * s.indicator (fun _ => (1 : ℝ≥0∞)) r := by
      intro r
      rw [ENNReal.ofReal_mul hC]
      congr 1
      by_cases hr : r ∈ s
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]; simp
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]; simp
    rw [lintegral_congr h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator_const hs, one_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol
  have hmono : ∫⁻ r, ENNReal.ofReal (m r) ∂volume
      ≤ ∫⁻ r, ENNReal.ofReal (m r + h r) ∂volume :=
    lintegral_mono (fun r => ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hh r)))
  have hbound : ∫⁻ r, ENNReal.ofReal (m r + h r) ∂volume
      ≤ (∫⁻ r, ENNReal.ofReal (m r) ∂volume)
        + ∫⁻ r, ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r) ∂volume := by
    calc ∫⁻ r, ENNReal.ofReal (m r + h r) ∂volume
        ≤ ∫⁻ r, (ENNReal.ofReal (m r)
            + ENNReal.ofReal (C * s.indicator (fun _ => (1 : ℝ)) r)) ∂volume :=
          lintegral_mono hpt
      _ = _ := lintegral_add_right' _ hmeasχ.aemeasurable
  rcases eq_or_ne (∫⁻ r, ENNReal.ofReal (m r) ∂volume) ⊤ with htop | hne
  · have h2 : ∫⁻ r, ENNReal.ofReal (m r + h r) ∂volume = ⊤ := by
      rw [eq_top_iff]
      rw [← htop]; exact hmono
    rw [htop, h2]
  · have hlt : ∫⁻ r, ENNReal.ofReal (m r) ∂volume < ⊤ := lt_top_iff_ne_top.mpr hne
    have hfin : ∫⁻ r, ENNReal.ofReal (m r + h r) ∂volume < ⊤ := by
      refine lt_of_le_of_lt hbound ?_
      exact ENNReal.add_lt_top.mpr ⟨hlt, hM⟩
    exact ENNReal.toReal_mono hfin.ne hmono


/-! ## 6. The named objects of the per-slot argument -/

/-- The **`p`-density of the slot-`i` diagonal mode form**:
`pDens = (ℓ³)⁻¹∫_{abox (m+1) ℓ} ‖pSlotAmp ℓ p Φ i‖²` — the inner factor of the `i`-th summand
of `pDiagForm ℓ F Φ`. -/
def pDens (ℓ : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (p : ℝ³) : ℝ :=
  (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
    ‖Submission.BoseGases.pSlotAmp ℓ p Φ i x‖ ^ 2

/-- The **`r`-kernel** of the slot-`i` density: `fibKT` restricted to the centred box
`abox m ℓ` by the indicator, so that `pDens ℓ Φ i p = ∫_r rKern ℓ Φ i r p`. -/
def rKern (ℓ : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) (p : ℝ³) : ℝ :=
  fibKT ℓ Φ i r p * (Submission.BoseGases.abox m ℓ).indicator (fun _ => (1 : ℝ)) r

/-- The `r`-lintegral of the `p`-integers of the kernel: the `r`-density of the double
lintegral to which `lintegral_step` rewrites the slot-`i` `p`-lintegral. -/
def rLint (ℓ : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (c : ℝ) (r : Submission.BoseGases.X m) : ℝ≥0∞ :=
  ∫⁻ p : ℝ³, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ * fibKT ℓ Φ i r p)

/-- The slot-`i` fibre of FS's main kinetic word `mainWord` at the anchored box `Λ(0)`. -/
def mWord (ℓ d s eT : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) : ℝ :=
  Work.BoseKinLoc.mainWord ℓ d s eT 0
    (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r)))

/-- The slot-`i` fibre of FS's localised kinetic word `fsT` at the anchored box `Λ(0)`. -/
def fsWord (ℓ d s eT b : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) : ℝ :=
  Work.BoseKinLoc.fsT ℓ d s eT b 0
    (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r)))

/-- The sum of the three **bounded** pieces of `fsT` along the slot-`i` fibre (the Neumann
fraction, the gap and the large-momentum term): `fsWord = neuGapMom + mWord`. -/
def neuGapMom (ℓ d s eT b : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ)
    (i : Fin (m + 1)) (r : Submission.BoseGases.X m) : ℝ :=
  Work.BoseKinLoc.neuWord ℓ d eT 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r)))
    + Work.BoseKinLoc.gapWord ℓ b 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r)))
    + Work.BoseKinLoc.momWord ℓ d eT b 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r)))

/-- `fsWord` splits into its four pieces. -/
lemma fsWord_eq (ℓ d s eT b : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ)
    (i : Fin (m + 1)) (r : Submission.BoseGases.X m) :
    fsWord ℓ d s eT b Φ i r = neuGapMom ℓ d s eT b Φ i r + mWord ℓ d s eT Φ i r := by
  unfold fsWord neuGapMom mWord Work.BoseKinLoc.fsT
  ring

/-- `mWord` is the `(2π)⁻³`-weighted combination of the two cut-off slot integrals. -/
lemma mWord_eq (ℓ d s eT : ℝ) {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ)
    (i : Fin (m + 1)) (r : Submission.BoseGases.X m) :
    mWord ℓ d s eT Φ i r
      = (1 - eT) * ((((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³,
            Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ * fibKT ℓ Φ i r p)
        + eT * ((((2 * Real.pi) ^ 3)⁻¹) * ∫ p : ℝ³,
            Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ * fibKT ℓ Φ i r p) := by
  unfold mWord Work.BoseKinLoc.mainWord
  rw [Work.BSKinetic.bsOneBody, Work.BSKinetic.bsOneBody]
  unfold fibKT bOKT
  rfl

/-- The **the two cut-off inequalities**: `(2dsℓ)⁻¹ ≤ (dsℓ)⁻¹` and `(2sℓ)⁻¹ ≤ (dsℓ)⁻¹`. -/
lemma two_cutoff_le {ℓ d s : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hℓ : 0 < ℓ) :
    (2 * (s * ℓ))⁻¹ ≤ (d * s * ℓ)⁻¹ ∧ (2 * (d * s * ℓ))⁻¹ ≤ (d * s * ℓ)⁻¹ := by
  have hpos : 0 < d * s * ℓ := by positivity
  constructor
  · refine inv_anti₀ hpos ?_
    nlinarith [hd, hd1, hs, hℓ]
  · refine inv_anti₀ hpos ?_
    nlinarith [hd, hs, hℓ]

end Work.BoseBox
