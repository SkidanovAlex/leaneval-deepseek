import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le
import Submission.Work.SmallBoxD1Integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-283 — the D1 Newtonian main term (M1)

FS `lm:appbogolubov`'s leading term is

  `¼(2π)⁻³ ∫_ℝ³ \widehat{WS₁}(p)²/p² dp = ¼ ∬ WS₁(x)WS₁(y)/(4π|x−y|) dx dy`,

and the corpus identifies the right-hand side with `½ ĝω(0)`
(`SmallBoxBogMainTerm.mainMassCoeff_le_coarse`, which proves
`½(1/(8π))∬W₁W₁/‖x−y‖ ≤ ½(1+6C(R/ℓ)²)g0w0Mass`).  This module supplies the
FOURIER-side half: the pairing weight `ℬ(q) = pairW (wScaled ℓ (g₀)) q` satisfies

  `(2π)⁻³ ∫_q ℬ(q)²/‖q‖² dq ≤ (1/(4π)) ∬ W(x)W(y)/‖x−y‖ = 2J(W)`.

The route is the commons `coulomb_energy_fourier_lintegral_le`
(`∫⁻‖𝓕f‖²/‖p‖² ≤ π ∫⁻∫⁻ f x f y/‖x−y‖` for `f ≥ 0` integrable), which needs NO
smoothness of `W` — only `Integrable` and pointwise non-negativity.  Since `W₁` is
only a.e.-nonnegative, it is replaced by `W₊ := max W 0` (equal a.e.), which does
not change either `𝓕W` or the position-space double integral.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the complex Fourier transform of the complexification of a real function. -/
noncomputable def cfourier (W : ℝ³ → ℝ) : ℝ³ → ℂ :=
  FourierTransform.fourier (fun x => (W x : ℂ))

/-- `pairW` is the real part of `cfourier`. -/
lemma pairW_eq_cfourier_re (W : ℝ³ → ℝ) (q : ℝ³) :
    pairW W q = (cfourier W (((2 * π : ℝ)⁻¹) • q)).re := rfl

/-- the pointwise comparison `(Re z)² ≤ ‖z‖²`. -/
lemma pairW_sq_le_normSq_cfourier (W : ℝ³ → ℝ) (q : ℝ³) :
    (pairW W q) ^ 2 ≤ ‖cfourier W (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 := by
  rw [pairW_eq_cfourier_re]
  set z := cfourier W (((2 * π : ℝ)⁻¹) • q) with hz
  have h : z.re ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  rwa [Complex.normSq_eq_norm_sq] at h

/-- a.e.-equality of `W` with its positive part, given a.e.-non-negativity. -/
lemma max_zero_ae_eq {W : ℝ³ → ℝ} (hW0 : 0 ≤ᵐ[volume] W) :
    (fun x : ℝ³ => max (W x) 0) =ᵐ[volume] W := by
  filter_upwards [hW0] with x hx
  exact max_eq_left hx

/-- the complexification of the positive part has the same Fourier transform as `W`. -/
lemma cfourier_max_eq {W : ℝ³ → ℝ} (hW0 : 0 ≤ᵐ[volume] W) :
    cfourier (fun x : ℝ³ => max (W x) 0) = cfourier W := by
  have hae : (fun x : ℝ³ => ((max (W x) 0 : ℝ) : ℂ)) =ᵐ[volume] (fun x : ℝ³ => (W x : ℂ)) := by
    filter_upwards [max_zero_ae_eq hW0] with x hx
    rw [hx]
  funext q
  simp only [cfourier]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-! ## The lintegral ⇄ Bochner bridge for the Newton double integral -/

/-- For a measurable, bounded, nonnegative integrable `W`, the double lintegral of
`ofReal (W x * W y / ‖x−y‖)` has `toReal` equal to the Bochner double integral
`∫x ∫y W x * W y * ‖x−y‖⁻¹`. -/
lemma toReal_lintegral_lintegral_eq_integral {W : ℝ³ → ℝ} (hW : Integrable W)
    (hW0 : ∀ x, 0 ≤ W x) (hWbdd : ∃ C : ℝ, ∀ x, |W x| ≤ C) (hWmeas : Measurable W) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal
      = ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by
  set F : ℝ³ × ℝ³ → ℝ := fun p => W p.1 * W p.2 * (‖p.1 - p.2‖)⁻¹ with hFdef
  have hFint : Integrable F (volume.prod volume) := by
    have h := Commons.Analysis.Fourier.newton_double_integrable W hWmeas hWbdd hW
    refine h.congr (Filter.Eventually.of_forall fun p => by simp only [hFdef])
  have hF0 : 0 ≤ᵐ[volume.prod volume] F := by
    filter_upwards with p
    exact mul_nonneg (mul_nonneg (hW0 _) (hW0 _))
      (inv_nonneg.mpr (norm_nonneg _))
  have hFmeas : AEMeasurable F (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : ℝ³ × ℝ³ => W p.1) (volume.prod volume) :=
      hWmeas.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun p : ℝ³ × ℝ³ => W p.2) (volume.prod volume) :=
      hWmeas.aemeasurable.comp_snd
    have h3 : AEMeasurable (fun p : ℝ³ × ℝ³ => (‖p.1 - p.2‖ : ℝ)⁻¹) (volume.prod volume) :=
      ((measurable_fst.sub measurable_snd).norm.inv).aemeasurable
    exact (h1.mul h2).mul h3
  have h1 : ENNReal.ofReal (∫ p : ℝ³ × ℝ³, F p)
      = ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (F p) :=
    ofReal_integral_eq_lintegral_ofReal hFint hF0
  have hFmeasE : AEMeasurable (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (F p)) (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hFmeas
  have h2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)))
      = ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (F p) :=
    MeasureTheory.lintegral_lintegral (f := fun x y => ENNReal.ofReal (F (x, y))) hFmeasE
  have h3 : (∫ p : ℝ³ × ℝ³, F p) = ∫ x, ∫ y, F (x, y) :=
    MeasureTheory.integral_prod (f := F) hFint
  have hgoal : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFdef, div_eq_mul_inv]
  have hIntF : (0 : ℝ) ≤ ∫ p : ℝ³ × ℝ³, F p := by
    refine integral_nonneg (fun p => ?_)
    simp only [hFdef]
    exact mul_nonneg (mul_nonneg (hW0 p.1) (hW0 p.2)) (inv_nonneg.mpr (norm_nonneg _))
  have htoReal : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y))).toReal = ∫ x, ∫ y, F (x, y) := by
    rw [h2, ← h1, ENNReal.toReal_ofReal hIntF, h3]
  rw [← hgoal, htoReal]

/-! ## The M1 main theorem: the Fourier-side Newtonian bound for the D1 pairing weight -/

/-- the complex Fourier transform of an integrable real function is continuous. -/
lemma continuous_cfourier {W : ℝ³ → ℝ} (hW : Integrable W) : Continuous (cfourier W) := by
  have h1 : Integrable (fun x : ℝ³ => (W x : ℂ)) := hW.ofReal
  have h2 : cfourier W = VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ³) (fun x : ℝ³ => (W x : ℂ)) := rfl
  rw [h2]
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_ h1
  rw [continuous_iff_continuousAt]
  intro p
  exact (continuous_fst.inner continuous_snd).continuousAt

/-- the positive part of `W` has the same lintegral weight. -/
lemma lintegral_max_eq {W : ℝ³ → ℝ} (hW0 : 0 ≤ᵐ[volume] W) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (max (W x) 0 * max (W y) 0 / ‖x - y‖) := by
  have hae := max_zero_ae_eq hW0
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hx, hy]

/-- the double Bochner integral of `W x * W y * ‖x−y‖⁻¹` is unchanged by the positive part. -/
lemma integral_integral_max_eq {W : ℝ³ → ℝ} (hW0 : 0 ≤ᵐ[volume] W) :
    (∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹)
      = ∫ x, ∫ y, max (W x) 0 * max (W y) 0 * (‖x - y‖)⁻¹ := by
  have hae := max_zero_ae_eq hW0
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hx, hy]

/-- **M1 — the Fourier-side Newtonian bound for the D1 pairing weight.**
For a measurable, bounded, a.e.-nonnegative integrable `W`,

  `(2π)⁻³ ∫_q pairW W q ²/‖q‖² dq ≤ (1/(4π)) ∬ W(x)W(y)/‖x−y‖ dx dy`,

i.e. FS's `¼(2π)⁻³∫\widehat{WS₁}(p)²/p² dp = ¼∬WS₁(x)WS₁(y)/(4π|x−y|)` in corpus notation.
The route is the commons `coulomb_energy_fourier_lintegral_le` (the `∫⁻`-level Coulomb
inequality for `L¹` data). -/
theorem integral_pairW_sq_div_sq_le_newtonian {W : ℝ³ → ℝ} (hW : Integrable W)
    (hW0 : 0 ≤ᵐ[volume] W) (hWbdd : ∃ C : ℝ, ∀ x, |W x| ≤ C) (hWmeas : Measurable W)
    (hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (pairW W q) ^ 2 / ‖q‖ ^ 2
      ≤ (1 / (4 * π)) * ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by
  set Wp : ℝ³ → ℝ := fun x => max (W x) 0 with hWp
  have hWp0 : ∀ x, 0 ≤ Wp x := fun x => le_max_right _ _
  have hWpint : Integrable Wp := by
    rw [hWp]
    refine Integrable.mono' hW.abs (hWmeas.max measurable_const).aestronglyMeasurable ?_
    filter_upwards with x
    have h0 : (0 : ℝ) ≤ max (W x) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hWpbdd : ∃ C : ℝ, ∀ x, |Wp x| ≤ C := by
    obtain ⟨C, hC⟩ := hWbdd
    refine ⟨max C 0, fun x => ?_⟩
    have h1 : |Wp x| = Wp x := abs_of_nonneg (hWp0 x)
    rw [h1, hWp]
    exact max_le (le_trans (le_trans (le_abs_self _) (hC x)) (le_max_left _ _)) (le_max_right _ _)
  have hWpmeas : Measurable Wp := by
    rw [hWp]
    exact hWmeas.max measurable_const
  have hcfsame : cfourier Wp = cfourier W := cfourier_max_eq hW0
  have hpairfun : (fun q : ℝ³ => pairW W q) = fun q : ℝ³ => pairW Wp q := by
    funext q
    rw [pairW_eq_cfourier_re, pairW_eq_cfourier_re, hcfsame]
  -- (a) Bochner ⇄ lintegral for the momentum side
  have hmommeas : AEStronglyMeasurable (fun q : ℝ³ => (pairW W q) ^ 2 / ‖q‖ ^ 2) := by
    have hc : Continuous (fun q : ℝ³ => pairW W q) := by
      rw [hpairfun]
      exact Complex.continuous_re.comp
        ((continuous_cfourier hWpint).comp (continuous_const_smul ((2 * π : ℝ)⁻¹)))
    exact ((hc.pow 2).measurable.div (continuous_norm.pow 2).measurable).aestronglyMeasurable
  have hmom0 : ∀ q : ℝ³, 0 ≤ (pairW W q) ^ 2 / ‖q‖ ^ 2 := fun q =>
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmom : (∫ q, (pairW W q) ^ 2 / ‖q‖ ^ 2)
      = (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hmom0) hmommeas
  -- (b) the pointwise comparison to the Fourier modulus
  have hLI : (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2))
      ≤ ∫⁻ q, ENNReal.ofReal (‖cfourier Wp (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 / ‖q‖ ^ 2) := by
    refine lintegral_mono (fun q => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show pairW W q = pairW Wp q from congrFun hpairfun q]
    exact div_le_div_of_nonneg_right (pairW_sq_le_normSq_cfourier Wp q) (sq_nonneg _)
  -- (c) the Coulomb inequality
  have hfleet := Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le hWpint hWp0
  -- (d) the position-side conversion
  have hJto : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal
      = ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by
    rw [lintegral_max_eq hW0,
      toReal_lintegral_lintegral_eq_integral hWpint hWp0 hWpbdd hWpmeas,
      ← integral_integral_max_eq hW0]
  have hcnonneg : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  have hc2nonneg : (0 : ℝ) ≤ 1 / (4 * π) := by positivity
  have hfleet' : ENNReal.ofReal (((2 * π) ^ 3)⁻¹)
        * (∫⁻ q, ENNReal.ofReal (‖cfourier Wp (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal (1 / (4 * π))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) := by
    rw [← lintegral_max_eq hW0] at hfleet
    exact hfleet
  have hcomb : ENNReal.ofReal (((2 * π) ^ 3)⁻¹)
        * (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal (1 / (4 * π))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) :=
    le_trans (mul_le_mul_of_nonneg_left hLI zero_le) hfleet'
  have hcombne : ENNReal.ofReal (1 / (4 * π))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) hfin
  calc ((2 * π) ^ 3)⁻¹ * ∫ q, (pairW W q) ^ 2 / ‖q‖ ^ 2
      = (ENNReal.ofReal (((2 * π) ^ 3)⁻¹)
          * (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2))).toReal := by
          rw [hmom, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcnonneg]
    _ ≤ (ENNReal.ofReal (1 / (4 * π))
          * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))).toReal :=
          ENNReal.toReal_mono hcombne hcomb
    _ = (1 / (4 * π))
          * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc2nonneg]
    _ = (1 / (4 * π)) * ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by rw [hJto]

end BoseGases
end Submission
