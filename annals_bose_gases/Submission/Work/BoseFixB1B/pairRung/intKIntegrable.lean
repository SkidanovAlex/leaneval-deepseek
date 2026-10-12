import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.intKIntegrable`

The `q`-integrand of the pairing rung's Bogoliubov correction, namely

  `q ↦ 𝓑(q)²/V² / 𝒜(q)`,  `𝒜(q) = [(N+1)]⁻¹·[‖q‖−c]₊² + 2K_s a/V`,

is Lebesgue integrable (it is the hypothesis under which the `q`-integral of the rung may be
manipulated, e.g. by `Work.BoseFixB1B.pairRung.integralAddLe`).

The content is the lower bound `𝒜(q) ≥ ‖q‖²/C` with an explicit positive constant `C`, which makes
`𝓑(q)²/(V²𝒜(q))` dominated by a constant times `𝓑(q)²/‖q‖²` — the integrable function supplied as
`hfin`.  Two regimes:

* `‖q‖ ≥ 2c`: `[‖q‖−c]₊² = (‖q‖−c)² ≥ ‖q‖²/4`, so `𝒜(q) ≥ ‖q‖²/(4(N+1))`;
* `‖q‖ < 2c`: `𝒜(q) ≥ 2K_s a/V`, and `‖q‖² < 4c² = (2c²V/(K_s a))·(2K_s a/V)`.

Combining, `‖q‖² ≤ C·𝒜(q)` for `C = max (4(N+1)) (2c²V/(K_s a)) > 0`.

The pointwise domination holds off the single point `q = 0` (where Lean's `x/0 = 0` makes
`𝓑(0)²/‖0‖² = 0`); `{0}` is Lebesgue-null, so the a.e. form of `Integrable.mono'` applies.
Measurability of the integrand comes from the continuity of the Fourier transform of an `L¹`
function (`hWint`).
-/

namespace Work.BoseFixB1B.pairRung

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Fourier transform of an `L¹` function is continuous. -/
private lemma continuous_fourier_of_integrable {f : E3 → ℂ}
    (hf : MeasureTheory.Integrable f) : Continuous (𝓕 f) := by
  rw [show 𝓕 f = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E3) f from rfl]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

/-- The `q`-space denominator `𝒜` of the pairing rung's Bogoliubov coefficient. -/
private noncomputable def fsDen (N : ℕ) (V Ks c a : ℝ) (q : E3) : ℝ :=
  1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V

/-- The kinetic part of `𝒜` is nonnegative. -/
private lemma fsDen_kin_nonneg (N : ℕ) (c : ℝ) (q : E3) :
    0 ≤ 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
  mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)

/-- `𝒜` is positive. -/
private lemma fsDen_pos {N : ℕ} {V Ks c a : ℝ} (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < a)
    (q : E3) : 0 < fsDen N V Ks c a q := by
  have h2 : (0 : ℝ) < 2 * Ks * a / V := by positivity
  simp only [fsDen]
  linarith [fsDen_kin_nonneg N c q]

/-- `𝒜` dominates its constant part. -/
private lemma le_fsDen {N : ℕ} {V Ks c a : ℝ} {q : E3} :
    2 * Ks * a / V ≤ fsDen N V Ks c a q := by
  simp only [fsDen]
  linarith [fsDen_kin_nonneg N c q]

/-- `𝒜` is continuous. -/
private lemma fsDen_continuous {N : ℕ} (V Ks c a : ℝ) :
    Continuous (fsDen N V Ks c a) := by
  have hkin : Continuous (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖) := by
    simp only [Submission.BoseGases.fsKinCoeff]
    exact ((continuous_norm.sub continuous_const).max continuous_const).pow 2
  change Continuous (fun q : E3 =>
    1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V)
  exact (continuous_const.mul hkin).add continuous_const

/-- **The denominator dominates `‖q‖²`.**  With `C = max (4(N+1)) (2c²V/(K_s a)) > 0` one has
`‖q‖² ≤ C·𝒜(q)` for every `q`. -/
private lemma sq_le_fsDen {N : ℕ} {V Ks c a : ℝ}
    (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < a) (hc : 0 ≤ c) (q : E3) :
    ‖q‖ ^ 2 ≤ max (4 * ((N : ℝ) + 1)) (2 * c ^ 2 * V / (Ks * a)) * fsDen N V Ks c a q := by
  rcases le_or_gt (2 * c) ‖q‖ with h2c | h2c
  · -- large `‖q‖`: the kinetic coefficient is at least `‖q‖²/4`
    have hcr : c ≤ ‖q‖ := by linarith
    have hfs : Submission.BoseGases.fsKinCoeff c ‖q‖ = (‖q‖ - c) ^ 2 := by
      simp only [Submission.BoseGases.fsKinCoeff]
      rw [max_eq_left (by linarith)]
    have hhalf : ‖q‖ / 2 ≤ ‖q‖ - c := by linarith
    have hstep : 1 / ((N : ℝ) + 1) * (‖q‖ / 2) ^ 2 ≤ fsDen N V Ks c a q := by
      have h1 : 1 / ((N : ℝ) + 1) * (‖q‖ / 2) ^ 2
          ≤ 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hfs]
        exact pow_le_pow_left₀ (by positivity) hhalf 2
      have h2 : (0 : ℝ) < 2 * Ks * a / V := by positivity
      simp only [fsDen]
      linarith
    have h4 : 4 * ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) * (‖q‖ / 2) ^ 2) = ‖q‖ ^ 2 := by
      have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    calc ‖q‖ ^ 2 = 4 * ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) * (‖q‖ / 2) ^ 2) := h4.symm
      _ ≤ 4 * ((N : ℝ) + 1) * fsDen N V Ks c a q :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ max (4 * ((N : ℝ) + 1)) (2 * c ^ 2 * V / (Ks * a)) * fsDen N V Ks c a q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (fsDen_pos hV hKs ha q).le
  · -- small `‖q‖`: the constant part `2K_s a/V` carries the bound
    have hlt : ‖q‖ ^ 2 < 4 * c ^ 2 := by
      nlinarith [mul_pos (by linarith [norm_nonneg q] : (0 : ℝ) < 2 * c - ‖q‖)
        (by linarith [norm_nonneg q] : (0 : ℝ) < 2 * c + ‖q‖)]
    have hcoef : (2 * c ^ 2 * V / (Ks * a)) * (2 * Ks * a / V) = 4 * c ^ 2 := by
      have h1 : Ks * a ≠ 0 := by positivity
      have h2 : V ≠ 0 := by positivity
      field_simp
      ring
    have hmaxnn : (0 : ℝ) ≤ max (4 * ((N : ℝ) + 1)) (2 * c ^ 2 * V / (Ks * a)) :=
      le_trans (by positivity) (le_max_left _ _)
    have hmono : (2 * c ^ 2 * V / (Ks * a)) * (2 * Ks * a / V)
        ≤ max (4 * ((N : ℝ) + 1)) (2 * c ^ 2 * V / (Ks * a)) * fsDen N V Ks c a q :=
      mul_le_mul (le_max_right _ _) (le_fsDen (N := N) (V := V) (Ks := Ks) (c := c) (a := a))
        (by positivity) hmaxnn
    calc ‖q‖ ^ 2 ≤ 4 * c ^ 2 := le_of_lt hlt
      _ = (2 * c ^ 2 * V / (Ks * a)) * (2 * Ks * a / V) := hcoef.symm
      _ ≤ max (4 * ((N : ℝ) + 1)) (2 * c ^ 2 * V / (Ks * a)) * fsDen N V Ks c a q := hmono

/-- **The domination step.**  If `‖q‖² ≤ C·𝒜(q)` for a constant `C`, then
`𝓑(q)²/(V²𝒜(q))` is integrable as soon as `𝓑(q)²/‖q‖²` is.  (The pointwise domination
`𝓑(q)²/V²/𝒜(q) ≤ (C/V²)·𝓑(q)²/‖q‖²` holds for `q ≠ 0`, and `{0}` is null.) -/
private lemma integrable_of_bound {N : ℕ} {V Ks c a C : ℝ} {𝒲 : E3 → ℝ}
    (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < a)
    (hkey : ∀ q : E3, ‖q‖ ^ 2 ≤ C * fsDen N V Ks c a q)
    (hWint : MeasureTheory.Integrable 𝒲)
    (hfin : MeasureTheory.Integrable (fun q : E3 =>
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) :
    MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2 / fsDen N V Ks c a q) := by
  have hg : MeasureTheory.Integrable (fun q : E3 =>
      (C / V ^ 2) * ((Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) :=
    hfin.const_mul (C / V ^ 2)
  refine hg.mono' ?_ ?_
  · -- measurability: the Fourier transform of `𝒲 ∈ L¹` is continuous
    have hpW : Continuous (fun q : E3 => Submission.BoseGases.pairW 𝒲 q) := by
      have hc1 : Continuous (fun q : E3 =>
          𝓕 (fun x : E3 => (𝒲 x : ℂ)) (((2 * Real.pi : ℝ)⁻¹) • q)) :=
        (continuous_fourier_of_integrable hWint.ofReal).comp (continuous_const_smul _)
      have hc2 : Continuous (fun q : E3 =>
          (𝓕 (fun x : E3 => (𝒲 x : ℂ)) (((2 * Real.pi : ℝ)⁻¹) • q)).re) :=
        Complex.continuous_re.comp hc1
      simpa [Submission.BoseGases.pairW] using hc2
    exact (((hpW.pow 2).div_const (V ^ 2)).div (fsDen_continuous V Ks c a)
      (fun q => (fsDen_pos hV hKs ha q).ne')).aestronglyMeasurable
  · -- a.e. domination, all `q ≠ 0`
    have hne : ∀ᵐ q : E3 ∂(volume : Measure E3), q ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with q hq
    have hnorm : (0 : ℝ) < ‖q‖ ^ 2 := pow_pos (norm_pos_iff.mpr hq) 2
    have hApos : 0 < fsDen N V Ks c a q := fsDen_pos hV hKs ha q
    have hW2 : 0 ≤ (Submission.BoseGases.pairW 𝒲 q) ^ 2 := sq_nonneg _
    have h1 : 1 / fsDen N V Ks c a q ≤ C / ‖q‖ ^ 2 := by
      rw [div_le_div_iff₀ hApos hnorm]
      simpa using hkey q
    have h2 : 0 ≤ (Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2 :=
      div_nonneg hW2 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have hTnn : 0 ≤ (Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2 / fsDen N V Ks c a q :=
      div_nonneg h2 hApos.le
    rw [Real.norm_of_nonneg hTnn]
    calc (Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2 / fsDen N V Ks c a q
        = ((Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2) * (1 / fsDen N V Ks c a q) := by
          ring
      _ ≤ ((Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2) * (C / ‖q‖ ^ 2) := h3
      _ = (C / V ^ 2) * ((Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2) := by ring

theorem intKIntegrable {N : ℕ} {V Ks c a : ℝ}
    {𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < a) (hc : 0 ≤ c)
    (hWint : MeasureTheory.Integrable 𝒲)
    (hfin : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.pairW 𝒲 q) ^ 2 / ‖q‖ ^ 2)) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2 /
        (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
          + 2 * Ks * a / V)) := by
  change MeasureTheory.Integrable (fun q : E3 =>
    (Submission.BoseGases.pairW 𝒲 q) ^ 2 / V ^ 2 / fsDen N V Ks c a q)
  exact integrable_of_bound hV hKs ha (fun q => sq_le_fsDen hV hKs ha hc q) hWint hfin

end Work.BoseFixB1B.pairRung
