import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseKinLoc.Momentum.abs_cubFT_le_prod
import Submission.Work.BoseKinLoc.Momentum.cubFT_deriv_facts
import Submission.Work.BoseKinLoc.Momentum.fderiv_basis_sq_le
import Submission.Work.BoseKinLoc.Momentum.interval_integral_sq_le
import Submission.Work.BoseKinLoc.Momentum.symbol_real_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.symbol_bound`

This module proves the momentum-space bound needed for the sliding localisation of the
kinetic energy (Fournais–Solovej, *The energy of dilute Bose gases*, the proof of
`eq:Q1Qslide`):

    `∫_{‖w‖ > L} (θ̂(w−v) − θ̂(v)θ̂(w))² dw ≤ C ‖v‖² / (‖v‖² + L)`,

with `θ̂ = cubFT` the unit-cube Fourier symbol and `cubeB v w = cubFT (w−v) − cubFT v * cubFT w`
(the "sliding symbol").  The two terms of the pointwise split

    `(θ̂(w−v) − θ̂(v)θ̂(w))² ≤ 2 (θ̂(w−v) − θ̂(w))² + 2 θ̂(w)² (1 − θ̂(v))²`

are responsible for the two regimes of the bound:

* the difference term gains a factor `‖v‖²` from the derivative (`fderiv cubFT`) together with
  the tail bound `hH` (this is the `1/L` of the bound);
* the second term gains `(1 − θ̂(v))² ≤ min 4 (3‖v‖²/8)²` from `hq`, multiplied by the tail
  decay `∫_{‖w‖>L} θ̂(w)² ≤ C₁/L` from `hM`;
* the small-`v` regime is handled by the total mass bound `hTot` and by the crude volume bound
  on the region `{L < ‖w‖ ≤ 2‖v‖}`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The Euclidean three-space of the chapter. -/
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ## 0. Continuity, measurability and integrability of the symbol

The symbol `cubFT` factorises as `∏ᵢ hFT (qᵢ)` (`cubFT_eq_prod_of`, with the 1D factor
`hFT t = ∫_{-1/2}^{1/2} cos (t s) ds`), so it is continuous; the pointwise product bound
`|cubFT q| ≤ ∏ᵢ 2/max 1 |qᵢ|` (`abs_cubFT_le_prod`) then makes `cubFT²` integrable, the
dominating function being `∏ᵢ 8/(1+qᵢ²)`.
-/

/-- The product formula for the cube Fourier symbol. -/
private lemma cubFT_eq_prod (q : E3) : cubFT q = ∏ i : Fin 3, hFT (q i) :=
  cubFT_eq_prod_of chFT_eq_ofReal q

/-- `cubFT` is continuous. -/
private lemma continuous_cubFT : Continuous cubFT := by
  have h : cubFT = fun q : E3 => ∏ i : Fin 3, hFT (q i) := funext cubFT_eq_prod
  rw [h]
  exact continuous_finsetProd Finset.univ (fun i _ =>
    continuous_hFT.comp (by fun_prop : Continuous fun q : E3 => q i))

/-- The dominating weight `∏ᵢ 8/(1+qᵢ²)` is integrable on `ℝ³`. -/
private lemma integrable_weight :
    Integrable (fun q : E3 => ∏ i : Fin 3, 8 * (1 + (q i) ^ 2)⁻¹) volume := by
  have h1 : Integrable (fun y : Fin 3 → ℝ => ∏ i : Fin 3, 8 * (1 + (y i) ^ 2)⁻¹)
      (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) :=
    Integrable.fintype_prod (fun _ => integrable_inv_one_add_sq.const_mul 8)
  have h2 := (PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable h1
  simpa [Function.comp_def] using h2

/-- `(2/max 1 |t|)² ≤ 8/(1+t²)` for every real `t`. -/
private lemma weight_le (t : ℝ) : (2 / max 1 |t|) ^ 2 ≤ 8 * (1 + t ^ 2)⁻¹ := by
  have hM1 : (1 : ℝ) ≤ max 1 |t| := le_max_left _ _
  have hMt : |t| ≤ max 1 |t| := le_max_right _ _
  have hMpos : 0 < max 1 |t| := lt_of_lt_of_le one_pos hM1
  have ht2 : t ^ 2 ≤ (max 1 |t|) ^ 2 := by nlinarith [hMt, abs_nonneg t, sq_abs t]
  have h1 : (1 : ℝ) ≤ (max 1 |t|) ^ 2 := by nlinarith
  have key : 4 * (1 + t ^ 2) ≤ 8 * (max 1 |t|) ^ 2 := by linarith
  have h1t : 0 < 1 + t ^ 2 := by positivity
  rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
    show (8 : ℝ) * (1 + t ^ 2)⁻¹ = 8 / (1 + t ^ 2) by rw [div_eq_mul_inv],
    div_le_div_iff₀ (by positivity) h1t]
  linarith

/-- `(cubFT q)²` is integrable. -/
private lemma integrable_cubFT_sq : Integrable (fun q : E3 => (cubFT q) ^ 2) volume := by
  refine Integrable.mono' integrable_weight (continuous_cubFT.pow 2).aestronglyMeasurable ?_
  filter_upwards with q
  calc ‖(cubFT q) ^ 2‖ = |cubFT q| ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (cubFT q)), sq_abs]
    _ ≤ (∏ i : Fin 3, 2 / max 1 |q i|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_cubFT_le_prod q) 2
    _ = ∏ i : Fin 3, (2 / max 1 |q i|) ^ 2 :=
        (Finset.prod_pow Finset.univ 2 (fun i : Fin 3 => 2 / max 1 |q i|)).symm
    _ ≤ ∏ i : Fin 3, 8 * (1 + (q i) ^ 2)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
        exact weight_le (q i)

/-! ## 1. Translating a set integral and the linearity of the integral -/

/-- Shifting the integration variable in a set integral moves the shift into the set. -/
private lemma setIntegral_sub_shift (s : Set E3) (hs : MeasurableSet s) (f : E3 → ℝ) (v : E3) :
    ∫ w in s, f (w - v) = ∫ z in {z : E3 | z + v ∈ s}, f z := by
  have hms : MeasurableSet {z : E3 | z + v ∈ s} :=
    hs.preimage ((continuous_id.add continuous_const).measurable)
  have hpt : ∀ z : E3, s.indicator (fun w : E3 => f (w - v)) (z + v)
      = ({z : E3 | z + v ∈ s}).indicator f z := by
    intro z
    by_cases hz : z + v ∈ s
    · rw [Set.indicator_of_mem hz (fun w : E3 => f (w - v)),
        Set.indicator_of_mem (show z ∈ {z : E3 | z + v ∈ s} from hz)]
      congr 1
      abel
    · rw [Set.indicator_of_notMem hz (fun w : E3 => f (w - v)),
        Set.indicator_of_notMem (show z ∉ {z : E3 | z + v ∈ s} from hz)]
  calc ∫ w in s, f (w - v)
      = ∫ w, s.indicator (fun w : E3 => f (w - v)) w := (integral_indicator hs).symm
    _ = ∫ w, s.indicator (fun w : E3 => f (w - v)) (w + v) :=
        (integral_add_right_eq_self (μ := (volume : Measure E3))
          (fun w : E3 => s.indicator (fun w : E3 => f (w - v)) w) v).symm
    _ = ∫ w, ({z : E3 | z + v ∈ s}).indicator f w :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => hpt w)
    _ = ∫ z in {z : E3 | z + v ∈ s}, f z := integral_indicator hms

/-- Integrability is invariant under translation. -/
private lemma integrable_sub_shift (f : E3 → ℝ) (hf : Integrable f volume) (v : E3) :
    Integrable (fun w : E3 => f (w - v)) volume :=
  (measurePreserving_add_right (volume : Measure E3) (-v)).integrable_comp_of_integrable hf

/-- Translating the integration variable does not change the integral over all of space. -/
private lemma integral_sub_shift (f : E3 → ℝ) (v : E3) :
    ∫ w : E3, f (w - v) = ∫ w : E3, f w := by
  have h := integral_add_right_eq_self (μ := (volume : Measure E3)) f (-v)
  simpa [sub_eq_add_neg] using h

/-- The exterior region `{q | L < ‖q‖}` is measurable. -/
private lemma tail_measurable (L : ℝ) : MeasurableSet {q : E3 | L < ‖q‖} :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

/-- Linearity of the integral on `2 F + 2 G` (kept as a named lemma so that the integrands
below never have to be compared syntactically). -/
private lemma integral_two_mul_add (F G : E3 → ℝ) (hF : Integrable F volume)
    (hG : Integrable G volume) :
    ∫ w : E3, (2 * F w + 2 * G w) = 2 * (∫ w : E3, F w) + 2 * (∫ w : E3, G w) := by
  have h1 : ∫ w : E3, (2 * F w + 2 * G w) = (∫ w : E3, 2 * F w) + (∫ w : E3, 2 * G w) :=
    integral_add (hF.const_mul 2) (hG.const_mul 2)
  have h2 : (∫ w : E3, 2 * F w) = 2 * (∫ w : E3, F w) := integral_const_mul 2 F
  have h3 : (∫ w : E3, 2 * G w) = 2 * (∫ w : E3, G w) := integral_const_mul 2 G
  rw [h1, h2, h3]

/-! ## 2. The two elementary bounds -/

/-- `(cubFT (w − v) − cubFT w)² ≤ 2 (cubFT (w − v))² + 2 (cubFT w)²`. -/
private lemma diff_sq_le (v w : E3) :
    (cubFT (w - v) - cubFT w) ^ 2 ≤ 2 * (cubFT (w - v)) ^ 2 + 2 * (cubFT w) ^ 2 := by
  nlinarith [sq_nonneg (cubFT (w - v) + cubFT w)]

/-- **Total-mass bound on the difference term**: `∫_{‖w‖>L} (cubFT(w−v) − cubFT w)² ≤ 4C₁`. -/
private lemma diff_le_const (C₁ : ℝ) (hTot : ∫ q : E3, (cubFT q) ^ 2 ≤ C₁)
    (v : E3) (L : ℝ) :
    ∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2 ≤ 4 * C₁ := by
  have hI : Integrable (fun q : E3 => (cubFT q) ^ 2) volume := integrable_cubFT_sq
  have hshift : Integrable (fun w : E3 => (cubFT (w - v)) ^ 2) volume :=
    integrable_sub_shift (fun q : E3 => (cubFT q) ^ 2) hI v
  have hshift_eq : ∫ w : E3, (cubFT (w - v)) ^ 2 = ∫ w : E3, (cubFT w) ^ 2 :=
    integral_sub_shift (fun q : E3 => (cubFT q) ^ 2) v
  have hlin := integral_two_mul_add (fun w : E3 => (cubFT (w - v)) ^ 2)
    (fun w : E3 => (cubFT w) ^ 2) hshift hI
  have hdom : Integrable (fun w : E3 => 2 * (cubFT (w - v)) ^ 2 + 2 * (cubFT w) ^ 2) volume :=
    (hshift.const_mul 2).add (hI.const_mul 2)
  have hdiff : Integrable (fun w : E3 =>
      (cubFT (w - v) - cubFT w) ^ 2) volume :=
    hdom.mono' (((continuous_cubFT.comp (continuous_id.sub continuous_const)).sub
      continuous_cubFT).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact diff_sq_le v w)
  calc ∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2
      ≤ ∫ w : E3, (cubFT (w - v) - cubFT w) ^ 2 :=
        setIntegral_le_integral hdiff (Filter.Eventually.of_forall fun w => sq_nonneg _)
    _ ≤ ∫ w : E3, (2 * (cubFT (w - v)) ^ 2 + 2 * (cubFT w) ^ 2) :=
        integral_mono hdiff hdom (fun w => diff_sq_le v w)
    _ = 2 * (∫ w : E3, (cubFT (w - v)) ^ 2) + 2 * (∫ w : E3, (cubFT w) ^ 2) := hlin
    _ = 2 * (∫ w : E3, (cubFT w) ^ 2) + 2 * (∫ w : E3, (cubFT w) ^ 2) := by rw [hshift_eq]
    _ ≤ 4 * C₁ := by linarith

/-- **Tail bound**: `(1 − cubFT v)² ∫_{‖w‖>L} cubFT(w)² ≤ min 4 (3‖v‖²/8)² * min C₁ (C₁/L)`. -/
private lemma tail_le (C₁ : ℝ)
    (hM : ∀ L : ℝ, 0 < L →
      ∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2 ≤ C₁ / L)
    (hTot : ∫ q : E3, (cubFT q) ^ 2 ≤ C₁)
    (hq : ∀ v : E3, |1 - cubFT v| ≤ min 2 (3 * ‖v‖ ^ 2 / 8))
    (v : E3) (L : ℝ) (hL : 0 < L) :
    (1 - cubFT v) ^ 2 * (∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2)
      ≤ min 4 ((3 * ‖v‖ ^ 2 / 8) ^ 2) * min C₁ (C₁ / L) := by
  have htail : ∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2 ≤ min C₁ (C₁ / L) :=
    le_min (le_trans (setIntegral_le_integral integrable_cubFT_sq
      (Filter.Eventually.of_forall fun w => sq_nonneg _)) hTot) (hM L hL)
  have hpw : (1 - cubFT v) ^ 2 ≤ min 4 ((3 * ‖v‖ ^ 2 / 8) ^ 2) := by
    have h := hq v
    have h2 : |1 - cubFT v| ≤ 2 := le_trans h (min_le_left _ _)
    have h3 : |1 - cubFT v| ≤ 3 * ‖v‖ ^ 2 / 8 := le_trans h (min_le_right _ _)
    refine le_min ?_ ?_
    · nlinarith [h2, abs_nonneg (1 - cubFT v), sq_abs (1 - cubFT v)]
    · nlinarith [h3, abs_nonneg (1 - cubFT v), sq_abs (1 - cubFT v)]
  have hnn : 0 ≤ ∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2 :=
    setIntegral_nonneg (tail_measurable L) fun w _ => sq_nonneg _
  exact mul_le_mul hpw htail hnn (le_min (by norm_num) (by positivity))

/-! ## 3. Integrability of the derivative weights -/

/-- The coordinate derivatives of `cubFT` are dominated by the integrable weight `∏ᵢ 8/(1+qᵢ²)`. -/
private lemma integrable_fderiv_basis_sq (i : Fin 3) :
    Integrable (fun q : E3 => (fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2)
      volume := by
  refine Integrable.mono' integrable_weight
    (((continuous_fderiv_cubFT_apply (Submission.BoseGases.kcStdBasis i)).pow 2).aestronglyMeasurable)
    ?_
  filter_upwards with q
  have h := fderiv_cubFT_basis_abs_le q i
  calc ‖(fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2‖
      = |fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)| ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    _ ≤ (∏ j : Fin 3, 2 / max 1 |q j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = ∏ j : Fin 3, (2 / max 1 |q j|) ^ 2 :=
        (Finset.prod_pow Finset.univ 2 (fun j : Fin 3 => 2 / max 1 |q j|)).symm
    _ ≤ ∏ j : Fin 3, 8 * (1 + (q j) ^ 2)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => ?_)
        exact weight_le (q j)

/-- The sum of the squared coordinate derivatives is integrable. -/
private lemma integrable_sum_fderiv_basis_sq :
    Integrable (fun q : E3 => ∑ i : Fin 3,
      (fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2) volume :=
  integrable_finsetSum Finset.univ fun i _ => integrable_fderiv_basis_sq i

/-- For every direction `h`, the squared directional derivative is integrable. -/
private lemma integrable_fderiv_sq (h : E3) :
    Integrable (fun q : E3 => (fderiv ℝ cubFT q h) ^ 2) volume := by
  have hsum_int : Integrable (fun q : E3 => (3 * ‖h‖ ^ 2) *
      ∑ i : Fin 3, (fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2) volume :=
    (integrable_sum_fderiv_basis_sq.const_mul (3 * ‖h‖ ^ 2))
  refine Integrable.mono' hsum_int (((continuous_fderiv_cubFT_apply h).pow 2).aestronglyMeasurable) ?_
  filter_upwards with q
  have hb := fderiv_basis_sq_le (f := cubFT) q h
  calc ‖(fderiv ℝ cubFT q h) ^ 2‖ = |fderiv ℝ cubFT q h| ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    _ ≤ (‖h‖ ^ 2 * ∑ i : Fin 3,
          (fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2) := by
        rw [sq_abs]; exact hb
    _ ≤ (3 * ‖h‖ ^ 2) * ∑ i : Fin 3,
          (fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2 := by
        have hnn : 0 ≤ ∑ i : Fin 3,
            (fderiv ℝ cubFT q (Submission.BoseGases.kcStdBasis i)) ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        nlinarith [sq_nonneg ‖h‖, norm_nonneg h]

/-- Integrability of the squared difference term. -/
private lemma integrable_diff_sq (v : E3) :
    Integrable (fun w : E3 => (cubFT (w - v) - cubFT w) ^ 2) volume := by
  have hI : Integrable (fun q : E3 => (cubFT q) ^ 2) volume := integrable_cubFT_sq
  have hshift : Integrable (fun w : E3 => (cubFT (w - v)) ^ 2) volume :=
    integrable_sub_shift (fun q : E3 => (cubFT q) ^ 2) hI v
  have hdom : Integrable (fun w : E3 => 2 * (cubFT (w - v)) ^ 2 + 2 * (cubFT w) ^ 2) volume :=
    (hshift.const_mul 2).add (hI.const_mul 2)
  exact hdom.mono' (((continuous_cubFT.comp (continuous_id.sub continuous_const)).sub
    continuous_cubFT).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact diff_sq_le v w)

/-! ## 4. The small-`v` region and the splitting of the exterior integral -/

/-- `(cubeB v w)² ≤ 2 (cubFT (w−v) − cubFT w)² + 2 (1 − cubFT v)² (cubFT w)²`. -/
private lemma cubeB_sq_le (v w : E3) :
    (cubeB v w) ^ 2 ≤ 2 * (cubFT (w - v) - cubFT w) ^ 2
      + 2 * ((1 - cubFT v) ^ 2 * (cubFT w) ^ 2) := by
  have h : cubeB v w = (cubFT (w - v) - cubFT w) + (1 - cubFT v) * cubFT w := by
    rw [cubeB]; ring
  rw [h]
  nlinarith [sq_nonneg ((cubFT (w - v) - cubFT w) - (1 - cubFT v) * cubFT w)]

/-- Linearity of the set integral on `2 F + 2 G`. -/
private lemma setIntegral_two_mul_add (s : Set E3) (F G : E3 → ℝ)
    (hF : IntegrableOn F s volume) (hG : IntegrableOn G s volume) :
    ∫ w in s, (2 * F w + 2 * G w) = 2 * (∫ w in s, F w) + 2 * (∫ w in s, G w) := by
  have h1 : ∫ w in s, (2 * F w + 2 * G w) = (∫ w in s, 2 * F w) + (∫ w in s, 2 * G w) :=
    integral_add (hF.const_mul 2) (hG.const_mul 2)
  have h2 : (∫ w in s, 2 * F w) = 2 * (∫ w in s, F w) := integral_const_mul 2 F
  have h3 : (∫ w in s, 2 * G w) = 2 * (∫ w in s, G w) := integral_const_mul 2 G
  rw [h1, h2, h3]

/-- The exterior integral of the difference term, split into the region `{L < ‖w‖ ≤ 2‖v‖}`
and the region `{L < ‖w‖ ∧ 2‖v‖ < ‖w‖}`. -/
private lemma diff_le_region (C₁ : ℝ) (hTot : ∫ q : E3, (cubFT q) ^ 2 ≤ C₁)
    (v : E3) (L : ℝ) :
    ∫ w in {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖}, (cubFT (w - v) - cubFT w) ^ 2
      ≤ min (256 * ‖v‖ ^ 2 * Real.sqrt (‖v‖ ^ 2)) (4 * C₁) := by
  refine le_min ?_ ?_
  · have hsub : {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖} ⊆ acube (4 * ‖v‖) := by
      intro q hq
      rw [mem_acube_iff]
      intro m
      have h1 : |q m| ≤ ‖q‖ := by
        have h2 : ‖q m‖ ^ 2 ≤ ‖q‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          exact Finset.single_le_sum (f := fun j : Fin 3 => ‖q j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ m)
        rw [Real.norm_eq_abs] at h2
        nlinarith [h2, abs_nonneg (q m), norm_nonneg q]
      have h2 := hq.2
      rw [Set.mem_Icc]
      constructor <;> linarith [abs_le.mp h1]
    have hfinite : volume {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖} ≠ ⊤ := by
      have hle : volume {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖} ≤ volume (acube (4 * ‖v‖)) :=
        measure_mono hsub
      have hne : volume (acube (4 * ‖v‖)) ≠ ⊤ := by
        rw [acube_volume (4 * ‖v‖) (by positivity)]
        exact ENNReal.ofReal_ne_top
      exact ne_top_of_le_ne_top hne hle
    have hvol : (volume {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖}).toReal ≤ (4 * ‖v‖) ^ 3 := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (calc volume {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖}
            ≤ volume (acube (4 * ‖v‖)) := measure_mono hsub
          _ = ENNReal.ofReal ((4 * ‖v‖) ^ 3) := acube_volume _ (by positivity))
      rwa [ENNReal.toReal_ofReal (by positivity)] at h1
    have hpt : ∀ w ∈ {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖},
        (cubFT (w - v) - cubFT w) ^ 2 ≤ (4 : ℝ) := by
      intro w _
      have h1 : |cubFT (w - v)| ≤ 1 := abs_cubFT_le_one _
      have h2 : |cubFT w| ≤ 1 := abs_cubFT_le_one _
      have h3 : |cubFT (w - v) - cubFT w| ≤ 2 := by
        calc |cubFT (w - v) - cubFT w| ≤ |cubFT (w - v)| + |cubFT w| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add h1 h2
          _ = 2 := by norm_num
      nlinarith [h3, abs_nonneg (cubFT (w - v) - cubFT w), sq_abs (cubFT (w - v) - cubFT w)]
    calc ∫ w in {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖}, (cubFT (w - v) - cubFT w) ^ 2
        ≤ ∫ w in {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖}, (4 : ℝ) :=
          setIntegral_mono_of_nonneg (f := fun w : E3 => (cubFT (w - v) - cubFT w) ^ 2)
            (g := fun _ : E3 => (4 : ℝ)) (fun w _ => sq_nonneg _) hpt
            (integrableOn_const (C := (4 : ℝ)) hfinite (by norm_num))
      _ = 4 * (volume {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖}).toReal := by
          rw [setIntegral_const, Measure.real]; simp only [smul_eq_mul]; ring
      _ ≤ 4 * (4 * ‖v‖) ^ 3 := by linarith
      _ = 256 * ‖v‖ ^ 2 * Real.sqrt (‖v‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg v)]; ring
  · have hsub : {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖} ⊆ {q : E3 | L < ‖q‖} :=
      fun q hq => hq.1
    refine le_trans (setIntegral_mono_set (integrable_diff_sq v).integrableOn
      (Filter.Eventually.of_forall fun w => sq_nonneg _) ?_) (diff_le_const C₁ hTot v L)
    exact Filter.Eventually.of_forall fun w hw => hsub hw

/-! ## 5. Assembling the exterior integral and the final bound -/

/-- Shifting the variable in a set `∫⁻`. -/
private lemma lintegral_sub_shift (s : Set E3) (hs : MeasurableSet s) (f : E3 → ℝ≥0∞)
    (v : E3) :
    ∫⁻ w in s, f (w - v) = ∫⁻ z in {z : E3 | z + v ∈ s}, f z := by
  have hms : MeasurableSet {z : E3 | z + v ∈ s} :=
    hs.preimage ((continuous_id.add continuous_const).measurable)
  have hpt : ∀ z : E3, s.indicator (fun w : E3 => f (w - v)) (z + v)
      = ({z : E3 | z + v ∈ s}).indicator f z := by
    intro z
    by_cases hz : z + v ∈ s
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (show z ∈ {z : E3 | z + v ∈ s} from hz)]
      congr 1
      abel
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (show z ∉ {z : E3 | z + v ∈ s} from hz)]
  calc ∫⁻ w in s, f (w - v)
      = ∫⁻ w, s.indicator (fun w : E3 => f (w - v)) w :=
        (lintegral_indicator hs _).symm
    _ = ∫⁻ w, s.indicator (fun w : E3 => f (w - v)) (w + v) :=
        (lintegral_add_right_eq_self
          (fun w : E3 => s.indicator (fun w : E3 => f (w - v)) w) v).symm
    _ = ∫⁻ w, ({z : E3 | z + v ∈ s}).indicator f w := lintegral_congr fun w => hpt w
    _ = ∫⁻ z in {z : E3 | z + v ∈ s}, f z := lintegral_indicator hms f

/-- For a nonnegative function integrable on `s`: `∫⁻_s ofReal ∘ f = ofReal (∫_s f)`. -/
private lemma lintegral_ofReal_eq_ofReal_integral {s : Set E3} {f : E3 → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hint : IntegrableOn f s volume) :
    (∫⁻ x in s, ENNReal.ofReal (f x)) = ENNReal.ofReal (∫ x in s, f x) := by
  have hfin : (∫⁻ x in s, ENNReal.ofReal (f x)) < ∞ := hint.lintegral_lt_top
  rw [← ENNReal.ofReal_toReal (ne_of_lt hfin)]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf) hint.1).symm

/-- **The exterior bound on the difference term** in the region `{2‖v‖ < ‖w‖}`: the fundamental
theorem of calculus turns the difference into an integral of the directional derivative, and the
`L²`-average of the latter is controlled by the tail bound `hH`. -/
private lemma diff_tail_bound (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hH : ∀ R : ℝ, 0 < R → ∑ i : Fin 3,
      ∫ w in {q : E3 | R < ‖q‖},
        (fderiv ℝ cubFT w (Submission.BoseGases.kcStdBasis i)) ^ 2 ≤ C₁ / R)
    (v : E3) (L : ℝ) (hL : 0 < L) :
    ∫ w in {q : E3 | L < ‖q‖ ∧ 2 * ‖v‖ < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2
      ≤ 2 * C₁ * ‖v‖ ^ 2 / L := by
  set s : Set E3 := {q : E3 | L < ‖q‖ ∧ 2 * ‖v‖ < ‖q‖} with hs
  have hsmeas : MeasurableSet s :=
    (tail_measurable L).inter (isOpen_lt continuous_const continuous_norm).measurableSet
  have hGint : Integrable (fun z : E3 => ∑ i : Fin 3,
      (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2) volume :=
    integrable_sum_fderiv_basis_sq
  have hGnn : ∀ z : E3, 0 ≤ ∑ i : Fin 3,
      (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2 :=
    fun z => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the Cauchy–Schwarz bound on the difference, for every `w`
  have hcs : ∀ w : E3, (cubFT (w - v) - cubFT w) ^ 2
      ≤ ∫ t in (0:ℝ)..1, (fderiv ℝ cubFT (w - t • v) (-v)) ^ 2 := by
    intro w
    rw [cubFT_sub_eq_integral_fderiv w v]
    exact interval_integral_sq_le (fun t : ℝ => fderiv ℝ cubFT (w - t • v) (-v))
      ((continuous_fderiv_cubFT_along w v).intervalIntegrable 0 1)
      (((continuous_fderiv_cubFT_along w v).pow 2).intervalIntegrable 0 1)
  -- the tail bound for the sum of the squared coordinate derivatives
  have hTailInt : ∫ z in {q : E3 | L / 2 < ‖q‖}, ∑ i : Fin 3,
      (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2 ≤ C₁ / (L / 2) := by
    rw [integral_finsetSum]
    · exact hH (L / 2) (by linarith)
    · intro i _
      exact (integrable_fderiv_basis_sq i).integrableOn
  have hTail : (∫⁻ z in {q : E3 | L / 2 < ‖q‖}, ENNReal.ofReal
      (∑ i : Fin 3, (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2))
      ≤ ENNReal.ofReal (C₁ / (L / 2)) := by
    rw [lintegral_ofReal_eq_ofReal_integral hGnn hGint.integrableOn]
    exact ENNReal.ofReal_le_ofReal hTailInt
  -- the lintegral chain
  have key : (∫⁻ w in s, ENNReal.ofReal ((cubFT (w - v) - cubFT w) ^ 2))
      ≤ ENNReal.ofReal (‖v‖ ^ 2 * (C₁ / (L / 2))) := by
    calc (∫⁻ w in s, ENNReal.ofReal ((cubFT (w - v) - cubFT w) ^ 2))
        ≤ ∫⁻ w in s, ENNReal.ofReal (∫ t in (0:ℝ)..1,
            (fderiv ℝ cubFT (w - t • v) (-v)) ^ 2) :=
          lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hcs w)
      _ ≤ ∫⁻ w in s, ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
            ((fderiv ℝ cubFT (w - t • v) (-v)) ^ 2) := by
          refine lintegral_mono fun w => ?_
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
          calc ENNReal.ofReal (∫ t in Set.Ioc (0:ℝ) 1,
                (fderiv ℝ cubFT (w - t • v) (-v)) ^ 2)
              = ENNReal.ofReal ((∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
                  ((fderiv ℝ cubFT (w - t • v) (-v)) ^ 2)).toReal) := by
                congr 1
                exact (integral_eq_lintegral_of_nonneg_ae
                  (μ := (volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1))
                  (Filter.Eventually.of_forall fun t => sq_nonneg _)
                  (((continuous_fderiv_cubFT_along w v).pow 2).aestronglyMeasurable))
            _ ≤ _ := ENNReal.ofReal_toReal_le
      _ = ∫⁻ t in Set.Ioc (0:ℝ) 1, ∫⁻ w in s, ENNReal.ofReal
            ((fderiv ℝ cubFT (w - t • v) (-v)) ^ 2) := by
          symm
          refine lintegral_lintegral_swap ?_
          refine ENNReal.continuous_ofReal.comp
            (((continuous_fderiv_cubFT_apply (-v)).comp ?_).pow 2) |>.aemeasurable
          exact continuous_snd.sub (continuous_fst.smul continuous_const)
      _ ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (‖v‖ ^ 2)
            * (∫⁻ z in {q : E3 | L / 2 < ‖q‖}, ENNReal.ofReal (∑ i : Fin 3,
              (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2)) := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' measurableSet_Ioc]
          filter_upwards with t ht
          have ht1 : |t| ≤ 1 := by
            rw [abs_of_pos ht.1]
            exact ht.2
          have htv : ‖t • v‖ ≤ ‖v‖ := by
            rw [norm_smul]
            exact mul_le_of_le_one_left (norm_nonneg v) ht1
          have hpt : ∀ w : E3, (fderiv ℝ cubFT (w - t • v) (-v)) ^ 2
              ≤ ‖v‖ ^ 2 * ∑ i : Fin 3,
                (fderiv ℝ cubFT (w - t • v) (Submission.BoseGases.kcStdBasis i)) ^ 2 := by
            intro w
            have h := fderiv_basis_sq_le (f := cubFT) (w - t • v) (-v)
            rwa [norm_neg] at h
          calc (∫⁻ w in s, ENNReal.ofReal ((fderiv ℝ cubFT (w - t • v) (-v)) ^ 2))
              ≤ ∫⁻ w in s, ENNReal.ofReal (‖v‖ ^ 2 * ∑ i : Fin 3,
                  (fderiv ℝ cubFT (w - t • v) (Submission.BoseGases.kcStdBasis i)) ^ 2) :=
                lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hpt w)
            _ = ENNReal.ofReal (‖v‖ ^ 2) * ∫⁻ w in s, ENNReal.ofReal (∑ i : Fin 3,
                  (fderiv ℝ cubFT (w - t • v) (Submission.BoseGases.kcStdBasis i)) ^ 2) := by
                rw [show (fun w : E3 => ENNReal.ofReal (‖v‖ ^ 2 * ∑ i : Fin 3,
                      (fderiv ℝ cubFT (w - t • v) (Submission.BoseGases.kcStdBasis i)) ^ 2))
                    = (fun w : E3 => ENNReal.ofReal (‖v‖ ^ 2) * ENNReal.ofReal (∑ i : Fin 3,
                      (fderiv ℝ cubFT (w - t • v) (Submission.BoseGases.kcStdBasis i)) ^ 2)) from
                    funext fun w => ENNReal.ofReal_mul (by positivity)]
                exact lintegral_const_mul (ENNReal.ofReal (‖v‖ ^ 2))
                  ((ENNReal.continuous_ofReal.comp
                    (continuous_finsetSum Finset.univ (fun i _ =>
                      (((continuous_fderiv_cubFT_apply
                          (Submission.BoseGases.kcStdBasis i)).comp
                        (continuous_id.sub
                          (continuous_const : Continuous fun _ : E3 => t • v))).pow 2)))).measurable)
            _ ≤ ENNReal.ofReal (‖v‖ ^ 2) * (∫⁻ z in {q : E3 | L / 2 < ‖q‖},
                  ENNReal.ofReal (∑ i : Fin 3,
                    (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                have hcont : {z : E3 | z + t • v ∈ s} ⊆ {q : E3 | L / 2 < ‖q‖} := by
                  intro z hz
                  rw [hs] at hz
                  simp only [Set.mem_setOf_eq] at hz ⊢
                  have h1 : 2 * ‖v‖ < ‖z + t • v‖ := hz.2
                  have h2 : ‖z + t • v‖ - ‖t • v‖ ≤ ‖z‖ := by
                    have h := abs_norm_sub_norm_le (z + t • v) z
                    rw [add_sub_cancel_left] at h
                    have h' := abs_le.mp h
                    linarith [h'.1]
                  have h3 : L < ‖z + t • v‖ := hz.1
                  nlinarith [h1, h2, h3, htv, norm_nonneg (t • v), norm_nonneg v]
                rw [lintegral_sub_shift s hsmeas
                  (fun z : E3 => ENNReal.ofReal (∑ i : Fin 3,
                    (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2)) (t • v)]
                exact lintegral_mono_set hcont
      _ = ENNReal.ofReal (‖v‖ ^ 2) * (∫⁻ z in {q : E3 | L / 2 < ‖q‖}, ENNReal.ofReal
            (∑ i : Fin 3, (fderiv ℝ cubFT z (Submission.BoseGases.kcStdBasis i)) ^ 2)) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc,
            show (1 : ℝ) - 0 = 1 by norm_num, ENNReal.ofReal_one, mul_one]
      _ ≤ ENNReal.ofReal (‖v‖ ^ 2) * ENNReal.ofReal (C₁ / (L / 2)) :=
          mul_le_mul_of_nonneg_left hTail (by positivity)
      _ = ENNReal.ofReal (‖v‖ ^ 2 * (C₁ / (L / 2))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  -- back to the Bochner integral
  have hnonneg : (0 : E3 → ℝ) ≤ fun w => (cubFT (w - v) - cubFT w) ^ 2 :=
    fun w => sq_nonneg _
  calc ∫ w in s, (cubFT (w - v) - cubFT w) ^ 2
      = (∫⁻ w in s, ENNReal.ofReal ((cubFT (w - v) - cubFT w) ^ 2)).toReal :=
        (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
          (((continuous_cubFT.comp (continuous_id.sub continuous_const)).sub
            continuous_cubFT).pow 2).aestronglyMeasurable)
    _ ≤ (ENNReal.ofReal (‖v‖ ^ 2 * (C₁ / (L / 2)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = 2 * C₁ * ‖v‖ ^ 2 / L := by
        rw [ENNReal.toReal_ofReal (by positivity)]
        field_simp

/-- The exterior integral of the difference term, in the form consumed by the scalar
assembly `symbol_real_assembly`. -/
private lemma diff_le_tail_form (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hTot : ∫ q : E3, (cubFT q) ^ 2 ≤ C₁)
    (hH : ∀ R : ℝ, 0 < R → ∑ i : Fin 3,
      ∫ w in {q : E3 | R < ‖q‖},
        (fderiv ℝ cubFT w (Submission.BoseGases.kcStdBasis i)) ^ 2 ≤ C₁ / R)
    (v : E3) (L : ℝ) (hL : 0 < L) :
    ∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2
      ≤ 2 * C₁ * ‖v‖ ^ 2 / L
        + (if L < 2 * Real.sqrt (‖v‖ ^ 2) then
            min (256 * ‖v‖ ^ 2 * Real.sqrt (‖v‖ ^ 2)) (4 * C₁) else 0) := by
  set R1 : Set E3 := {q : E3 | L < ‖q‖ ∧ ‖q‖ ≤ 2 * ‖v‖} with hR1
  set R2 : Set E3 := {q : E3 | L < ‖q‖ ∧ 2 * ‖v‖ < ‖q‖} with hR2
  have hmeas1 : MeasurableSet R1 :=
    (tail_measurable L).inter (isClosed_le continuous_norm continuous_const).measurableSet
  have hmeas2 : MeasurableSet R2 :=
    (tail_measurable L).inter (isOpen_lt continuous_const continuous_norm).measurableSet
  have hunion : {q : E3 | L < ‖q‖} = R1 ∪ R2 := by
    ext q
    simp only [hR1, hR2, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      rcases lt_or_ge (2 * ‖v‖) ‖q‖ with h' | h'
      · exact Or.inr ⟨h, h'⟩
      · exact Or.inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint R1 R2 := by
    rw [Set.disjoint_left]
    intro q h1 h2
    simp only [hR1, hR2, Set.mem_setOf_eq] at h1 h2
    linarith [h1.2, h2.2]
  have hsplit_int : ∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2
      = (∫ w in R1, (cubFT (w - v) - cubFT w) ^ 2)
        + (∫ w in R2, (cubFT (w - v) - cubFT w) ^ 2) := by
    rw [hunion]
    exact setIntegral_union hdisj hmeas2 (integrable_diff_sq v).integrableOn
      (integrable_diff_sq v).integrableOn
  have hA1 : ∫ w in R1, (cubFT (w - v) - cubFT w) ^ 2
      ≤ min (256 * ‖v‖ ^ 2 * Real.sqrt (‖v‖ ^ 2)) (4 * C₁) := by
    rw [hR1]
    exact diff_le_region C₁ hTot v L
  have hA2 : ∫ w in R2, (cubFT (w - v) - cubFT w) ^ 2 ≤ 2 * C₁ * ‖v‖ ^ 2 / L := by
    rw [hR2]
    exact diff_tail_bound C₁ hC₁ hH v L hL
  rw [hsplit_int]
  by_cases hcase : L < 2 * Real.sqrt (‖v‖ ^ 2)
  · rw [if_pos hcase]
    linarith [hA1, hA2]
  · rw [if_neg hcase]
    have hempty : R1 = ∅ := by
      ext q
      simp only [hR1, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      intro hq2
      have hle : 2 * Real.sqrt (‖v‖ ^ 2) ≤ L := le_of_not_gt hcase
      rw [Real.sqrt_sq (norm_nonneg v)] at hle
      linarith [hq2]
    rw [hempty, setIntegral_empty, zero_add, add_zero]
    exact hA2

theorem symbol_bound (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hM : ∀ L : ℝ, 0 < L →
      ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, (cubFT w) ^ 2 ≤ C₁ / L)
    (hTot : ∫ q : EuclideanSpace ℝ (Fin 3), (cubFT q) ^ 2 ≤ C₁)
    (hH : ∀ L : ℝ, 0 < L → ∑ i : Fin 3,
      ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖},
        (fderiv ℝ cubFT w (Submission.BoseGases.kcStdBasis i)) ^ 2 ≤ C₁ / L)
    (hq : ∀ v : EuclideanSpace ℝ (Fin 3), |1 - cubFT v| ≤ min 2 (3 * ‖v‖ ^ 2 / 8)) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : EuclideanSpace ℝ (Fin 3), ∀ L : ℝ, 0 < L →
      ∫ w in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, (cubeB v w) ^ 2 ≤
        C * ‖v‖ ^ 2 / (‖v‖ ^ 2 + L) := by
  refine ⟨20000 * (C₁ + 1), by positivity, ?_⟩
  intro v L hL
  set u : ℝ := ‖v‖ ^ 2 with hu
  set A : ℝ := ∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2 with hA
  set B : ℝ := (1 - cubFT v) ^ 2 * (∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2) with hB
  set I : ℝ := ∫ w in {q : E3 | L < ‖q‖}, (cubeB v w) ^ 2 with hI
  have hsplit : I ≤ 2 * A + 2 * B := by
    have hpt : ∀ w ∈ ({q : E3 | L < ‖q‖} : Set E3), (cubeB v w) ^ 2
        ≤ 2 * (cubFT (w - v) - cubFT w) ^ 2 + 2 * ((1 - cubFT v) ^ 2 * (cubFT w) ^ 2) :=
      fun w _ => cubeB_sq_le v w
    have hInt : IntegrableOn (fun w : E3 => 2 * (cubFT (w - v) - cubFT w) ^ 2
        + 2 * ((1 - cubFT v) ^ 2 * (cubFT w) ^ 2)) {q : E3 | L < ‖q‖} volume :=
      (((integrable_diff_sq v).const_mul 2).add
        ((integrable_cubFT_sq.const_mul ((1 - cubFT v) ^ 2)).const_mul 2)).integrableOn
    have h1 := setIntegral_mono_of_nonneg (f := fun w : E3 => (cubeB v w) ^ 2)
      (g := fun w : E3 => 2 * (cubFT (w - v) - cubFT w) ^ 2
        + 2 * ((1 - cubFT v) ^ 2 * (cubFT w) ^ 2)) (fun w _ => sq_nonneg _) hpt hInt
    have h2 := setIntegral_two_mul_add {q : E3 | L < ‖q‖}
      (fun w : E3 => (cubFT (w - v) - cubFT w) ^ 2)
      (fun w : E3 => (1 - cubFT v) ^ 2 * (cubFT w) ^ 2)
      (integrable_diff_sq v).integrableOn (integrable_cubFT_sq.const_mul _).integrableOn
    have h3 : (∫ w in {q : E3 | L < ‖q‖}, (1 - cubFT v) ^ 2 * (cubFT w) ^ 2)
        = (1 - cubFT v) ^ 2 * (∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2) :=
      integral_const_mul ((1 - cubFT v) ^ 2) (fun w : E3 => (cubFT w) ^ 2)
    rw [hI, hA, hB]
    calc ∫ w in {q : E3 | L < ‖q‖}, (cubeB v w) ^ 2
        ≤ ∫ w in {q : E3 | L < ‖q‖}, (2 * (cubFT (w - v) - cubFT w) ^ 2
            + 2 * ((1 - cubFT v) ^ 2 * (cubFT w) ^ 2)) := h1
      _ = 2 * (∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2)
          + 2 * (∫ w in {q : E3 | L < ‖q‖}, (1 - cubFT v) ^ 2 * (cubFT w) ^ 2) := h2
      _ = 2 * (∫ w in {q : E3 | L < ‖q‖}, (cubFT (w - v) - cubFT w) ^ 2)
          + 2 * ((1 - cubFT v) ^ 2 * (∫ w in {q : E3 | L < ‖q‖}, (cubFT w) ^ 2)) := by
          rw [h3]
  have hA1 : A ≤ 4 * C₁ := by
    rw [hA]; exact diff_le_const C₁ hTot v L
  have hA2 : A ≤ 2 * C₁ * u / L
      + (if L < 2 * Real.sqrt u then min (256 * u * Real.sqrt u) (4 * C₁) else 0) := by
    rw [hA, hu]
    exact diff_le_tail_form C₁ hC₁ hTot hH v L hL
  have hB' : B ≤ min 4 ((3 * u / 8) ^ 2) * min C₁ (C₁ / L) := by
    rw [hB, hu]
    exact tail_le C₁ hM hTot hq v L hL
  have hres := symbol_real_assembly C₁ u L A B I hC₁ (by rw [hu]; positivity) hL
    hsplit hA1 hA2 hB'
  rw [hI, hu] at hres
  exact hres

end Work.BoseKinLoc.Momentum
