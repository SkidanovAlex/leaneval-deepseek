import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.Integral.integral_Ioi_inv_sq_shift
import Submission.Work.BoseKinLoc.Momentum.abs_cubFT_le_prod
import Submission.Work.BoseKinLoc.Momentum.cubFT_fubini
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Totality of the unit-cube Fourier symbol (FS `eq:Q1Qslide`)

`cubFT q = ∫_{Λ(1)} cos ⟪q,x⟫ dx` is the (real form of the) Fourier transform of the unit
cube.  This module proves that its square is integrable on `ℝ³` and that

    `∫ q, (cubFT q)² ≤ 4096`,

with the explicit numerical bound `4096 = 16³` obtained from the momentum weight
`(2 / max 1 |qᵢ|)²`: `abs_cubFT_le_prod` gives `|cubFT q| ≤ ∏ᵢ 2/max(1,|qᵢ|)`, the one
dimensional weight has `∫_ℝ (2/max 1 |t|)² dt = 16` (it equals `4` on `[-1,1]` and `4/t²`
outside), and Fubini for the product measure turns `ℝ³` into the cube of that number.

The lemmas are organised in the order in which they are used:

* `two_div_max_sq_eq`, `two_div_max_sq_le`, `integrable_momW` — the one-dimensional weight;
* `integral_Ioc_momW`, `integral_Ioi_one_momW`, `integral_Ioi_zero_momW`, `integral_momW`
  — its integral, `16`;
* `momW_prod_integral` — Fubini/tonelli on `ℝ³`, giving integrability and the value `4096`;
* `cubFT_stronglyMeasurable` — measurability of `q ↦ cubFT q`;
* `cubFT_sq_le` — the pointwise bound by the product weight.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-! ### The one-dimensional momentum weight `(2 / max 1 |t|)²` -/

/-- The momentum weight is the elementary expression `4 / max 1 t²`. -/
lemma two_div_max_sq_eq (t : ℝ) : (2 / max 1 |t|) ^ 2 = 4 / max 1 (t ^ 2) := by
  rcases le_total |t| 1 with h | h
  · have h2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
    rw [max_eq_left h, max_eq_left h2]
    norm_num
  · have h2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith [h, abs_nonneg t, sq_abs t]
    rw [max_eq_right h, max_eq_right h2]
    rw [div_pow, sq_abs]
    norm_num

/-- The momentum weight is dominated by the integrable function `8/(1+t²)`. -/
lemma two_div_max_sq_le (t : ℝ) : (2 / max 1 |t|) ^ 2 ≤ 8 / (1 + t ^ 2) := by
  have hmax : (1 + t ^ 2) / 2 ≤ max 1 (t ^ 2) := by
    rcases le_total (t ^ 2) 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  have hm : 0 < max 1 (t ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h2 : 0 < (1 + t ^ 2) / 2 := by positivity
  rw [two_div_max_sq_eq, div_eq_mul_inv, div_eq_mul_inv]
  calc 4 * (max 1 (t ^ 2))⁻¹ ≤ 4 * ((1 + t ^ 2) / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ h2 hmax) (by norm_num)
    _ = 8 * (1 + t ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]; ring

/-- The momentum weight is integrable on `ℝ`. -/
lemma integrable_momW : Integrable (fun t : ℝ => (2 / max 1 |t|) ^ 2) := by
  have hbase : Integrable (fun t : ℝ => 8 * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 8
  refine Integrable.mono' hbase ?_ ?_
  · exact (by fun_prop : Measurable (fun t : ℝ => (2 / max 1 |t|) ^ 2)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa [div_eq_mul_inv] using two_div_max_sq_le t

/-! ### The value of the one-dimensional integral -/

/-- On `(0,1]` the weight is the constant `4`. -/
lemma integral_Ioc_momW : (∫ t in Set.Ioc (0 : ℝ) 1, (2 / max 1 |t|) ^ 2) = 4 := by
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (2 / max 1 |t|) ^ 2 = (4 : ℝ) := by
    intro t ht
    have h2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    rw [two_div_max_sq_eq, max_eq_left h2]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, setIntegral_const]
  have hreal : volume.real (Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [Measure.real, Real.volume_Ioc]
    norm_num
  rw [hreal, one_smul]

/-- On `(1,∞)` the weight is `4/t²`, whose integral is `4`. -/
lemma integral_Ioi_one_momW : (∫ t in Set.Ioi (1 : ℝ), (2 / max 1 |t|) ^ 2) = 4 := by
  have hpt : ∀ t ∈ Set.Ioi (1 : ℝ),
      (2 / max 1 |t|) ^ 2 = 4 * ((t - 0)⁻¹ * (t - 0)⁻¹) := by
    intro t ht
    have h2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith [ht.out]
    rw [two_div_max_sq_eq, max_eq_right h2, sub_zero, div_eq_mul_inv, ← inv_pow, pow_two]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Commons.Analysis.Integral.integral_Ioi_inv_sq_shift (c := 0) (T := 1) (by norm_num)]
  norm_num

/-- `∫_{(0,∞)} (2/max 1 |t|)² = 8`. -/
lemma integral_Ioi_zero_momW : (∫ t in Set.Ioi (0 : ℝ), (2 / max 1 |t|) ^ 2) = 8 := by
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    rw [Set.Ioc_union_Ioi (by norm_num : (1 : ℝ) ≤ max 0 1)]
    simp
  rw [← hunion, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      integrable_momW.integrableOn integrable_momW.integrableOn,
    integral_Ioc_momW, integral_Ioi_one_momW]
  norm_num

/-- **The total mass of the momentum weight**: `∫_ℝ (2/max 1 |t|)² dt = 16`. -/
lemma integral_momW : (∫ t : ℝ, (2 / max 1 |t|) ^ 2) = 16 := by
  calc (∫ t : ℝ, (2 / max 1 |t|) ^ 2)
      = 2 * ∫ t in Set.Ioi (0 : ℝ), (2 / max 1 t) ^ 2 :=
        integral_comp_abs (f := fun s : ℝ => (2 / max 1 s) ^ 2)
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), (2 / max 1 |t|) ^ 2 := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [abs_of_pos hx])
    _ = 16 := by rw [integral_Ioi_zero_momW]; norm_num

/-! ### Fubini on `ℝ³` -/

/-- **Tonelli/Fubini for the product weight**: the product weight is integrable on `ℝ³` and
its total mass is the cube of the one-dimensional mass, `16³ = 4096`. -/
lemma momW_prod_integral :
    Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ∏ i, (2 / max 1 |q i|) ^ 2) ∧
      (∫ q : EuclideanSpace ℝ (Fin 3), ∏ i, (2 / max 1 |q i|) ^ 2) = 4096 := by
  constructor
  · have hpi : Integrable (fun y : Fin 3 → ℝ => ∏ i, (2 / max 1 |y i|) ^ 2) volume := by
      rw [MeasureTheory.volume_pi]
      exact Integrable.fintype_prod (μ := fun _ : Fin 3 => (volume : Measure ℝ))
        (f := fun _ : Fin 3 => fun t : ℝ => (2 / max 1 |t|) ^ 2) (fun _ => integrable_momW)
    have hiff := (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      (g := fun q : EuclideanSpace ℝ (Fin 3) => ∏ i, (2 / max 1 |q i|) ^ 2)
    exact hiff.mp (by simpa [Function.comp_def] using hpi)
  · rw [integral_euclidean_prod_real (fun _ : Fin 3 => fun t : ℝ => (2 / max 1 |t|) ^ 2),
      integral_momW, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num

/-! ### Measurability of the cube Fourier symbol -/

/-- `cubFT` is strongly measurable (it is in fact continuous). -/
lemma cubFT_stronglyMeasurable : StronglyMeasurable (cubFT) := by
  have h : StronglyMeasurable
      (fun q : ℝ³ => ∫ x, Real.cos (inner ℝ q x) ∂(volume.restrict (acube 1))) :=
    StronglyMeasurable.integral_prod_right (f := fun (q x : ℝ³) => Real.cos (inner ℝ q x))
      ((Real.continuous_cos.comp continuous_inner).stronglyMeasurable)
  have h2 : (fun q : ℝ³ => ∫ x, Real.cos (inner ℝ q x) ∂(volume.restrict (acube 1)))
      = cubFT := by
    funext q
    rw [cubFT]
  rwa [h2] at h

/-- **The pointwise momentum bound**: `(cubFT q)² ≤ ∏ᵢ (2/max 1 |qᵢ|)²`. -/
lemma cubFT_sq_le (q : EuclideanSpace ℝ (Fin 3)) :
    (cubFT q) ^ 2 ≤ ∏ i : Fin 3, (2 / max 1 |q i|) ^ 2 := by
  calc (cubFT q) ^ 2 = |cubFT q| ^ 2 := (sq_abs _).symm
    _ ≤ (∏ i : Fin 3, 2 / max 1 |q i|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_cubFT_le_prod q) 2
    _ = ∏ i : Fin 3, (2 / max 1 |q i|) ^ 2 := (Finset.prod_pow _ _ _).symm

/-! ### The target -/

theorem cubFT_total :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Momentum.cubFT q) ^ 2) ∧
      ∫ q : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.Momentum.cubFT q) ^ 2 ≤ 4096 := by
  obtain ⟨hGint, hGval⟩ := momW_prod_integral
  constructor
  · refine Integrable.mono' hGint (cubFT_stronglyMeasurable.pow 2).aestronglyMeasurable ?_
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact cubFT_sq_le q
  · have hle := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun q : EuclideanSpace ℝ (Fin 3) => sq_nonneg (cubFT q))
      hGint (Filter.Eventually.of_forall cubFT_sq_le)
    rw [hGval] at hle
    exact hle

end Work.BoseKinLoc.Momentum
