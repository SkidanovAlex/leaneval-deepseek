import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.SmallBoxSliding.Indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open Submission.BoseGases

/-!
# The per-point `u`-integral of the box indicator

For a fixed point `x`, the integral over the position `u` of the small box of
the indicator `boxInd ℓ d u x = 1_{B(u)}(x)` is the indicator of the big box:
the `u`'s for which `x ∈ B(u)` are exactly those for which the small box of
side `ℓd` centred at `(ℓd)•u` covers `x` (given `x ∈ acube ℓ`), and that tube
has volume `1`.

Concretely, for a fixed `x` the map `u ↦ x - a•u` (`a = ℓd`) sends the
Lebesgue measure to `(a³)⁻¹ = |det|⁻¹` times itself (`addHaar_preimage_smul`),
while the relevant preimage of `acube a` is a translate of `acube a`
(measure `a³`); the two factors cancel.
-/

/-- **The `u`-tube has volume `1`.** For `a > 0` and any point `x`, the set of
positions `u` for which the translate-scale `x - a•u` lies in the small cube
`acube a` has Lebesgue measure `1`. -/
lemma boxInd_volume_preimage {a : ℝ} (ha : 0 < a) (x : ℝ³) :
    (volume : Measure ℝ³) {u : ℝ³ | x - a • u ∈ acube a} = 1 := by
  -- rewrite the tube as a (degenerate) rescaling of a translate of the cube
  have hset : {u : ℝ³ | x - a • u ∈ acube a}
      = (fun u : ℝ³ => (-a) • u) ⁻¹' ((fun z : ℝ³ => z + x) ⁻¹' (acube a)) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [sub_eq_add_neg, neg_smul, add_comm x (-(a • u))]
  rw [hset, MeasureTheory.Measure.addHaar_preimage_smul]
  · rw [show Module.finrank ℝ ℝ³ = 3 by simp]
    rw [MeasureTheory.measure_preimage_add_right, acube_volume a (le_of_lt ha)]
    have h3 : ((-a : ℝ)) ^ 3 = -(a ^ 3) := by ring
    rw [h3, abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (a : ℝ) ^ 3)]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) ^ 3)⁻¹)]
    rw [inv_mul_cancel₀ (by positivity : (a : ℝ) ^ 3 ≠ 0), ENNReal.ofReal_one]
  · exact neg_ne_zero.mpr (ne_of_gt ha)

/-- **The `u`-integral of the small-cube indicator is `1`.** -/
lemma boxInd_integral_aux {a : ℝ} (ha : 0 < a) (x : ℝ³) :
    (∫ u : ℝ³, (acube a).indicator (1 : ℝ³ → ℝ) (x - a • u)) = 1 := by
  have hms : MeasurableSet {u : ℝ³ | x - a • u ∈ acube a} :=
    (acube_measurable a).preimage (by fun_prop)
  -- the integrand is the indicator function of the tube
  have hfun : (fun u : ℝ³ => (acube a).indicator (1 : ℝ³ → ℝ) (x - a • u))
      = (fun u : ℝ³ => ({u : ℝ³ | x - a • u ∈ acube a}).indicator (1 : ℝ³ → ℝ) u) := by
    funext u
    by_cases h : x - a • u ∈ acube a
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show u ∈ {u : ℝ³ | x - a • u ∈ acube a} from h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show u ∉ {u : ℝ³ | x - a • u ∈ acube a} from h)]
  rw [hfun, MeasureTheory.integral_indicator_one hms, MeasureTheory.Measure.real_def,
      boxInd_volume_preimage ha x, ENNReal.toReal_one]

/-- **`u`-integral of the box indicator.**  Integrating `boxInd ℓ d u x` over
all positions `u` of the small box recovers the indicator of the big box
`acube ℓ`; the tube of a point `x` has volume `1` (FS's
`∫_u 1_{B(u)}(x) du = 1_{x ∈ acube ℓ}`). -/
theorem boxInd_integral_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u x)
      = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) x := by
  -- pointwise, `boxInd` factorises as the product of the two cube indicators
  have hpt : (fun u : ℝ³ => boxInd ℓ d u x)
      = (fun u : ℝ³ => (acube ℓ).indicator (1 : ℝ³ → ℝ) x *
          (acube (ℓ * d)).indicator (1 : ℝ³ → ℝ) (x - (ℓ * d) • u)) := by
    funext u
    rw [boxInd]
    by_cases h1 : x ∈ acube ℓ
    · by_cases h2 : x - (ℓ * d) • u ∈ acube (ℓ * d)
      · have hmem : x ∈ dlBox ℓ d u := (mem_dlBox_iff ℓ d u x).2 ⟨h1, h2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        simp
      · have hmem : x ∉ dlBox ℓ d u := fun h => h2 ((mem_dlBox_iff ℓ d u x).1 h).2
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
        simp
    · have hmem : x ∉ dlBox ℓ d u := fun h => h1 ((mem_dlBox_iff ℓ d u x).1 h).1
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]
      simp
  rw [hpt, MeasureTheory.integral_const_mul,
      boxInd_integral_aux (mul_pos hℓ hd) x, mul_one]
  rfl

end Work.SmallBoxSliding
