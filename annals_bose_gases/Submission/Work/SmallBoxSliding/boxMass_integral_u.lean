import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.Indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-integral of the true box volume `boxMass`

`boxMass ℓ d u = ∫_x 1_{B(u)}(x) dx` is the true volume of the sliding small
box `B(u) = acube ℓ ∩ ((ℓd)•u + acube(ℓd))`.  This file proves the
normalisation of FS `eq:appsliding`

    ∫_u boxMass ℓ d u = ℓ³ ,

i.e. that averaging the box volume over the sliding centre recovers the volume
of the big box `acube ℓ`.  The mathematical content is that the `u`-tube of a
point has volume `1`: for fixed `x`,

    ∫_u 1_{B(u)}(x) du = 1_{acube ℓ}(x) · |acube 1| = 1_{acube ℓ}(x) ,

after the change of variable `v = (ℓd)⁻¹•x - u` (translation/negation
invariance of Lebesgue measure), followed by Fubini for the nonnegative
integrand (`Integrable` from the finite product measure of the joint support)
and `|acube ℓ| = ℓ³`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

set_option linter.unusedVariables false

/-! ## The scaling identity `acube(ℓd) ↦ acube 1` -/

/-- Scaling a difference of cubes: `x - (ℓd)•u ∈ acube(ℓd)` iff
`(ℓd)⁻¹•x - u ∈ acube 1` (the change of variable that shows the `u`-tube has
volume `|acube 1| = 1`). -/
lemma scaled_mem_acube_iff {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u x : ℝ³) :
    x - (ℓ * d) • u ∈ acube (ℓ * d) ↔ (ℓ * d)⁻¹ • x - u ∈ acube 1 := by
  have hld : (0 : ℝ) < ℓ * d := mul_pos hℓ hd
  have hw : 0 < (ℓ * d)⁻¹ := inv_pos.mpr hld
  rw [mem_acube_iff, mem_acube_iff]
  constructor
  · intro h m
    have hh := h m
    rw [Set.mem_Icc] at hh ⊢
    rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hh
    rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hrw : (ℓ * d)⁻¹ * x.ofLp m - u.ofLp m
        = (ℓ * d)⁻¹ * (x.ofLp m - ℓ * d * u.ofLp m) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hld), one_mul]
    rw [hrw]
    exact ⟨by nlinarith [hh.1, hw, inv_mul_cancel₀ (ne_of_gt hld)],
           by nlinarith [hh.2, hw, inv_mul_cancel₀ (ne_of_gt hld)]⟩
  · intro h m
    have hh := h m
    rw [Set.mem_Icc] at hh ⊢
    rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hh
    rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hrw : (ℓ * d)⁻¹ * x.ofLp m - u.ofLp m
        = (ℓ * d)⁻¹ * (x.ofLp m - ℓ * d * u.ofLp m) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hld), one_mul]
    rw [hrw] at hh
    exact ⟨by nlinarith [hh.1, hh.2, hld, inv_mul_cancel₀ (ne_of_gt hld), mul_pos hw hld],
           by nlinarith [hh.1, hh.2, hld, inv_mul_cancel₀ (ne_of_gt hld), mul_pos hw hld]⟩

/-- Membership in the sliding box in the scaled coordinates. -/
lemma mem_dlBox_iff_scaled {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u x : ℝ³) :
    x ∈ dlBox ℓ d u ↔ x ∈ acube ℓ ∧ (ℓ * d)⁻¹ • x - u ∈ acube 1 := by
  rw [mem_dlBox_iff, scaled_mem_acube_iff hℓ hd u x]

/-! ## Basic measurability and volume facts -/

lemma measurableSet_dlBox (ℓ d : ℝ) (u : ℝ³) : MeasurableSet (dlBox ℓ d u) := by
  have h : dlBox ℓ d u
      = acube ℓ ∩ (fun x : ℝ³ => x - (ℓ * d) • u) ⁻¹' acube (ℓ * d) := by
    ext x; rw [mem_dlBox_iff, Set.mem_inter_iff, Set.mem_preimage]
  rw [h]
  exact (acube_measurable ℓ).inter
    (measurableSet_preimage (by fun_prop) (acube_measurable (ℓ * d)))

lemma dlBox_subset_acube (ℓ d : ℝ) (u : ℝ³) : dlBox ℓ d u ⊆ acube ℓ :=
  fun x hx => (mem_dlBox_iff ℓ d u x).mp hx |>.1

lemma volume_dlBox_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ℝ) (u : ℝ³) :
    (volume : Measure ℝ³) (dlBox ℓ d u) < ⊤ :=
  lt_of_le_of_lt (measure_mono (dlBox_subset_acube ℓ d u)) (acube_lt_top ℓ hℓ.le)

/-- The `u`-tube of a point has volume `1`: the preimage of the unit cube under
the reflection-translation `u ↦ a - u`. -/
lemma volume_preimage_sub_acube_one (a : ℝ³) :
    (volume : Measure ℝ³) ((fun u : ℝ³ => a - u) ⁻¹' acube 1) = 1 := by
  have hmeas : Measurable (fun u : ℝ³ => a - u) := by fun_prop
  rw [← Measure.map_apply hmeas (acube_measurable 1),
      Measure.map_sub_left_eq_self, acube_volume 1 (by norm_num)]
  norm_num

/-! ## `boxMass` as a measure, and its `ENNReal`-isation -/

lemma boxMass_eq_measureReal (ℓ d : ℝ) (u : ℝ³) :
    boxMass ℓ d u = (volume : Measure ℝ³).real (dlBox ℓ d u) := by
  simp only [boxMass, boxInd]
  exact integral_indicator_one (measurableSet_dlBox ℓ d u)

lemma lintegral_ofReal_boxInd (ℓ d : ℝ) (u : ℝ³) :
    (∫⁻ x : ℝ³, ENNReal.ofReal (boxInd ℓ d u x)) = (volume : Measure ℝ³) (dlBox ℓ d u) := by
  have h : (fun x : ℝ³ => ENNReal.ofReal (boxInd ℓ d u x))
      = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    simp only [boxInd]
    by_cases hx : x ∈ dlBox ℓ d u
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
  rw [h]
  exact lintegral_indicator_one (measurableSet_dlBox ℓ d u)

/-- `boxMass` is the `toReal` of the `u`-marginal of the joint `ENNReal`
integrand. -/
lemma ofReal_boxMass_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    ENNReal.ofReal (boxMass ℓ d u) = ∫⁻ x : ℝ³, ENNReal.ofReal (boxInd ℓ d u x) := by
  have hfin : (∫⁻ x : ℝ³, ENNReal.ofReal (boxInd ℓ d u x)) ≠ ⊤ := by
    rw [lintegral_ofReal_boxInd]
    exact ne_of_lt (volume_dlBox_lt_top hℓ d u)
  rw [boxMass_eq_measureReal, Measure.real_def, ← lintegral_ofReal_boxInd ℓ d u]
  exact ENNReal.ofReal_toReal hfin

/-! ## Joint measurability of the `(u,x)`-integrand -/

lemma measurableSet_boxIndSet (ℓ d : ℝ) :
    MeasurableSet {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1} := by
  have h : {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1}
      = (Set.univ ×ˢ acube ℓ)
        ∩ (fun p : ℝ³ × ℝ³ => p.2 - (ℓ * d) • p.1) ⁻¹' acube (ℓ * d) := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, mem_dlBox_iff]
    exact ⟨fun h => ⟨⟨trivial, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  rw [h]
  exact (MeasurableSet.univ.prod (acube_measurable ℓ)).inter
    (measurableSet_preimage (by fun_prop) (acube_measurable (ℓ * d)))

lemma uncurry_ofReal_boxInd_eq_indicator (ℓ d : ℝ) :
    Function.uncurry (fun u x : ℝ³ => ENNReal.ofReal (boxInd ℓ d u x))
      = {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1}.indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext p
  obtain ⟨u, x⟩ := p
  simp only [Function.uncurry_apply_pair]
  by_cases hx : x ∈ dlBox ℓ d u
  · rw [Set.indicator_of_mem (show (u, x) ∈ {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1} from hx)]
    simp only [boxInd, Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem (show (u, x) ∉ {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1} from hx)]
    simp only [boxInd, Set.indicator_of_notMem hx]
    simp

lemma aemeasurable_ofReal_boxInd (ℓ d : ℝ) :
    AEMeasurable (Function.uncurry (fun u x : ℝ³ => ENNReal.ofReal (boxInd ℓ d u x)))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  rw [uncurry_ofReal_boxInd_eq_indicator]
  exact (measurable_const.indicator (measurableSet_boxIndSet ℓ d)).aemeasurable

/-! ## The per-`x` sliding identity -/

/-- The `u`-integral of the box indicator at a point: the sliding partition
`∫_u 1_{B(u)}(x) du = 1_{acube ℓ}(x)` (the `u`-tube of a point has volume `1`). -/
lemma lintegral_boxInd_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (x : ℝ³) :
    (∫⁻ u : ℝ³, ENNReal.ofReal (boxInd ℓ d u x))
      = (acube ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hS : MeasurableSet {u : ℝ³ | x ∈ dlBox ℓ d u} := by
    have he : {u : ℝ³ | x ∈ dlBox ℓ d u}
        = {u : ℝ³ | x ∈ acube ℓ} ∩ (fun u : ℝ³ => (ℓ * d)⁻¹ • x - u) ⁻¹' acube 1 := by
      ext u
      rw [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        mem_dlBox_iff_scaled hℓ hd u x]
    rw [he]
    exact (measurableSet_preimage (measurable_const) (acube_measurable ℓ)).inter
      (measurableSet_preimage (by fun_prop) (acube_measurable 1))
  have hfun : (fun u : ℝ³ => ENNReal.ofReal (boxInd ℓ d u x))
      = {u : ℝ³ | x ∈ dlBox ℓ d u}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext u
    simp only [boxInd]
    by_cases h : x ∈ dlBox ℓ d u
    · have hR : ({u : ℝ³ | x ∈ dlBox ℓ d u}.indicator (fun _ => (1 : ℝ≥0∞))) u = 1 :=
        Set.indicator_of_mem (show u ∈ {u : ℝ³ | x ∈ dlBox ℓ d u} from h) _
      have hL : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem h _
      rw [hR, hL]; simp
    · have hR : ({u : ℝ³ | x ∈ dlBox ℓ d u}.indicator (fun _ => (1 : ℝ≥0∞))) u = 0 :=
        Set.indicator_of_notMem (show u ∉ {u : ℝ³ | x ∈ dlBox ℓ d u} from h) _
      have hL : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem h _
      rw [hR, hL]; simp
  rw [hfun]
  rw [show (∫⁻ u : ℝ³, {u : ℝ³ | x ∈ dlBox ℓ d u}.indicator (fun _ => (1 : ℝ≥0∞)) u)
        = (volume : Measure ℝ³) {u : ℝ³ | x ∈ dlBox ℓ d u} from lintegral_indicator_one hS]
  by_cases hx : x ∈ acube ℓ
  · rw [Set.indicator_of_mem hx]
    have hset : {u : ℝ³ | x ∈ dlBox ℓ d u}
        = (fun u : ℝ³ => (ℓ * d)⁻¹ • x - u) ⁻¹' acube 1 := by
      ext u
      rw [Set.mem_ofPred_eq, Set.mem_preimage, mem_dlBox_iff_scaled hℓ hd u x,
        and_iff_right hx]
    rw [hset, volume_preimage_sub_acube_one]
  · rw [Set.indicator_of_notMem hx]
    have hset : {u : ℝ³ | x ∈ dlBox ℓ d u} = ∅ := by
      ext u
      rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hx ((mem_dlBox_iff ℓ d u x).mp h).1
    rw [hset]
    simp

/-! ## The main theorem -/

theorem boxMass_integral_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxMass ℓ d u) = ℓ ^ 3 := by
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
    (f := fun u x : ℝ³ => ENNReal.ofReal (boxInd ℓ d u x)) (aemeasurable_ofReal_boxInd ℓ d)
  have hinner : (∫⁻ u : ℝ³, ENNReal.ofReal (boxMass ℓ d u))
      = ∫⁻ u : ℝ³, ∫⁻ x : ℝ³, ENNReal.ofReal (boxInd ℓ d u x) :=
    lintegral_congr (fun u => ofReal_boxMass_eq hℓ u)
  have hRHS : (∫⁻ x : ℝ³, ∫⁻ u : ℝ³, ENNReal.ofReal (boxInd ℓ d u x))
      = ENNReal.ofReal (ℓ ^ 3) := by
    rw [show (fun x : ℝ³ => ∫⁻ u : ℝ³, ENNReal.ofReal (boxInd ℓ d u x))
          = fun x : ℝ³ => (acube ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x
        from funext (fun x => lintegral_boxInd_u hℓ hd x)]
    rw [show (∫⁻ x : ℝ³, (acube ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x)
          = (volume : Measure ℝ³) (acube ℓ) from lintegral_indicator_one (acube_measurable ℓ)]
    rw [acube_volume ℓ hℓ.le]
  have hkey : (∫⁻ u : ℝ³, ENNReal.ofReal (boxMass ℓ d u)) = ENNReal.ofReal (ℓ ^ 3) := by
    rw [hinner, hswap, hRHS]
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun u : ℝ³ => boxMass ℓ d u) := by
    filter_upwards with u
    rw [boxMass_eq_measureReal, Measure.real_def]
    exact ENNReal.toReal_nonneg
  have haesm : AEStronglyMeasurable (fun u : ℝ³ => boxMass ℓ d u) (volume : Measure ℝ³) := by
    have hmarg := (aemeasurable_ofReal_boxInd ℓ d).lintegral_prod_right
      (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
    have heqfun : (fun u : ℝ³ => ∫⁻ x : ℝ³, ENNReal.ofReal (boxInd ℓ d u x))
        = fun u : ℝ³ => ENNReal.ofReal (boxMass ℓ d u) :=
      funext (fun u => (ofReal_boxMass_eq hℓ u).symm)
    rw [heqfun] at hmarg
    have h2 := hmarg.ennreal_toReal
    have heq2 : (fun u : ℝ³ => (ENNReal.ofReal (boxMass ℓ d u)).toReal)
        = fun u : ℝ³ => boxMass ℓ d u := by
      funext u
      rw [ENNReal.toReal_ofReal]
      rw [boxMass_eq_measureReal, Measure.real_def]
      exact ENNReal.toReal_nonneg
    rw [heq2] at h2
    exact h2.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg haesm]
  rw [hkey, ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]

end Work.SmallBoxSliding
