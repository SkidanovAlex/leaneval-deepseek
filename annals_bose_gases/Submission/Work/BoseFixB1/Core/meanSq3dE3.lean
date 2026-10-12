import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1S.MeanSq.Box3
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core

open MeasureTheory
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Coordinate form of `acube ℓ`: the pushforward of `slBig ℓ` under `WithLp.toLp 2`. -/
lemma toLp_mem_acube_iff {ℓ : ℝ} (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y ∈ Submission.BoseGases.acube ℓ ↔ y ∈ Work.BoseFixB1S.slBig ℓ := by
  rw [Submission.BoseGases.mem_acube_iff, Work.BoseFixB1S.mem_slBig]

/-- Coordinate form of `dlBox ℓ d u`: the pushforward of `slBox ℓ (ℓ*d) u.ofLp`. -/
lemma toLp_mem_dlBox_iff {ℓ d : ℝ} (y : Fin 3 → ℝ) (u : E3) :
    WithLp.toLp 2 y ∈ Submission.BoseGases.dlBox ℓ d u ↔
      y ∈ Work.BoseFixB1S.slBox ℓ (ℓ * d) u.ofLp := by
  rw [Submission.BoseGases.mem_dlBox_iff, Submission.BoseGases.mem_acube_iff,
    Work.BoseFixB1S.mem_slBox]
  constructor
  · rintro ⟨h1, h2⟩ j
    rw [Work.BoseFixB1S.slI_eq, Set.mem_inter_iff, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h1j := h1 j
      simp only [Set.mem_Icc] at h1j
      exact h1j
    · rw [Set.mem_Icc]
      have h2j := h2
      rw [Submission.BoseGases.mem_acube_iff] at h2j
      have h2jj := h2j j
      simp only [Set.mem_Icc] at h2jj
      have hcoord : (WithLp.toLp 2 y - (ℓ * d) • u).ofLp j = y j - ℓ * d * u.ofLp j := by
        rw [PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
      rw [hcoord] at h2jj
      exact ⟨by linarith [h2jj.1], by linarith [h2jj.2]⟩
  · intro h
    refine ⟨fun m => ?_, ?_⟩
    · have hm := h m
      rw [Work.BoseFixB1S.slI_eq, Set.mem_inter_iff, Set.mem_Icc] at hm
      simp only [Set.mem_Icc]
      exact hm.1
    · rw [Submission.BoseGases.mem_acube_iff]
      intro j
      have hj := h j
      rw [Work.BoseFixB1S.slI_eq, Set.mem_inter_iff, Set.mem_Icc] at hj
      simp only [Set.mem_Icc]
      have hcoord : (WithLp.toLp 2 y - (ℓ * d) • u).ofLp j = y j - ℓ * d * u.ofLp j := by
        rw [PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
      rw [hcoord]
      exact ⟨by linarith [hj.2.1], by linarith [hj.2.2]⟩

/-- The volume of `dlBox ℓ d u` equals that of its coordinate model `slBox ℓ (ℓ*d) u.ofLp`. -/
lemma volume_dlBox_eq (ℓ d : ℝ) (u : E3) :
    volume (Submission.BoseGases.dlBox ℓ d u) =
      volume (Work.BoseFixB1S.slBox ℓ (ℓ * d) u.ofLp) := by
  have hpre : WithLp.toLp 2 ⁻¹' (Submission.BoseGases.dlBox ℓ d u)
      = Work.BoseFixB1S.slBox ℓ (ℓ * d) u.ofLp := by
    ext y
    rw [Set.mem_preimage, toLp_mem_dlBox_iff]
  rw [← hpre, MeasureTheory.MeasurePreserving.measure_preimage
    (PiLp.volume_preserving_toLp (Fin 3))
    (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u).nullMeasurableSet]

/-- **The `EuclideanSpace ℝ (Fin 3)` transport of the three-dimensional sliding-box
mean-square bound.**

`Submission.BoseGases.dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` is, in coordinates, the
product `Work.BoseFixB1S.slBox ℓ (ℓ*d) u.ofLp` of the one-dimensional sliding intervals
`Work.BoseFixB1S.slI ℓ (ℓ*d) (u j)` (`toLp_mem_dlBox_iff` in
`Submission/Work/BoseFixB1S/MeanSq/E3Box.lean`), and `acube ℓ` is `Work.BoseFixB1S.slBig ℓ`
(`toLp_mem_acube_iff`); the measure on `EuclideanSpace ℝ (Fin 3)` is the
pushforward of the product measure under `WithLp.toLp 2` (`PiLp.volume_preserving_toLp`).  Hence
the coordinate-space bound `H3` (taken here as a hypothesis, to be instantiated later by the
`Fin 3 → ℝ` tensorisation) transports verbatim.

USEFUL EXISTING MATERIAL: `Submission/Work/BoseFixB1S/MeanSq/E3Box.lean` contains a *complete*
proof of exactly this statement with the coordinate-space instance of `H3` called at its last
line; adapt that proof (the only change is replacing the call
`meanSq3d (by positivity) (by nlinarith [hd1, hℓ]) hFmeas` by
`H3 (by positivity) (by nlinarith [hd1, hℓ]) hFmeas`), together with `volume_dlBox_eq`,
`toLp_mem_dlBox_iff`, `toLp_mem_acube_iff`.  END OF HINT. -/
theorem meanSq3dE3 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (H3 : ∀ {ℓ' h : ℝ}, 0 < h → h ≤ ℓ' → ∀ F : (Fin 3 → ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ u : Fin 3 → ℝ,
          ((∫⁻ y in Work.BoseFixB1S.slBox ℓ' h u, F y)
            / (volume (Work.BoseFixB1S.slBox ℓ' h u))) ^ 2
        ≤ ENNReal.ofReal ((30 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ', (F y) ^ 2)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞} (hW : Measurable W) :
    ∫⁻ u : EuclideanSpace ℝ (Fin 3),
        ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / (volume (Submission.BoseGases.dlBox ℓ d u))) ^ 2
      ≤ ENNReal.ofReal ((30 / (ℓ * d)) ^ 3) * ∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2 := by
  classical
  set F : (Fin 3 → ℝ) → ℝ≥0∞ := fun y => W (WithLp.toLp 2 y) with hFdef
  have hFmeas : Measurable F := hW.comp (by fun_prop)
  -- measurability of the integrand on `E3`
  have hset : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
      p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} :=
    Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d
  have hjoint : Measurable (Function.uncurry (fun (u : EuclideanSpace ℝ (Fin 3))
      (x : EuclideanSpace ℝ (Fin 3)) =>
      (Submission.BoseGases.dlBox ℓ d u).indicator W x)) := by
    have hEq : Function.uncurry (fun (u : EuclideanSpace ℝ (Fin 3))
        (x : EuclideanSpace ℝ (Fin 3)) =>
        (Submission.BoseGases.dlBox ℓ d u).indicator W x)
        = {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
            p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
            (fun p => W p.2) := by
      funext p
      obtain ⟨u, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
      · rw [Set.indicator_of_mem hx,
          Set.indicator_of_mem (show (u, x) ∈ {p : EuclideanSpace ℝ (Fin 3) ×
            EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show (u, x) ∉ {p : EuclideanSpace ℝ (Fin 3) ×
            EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    rw [hEq]
    exact (hW.comp measurable_snd).indicator hset
  have hnum : Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      ∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x) := by
    have h := Measurable.lintegral_prod_right
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hjoint
    convert h using 2 with u
    exact (MeasureTheory.lintegral_indicator
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) W).symm
  have hvol : Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      volume (Submission.BoseGases.dlBox ℓ d u)) := by
    have hjoint1 : Measurable (Function.uncurry (fun (u : EuclideanSpace ℝ (Fin 3))
        (x : EuclideanSpace ℝ (Fin 3)) =>
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
      have hEq : Function.uncurry (fun (u : EuclideanSpace ℝ (Fin 3))
          (x : EuclideanSpace ℝ (Fin 3)) =>
          (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ≥0∞)) x)
          = {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
              p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
              (fun _ => (1 : ℝ≥0∞)) := by
        funext p
        obtain ⟨u, x⟩ := p
        simp only [Function.uncurry_apply_pair]
        by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem hx,
            Set.indicator_of_mem (show (u, x) ∈ {p : EuclideanSpace ℝ (Fin 3) ×
              EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (show (u, x) ∉ {p : EuclideanSpace ℝ (Fin 3) ×
              EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      rw [hEq]
      exact measurable_const.indicator hset
    have h := Measurable.lintegral_prod_right
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hjoint1
    convert h using 2 with u
    exact (lintegral_indicator_one (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)).symm
  have hmeas : Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
        / (volume (Submission.BoseGases.dlBox ℓ d u)))^2) :=
    Measurable.pow_const (hnum.div hvol) 2
  -- transfer the left-hand side to `Fin 3 → ℝ`
  rw [← MeasureTheory.MeasurePreserving.lintegral_comp
    (PiLp.volume_preserving_toLp (Fin 3)) hmeas]
  -- transfer the right-hand side as well
  have hRHS : (∫⁻ x in Submission.BoseGases.acube ℓ, (W x)^2)
      = ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y)^2 := by
    rw [← lintegral_indicator (Submission.BoseGases.acube_measurable ℓ) (fun x => (W x)^2)]
    rw [← MeasureTheory.MeasurePreserving.lintegral_comp (PiLp.volume_preserving_toLp (Fin 3))
      ((Measurable.pow_const hW 2).indicator (Submission.BoseGases.acube_measurable ℓ))]
    rw [show (∫⁻ a : Fin 3 → ℝ,
          (Submission.BoseGases.acube ℓ).indicator (fun x => (W x)^2) (WithLp.toLp 2 a))
        = ∫⁻ a : Fin 3 → ℝ, (Work.BoseFixB1S.slBig ℓ).indicator (fun y => (F y)^2) a from by
      refine lintegral_congr fun a => ?_
      have hpt : (Submission.BoseGases.acube ℓ).indicator (fun x => (W x)^2) (WithLp.toLp 2 a)
          = (Work.BoseFixB1S.slBig ℓ).indicator (fun y => (F y)^2) a := by
        by_cases ha : WithLp.toLp 2 a ∈ Submission.BoseGases.acube ℓ
        · rw [Set.indicator_of_mem ha,
            Set.indicator_of_mem ((toLp_mem_acube_iff a).mp ha)]
        · rw [Set.indicator_of_notMem ha,
            Set.indicator_of_notMem (mt (toLp_mem_acube_iff a).mpr ha)]
      exact hpt]
    rw [lintegral_indicator (Work.BoseFixB1S.measurableSet_slBig ℓ)]
  rw [hRHS]
  -- pointwise rewrite of the integrand
  have hLHS : (∫⁻ y : Fin 3 → ℝ,
        ((∫⁻ x in Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y), W x)
          / (volume (Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y))))^2)
      = ∫⁻ y : Fin 3 → ℝ,
        ((∫⁻ z in Work.BoseFixB1S.slBox ℓ (ℓ*d) y, F z)
          / (volume (Work.BoseFixB1S.slBox ℓ (ℓ*d) y)))^2 := by
    refine lintegral_congr fun y => ?_
    rw [volume_dlBox_eq ℓ d (WithLp.toLp 2 y), WithLp.ofLp_toLp]
    congr 2
    rw [← lintegral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d
      (WithLp.toLp 2 y)) W]
    rw [← MeasureTheory.MeasurePreserving.lintegral_comp (PiLp.volume_preserving_toLp (Fin 3))
      ((hW.indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d (WithLp.toLp 2 y))))]
    rw [show (∫⁻ b : Fin 3 → ℝ,
          (Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y)).indicator W (WithLp.toLp 2 b))
        = ∫⁻ b : Fin 3 → ℝ, (Work.BoseFixB1S.slBox ℓ (ℓ*d) y).indicator F b from by
      refine lintegral_congr fun b => ?_
      have hpt : (Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y)).indicator W
            (WithLp.toLp 2 b)
          = (Work.BoseFixB1S.slBox ℓ (ℓ*d) y).indicator F b := by
        by_cases hb : WithLp.toLp 2 b ∈ Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y)
        · rw [Set.indicator_of_mem hb,
            Set.indicator_of_mem ((toLp_mem_dlBox_iff b (WithLp.toLp 2 y)).mp hb)]
        · rw [Set.indicator_of_notMem hb,
            Set.indicator_of_notMem
              (mt (toLp_mem_dlBox_iff b (WithLp.toLp 2 y)).mpr hb)]
      exact hpt]
    rw [lintegral_indicator (Work.BoseFixB1S.measurableSet_slBox ℓ (ℓ*d) y)]
  rw [hLHS]
  exact H3 (ℓ' := ℓ) (h := ℓ * d) (by positivity) (by nlinarith [hd1, hℓ]) F hFmeas

end Work.BoseFixB1.Core
