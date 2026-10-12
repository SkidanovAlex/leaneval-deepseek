import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1S.MeanSq.Box3
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Smear

open MeasureTheory
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Coordinate form of `acube ℓ`: the pushforward of `Work.BoseFixB1S.slBig ℓ` under
`WithLp.toLp 2`. -/
lemma toLp_mem_acube_iff {ℓ : ℝ} (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y ∈ Submission.BoseGases.acube ℓ ↔ y ∈ Work.BoseFixB1S.slBig ℓ := by
  rw [Submission.BoseGases.mem_acube_iff, Work.BoseFixB1S.mem_slBig]

/-- Coordinate form of `dlBox ℓ d u`: the pushforward of `Work.BoseFixB1S.slBox ℓ (ℓ*d) u.ofLp`
under `WithLp.toLp 2`. -/
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

/-- The volume of `dlBox ℓ d u` equals that of its coordinate model
`Work.BoseFixB1S.slBox ℓ (ℓ*d) u.ofLp`. -/
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

set_option maxHeartbeats 800000 in
/-- **The sliding-box mean-square bound on `EuclideanSpace ℝ (Fin 3)`** (transfer form).  For
`0 < ℓ`, `0 < d ≤ 1` and `W : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞` measurable, *given* the `slBox`
three-dimensional bound `h3d` at `(ℓ, ℓ*d)`:

  `∫_u ( (∫_{x ∈ dlBox ℓ d u} W x) / |dlBox ℓ d u| )² du  ≤  (9/(ℓ d))³ · ∫_{x ∈ acube ℓ} W x² dx`.

This is a verbatim copy of the statement of `Work.BoseFixB1S.meanSq3d_E3`
(`Submission/Work/BoseFixB1S/MeanSq/E3Box.lean`), which is *proved* there but only modulo the
`sorry`-skeleton `Work.BoseFixB1S.meanSq3d`; here the missing input is an explicit hypothesis, so
this copy is provable (and `sorry`-free) while that skeleton is unfinished.

PROOF ROUTE: copy the proof of `Work.BoseFixB1S.meanSq3d_E3` verbatim, replacing its last line
`exact meanSq3d (by positivity) (by nlinarith [hd1, hℓ]) hFmeas` by `exact h3d hFmeas`.  That proof
pulls everything back along the volume-preserving measurable equivalence
`WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)`, using its own lemmas
`toLp_mem_dlBox_iff`, `toLp_mem_acube_iff`, `volume_dlBox_eq` (all proved in `E3Box.lean` without
the skeleton).  Since `E3Box.lean` currently does not BUILD (it imports the broken in-progress
skeleton `Submission.Work.BoseFixB1S.meanSq3d`), COPY the text of `E3Box.lean` (the three helper
lemmas plus the body of the theorem) into the new file and DROP the `import
Submission.Work.BoseFixB1S.meanSq3d` line; take `Work.SmallBoxSliding.measurableSet_dlBox` etc. from
`Submission.Work.SmallBoxSliding.Defs`/`boxMass_integral_u`. -/
theorem meanSq3dE3H {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (h3d : ∀ {F : (Fin 3 → ℝ) → ℝ≥0∞}, Measurable F →
      ∫⁻ u : Fin 3 → ℝ,
          ((∫⁻ y in Work.BoseFixB1S.slBox ℓ (ℓ * d) u, F y)
            / (volume (Work.BoseFixB1S.slBox ℓ (ℓ * d) u))) ^ 2
        ≤ ENNReal.ofReal ((9 / (ℓ * d)) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞} (hW : Measurable W) :
    ∫⁻ u : EuclideanSpace ℝ (Fin 3),
        ((∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x)
          / (volume (Submission.BoseGases.dlBox ℓ d u))) ^ 2
      ≤ ENNReal.ofReal ((9 / (ℓ * d)) ^ 3)
          * ∫⁻ x in Submission.BoseGases.acube ℓ, (W x) ^ 2 := by
  classical
  set F : (Fin 3 → ℝ) → ℝ≥0∞ := fun y => W (WithLp.toLp 2 y) with hFdef
  have hFmeas : Measurable F := hW.comp (by fun_prop)
  -- measurability of the integrand on `E3`
  have hset : MeasurableSet {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} :=
    Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d
  have hjoint : Measurable (Function.uncurry (fun (u : E3) (x : E3) =>
      (Submission.BoseGases.dlBox ℓ d u).indicator W x)) := by
    have hEq : Function.uncurry (fun (u : E3) (x : E3) =>
        (Submission.BoseGases.dlBox ℓ d u).indicator W x)
        = {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
            (fun p => W p.2) := by
      funext p
      obtain ⟨u, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
      · rw [Set.indicator_of_mem hx,
          Set.indicator_of_mem (show (u, x) ∈ {p : E3 × E3 | p.2 ∈
            Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show (u, x) ∉ {p : E3 × E3 | p.2 ∈
            Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    rw [hEq]
    exact (hW.comp measurable_snd).indicator hset
  have hnum : Measurable (fun u : E3 =>
      ∫⁻ x in Submission.BoseGases.dlBox ℓ d u, W x) := by
    have h := Measurable.lintegral_prod_right (ν := (volume : Measure E3)) hjoint
    convert h using 2 with u
    exact (MeasureTheory.lintegral_indicator
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) W).symm
  have hvol : Measurable (fun u : E3 => volume (Submission.BoseGases.dlBox ℓ d u)) := by
    have hjoint1 : Measurable (Function.uncurry (fun (u : E3) (x : E3) =>
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
      have hEq : Function.uncurry (fun (u : E3) (x : E3) =>
          (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ≥0∞)) x)
          = {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
              (fun _ => (1 : ℝ≥0∞)) := by
        funext p
        obtain ⟨u, x⟩ := p
        simp only [Function.uncurry_apply_pair]
        by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem hx,
            Set.indicator_of_mem (show (u, x) ∈ {p : E3 × E3 | p.2 ∈
              Submission.BoseGases.dlBox ℓ d p.1} from hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (show (u, x) ∉ {p : E3 × E3 | p.2 ∈
              Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      rw [hEq]
      exact measurable_const.indicator hset
    have h := Measurable.lintegral_prod_right (ν := (volume : Measure E3)) hjoint1
    convert h using 2 with u
    exact (lintegral_indicator_one (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)).symm
  have hmeas : Measurable (fun u : E3 =>
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
        = ∫⁻ a : Fin 3 → ℝ,
            (Work.BoseFixB1S.slBig ℓ).indicator (fun y => (F y)^2) a from by
      refine lintegral_congr fun a => ?_
      have hpt : (Submission.BoseGases.acube ℓ).indicator (fun x => (W x)^2) (WithLp.toLp 2 a)
          = (Work.BoseFixB1S.slBig ℓ).indicator (fun y => (F y)^2) a := by
        by_cases ha : WithLp.toLp 2 a ∈ Submission.BoseGases.acube ℓ
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ((toLp_mem_acube_iff a).mp ha)]
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
    rw [← lintegral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d (WithLp.toLp 2 y)) W]
    rw [← MeasureTheory.MeasurePreserving.lintegral_comp (PiLp.volume_preserving_toLp (Fin 3))
      ((hW.indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d (WithLp.toLp 2 y))))]
    rw [show (∫⁻ b : Fin 3 → ℝ,
          (Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y)).indicator W (WithLp.toLp 2 b))
        = ∫⁻ b : Fin 3 → ℝ, (Work.BoseFixB1S.slBox ℓ (ℓ*d) y).indicator F b from by
      refine lintegral_congr fun b => ?_
      have hpt : (Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y)).indicator W (WithLp.toLp 2 b)
          = (Work.BoseFixB1S.slBox ℓ (ℓ*d) y).indicator F b := by
        by_cases hb : WithLp.toLp 2 b ∈ Submission.BoseGases.dlBox ℓ d (WithLp.toLp 2 y)
        · rw [Set.indicator_of_mem hb,
            Set.indicator_of_mem ((toLp_mem_dlBox_iff b (WithLp.toLp 2 y)).mp hb)]
        · rw [Set.indicator_of_notMem hb,
            Set.indicator_of_notMem (mt (toLp_mem_dlBox_iff b (WithLp.toLp 2 y)).mpr hb)]
      exact hpt]
    rw [lintegral_indicator (Work.BoseFixB1S.measurableSet_slBox ℓ (ℓ*d) y)]
  rw [hLHS]
  exact h3d hFmeas

end Work.BoseFixB1.Smear
