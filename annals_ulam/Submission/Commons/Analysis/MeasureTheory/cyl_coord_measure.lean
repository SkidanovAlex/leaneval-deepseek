import Mathlib
import Submission.Commons.Analysis.MeasureTheory.pair_cyl_coord_measure

open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

noncomputable section

namespace Commons.Analysis.MeasureTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W]

/-- `WithLp.toLp 2 : ℝ × W → WithLp 2 (ℝ × W)` is measurable. -/
private lemma cylCoord_measurable_toLp :
    Measurable (WithLp.toLp 2 : ℝ × W → WithLp 2 (ℝ × W)) :=
  (WithLp.volume_preserving_toLp (U := ℝ) (V := W)).measurable

/-- The set `{x : WithLp 2 (ℝ × W) | x.ofLp.2 ≠ 0}` is measurable. -/
private lemma cylCoord_measurableSet_ofLp_snd_ne :
    MeasurableSet {x : WithLp 2 (ℝ × W) | x.ofLp.2 ≠ (0 : W)} := by
  apply MeasurableSet.compl
  exact measurableSet_eq_fun (by fun_prop) measurable_const

/-- Pushing `volume.restrict {p : ℝ × W | p.2 ≠ 0}` forward along the volume-preserving
`WithLp.toLp 2` gives `volume.restrict {x : WithLp 2 (ℝ × W) | x.ofLp.2 ≠ 0}`. -/
private lemma cylCoord_map_toLp_restrict :
    Measure.map (WithLp.toLp 2 : ℝ × W → WithLp 2 (ℝ × W))
      ((volume : Measure (ℝ × W)).restrict {p | p.2 ≠ (0 : W)}) =
      (volume : Measure (WithLp 2 (ℝ × W))).restrict {x | x.ofLp.2 ≠ (0 : W)} := by
  have hmp := WithLp.volume_preserving_toLp (U := ℝ) (V := W)
  have h := Measure.restrict_map (μ := (volume : Measure (ℝ × W))) hmp.measurable
    cylCoord_measurableSet_ofLp_snd_ne
  rw [hmp.map_eq] at h
  have hpre : (WithLp.toLp 2 : ℝ × W → WithLp 2 (ℝ × W)) ⁻¹' {x | x.ofLp.2 ≠ (0:W)} =
      {p : ℝ × W | p.2 ≠ (0:W)} := by
    ext p; simp
  rw [hpre] at h
  exact h.symm

/-- Composing a map `f : α → ℝ × W` with `WithLp.toLp 2` turns a pushforward into a pushforward. -/
private lemma cylCoord_map_toLp_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ × W} (hf : Measurable f) :
    Measure.map (fun q => WithLp.toLp 2 (f q)) μ =
      Measure.map (WithLp.toLp 2) (Measure.map f μ) :=
  (Measure.map_map cylCoord_measurable_toLp hf).symm

/-- The cylindrical-coordinate change-of-variables for Haar/Lebesgue measure on the
real inner-product space `E = WithLp 2 (ℝ × W)`, where `W` is a nontrivial
finite-dimensional real inner-product space of dimension `d`.

Let `It = Ioo (-1) 1`, `SW` = the unit sphere of `W`, `τ` = Lebesgue measure on
`Ioo (-1) 1` with density `t ↦ (1-t²)^((d-2)/2)`, and `volumeIoiPow d` =
Mathlib's measure on `Ioi (0,∞)` with density `s ↦ s^d`.  Define the source
measure `μ` on `(It × SW) × Ioi (0,∞)` as
`(τ.comap val ⊗ volume.toSphere₌W) ⊗ volumeIoiPow d`, and the map
`Λ (t, ω, s) = toLp (s·t, s·√(1-t²)·ω) : (It × SW) × Ioi (0,∞) → E`
(cone/cylindrical coordinates about the first axis; bijective onto
`E \ {x | x.ofLp.2 = 0}`).

Claim: `map Λ μ = volume.restrict {x : E | x.ofLp.2 ≠ 0}`.

This is the `WithLp`-transport of the commons lemma
`Commons.Analysis.MeasureTheory.pair_cyl_coord_measure` (same statement with the
product `ℝ × W` in place of `E`), using that
`WithLp.toLp 2 : ℝ × W → E` is volume-preserving
(`WithLp.volume_preserving_toLp (U := ℝ) (V := W)`): compose the pair statement
with `Measure.map_map` and then rewrite `map toLp (volume.restrict {p | p.2 ≠ 0})`
as `volume.restrict {x | x.ofLp.2 ≠ 0}` using `Measure.restrict_map` together
with `toLp '' {p | p.2 ≠ 0} = {x | x.ofLp.2 ≠ 0}` and injectivity of `toLp`. -/
theorem cyl_coord_measure
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    let d : ℕ := Module.finrank ℝ W
    let expo : ℝ := (((d : ℝ) - 2) / 2)
    let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
    let tau : MeasureTheory.Measure ℝ :=
      (MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
        (fun t => ENNReal.ofReal (rho t))
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let SW := Metric.sphere (0 : W) 1
    let μ : MeasureTheory.Measure ((It × SW) × Set.Ioi (0 : ℝ)) :=
      ((tau.comap (Subtype.val : It → ℝ)).prod MeasureTheory.volume.toSphere).prod
        (MeasureTheory.Measure.volumeIoiPow d)
    let Λ : (It × SW) × Set.Ioi (0 : ℝ) → WithLp 2 (ℝ × W) := fun q =>
      let t : ℝ := (q.1.1 : It).1
      let ω : W := (q.1.2 : SW)
      let s : ℝ := (q.2 : Set.Ioi (0 : ℝ)).1
      WithLp.toLp 2 (s * t, (s * Real.sqrt (1 - t ^ 2)) • ω)
    MeasureTheory.Measure.map Λ μ = MeasureTheory.volume.restrict
      {x : WithLp 2 (ℝ × W) | x.ofLp.2 ≠ (0 : W)} := by
  -- Unfold the `let`-bindings of the statement, both in the goal and in the pair lemma.
  dsimp only
  have hbase := pair_cyl_coord_measure (W := W)
  dsimp only at hbase
  -- Measurability of the (un-transported) cylindrical map.
  have hF : Measurable (fun q : ({t : ℝ // t ∈ Set.Ioo (-1) 1} × Metric.sphere (0 : W) 1) ×
      Set.Ioi (0 : ℝ) =>
      ((q.2.1 * (q.1.1 : {t : ℝ // t ∈ Set.Ioo (-1) 1}).1,
        (q.2.1 * Real.sqrt (1 - (q.1.1 : {t : ℝ // t ∈ Set.Ioo (-1) 1}).1 ^ 2)) •
          ((q.1.2 : Metric.sphere (0 : W) 1) : W)) : ℝ × W)) := by fun_prop
  -- `Λ = toLp ∘ Λ₀`: split off the (volume-preserving) `toLp` factor.
  rw [cylCoord_map_toLp_comp hF]
  -- Apply the pair-level cylindrical coordinate formula.
  rw [hbase]
  -- Transport the restricted Lebesgue measure along `toLp`.
  exact cylCoord_map_toLp_restrict

end Commons.Analysis.MeasureTheory
