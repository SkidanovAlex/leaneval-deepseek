import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Commons.Analysis.MeasureTheory.sphere_coordinate_core
import Submission.Commons.Analysis.MeasureTheory.sphere_coordinate_poles_null
import Submission.Commons.Analysis.MeasureTheory.sphere_coordinate_cylinder

noncomputable section
open MeasureTheory Metric Set Function
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

set_option linter.unusedSectionVars false

/-- The ambient L²-product space `ℝ × W`. -/
abbrev margE (W : Type*) := WithLp 2 (ℝ × W)
/-- The unit sphere in a normed space. -/
abbrev margSph (V : Type*) [NormedAddCommGroup V] := Metric.sphere (0 : V) 1
/-- The interval `(-1,1)`, as a type. -/
abbrev margIt (_W : Type*) := {t : ℝ // t ∈ Set.Ioo (-1) 1}
/-- Unit sphere of `W`. -/
abbrev margSW (W : Type*) [NormedAddCommGroup W] := margSph W
/-- The cylinder `(-1,1) × S_W`. -/
abbrev margCyl (W : Type*) [NormedAddCommGroup W] := margIt W × margSW W

/-- First coordinate on the sphere of `ℝ × W`. -/
def margT (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
    (θ : margSph (margE W)) : ℝ := ((θ : margE W).ofLp.1)
/-- Second (`W`-)coordinate on the sphere of `ℝ × W`. -/
def margW (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
    (θ : margSph (margE W)) : W := ((θ : margE W).ofLp.2)
/-- The radial exponent `((finrank ℝ W) - 2)/2`. -/
def margExpo (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] : ℝ :=
  (((Module.finrank ℝ W : ℝ) - 2) / 2)
/-- The marginal density `t ↦ (1 - t²)^e`. -/
def margRho (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (t : ℝ) : ℝ :=
  (1 - t ^ 2) ^ margExpo W
/-- The density measure on `(-1,1)`. -/
def margTau (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] : Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
    (fun t => ENNReal.ofReal (margRho W t))
/-- The corresponding measure on the interval type. -/
def margTauIt (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    Measure (margIt W) :=
  (margTau W).comap (Subtype.val : margIt W → ℝ)
/-- The sphere surface measure on `S_W`. -/
def margSigW (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    Measure (margSW W) :=
  MeasureTheory.volume.toSphere
/-- The cylindrical measure on `(-1,1) × S_W`. -/
def margCylMeasure (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    Measure (margCyl W) :=
  (margTauIt W).prod (margSigW W)
/-- The pole-free part of the sphere of `ℝ × W`. -/
def margS0set (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    Set (margSph (margE W)) := {θ | margW W θ ≠ 0}
/-- The pole-free sphere as a type. -/
abbrev margS0ty (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :=
  {θ : margSph (margE W) // θ ∈ margS0set W}
/-- The surface measure restricted to the pole-free part of the sphere. -/
def margS0Measure (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    Measure (margS0ty W) :=
  (MeasureTheory.volume.toSphere : Measure (margSph (margE W))).comap
    (Subtype.val : margS0ty W → margSph (margE W))

/-- The measure on the pole-free sphere equals the pushforward of the cylindrical
measure under the coordinate equivalence of `sphere_coordinate_core`. -/
lemma marg_core_key (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    ∃ e : margCyl W ≃ᵐ margS0ty W,
      Measure.map (⇑e) (margCylMeasure W) = margS0Measure W ∧
      ∀ q : margCyl W, margT W ((e q : margS0ty W) : margSph (margE W)) = q.1.1 := by
  obtain ⟨e, he_map, he_t⟩ := sphere_coordinate_core (W := W)
  exact ⟨e, he_map, he_t⟩

/-- The pole set of the sphere of `ℝ × W` has zero surface measure. -/
lemma marg_poles_null (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    (MeasureTheory.volume.toSphere : Measure (margSph (margE W))) {θ | margW W θ = 0} = 0 := by
  have h := sphere_coordinate_poles_null (W := W)
  simpa [margW, margSph, margE] using h

/-- The cylindrical marginal identity (restatement of `sphere_coordinate_cylinder`). -/
lemma marg_cyl_identity (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (F : ℝ → ℝ) :
    (∫ q : margCyl W, F q.1.1 ∂(margCylMeasure W)) =
      ∫ t : ℝ in Set.Ioo (-1) 1,
        (∫ ω : margSW W, F t * margRho W t ∂(margSigW W)) := by
  have h := sphere_coordinate_cylinder (W := W) F
  simpa [margCyl, margIt, margSW, margExpo, margRho, margTau, margCylMeasure,
    margTauIt, margSigW, margE] using h

/-- **Coordinate marginal of the spherical surface measure.** -/
theorem sphere_coordinate_marginal
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
    (F : ℝ → ℝ) :
    (∫ θ : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1,
        F ((θ : WithLp 2 (ℝ × W)).ofLp.1)
      ∂MeasureTheory.volume.toSphere) =
    ∫ t : ℝ in Set.Ioo (-1) 1,
      (∫ ω : Metric.sphere (0 : W) 1,
          F t * (1 - t ^ 2) ^ (((Module.finrank ℝ W : ℝ) - 2) / 2)
        ∂MeasureTheory.volume.toSphere) := by
  classical
  obtain ⟨e, he_map, he_t⟩ := marg_core_key W
  let μS : Measure (margSph (margE W)) := MeasureTheory.volume.toSphere
  have hL1 : (∫ θ : margSph (margE W), F (margT W θ) ∂μS) =
      ∫ θ0 : margS0ty W, F (margT W ((θ0 : margS0ty W) : margSph (margE W)))
        ∂(margS0Measure W) := by
    let s : Set (margSph (margE W)) := margS0set W
    have hc : sᶜ = ({θ | margW W θ = 0} : Set (margSph (margE W))) := by
      ext θ; simp [s, margS0set]
    have hnull : μS sᶜ = 0 := by
      rw [hc]
      exact marg_poles_null W
    have hrestrict : μS.restrict s = μS := by
      calc μS.restrict s = μS.restrict Set.univ :=
            Measure.restrict_congr_set (ae_eq_univ.mpr hnull)
           _ = μS := by simp
    have hwE : Measurable (fun x : margE W => ((x.ofLp.2 : W))) :=
      measurable_snd.comp (WithLp.measurable_ofLp 2 (ℝ × W))
    have hval : Measurable (fun θ : margSph (margE W) => (θ : margE W)) :=
      Continuous.measurable continuous_subtype_val
    have hmeas : Measurable (fun θ : margSph (margE W) => margW W θ) := hwE.comp hval
    have hsmeas : MeasurableSet (margS0set W) := by
      change MeasurableSet ((fun θ : margSph (margE W) => margW W θ) ⁻¹' ({0}ᶜ : Set W))
      exact measurableSet_preimage hmeas (isOpen_compl_singleton.measurableSet)
    calc
      (∫ θ : margSph (margE W), F (margT W θ) ∂μS)
          = ∫ θ : margSph (margE W), F (margT W θ) ∂(μS.restrict s) := by
              congr 1
              exact hrestrict.symm
      _ = ∫ θ0 : margS0ty W, F (margT W ((θ0 : margS0ty W) : margSph (margE W)))
            ∂(μS.comap (Subtype.val : margS0ty W → margSph (margE W))) := by
              rw [← MeasureTheory.integral_subtype_comap (μ := μS) (s := margS0set W)
                (f := fun θ : margSph (margE W) => F (margT W θ)) hsmeas]
      _ = ∫ θ0 : margS0ty W, F (margT W ((θ0 : margS0ty W) : margSph (margE W)))
            ∂(margS0Measure W) := by
              simp [margS0Measure, μS]
  have hL2 : (∫ θ0 : margS0ty W, F (margT W ((θ0 : margS0ty W) : margSph (margE W)))
        ∂(margS0Measure W)) =
      ∫ q : margCyl W, F q.1.1 ∂(margCylMeasure W) := by
    calc
      (∫ θ0 : margS0ty W, F (margT W ((θ0 : margS0ty W) : margSph (margE W)))
            ∂(margS0Measure W))
          = ∫ θ0 : margS0ty W, F (margT W ((θ0 : margS0ty W) : margSph (margE W)))
              ∂(Measure.map (⇑e) (margCylMeasure W)) := by rw [he_map]
      _ = ∫ q : margCyl W, F (margT W (((e q : margS0ty W) : margSph (margE W))))
              ∂(margCylMeasure W) := by
              simpa using (MeasureTheory.integral_map_equiv e
                (fun θ0 : margS0ty W =>
                  F (margT W ((θ0 : margS0ty W) : margSph (margE W)))))
      _ = ∫ q : margCyl W, F q.1.1 ∂(margCylMeasure W) := by
              apply integral_congr_ae
              filter_upwards with q
              exact congrArg F (he_t q)
  calc
    (∫ θ : margSph (margE W), F (margT W θ) ∂μS)
        = ∫ q : margCyl W, F q.1.1 ∂(margCylMeasure W) := by
            rw [hL1, hL2]
    _ = ∫ t : ℝ in Set.Ioo (-1) 1,
          (∫ ω : margSW W, F t * margRho W t ∂(margSigW W)) := marg_cyl_identity W F
    _ = ∫ t : ℝ in Set.Ioo (-1) 1,
          (∫ ω : Metric.sphere (0 : W) 1,
              F t * (1 - t ^ 2) ^ (((Module.finrank ℝ W : ℝ) - 2) / 2)
            ∂MeasureTheory.volume.toSphere) := by
          apply integral_congr_ae
          filter_upwards with t
          apply integral_congr_ae
          filter_upwards with ω
          simp [margRho, margExpo]

end Commons.Analysis.MeasureTheory
