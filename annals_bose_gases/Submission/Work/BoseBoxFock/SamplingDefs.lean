import Mathlib.Analysis.Fourier.AddCircleMulti
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

/-- The quotient map `(Fin 3 → ℝ) → 𝕋³ = (ℝ/ℤ)³`. -/
abbrev torusProj : (Fin 3 → ℝ) → UnitAddTorus (Fin 3) := fun x i => (x i : UnitAddCircle)

@[simp] lemma torusProj_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    torusProj x i = (x i : UnitAddCircle) := rfl

/-- The half-open unit box `(-1/2,1/2]³` (`Set.pi` form, as produced by
`UnitAddTorus.mFourierCoeff_eq_integral` and `UnitAddTorus.integral_preimage`). -/
def boxIoc : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (-(1/2) : ℝ) (1/2))

/-- The closed unit box `[-1/2,1/2]³` (`Set.Icc` form, as produced by
`Measure.univ_pi_Ioc_ae_eq_Icc`). -/
def boxIcc : Set (Fin 3 → ℝ) :=
  Set.Icc (fun _ : Fin 3 => -(1/2 : ℝ)) (fun _ : Fin 3 => (1/2 : ℝ))

lemma mem_boxIoc {x : Fin 3 → ℝ} :
    x ∈ boxIoc ↔ ∀ i, -(1/2 : ℝ) < x i ∧ x i ≤ 1/2 := by
  simp [boxIoc, Set.mem_pi, Set.mem_Ioc]

lemma mem_boxIcc {x : Fin 3 → ℝ} : x ∈ boxIcc ↔ ∀ i, |x i| ≤ (1/2 : ℝ) := by
  simp only [boxIcc, Set.mem_Icc, Pi.le_def, abs_le, forall_and]

lemma measurableSet_boxIoc : MeasurableSet boxIoc :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc

lemma measurableSet_boxIcc : MeasurableSet boxIcc :=
  measurableSet_Icc

/-- `volume` on `Fin 3 → ℝ` is the product Lebesgue measure. -/
lemma volume_pi_fin3 : (volume : Measure (Fin 3 → ℝ))
    = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) := rfl

/-- The half-open and the closed unit boxes agree almost everywhere. -/
lemma boxIoc_ae_eq_boxIcc : boxIoc =ᵐ[volume] boxIcc := by
  rw [volume_pi_fin3]
  have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ : Fin 3 => -(1/2 : ℝ)) (g := fun _ : Fin 3 => (1/2 : ℝ))
  simpa [boxIoc, boxIcc] using h

/-- The Haar probability measure of the unit torus `𝕋³ = (ℝ/ℤ)³`, i.e. `(AddCircle.haarAddCircle)³`.
This is the measure for which Mathlib's torus Fourier basis `UnitAddTorus.mFourierBasis` is
orthonormal; it is definitionally equal to `volume` once the local instance
`instMeasureSpaceUnitAddCircle` is registered (see the module docstring and
`torusVol_eq_volume`). -/
noncomputable def torusVol : Measure (UnitAddTorus (Fin 3)) :=
  Measure.pi (fun _ : Fin 3 => @AddCircle.haarAddCircle 1 (Fact.mk (by norm_num : (0:ℝ) < 1)))

instance : IsFiniteMeasure torusVol :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Fin 3 =>
    @AddCircle.haarAddCircle 1 (Fact.mk (by norm_num : (0:ℝ) < 1))))

instance : IsProbabilityMeasure torusVol :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    @AddCircle.haarAddCircle 1 (Fact.mk (by norm_num : (0:ℝ) < 1))))

/-- The lift of a function on `ℝ³` to the torus `𝕋³`, through the representative in
`(-1/2,1/2]³` of `Mathlib.Analysis.Fourier.AddCircleMulti.measurableEquivPiIoc`. -/
def torusLift (g : ℝ³ → ℂ) : UnitAddTorus (Fin 3) → ℂ :=
  fun t => g (WithLp.toLp 2 fun i : Fin 3 => (AddCircle.equivIoc 1 (-(1/2) : ℝ) (t i)).1)

/-- On the half-open box, the torus lift of `g` is the lift of `g` itself. -/
lemma torusLift_apply_proj {g : ℝ³ → ℂ} {x : Fin 3 → ℝ} (hx : x ∈ boxIoc) :
    torusLift g (torusProj x) = g (WithLp.toLp 2 x) := by
  unfold torusLift
  apply congrArg g
  congr 1
  funext i
  have hmem : x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1) := by
    have h := (mem_boxIoc.mp hx) i
    exact ⟨h.1, by linarith [h.2]⟩
  have h2 := AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := -(1/2 : ℝ)) (x := x i) hmem
  simpa using congrArg Subtype.val h2

section
attribute [local instance] instMeasureSpaceUnitAddCircle

/-- With Mathlib's Haar measure instance on `UnitAddCircle` registered, `torusVol` *is* `volume`
on the unit torus. -/
theorem torusVol_eq_volume : torusVol = (volume : Measure (UnitAddTorus (Fin 3))) := rfl

/-- The Haar measure on the unit torus has total mass one. -/
theorem isProbabilityMeasure_torus_volume :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin 3))) := by
  rw [← torusVol_eq_volume]
  exact inferInstance

end

end Work.BoseBoxFock
