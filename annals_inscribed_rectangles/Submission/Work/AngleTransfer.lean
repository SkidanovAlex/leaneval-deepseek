import Mathlib
import Submission.Commons.Measure.RealEndgame.endgame_measure
import Submission.Commons.Measure.RealEndgame.measureReal_smul_image

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace Submission.AngleTransfer

/-- The point of the additive circle `ℝ/ℤ` corresponding to the angle `θ`, i.e. `e^{iθ}`. -/
def anglePoint (θ : ℝ) : UnitAddCircle := ((1 / (2 * Real.pi)) * θ : ℝ)

/-- The set of angles `θ ∈ [0, 2π]` whose circle point lies in `X`. -/
def angleSet (X : Set UnitAddCircle) : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ θ ≤ 2 * Real.pi ∧ anglePoint θ ∈ X}

lemma angleSet_subset (X : Set UnitAddCircle) : angleSet X ⊆ Set.Icc 0 (2 * Real.pi) :=
  fun _ h => ⟨h.1, h.2.1⟩

lemma one_div_two_pi_mul_nonneg {θ : ℝ} : 0 ≤ (1 / (2 * Real.pi)) * θ ↔ 0 ≤ θ := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · intro h
    have hm := mul_nonneg h hπ.le
    field_simp at hm
    linarith
  · intro h; positivity

lemma one_div_two_pi_mul_le_one {θ : ℝ} : (1 / (2 * Real.pi)) * θ ≤ 1 ↔ θ ≤ 2 * Real.pi := by
  rw [one_div_mul_eq_div, div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)]

lemma anglePoint_two_pi_sub (θ : ℝ) : anglePoint (2 * Real.pi - θ) = -anglePoint θ := by
  have h : (1 / (2 * Real.pi)) * (2 * Real.pi - θ) = 1 - (1 / (2 * Real.pi)) * θ := by
    field_simp
  unfold anglePoint
  rw [h, AddCircle.coe_sub, AddCircle.coe_period]
  simp

lemma anglePoint_measurable : Measurable (anglePoint : ℝ → UnitAddCircle) := by
  unfold anglePoint
  exact AddCircle.measurable_mk'.comp (by fun_prop)

lemma angleSet_measurable {X : Set UnitAddCircle} (hX : MeasurableSet X) :
    MeasurableSet (angleSet X) := by
  have hset : angleSet X = anglePoint ⁻¹' X ∩ Set.Icc 0 (2 * Real.pi) := by
    ext θ
    exact ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩
  rw [hset]
  exact (hX.preimage anglePoint_measurable).inter measurableSet_Icc

lemma angleSet_symm {X : Set UnitAddCircle} (hneg : X = -X) {θ : ℝ} (hθ : θ ∈ angleSet X) :
    2 * Real.pi - θ ∈ angleSet X := by
  obtain ⟨h0, h2π, hX⟩ := hθ
  refine ⟨by linarith, by linarith, ?_⟩
  rw [anglePoint_two_pi_sub]
  have : -anglePoint θ ∈ -X := by
    rw [Set.mem_neg]; simpa using hX
  rwa [← hneg] at this

/-- The set of `s ∈ [0,1]` whose circle point lies in `X` has the same measure as `X`. -/
lemma volumeReal_preimage_eq {X : Set UnitAddCircle} (hX : MeasurableSet X) :
    volume.real {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (s : UnitAddCircle) ∈ X}
      = volume.real X := by
  set S : Set ℝ := {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (s : UnitAddCircle) ∈ X} with hS
  set T : Set ℝ := (fun s : ℝ => (s : UnitAddCircle)) ⁻¹' X ∩ Set.Ioc 0 1 with hT
  have hTvol : volume.real T = volume.real X := by
    rw [hT, measureReal_def, measureReal_def]
    rw [AddCircle.add_projection_respects_measure (1:ℝ) (0:ℝ) hX]
    norm_num
  have hTfin : volume (T ∪ ({0} : Set ℝ)) ≠ ∞ := by
    refine measure_ne_top_of_subset (s := Set.Icc 0 1) (t := T ∪ ({0} : Set ℝ)) ?_
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.2.1.le, hx.2.2⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      constructor <;> norm_num
  have hST : S ⊆ T ∪ ({0} : Set ℝ) := by
    intro s hs
    obtain ⟨hs0, hs1, hsX⟩ := hs
    rw [Set.mem_union]
    by_cases h0 : s = 0
    · exact Or.inr h0
    · exact Or.inl ⟨hsX, ⟨lt_of_le_of_ne hs0 (Ne.symm h0), hs1⟩⟩
  have hTS : T ⊆ S := by
    intro s hs
    obtain ⟨hsX, hs0, hs1⟩ := hs
    exact ⟨hs0.le, hs1, hsX⟩
  have h1 : volume.real S ≤ volume.real T := by
    have h := measureReal_mono hST hTfin
    refine le_trans h ?_
    have h2 := measureReal_union_le (μ := (volume : Measure ℝ)) T ({0} : Set ℝ)
    have h3 : volume.real ({0} : Set ℝ) = 0 := by rw [measureReal_def]; simp
    linarith
  have hSfin : volume S ≠ ∞ := by
    refine measure_ne_top_of_subset (s := Set.Icc 0 1) (t := S) ?_
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    intro x hx
    exact ⟨hx.1, hx.2.1⟩
  have h2 : volume.real T ≤ volume.real S := measureReal_mono hTS hSfin
  rw [hTvol] at h2
  linarith

lemma angleSet_eq_preimage {X : Set UnitAddCircle} :
    angleSet X = (fun θ : ℝ => (1 / (2 * Real.pi)) * θ) ⁻¹'
      {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (s : UnitAddCircle) ∈ X} := by
  ext θ
  exact ⟨fun h => ⟨one_div_two_pi_mul_nonneg.mpr h.1, one_div_two_pi_mul_le_one.mpr h.2.1, h.2.2⟩,
    fun h => ⟨one_div_two_pi_mul_nonneg.mp h.1, one_div_two_pi_mul_le_one.mp h.2.1, h.2.2⟩⟩

lemma measurableSet_preimage_one {X : Set UnitAddCircle} (hX : MeasurableSet X) :
    MeasurableSet {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (s : UnitAddCircle) ∈ X} := by
  have heq : {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (s : UnitAddCircle) ∈ X} =
      Set.Icc 0 1 ∩ (fun s : ℝ => (s : UnitAddCircle)) ⁻¹' X := by
    ext s
    exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  rw [heq]
  exact measurableSet_Icc.inter (hX.preimage AddCircle.measurable_mk')

lemma volumeReal_angleSet {X : Set UnitAddCircle} (hX : MeasurableSet X) :
    volume.real (angleSet X) = 2 * Real.pi * volume.real X := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [angleSet_eq_preimage,
    Commons.Measure.RealEndgame.measureReal_smul_image
      (c := 1 / (2 * Real.pi)) (by positivity) (measurableSet_preimage_one hX),
    volumeReal_preimage_eq hX]
  have h : (1 / (2 * Real.pi))⁻¹ = 2 * Real.pi := by field_simp
  rw [h, abs_of_pos h2π]

/-- **Assembly of the measure-theoretic endgame**: a measurable, inversion-invariant subset of the
circle of measure at least `1/3` gives at least `1/3` of the parameters `r ∈ [0,1]` whose
half-angle point lies in the set. -/
theorem third_measure_of_neg_invariant {X : Set UnitAddCircle} (hX : MeasurableSet X)
    (hneg : X = -X) (h : (1 / 3 : ℝ) ≤ volume.real X) :
    (1 / 3 : ℝ) ≤ volume.real
      {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ anglePoint (Real.pi * r) ∈ X} := by
  have hAmeas : MeasurableSet (angleSet X) := angleSet_measurable hX
  have hA01 : angleSet X ⊆ Set.Icc 0 (2 * Real.pi) := angleSet_subset X
  have hAsym : ∀ ⦃x : ℝ⦄, x ∈ angleSet X → 2 * Real.pi - x ∈ angleSet X :=
    fun x hx => angleSet_symm hneg hx
  have hvol : 2 * Real.pi / 3 ≤ volume.real (angleSet X) := by
    rw [volumeReal_angleSet hX]
    nlinarith [Real.pi_pos, h]
  have hend := Commons.Measure.RealEndgame.endgame_measure hAmeas hA01 hAsym hvol
  have hset : {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ Real.pi * r ∈ angleSet X} =
      {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ anglePoint (Real.pi * r) ∈ X} := by
    ext r
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.1, h.2.1, mul_nonneg Real.pi_pos.le h.1,
        by nlinarith [Real.pi_pos, h.2.1], h.2.2⟩⟩
  rwa [hset] at hend

end Submission.AngleTransfer
