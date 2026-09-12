import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]

/-- The cone (scalar multiples by numbers in `(0,1)`) over the pointwise-negated set
equals the preimage of the cone under negation. -/
lemma cone_neg_preimage (X : Set V) :
    Ioo (0 : ℝ) 1 • ((fun x : V => -x) '' X) =
      (fun x : V => -x) ⁻¹' (Ioo (0 : ℝ) 1 • X) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_preimage]
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rw [Set.mem_image] at hy
    rcases hy with ⟨b, hbX, hyb⟩
    have hyb' : -b = y := by simpa using hyb
    have hb_eq : b = -y := by simpa using congrArg Neg.neg hyb'
    rw [Set.mem_smul]
    refine ⟨r, hr, b, hbX, ?_⟩
    calc
      r • b = r • (-y) := by rw [hb_eq]
      _ = -(r • y) := by rw [smul_neg]
      _ = -x := by simpa using congrArg Neg.neg hxy
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, b, hbX, hrb⟩
    rw [Set.mem_smul]
    refine ⟨r, hr, -b, ?_, ?_⟩
    · rw [Set.mem_image]
      exact ⟨b, hbX, rfl⟩
    · calc
        r • (-b) = -(r • b) := by rw [smul_neg]
        _ = -(-x) := by simpa using congrArg Neg.neg hrb
        _ = x := by simp

theorem toSphere_neg_preimage
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    (B : Set V) (hBmeas : MeasurableSet B) (hB : B ⊆ Metric.sphere (0 : V) 1) :
    MeasureTheory.volume.toSphere {θ : Metric.sphere (0 : V) 1 | -(θ : V) ∈ B} =
    MeasureTheory.volume.toSphere {θ : Metric.sphere (0 : V) 1 | (θ : V) ∈ B} := by
  let S : Set V := Metric.sphere (0 : V) 1
  let A : Set S := {θ : S | (θ : V) ∈ B}
  let C : Set S := {θ : S | -(θ : V) ∈ B}
  change (volume.toSphere : Measure S) C = (volume.toSphere : Measure S) A
  have hA : MeasurableSet A := by
    change MeasurableSet ((Subtype.val : S → V) ⁻¹' B)
    exact measurable_subtype_coe hBmeas
  have hC : MeasurableSet C := by
    change MeasurableSet ((fun x : V => -x) ∘ (Subtype.val : S → V) ⁻¹' B)
    exact (measurable_neg.comp measurable_subtype_coe) hBmeas
  have himgA : (fun θ : S => (θ : V)) '' A = B := by
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      simpa [A] using hθ
    · intro hx
      refine ⟨⟨x, hB hx⟩, ?_, rfl⟩
      simpa [A] using hx
  have himgC : (fun θ : S => (θ : V)) '' C = (fun x : V => -x) '' B := by
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      refine ⟨-(θ : V), ?_, ?_⟩
      · simpa [C] using hθ
      · simp
    · rintro ⟨b, hbB, hx⟩
      have hxsphere : x ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_zero_iff_norm, ← hx, norm_neg]
        exact (mem_sphere_zero_iff_norm).mp (hB hbB)
      refine ⟨⟨x, hxsphere⟩, ?_, rfl⟩
      simpa [C, ← hx] using hbB
  calc
    (volume.toSphere : Measure S) C
        = ↑(Module.finrank ℝ V) * volume (Ioo (0 : ℝ) 1 • ((fun θ : S => (θ : V)) '' C)) := by
          exact Measure.toSphere_apply' (μ := (volume : Measure V)) (s := C) hC
    _ = ↑(Module.finrank ℝ V) * volume (Ioo (0 : ℝ) 1 • ((fun x : V => -x) '' B)) := by
          rw [himgC]
    _ = ↑(Module.finrank ℝ V) * volume (Ioo (0 : ℝ) 1 • B) := by
          rw [cone_neg_preimage B]
          congr 1
          exact (Measure.measure_preimage_neg (volume : Measure V) (Ioo (0 : ℝ) 1 • B))
    _ = ↑(Module.finrank ℝ V) * volume (Ioo (0 : ℝ) 1 • ((fun θ : S => (θ : V)) '' A)) := by
          rw [← himgA]
    _ = (volume.toSphere : Measure S) A := by
          rw [Measure.toSphere_apply' (μ := (volume : Measure V)) (s := A) hA]

end Commons.Analysis.MeasureTheory