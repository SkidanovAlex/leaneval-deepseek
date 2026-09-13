import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace Commons.Analysis.Measure.Integral

open MeasureTheory Metric Set
open scoped Pointwise

/-- **Rotation invariance of the Haar measure on the unit sphere.**
For a linear isometry equivalence `S` of a finite-dimensional real inner product space, the
spherical measure `volume.toSphere` is `S`-invariant. -/
theorem integral_toSphere_comp_linearIsometryEquiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S : E ≃ₗᵢ[ℝ] E) (f : E → ℝ) :
    (∫ u : sphere (0 : E) 1, f (S u) ∂(MeasureTheory.volume : Measure E).toSphere)
      = ∫ u : sphere (0 : E) 1, f u ∂(MeasureTheory.volume : Measure E).toSphere := by
  -- The homeomorphism of the unit sphere induced by `S`.
  let T : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
    S.toHomeomorph.subtype (fun x => by
      simp [S.norm_map])
  have hTemb : MeasurableEmbedding (T : sphere (0 : E) 1 → sphere (0 : E) 1) :=
    T.measurableEmbedding
  -- `S` preserves Lebesgue measure on `E`.
  have hvol : ∀ C : Set E, (volume : Measure E) (S '' C) = (volume : Measure E) C := by
    intro C
    have hSC : S '' C = S.symm ⁻¹' C := by
      ext x; constructor
      · rintro ⟨c, hc, rfl⟩; simpa using hc
      · intro hx; exact ⟨S.symm x, hx, by simp⟩
    rw [hSC]
    exact (LinearIsometryEquiv.measurePreserving (S.symm : E ≃ₗᵢ[ℝ] E)).measure_preimage_emb
      (S.symm.toMeasurableEquiv.measurableEmbedding) C
  -- The image of `T` inside `E` is the image of `S`.
  have himg1 : ∀ A : Set (sphere (0 : E) 1), ((↑) '' (T '' A) : Set E) = S '' ((↑) '' A) := by
    intro A
    rw [image_image, image_image]
    congr 1
  -- `S` commutes with the dilation `Ioo 0 1 • ·`.
  have himg2 : ∀ B : Set E, (Ioo (0 : ℝ) 1 • (S '' B) : Set E) = S '' (Ioo (0 : ℝ) 1 • B) := by
    intro B
    ext x
    simp only [Set.mem_smul, Set.mem_image]
    constructor
    · rintro ⟨r, hr, y, ⟨b, hb, hbS⟩, hry⟩
      refine ⟨r • b, ⟨r, hr, b, hb, rfl⟩, ?_⟩
      rw [LinearIsometryEquiv.map_smul, hbS, hry]
    · rintro ⟨y, ⟨r, hr, b, hb, rfl⟩, hy⟩
      refine ⟨r, hr, S b, ⟨b, hb, rfl⟩, ?_⟩
      rw [← LinearIsometryEquiv.map_smul, hy]
  -- `volume.toSphere` is invariant under `T`.
  have h_inv : ∀ A : Set (sphere (0 : E) 1), MeasurableSet A →
      (volume : Measure E).toSphere (T '' A) = (volume : Measure E).toSphere A := by
    intro A hA
    have hTA : MeasurableSet (T '' A) := hTemb.measurableSet_image' hA
    rw [Measure.toSphere_apply' (volume : Measure E) hTA,
      Measure.toSphere_apply' (volume : Measure E) hA]
    congr 1
    rw [himg1 A, himg2 ((↑) '' A)]
    exact hvol (Ioo (0 : ℝ) 1 • ((↑) '' A))
  -- Hence the measure is preserved.
  have hmapT : (volume : Measure E).toSphere.map (T : sphere (0 : E) 1 → sphere (0 : E) 1)
      = (volume : Measure E).toSphere := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply hTemb.measurable hs]
    have hsymm : T.symm '' s = T ⁻¹' s := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hx; exact ⟨T x, hx, T.symm_apply_apply x⟩
    rw [← hsymm]
    have hA : MeasurableSet (T.symm '' s) := T.symm.measurableEmbedding.measurableSet_image' hs
    have hset : T '' (T.symm '' s) = s := by
      rw [image_image]; simp
    have key := h_inv (T.symm '' s) hA
    rw [hset] at key
    exact key.symm
  have hmpT : MeasurePreserving (T : sphere (0 : E) 1 → sphere (0 : E) 1)
      (volume : Measure E).toSphere (volume : Measure E).toSphere :=
    ⟨hTemb.measurable, hmapT⟩
  have hfun : (fun u : sphere (0 : E) 1 => f (S u)) = fun u : sphere (0 : E) 1 => f (T u) := by
    funext u; rfl
  rw [hfun]
  exact MeasurePreserving.integral_comp hmpT hTemb (fun u : sphere (0 : E) 1 => f u)

end Commons.Analysis.Measure.Integral