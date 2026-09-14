import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

namespace Commons.NumberTheory.NumberField

noncomputable section

/-- If the images of elements of a number field `K` under the mixed embedding
into the mixed space `ℝ^{r₁} × ℂ^{r₂}` are linearly independent over `ℝ`,
then the elements themselves are linearly independent over `ℚ`.

Indeed, `ℝ`-linear independence restricts to `ℚ`-linear independence of the
images (via `LinearIndependent.restrict_scalars'`), and the mixed embedding is
a `ℚ`-linear map, so `LinearIndependent.of_comp` transfers independence back
to `K`. -/
theorem mixedEmbedding_linearIndependent_of_linearIndependent {K : Type*} [Field K]
    [NumberField K] {ι : Type*} (a : ι → K)
    (h : LinearIndependent ℝ (fun i : ι => NumberField.mixedEmbedding K (a i))) :
    LinearIndependent ℚ a := by
  let v : ι → NumberField.mixedEmbedding.mixedSpace K :=
    fun i => NumberField.mixedEmbedding K (a i)
  have h_rat : LinearIndependent ℚ v := by
    simpa [v] using
      (LinearIndependent.restrict_scalars' (R := ℚ) (K := ℝ)
        (M := NumberField.mixedEmbedding.mixedSpace K) h)
  let f : K →ₗ[ℚ] NumberField.mixedEmbedding.mixedSpace K :=
    (NumberField.mixedEmbedding K).toRatAlgHom.toLinearMap
  have hf : LinearIndependent ℚ (fun i => f (a i)) := by
    simpa [f, v] using h_rat
  exact LinearIndependent.of_comp (R := ℚ) (M := K) f hf

end

end Commons.NumberTheory.NumberField