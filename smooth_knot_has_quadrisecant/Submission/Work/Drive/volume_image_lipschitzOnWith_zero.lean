import Mathlib
import Submission.Work.Drive.trigBadnessDefs

namespace Work.Drive

set_option linter.unusedVariables false

/-- **The image of a compact subset of a lower-dimensional space under a Lipschitz map has
Lebesgue measure zero.**  Covering argument: a compact `K ⊂ ℝ^m` covered by finitely many
boxes of sidelength `δ` maps into a union of balls of radius `L δ √m`, whose total volume is
`≤ C δ^{N-m} → 0` when `m < N`. -/
theorem volume_image_lipschitzOnWith_zero {m N : ℕ} (hm : m < N)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K)
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin N)} {L : NNReal}
    (hf : LipschitzOnWith L f K) :
    MeasureTheory.volume (f '' K) = 0 := by
  -- `K` lives in the `m`-dimensional space, so its Hausdorff dimension is at most `m`.
  have h2 : dimH (Set.univ : Set (EuclideanSpace ℝ (Fin m))) = (m : ENNReal) := by
    rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
  have hdimK : dimH K ≤ (m : ENNReal) := (dimH_mono (Set.subset_univ K)).trans_eq h2
  -- Lipschitz maps do not increase Hausdorff dimension.
  have hdim : dimH (f '' K) < ((N : ℕ) : NNReal) := by
    refine lt_of_le_of_lt (hf.dimH_image_le.trans hdimK) ?_
    have : (m : NNReal) < (N : NNReal) := by exact_mod_cast hm
    exact_mod_cast this
  -- Hence the `N`-dimensional Hausdorff measure of the image vanishes.
  have hμ : MeasureTheory.Measure.hausdorffMeasure (N : ℝ) (f '' K) = 0 := by
    have h := hausdorffMeasure_of_dimH_lt (d := (N : NNReal)) hdim
    simpa using h
  -- `volume` on `ℝ^N` is a (nonzero) multiple of `μH[N]`, so it vanishes too.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume N,
    MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  simp [hμ]

end Work.Drive
