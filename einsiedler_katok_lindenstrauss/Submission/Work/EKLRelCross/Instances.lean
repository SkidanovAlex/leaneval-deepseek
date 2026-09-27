import Submission.Work.EKLContract.All

/-!
# Topological instances for `SL₃(ℝ)`

Mathlib does not synthesize the topological instances for
`SL3 = Matrix.SpecialLinearGroup (Fin 3) ℝ`, for two reasons:

* `Matrix m n R` is a plain `def` equal to the product `m → n → R`, and type class search does
  not unfold it (the fleet lemma `Lemmas.secondCountableTopology_matrix`/`polishSpace_matrix`
  records this).  We supply the instances for the matrix space by `inferInstanceAs`;
* `SL3` is a closed subspace (locus `det = 1`) of that space, and closedness is not a type class.

These instances are used (for example) by the Riesz representation theorem
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` and by Urysohn's lemma
`exists_continuousMap_one_of_isCompact_subset_isOpen`.
-/

open Matrix
open Work.EKLContract
open Work.EKLContract.Lemmas

namespace Work.EKLRelCross

instance instSecondCountableSL3 : SecondCountableTopology SL3 := by
  have : PolishSpace SL3 := polishSpace_specialLinearGroup
  infer_instance

instance instT2SL3 : T2Space SL3 := by
  have : PolishSpace SL3 := polishSpace_specialLinearGroup
  infer_instance

instance instPseudoMetrizableSL3 : TopologicalSpace.PseudoMetrizableSpace SL3 := by
  have : PolishSpace SL3 := polishSpace_specialLinearGroup
  infer_instance

/-- The matrix space is locally compact: it is a finite product of copies of `ℝ`. -/
instance instLocallyCompactMatrix : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))

/-- The matrix space is `σ`-compact, being a finite product of copies of `ℝ`. -/
instance instSigmaCompactMatrix : SigmaCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (SigmaCompactSpace (Fin 3 → Fin 3 → ℝ))

/-- `SL₃(ℝ)` is closed in the matrix space (it is the locus `det = 1`). -/
theorem isClosed_SL3 : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} :=
  isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const

instance instLocallyCompactSL3 : LocallyCompactSpace SL3 :=
  isClosed_SL3.locallyCompactSpace

instance instWeaklyLocallyCompactSL3 : WeaklyLocallyCompactSpace SL3 :=
  isClosed_SL3.weaklyLocallyCompactSpace

instance instSigmaCompactSL3 : SigmaCompactSpace SL3 :=
  isClosed_SL3.sigmaCompactSpace

end Work.EKLRelCross
