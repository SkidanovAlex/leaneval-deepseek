import Mathlib
import Submission.Work.Drive.injective_fderiv_sqDisk_foldBox
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.squareDisk

namespace Work.Drive

/-- **The lead's check for the `s = 1` bridge** (`NOTES_LEAD_hodd_blockT6.md` §4.1 and §7): the map
`z ↦ sqDisk (foldBox z)`, whose image is the disk of the plane chart, has an invertible derivative at
every point of the **open** square.

Reason (corrected — `sqWeight b = √(1 - b²/2)` on `[-1,1]`, it is *not* `≡ 1` there): `foldBox` is
diagonal with `foldFun' = π sin (π ·)/2 > 0` on `(0,1)`, and the Jacobian of `sqDisk` in the square
coordinates `(a,b) = (2y₀-1, 2y₁-1)` has determinant `(4 - 2a² - 2b²)/(4 w(a) w(b)) > 0` for
`|a|,|b| < 1`.  The derivative is a continuous linear map between two real `2`-dimensional spaces, so
injectivity is bijectivity; the injectivity is already proved as
`Work.Drive.injective_fderiv_sqDisk_foldBox`. -/
theorem bijective_fderiv_sqDisk_foldBox (y : EuclideanSpace ℝ (Fin 2))
    (hy : ∀ i : Fin 2, y i ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Bijective
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox z)) y) := by
  have hinj : Function.Injective
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.sqDisk (Work.Drive.foldBox z)) y) :=
    injective_fderiv_sqDisk_foldBox y (hy 0) (hy 1)
  refine ⟨hinj, ?_⟩
  -- source and target are both real `2`-dimensional, so injectivity is bijectivity
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ ℂ := by
    rw [Complex.finrank_real_complex, finrank_euclideanSpace]
    norm_num
  have hL : Function.Injective
      ((fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.sqDisk (Work.Drive.foldBox z)) y).toLinearMap) :=
    fun a b hab => hinj (by simpa using hab)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hL

end Work.Drive
