import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample

open HvdH

/-- The `zipWith` of the weight list with the vector, with the element map `buScProd`, is exactly
`buDscL Wd p s u` (up to `map cfxVal`).  Note `buDscL` uses `List.zip = List.zipWith Prod.mk`
(`List.zip_eq_zipWith`); both sides truncate at `min s u.length`. -/
theorem buScZipEq (Wd : ℤ → ℤ) (p s : ℕ) (u : List (ℤ × ℤ)) :
    List.zipWith (buScProd ((2 : ℤ) ^ p))
      ((List.ofFn (fun i : Fin s => Wd (i : ℤ))).map Val.int) (u.map cfxVal)
    = (buDscL Wd p s u).map cfxVal := by
  simp only [buDscL, List.zip_eq_zipWith, List.zipWith_map_left, List.zipWith_map_right,
    List.map_zipWith, buScProd_apply, cfxVal]

end Work.Resample
