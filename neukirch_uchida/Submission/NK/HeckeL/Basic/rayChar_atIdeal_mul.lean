import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.HeckeL.Basic.ideleOfFun_add
import Submission.NK.HeckeL.Basic.classOfIdeal_mul

namespace NK.HeckeL.Basic

/-- `χ` is a multiplicative function of ideals: the ray class character is a monoid homomorphism
`𝕀 K ⧸ (Kˣ · U) →* ℂˣ` and the class of a product of ideals is the product of the classes
(`classOfIdeal_mul`). -/
theorem rayChar_atIdeal_mul {K : Type*} [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (χ : NK.HeckeL.RayChar K U)
    (I J : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    χ.atIdeal (I * J) = χ.atIdeal I * χ.atIdeal J := by
  simp only [NK.HeckeL.RayChar.atIdeal]
  rw [classOfIdeal_mul U I J hI hJ, map_mul, Units.val_mul]

end NK.HeckeL.Basic
