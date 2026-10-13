import Mathlib
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.RealFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The definable order `leEL` on the standard `LRc`-structure `ℝ` is the usual order.**
`leEL x y` is `∃z, z*z = y - x`, i.e. `y - x` is a square, which for the reals means `x ≤ y`. -/
theorem leEL_real (x y : ℝ) : Work.WilC5.leEL x y ↔ x ≤ y := by
  -- the ring operations of the `LRc`-structure on `ℝ` agree with those of the `LEc`-structure
  have bridge : ∀ (n : ℕ) (g : FirstOrder.Language.ring.Functions n) (xs : Fin n → ℝ),
      @FirstOrder.Language.Structure.funMap LRc ℝ (inferInstance) n (Sum.inl (Sum.inl g)) xs =
      @FirstOrder.Language.Structure.funMap LEc ℝ _ n (Sum.inl (Sum.inl g)) xs := by
    intro n g xs
    rw [show (inferInstance : LRc.Structure ℝ) = reductStruct ℝ from reductStruct_real_eq.symm]
    rfl
  -- reduce `leEL` on `ℝ` to the syntactic `isSquare` of the `LEc`-language
  have key : leEL x y = isSquare (subE y x) := by
    simp only [leEL, isSquareL, isSquare, subEL, subE, addEL, addE, negEL, negE, mulEL, mulE,
      ringSymL, ringSym, bridge]
  rw [key, isSquare_real, subE_real]
  constructor <;> intro h <;> linarith

end Work.WilC5
