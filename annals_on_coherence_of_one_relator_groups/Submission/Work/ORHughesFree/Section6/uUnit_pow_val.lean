import Mathlib
import Submission.Work.Section6.StepA
import Submission.Work.ORHughesFree.Section6.ConjKN

namespace Work.ORHughesFree.Section6

theorem uUnit_pow_val {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U] [StarRing U]
    [Work.ORHughesFree.IsStarRegular U] (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (t : H)
    (k : ℤ) :
    (((Work.Section6.uUnit φ H t) ^ k : Uˣ) : U) =
      (φ.comp (Work.ORHughesFree.inducedMapRing (K := K) H))
        (MonoidAlgebra.single (t ^ k) (1 : K)) := by
  -- `φ(t)` is the image of the monomial `single t 1` under `g := φ.comp inducedMapRing`.
  let g : MonoidAlgebra K H →+* U := φ.comp (Work.ORHughesFree.inducedMapRing (K := K) H)
  -- The monoid homomorphism `H →* Uˣ`, `s ↦ g (single s 1)`; `single (·) 1 : H →* K[H]` is a
  -- monoid homomorphism into the units and `g` maps it into the units of `U`.
  let h : H →* Uˣ :=
    { toFun := fun s =>
        { val := g (MonoidAlgebra.single s 1)
          inv := g (MonoidAlgebra.single s⁻¹ 1)
          val_inv := by
            have hh : MonoidAlgebra.single s (1 : K) * MonoidAlgebra.single s⁻¹ (1 : K) = 1 := by
              rw [MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul]
              exact MonoidAlgebra.one_def.symm
            rw [← map_mul, hh, map_one]
          inv_val := by
            have hh : MonoidAlgebra.single s⁻¹ (1 : K) * MonoidAlgebra.single s (1 : K) = 1 := by
              rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul]
              exact MonoidAlgebra.one_def.symm
            rw [← map_mul, hh, map_one] }
      map_one' := by
        refine Units.ext ?_
        show g (MonoidAlgebra.single 1 1) = (1 : U)
        rw [← MonoidAlgebra.one_def, map_one]
      map_mul' := fun s r => by
        refine Units.ext ?_
        show g (MonoidAlgebra.single (s * r) 1) =
          g (MonoidAlgebra.single s 1) * g (MonoidAlgebra.single r 1)
        rw [← map_mul, MonoidAlgebra.single_mul_single, mul_one] }
  have ht : h t = Work.Section6.uUnit φ H t := Units.ext rfl
  rw [show Work.Section6.uUnit φ H t = h t from ht.symm, ← MonoidHom.map_zpow h t k]
  rfl

end Work.ORHughesFree.Section6
