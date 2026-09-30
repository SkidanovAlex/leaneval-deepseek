import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory
/-- For a pullback square of simplicial sets, the range of the left leg is the
preimage under the top leg of the range of the right leg. -/
theorem range_eq_preimage_range_of_isPullback {P X Y Z : SSet.{0}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : CategoryTheory.IsPullback fst snd f g) :
    SSet.Subcomplex.range fst = (SSet.Subcomplex.range g).preimage f := by
  apply Subfunctor.ext
  funext n
  have hp : IsPullback (fst.app n) (snd.app n) (f.app n) (g.app n) :=
    CategoryTheory.Functor.map_isPullback (SSet.evaluation.obj n) h
  have hset := CategoryTheory.Limits.Types.range_fst_of_isPullback hp
  rw [Subfunctor.range_obj, SSet.Subcomplex.preimage_obj, Subfunctor.range_obj]
  exact hset

end Work.SSSR
