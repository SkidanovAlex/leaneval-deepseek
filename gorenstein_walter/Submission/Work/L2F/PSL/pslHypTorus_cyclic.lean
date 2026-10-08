import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.hypTorus_cyclic

namespace Work.L2F.PSL

/-- The image of `hypTorus F d` (`d ≠ 0`) in `PSL(2,F)` is cyclic, as the image of a cyclic group
(`hypTorus_cyclic`) under `pslMap`. -/
theorem pslHypTorus_cyclic (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (d : F)
    (hd : d ≠ 0) : IsCyclic (Work.L2F.pslHypTorus F d) := by
  -- `pslHypTorus F d` is by definition the image of `hypTorus F d` under `pslMap`.
  show IsCyclic ((Work.L2F.hypTorus F d).map (Work.PSL2.pslMap F))
  -- `hypTorus F d` is cyclic.
  have hcyc : IsCyclic (Work.L2F.hypTorus F d) :=
    Work.L2F.Conic.hypTorus_cyclic F h2 d hd
  -- The restriction of `pslMap` onto `hypTorus F d` maps onto its image, and a surjective image of
  -- a cyclic group is cyclic.
  let φ : Work.L2F.hypTorus F d →* (Work.L2F.hypTorus F d).map (Work.PSL2.pslMap F) :=
    { toFun := fun x => ⟨Work.PSL2.pslMap F x, Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  exact isCyclic_of_surjective (hH := hcyc) φ (fun y => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

end Work.L2F.PSL
