import Mathlib
import Submission.Work.ORLyndon.mmConnDefs

namespace Work.ORLyndon

theorem mmBaseHom_comp_mk {α : Type*} [DecidableEq α] (t : α) (r : FreeGroup α)
    (h : Work.OROneRel.eps t r = 0) :
    (Work.OROneRel.mmBaseHom (t := t) (r := r) h).comp
        (PresentedGroup.mk ({Work.OROneRel.mmW t r} :
          Set (FreeGroup (Work.OROneRel.mmBeta t r))))
      = (Work.ORLyndon.presentRho r).comp (Work.ORLyndon.mmZeta t r) := by
  -- Both sides are homomorphisms out of the free group on the decorated alphabet `mmBeta t r`,
  -- so it suffices to check them on the generators.
  refine FreeGroup.ext_hom _ _ fun p => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (Work.OROneRel.mmBaseHom h) (PresentedGroup.of p) =
    (Work.ORLyndon.presentRho r) ((Work.ORLyndon.mmZeta t r) (FreeGroup.of p))
  -- On a generator `of p` the canonical map evaluates through the universal property.
  rw [Work.OROneRel.mmBaseHom_gen]
  -- On the other side `mmZeta` is `magnusMap`, whose value on `of p` is the conjugate
  -- `t ^ k * x * t ^ (-k)`; `presentRho` is a homomorphism, so the two sides agree.
  simp only [Work.ORLyndon.mmZeta, MonoidHom.comp_apply, FreeGroup.map.of,
    Work.OROneRel.zeta, FreeGroup.lift_apply_of, Work.ORLyndon.presentRho_apply,
    map_mul, map_zpow]
  simp only [PresentedGroup.of]

end Work.ORLyndon
