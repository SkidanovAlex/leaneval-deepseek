import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.PT.AlphaPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- Compatibility of `alphaTwo` with evaluation: `α²` is "cup with `n`", and evaluation at `n`
is the coefficient map `Hom_ℤ(N,C) → C`; the two agree at the level of cocycles.  Concretely,
`mapZ2` of the evaluation map sends a `2`-cocycle `c` to `(g,h) ↦ c(g,h)(n) = (c ⌣ n)(g,h)`. -/
theorem mapZ2_evalHom_eq_cupCochainZ2
    {G : Type*} [TopologicalSpace G] [Group G]
    {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (c : Work.AbsoluteKummer.Z2 G (ConjHom N C))
    (n : ↥(Work.GroupCohomology.invariants G N)) :
    Work.AbsoluteKummer.mapZ2 (ConjHom.evalHom (C := C) (n : N))
        (evalHom_smul (C := C) (n : N) n.2) c
      = cupCochainZ2 c n := by
  ext p
  rfl

theorem alphaTwo_evalHom {G : Type*} [Group G] [TopologicalSpace G]
    {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (x : Work.AbsoluteKummer.H2 G (Work.SSGRoute.PT.ConjHom N C))
    (n : ↥(Work.GroupCohomology.invariants G N)) :
    Work.SSGRoute.PT.alphaTwo x n
      = Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.evalHom (C := C) (n : N))
          (Work.SSGRoute.PT.evalHom_smul (C := C) (n : N) n.2) x := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G (Work.SSGRoute.PT.ConjHom N C)).comap
      (Work.AbsoluteKummer.Z2 G (Work.SSGRoute.PT.ConjHom N C)).subtype) x
  change Work.SSGRoute.PT.alphaTwo
        (Work.AbsoluteKummer.H2π G (Work.SSGRoute.PT.ConjHom N C) c) n
      = Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.ConjHom.evalHom (C := C) (n : N))
          (Work.SSGRoute.PT.evalHom_smul (C := C) (n : N) n.2)
          (Work.AbsoluteKummer.H2π G (Work.SSGRoute.PT.ConjHom N C) c)
  have hmap := Work.AbsoluteKummer.mapH2_H2π
    (φ := Work.SSGRoute.PT.ConjHom.evalHom (C := C) (n : N))
    (hφ := Work.SSGRoute.PT.evalHom_smul (C := C) (n : N) n.2) c
  rw [Work.SSGRoute.PT.alphaTwo_H2π, hmap]
  change Work.AbsoluteKummer.H2π G C (Work.SSGRoute.PT.cupCochainZ2 c n)
      = Work.AbsoluteKummer.H2π G C (Work.AbsoluteKummer.mapZ2
          (Work.SSGRoute.PT.ConjHom.evalHom (C := C) (n : N))
          (Work.SSGRoute.PT.evalHom_smul (C := C) (n : N) n.2) c)
  rw [mapZ2_evalHom_eq_cupCochainZ2]

end Work.SSGRoute.PT
