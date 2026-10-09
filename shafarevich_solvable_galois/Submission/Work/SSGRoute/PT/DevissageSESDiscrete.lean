import Mathlib
import Submission.Work.SSGRoute.PT.DevissageSESQuot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Discreteness of the cokernel `M₁`

`IsDiscreteModule G M` is `∀ m, IsOpen ↑(MulAction.stabilizer G m)`.  A stabiliser of a
representative `f` of a class `q : M₁` is open (discreteness of `Coind G U M`) and lies inside the
stabiliser of `q`, because the quotient map is `G`-equivariant; a subgroup containing an open
subgroup is open (`Subgroup.isOpen_mono`).
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- The cokernel of the dévissage inclusion is a discrete `G`-module. -/
theorem devissage_isDiscreteModule_m1 {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) {M : Type u} [AddCommGroup M]
    [DistribMulAction G M]
    (hN : Work.AbsoluteKummer.IsDiscreteModule G (Coind G U M)) :
    Work.AbsoluteKummer.IsDiscreteModule G (devissageM1 (M := M) U) := by
  intro q
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk'_surjective (devissageIota U).range q
  refine Subgroup.isOpen_mono ?_ (hN f)
  intro g hg
  simp only [MulAction.mem_stabilizer_iff] at hg ⊢
  have heq : g • (QuotientAddGroup.mk' (devissageIota U).range) f
      = QuotientAddGroup.mk' (devissageIota U).range (g • f) :=
    (devissagePi_equivariant U g f).symm
  rw [heq, hg]

end

end Work.SSGRoute.PT
