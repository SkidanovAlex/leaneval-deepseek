import Mathlib
import Submission.Work.SSGRoute.PT.DevissageSES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cokernel `M₁ = Coind^G_U M ⧸ range ι` and its `G`-action

The additive quotient does not inherit a `G`-action by instance search; it is constructed here by
`Quotient.liftOn`, its well-definedness being exactly the `G`-stability of `range ι` — i.e.
`devissageIota_equivariant`.
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- The cokernel `M₁ = (Coind^G_U M) ⧸ range ι` of the dévissage inclusion. -/
abbrev devissageM1 {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] : Type u :=
  (Coind G U M) ⧸ (devissageIota U).range

/-- The quotient map `Coind^G_U M → M₁`. -/
def devissagePi {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] :
    Coind G U M →+ devissageM1 (M := M) U :=
  QuotientAddGroup.mk' (devissageIota U).range

instance instSMulQuot {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] : SMul G (devissageM1 (M := M) U) where
  smul g q := Quotient.liftOn q
    (fun f => QuotientAddGroup.mk' (devissageIota U).range (g • f)) (by
      intro f f' h
      have h' : -f + f' ∈ (devissageIota U).range := QuotientAddGroup.leftRel_apply.mp h
      obtain ⟨m, hm⟩ := h'
      refine (QuotientAddGroup.eq (s := (devissageIota U).range)).mpr ?_
      exact ⟨g • m, by
        rw [devissageIota_equivariant U g m, hm, smul_add, smul_neg]⟩)

instance instDistribMulActionQuot {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] :
    DistribMulAction G (devissageM1 (M := M) U) where
  one_smul q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range ((1 : G) • f)
      = QuotientAddGroup.mk' (devissageIota U).range f
    rw [one_smul]
  mul_smul g h q := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range ((g * h) • f)
      = QuotientAddGroup.mk' (devissageIota U).range (g • (h • f))
    rw [mul_smul]
  smul_zero g := by
    show QuotientAddGroup.mk' (devissageIota U).range (g • (0 : Coind G U M))
      = QuotientAddGroup.mk' (devissageIota U).range (0 : Coind G U M)
    rw [smul_zero]
  smul_add g q r := by
    refine QuotientAddGroup.induction_on q (fun f => ?_)
    refine QuotientAddGroup.induction_on r (fun f' => ?_)
    show QuotientAddGroup.mk' (devissageIota U).range (g • (f + f'))
      = QuotientAddGroup.mk' (devissageIota U).range (g • f)
        + QuotientAddGroup.mk' (devissageIota U).range (g • f')
    rw [smul_add, map_add]

/-- `G`-equivariance of the quotient map. -/
theorem devissagePi_equivariant {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] :
    Work.GroupCohomology.IsEquivariant G (devissagePi (M := M) U) := by
  intro g q
  show QuotientAddGroup.mk' (devissageIota U).range (g • q)
    = g • QuotientAddGroup.mk' (devissageIota U).range q
  rfl

/-- `range ι = ker π`. -/
theorem devissage_range_iota_eq_ker_pi {G : Type u} [Group G] (U : Subgroup G)
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] :
    (devissageIota U).range = (devissagePi (M := M) U).ker :=
  (QuotientAddGroup.ker_mk' (devissageIota U).range).symm

end

end Work.SSGRoute.PT
