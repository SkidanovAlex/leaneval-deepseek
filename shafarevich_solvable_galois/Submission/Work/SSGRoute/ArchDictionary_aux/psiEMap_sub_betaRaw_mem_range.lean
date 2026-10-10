import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1cGeneric.Canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary_aux

theorem psiEMap_sub_betaRaw_mem_range {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) (SSGRoute.PTExt.unitsK k K) 0)
    (hy : Work.SSGRoute.ExtChain.E1cGeneric.PhiE R y = z)
    (cf : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (hcf : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) cf
             = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R z) :
    Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y
        - Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R cf
      ∈ (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range := by
  -- `e1cMap z` computed on the `PhiE`-generator `y`
  have hz : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R z
      = (Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv R).symm
          (QuotientAddGroup.mk' (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range
            (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y)) := by
    rw [← hy, Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_Phi]
  -- `betaEquiv` of the class of `cf` is the class of `betaRaw cf`
  have hb : Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv R
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) cf)
      = QuotientAddGroup.mk' (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range
          (Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R cf) := by
    rw [Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv_apply, Work.AbsoluteKummer.H1π]
    exact Work.SSGRoute.ExtChain.E1cGeneric.betaH_mk R cf
  -- apply `betaEquiv` to the hypothesis `hcf` and use `hz`
  have h := congrArg (Work.SSGRoute.ExtChain.E1cGeneric.betaEquiv R) (hcf.trans hz)
  rw [hb, AddEquiv.apply_symm_apply] at h
  -- now `h : mk' (betaRaw R cf) = mk' (PsiEMap (E1cR1 R) y)`
  have h0 : QuotientAddGroup.mk' (Work.SSGRoute.ExtChain.E1cGeneric.piH0 R).range
      (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y
        - Work.SSGRoute.ExtChain.E1cGeneric.betaRaw R cf) = 0 := by
    rw [map_sub, h, sub_self]
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h0
  exact h0

end Work.SSGRoute.ArchDictionary_aux
