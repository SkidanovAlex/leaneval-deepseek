import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Module.Injective
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `eOf` on a connecting-map class (installed copy of `ARCHP2_PLAN.lean` §A)

This is a **verbatim copy** of `Work.SSGRoute.LeadArchP2.eOf_connMap`
(`Submission/_lead_design/archp2_1008/ARCHP2_PLAN.lean`, §A, lines 41–65), installed into the
workspace so that it can be *imported* instead of copied.  The plan's own note for the dispatch
D3–D8 was "copy any helper you need from the plan `.lean`; **do not** import `_lead_design`", and
this is that copy: `eOf_connMap` is used by

* **D3** `Work.SSGRoute.ArchDictionary.eOf_connMap_cocycle` (`ArchDictionary/eOf_connMap_cocycle.lean`),
  which is its first step, and through D3 by
* **D2** `Work.SSGRoute.ArchDictionary.archPhiSeam_square` (step 5 of `ARCHP2_PLAN.md` §3);

so a consumer should `import Submission.Work.SSGRoute.ArchDictionary.eOfConnMap` and use
`Work.SSGRoute.ArchDictionary.eOf_connMap` **instead of** re-declaring a copy in their own file
(re-declaring it in this namespace would clash).

Proved: `#print axioms` of the original is `[propext, Classical.choice, Quot.sound]` (see
`_lead_design/archp2_1008/ARCHP2_PLAN.out`).
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

section A

variable {G : Type} [Group G]

theorem eOf_connMap (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    (M : Rep.{0} Coeff G) (a : Abelian.Ext (NatH1.pres M).X₁ N 0) :
    haveI : Subsingleton (Abelian.Ext (unitRep G) (NatH1.dpres N M).X₂ 1) :=
      ext_one_homRepFree_subsingleton G M.V N (X M) (hX M)
    NatH1.eOf N hInj X hX M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a) =
      (NatH1.gammaIso N M).symm
        (CokerNat.connMapCov (NatH1.dpres_shortExact N hInj M) (unitRep G) (NatH1.cEq N M a)) := by
  haveI : Subsingleton (Abelian.Ext (unitRep G) (NatH1.dpres N M).X₂ 1) :=
    ext_one_homRepFree_subsingleton G M.V N (X M) (hX M)
  show (NatH1.gammaIso N M).symm ((NatH1.e2 N hInj M).symm (NatH1.cmp N M
      (NatH1.e1 N M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)))) = _
  have h1 : NatH1.e1 N M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)
      = QuotientAddGroup.mk' (CokerNat.preMap (NatH1.pres M) N).range a :=
    CokerNat.cokerIso_apply_connMap (SSGRoute.ses_shortExact M) N a
  have h2 : NatH1.cmp N M (QuotientAddGroup.mk' (CokerNat.preMap (NatH1.pres M) N).range a)
      = QuotientAddGroup.mk' (CokerNat.postMap (NatH1.dpres N M) (unitRep G)).range
          (NatH1.cEq N M a) :=
    NatH1.cHom_mk' N M a
  rw [h1, h2]
  exact congrArg (NatH1.gammaIso N M).symm
    (CokerNat.cokerIsoCov_symm_mk (NatH1.dpres_shortExact N hInj M) (unitRep G)
      (NatH1.cEq N M a))

end A

end Work.SSGRoute.ArchDictionary
