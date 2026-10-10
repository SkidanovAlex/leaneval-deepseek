import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.mackey_iso_explicit
import Submission.Work.SSGRoute.natTrans_mapExactFunctor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# The Mackey formula `res_f ∘ cor_S^D = cor_{S'}^G ∘ res_{f|S'}` via the explicit Mackey isomorphism

`Work.SSGRoute.ext_conj_comp` (`Submission/Work/SSGRoute/extRes_extCor_comap.lean`) reduces the
Mackey formula for `extCor` to: a natural isomorphism `θ` between the two conjugate functors,
intertwining the units (`MackeyIso.unit_compat`) and the traces (`MackeyIso.trace_compat`).  Here the
isomorphism is the explicit one of `Submission/Work/SSGRoute/mackey_iso_explicit.lean`, whose unit
compatibility is already proved; only its trace compatibility is taken as a hypothesis.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module


namespace MackeyIso

variable {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]

/-- **Abstract conjugation step.**  For exact additive functors `Φ Ψ : C ⤳ D'`, a natural
transformation `θ : Φ ⟹ Ψ` and morphisms `u : X' ⟶ Φ X`, `u' : X' ⟶ Ψ X`, `t : Φ Y ⟶ Y'`,
`t' : Ψ Y ⟶ Y'` with `u ≫ θ_X = u'` and `θ_Y ≫ t' = t`,
`mk₀ u ∘ Φ(x) ∘ mk₀ t = mk₀ u' ∘ Ψ(x) ∘ mk₀ t'`. -/
theorem ext_conj_comp
    {C : Type*} [Category* C] [Abelian C] [HasExt.{0} C] [EnoughProjectives C]
    {D' : Type*} [Category* D'] [Abelian D'] [HasExt.{0} D']
    (Φ Ψ : C ⥤ D') [Φ.Additive] [CategoryTheory.Limits.PreservesFiniteLimits Φ]
    [CategoryTheory.Limits.PreservesFiniteColimits Φ] [Ψ.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits Ψ]
    [CategoryTheory.Limits.PreservesFiniteColimits Ψ]
    (θ : Φ ⟶ Ψ) {X Y : C} {X' Y' : D'} {n : ℕ} (x : Abelian.Ext X Y n)
    (u : X' ⟶ Φ.obj X) (u' : X' ⟶ Ψ.obj X) (t : Φ.obj Y ⟶ Y') (t' : Ψ.obj Y ⟶ Y')
    (hu : u ≫ θ.app X = u') (ht : θ.app Y ≫ t' = t) :
    ((Abelian.Ext.mk₀ u).comp (x.mapExactFunctor Φ) (zero_add n)).comp
        (Abelian.Ext.mk₀ t) (add_zero n)
      = ((Abelian.Ext.mk₀ u').comp (x.mapExactFunctor Ψ) (zero_add n)).comp
        (Abelian.Ext.mk₀ t') (add_zero n) := by
  have hnat := mapExactFunctor_natTrans_naturality (C := C) (D := D') Φ Ψ θ n X Y x
  conv_lhs => rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  conv_lhs => rw [← ht]
  conv_lhs => rw [← Abelian.Ext.mk₀_comp_mk₀]
  conv_lhs => rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
  conv_lhs => rw [hnat]
  conv_lhs => rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  conv_lhs => rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
  conv_lhs => rw [Abelian.Ext.mk₀_comp_mk₀, hu]
  conv_lhs => rw [← Abelian.Ext.comp_assoc_of_third_deg_zero]


/-- **The Mackey formula for `extCor`** (from the trace compatibility of the explicit Mackey
isomorphism). -/
theorem extRes_extCor_comap_of_trace (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (hTr : ∀ (A : Rep.{0} SSGRoute.PTExt.Coeff D),
      CategoryTheory.CategoryStruct.comp ((iso f hf S).inv.app (Rep.res S.subtype A))
        ((Rep.resFunctor f).map (coindTrace S A)) = coindTrace (S.comap f) (Rep.res f A))
    (M A : Rep.{0} SSGRoute.PTExt.Coeff D) (n : ℕ)
    (z : Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) n) :
    extRes f (extCor S M A n z) =
      extCor (S.comap f) (Rep.res f M) (Rep.res f A) n (extRes (f.subgroupComap S) z) := by
  classical
  have hL : extRes f (extCor S M A n z)
      = ((Abelian.Ext.mk₀ (Rep.resMap f
            ((Rep.resCoindAdjunction SSGRoute.PTExt.Coeff S.subtype).unit.app M))).comp
          (Abelian.Ext.mapExactFunctor
            (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f) z)
          (zero_add n)).comp
          (Abelian.Ext.mk₀ (Rep.resMap f (coindTrace S A))) (add_zero n) := by
    rw [extRes, extCor_apply]
    rw [Abelian.Ext.mapExactFunctor_comp]
    rw [Abelian.Ext.mapExactFunctor_comp]
    rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_mk₀]
    rw [ext_mapExactFunctor_comp_functor_aux]
  have hR : extCor (S.comap f) (Rep.res f M) (Rep.res f A) n
        (extRes (f.subgroupComap S) z)
      = ((Abelian.Ext.mk₀ ((Rep.resCoindAdjunction SSGRoute.PTExt.Coeff
              (S.comap f).subtype).unit.app (Rep.res f M))).comp
          (Abelian.Ext.mapExactFunctor
            (Rep.resFunctor (f.subgroupComap S) ⋙
              Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype) z)
          (zero_add n)).comp
          (Abelian.Ext.mk₀ (coindTrace (S.comap f) (Rep.res f A))) (add_zero n) := by
    rw [extRes, extCor_apply]
    rw [ext_mapExactFunctor_comp_functor_aux]
  rw [hL, hR]
  have ht : (iso f hf S).hom.app (Rep.res S.subtype A) ≫ coindTrace (S.comap f) (Rep.res f A)
      = Rep.resMap f (coindTrace S A) := by
    rw [← hTr A, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact ext_conj_comp
    (Φ := Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f)
    (Ψ := Rep.resFunctor (f.subgroupComap S) ⋙
      Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype)
    (iso f hf S).hom z (Rep.resMap f ((Rep.resCoindAdjunction SSGRoute.PTExt.Coeff
      S.subtype).unit.app M))
    ((Rep.resCoindAdjunction SSGRoute.PTExt.Coeff (S.comap f).subtype).unit.app (Rep.res f M))
    (Rep.resMap f (coindTrace S A)) (coindTrace (S.comap f) (Rep.res f A))
    (unit_compat f hf S M) ht

/-- **The Mackey formula for `extCor`** (unconditional, via the explicit Mackey isomorphism and its
unit and trace compatibilities). -/
theorem extRes_extCor_comap_rdos (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (M A : Rep.{0} SSGRoute.PTExt.Coeff D) (n : ℕ)
    (z : Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) n) :
    extRes f (extCor S M A n z) =
      extCor (S.comap f) (Rep.res f M) (Rep.res f A) n (extRes (f.subgroupComap S) z) :=
  extRes_extCor_comap_of_trace f hf S (fun A => trace_compat f hf S A) M A n z


end MackeyIso

end Work.SSGRoute
