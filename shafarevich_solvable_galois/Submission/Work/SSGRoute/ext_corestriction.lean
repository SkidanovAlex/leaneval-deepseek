import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Tactic.Have
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ext_cor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory Limits

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

universe u₁ u₂ u₃ v₁ v₂ v₃



open SSGRoute.PTExt CategoryTheory Limits

theorem ext_mapExactFunctor_comp_functor_aux
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E]
    [HasExt.{0} C] [HasExt.{0} D] [HasExt.{0} E] [EnoughProjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    ∀ (n : ℕ) (X Y : C) (x : Abelian.Ext X Y n),
      (x.mapExactFunctor F).mapExactFunctor G = x.mapExactFunctor (F ⋙ G) := by
  intro n
  induction n with
  | zero =>
      intro X Y x
      obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X Y).2 x
      simp only [Abelian.Ext.mapExactFunctor_mk₀]
      rfl
  | succ n ih =>
      intro X Y x
      obtain ⟨P⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
      haveI : Projective S.X₂ := P.projective
      haveI : Subsingleton (Abelian.Ext S.X₂ Y (n + 1)) :=
        Abelian.Ext.subsingleton_of_projective S.X₂ Y n
      have hn₀ : 1 + n = n + 1 := Nat.add_comm 1 n
      have hx0 : (Abelian.Ext.mk₀ S.g).comp x (zero_add (n + 1)) = 0 := Subsingleton.elim _ _
      obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y x hx0 (hn₀)
      rw [← hw]
      have hcomp := Abelian.Ext.mapExactFunctor_comp F hS.extClass w hn₀
      refine Eq.trans (b := Abelian.Ext.mapExactFunctor G
        ((Abelian.Ext.mapExactFunctor F hS.extClass).comp
          (Abelian.Ext.mapExactFunctor F w) hn₀))
        ?_ ?_
      · exact congrArg (Abelian.Ext.mapExactFunctor G) hcomp
      refine Eq.trans (b := Abelian.Ext.mapExactFunctor G
        (((hS.map_of_exact F).extClass).comp
          (Abelian.Ext.mapExactFunctor F w) hn₀)) ?_ ?_
      · exact congrArg (Abelian.Ext.mapExactFunctor G) (congrArg
          (fun z => Abelian.Ext.comp z (Abelian.Ext.mapExactFunctor F w) hn₀)
          (Abelian.Ext.mapExactFunctor_extClass F hS))
      refine Eq.trans (b := (Abelian.Ext.mapExactFunctor G ((hS.map_of_exact F).extClass)).comp
        (Abelian.Ext.mapExactFunctor G (Abelian.Ext.mapExactFunctor F w)) hn₀) ?_ ?_
      · exact Abelian.Ext.mapExactFunctor_comp G (hS.map_of_exact F).extClass
          (Abelian.Ext.mapExactFunctor F w) hn₀
      refine Eq.trans (b := (((hS.map_of_exact F).map_of_exact G).extClass).comp
        (Abelian.Ext.mapExactFunctor G (Abelian.Ext.mapExactFunctor F w)) hn₀) ?_ ?_
      · exact congrArg (fun z => Abelian.Ext.comp z
          (Abelian.Ext.mapExactFunctor G (Abelian.Ext.mapExactFunctor F w)) hn₀)
          (Abelian.Ext.mapExactFunctor_extClass G (hS.map_of_exact F))
      refine Eq.trans (b := (((hS.map_of_exact F).map_of_exact G).extClass).comp
        (Abelian.Ext.mapExactFunctor (F ⋙ G) w) hn₀) ?_ ?_
      · exact congrArg (fun z => Abelian.Ext.comp
          (((hS.map_of_exact F).map_of_exact G).extClass) z hn₀) (ih S.X₁ Y w)
      refine Eq.trans (b := ((hS.map_of_exact (F ⋙ G)).extClass).comp
        (Abelian.Ext.mapExactFunctor (F ⋙ G) w) hn₀) ?_ ?_
      · rfl
      · exact ((Abelian.Ext.mapExactFunctor_comp (F ⋙ G) hS.extClass w hn₀).trans
          (congrArg (fun z => Abelian.Ext.comp z
            (Abelian.Ext.mapExactFunctor (F ⋙ G) w) hn₀)
            (Abelian.Ext.mapExactFunctor_extClass (F ⋙ G) hS))).symm




theorem ext_mapExactFunctor_naturality_aux
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{0} C] [EnoughProjectives C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (θ : NatTrans F (𝟭 C)) :
    ∀ (n : ℕ) (X Y : C) (x : Abelian.Ext X Y n),
      (x.mapExactFunctor F).comp (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n) =
        (Abelian.Ext.mk₀ (θ.app X)).comp x (zero_add n) := by
  intro n
  induction n with
  | zero =>
      intro X Y x
      obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X Y).2 x
      simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
      rw [θ.naturality f]
      rfl
  | succ n ih =>
      intro X Y x
      obtain ⟨P⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
      haveI : Projective S.X₂ := P.projective
      haveI : Subsingleton (Abelian.Ext S.X₂ Y (n + 1)) :=
        Abelian.Ext.subsingleton_of_projective S.X₂ Y n
      have hn₀ : 1 + n = n + 1 := Nat.add_comm 1 n
      have hx0 : (Abelian.Ext.mk₀ S.g).comp x (zero_add (n + 1)) = 0 := Subsingleton.elim _ _
      obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y x hx0 hn₀
      rw [← hw]
      have hcomp := Abelian.Ext.mapExactFunctor_comp F hS.extClass w hn₀
      have hassoc1 := Abelian.Ext.comp_assoc_of_third_deg_zero
        (Abelian.Ext.mapExactFunctor F hS.extClass) (Abelian.Ext.mapExactFunctor F w)
        (Abelian.Ext.mk₀ (θ.app Y)) hn₀
      have hih := ih S.X₁ Y w
      have hassoc2 := (Abelian.Ext.comp_assoc_of_second_deg_zero
        (Abelian.Ext.mapExactFunctor F hS.extClass) (Abelian.Ext.mk₀ (θ.app S.X₁)) w hn₀).symm
      have hmec := Abelian.Ext.mapExactFunctor_extClass F hS
      have hnat := ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact F)
        (hS.map_of_exact (𝟭 C)) (S.mapNatTrans θ)
      have hassoc3 : ((Abelian.Ext.mk₀ (θ.app X)).comp hS.extClass (zero_add 1)).comp w hn₀
          = (Abelian.Ext.mk₀ (θ.app X)).comp ((hS.extClass).comp w hn₀) (zero_add (n + 1)) :=
        Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (θ.app X)) hS.extClass w (zero_add 1) hn₀ (by omega)
      refine Eq.trans (b := ((Abelian.Ext.mapExactFunctor F hS.extClass).comp
        (Abelian.Ext.mapExactFunctor F w) hn₀).comp
        (Abelian.Ext.mk₀ (θ.app Y)) (add_zero (n + 1))) ?_ ?_
      · exact congrArg (fun z => z.comp (Abelian.Ext.mk₀ (θ.app Y)) (add_zero (n + 1))) hcomp
      refine Eq.trans (b := (Abelian.Ext.mapExactFunctor F hS.extClass).comp
        ((Abelian.Ext.mapExactFunctor F w).comp (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n)) hn₀)
        ?_ ?_
      · exact hassoc1
      refine Eq.trans (b := (Abelian.Ext.mapExactFunctor F hS.extClass).comp
        ((Abelian.Ext.mk₀ (θ.app S.X₁)).comp w (zero_add n)) hn₀) ?_ ?_
      · exact congrArg (fun z => (Abelian.Ext.mapExactFunctor F hS.extClass).comp z hn₀) hih
      refine Eq.trans (b := ((Abelian.Ext.mapExactFunctor F hS.extClass).comp
        (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)).comp w hn₀) ?_ ?_
      · exact hassoc2
      refine Eq.trans (b := (((hS.map_of_exact F).extClass).comp
        (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)).comp w hn₀) ?_ ?_
      · exact congrArg (fun z => z.comp w hn₀)
          (congrArg (fun y => y.comp (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)) hmec)
      refine Eq.trans (b := (((Abelian.Ext.mk₀ (θ.app X)).comp hS.extClass (zero_add 1)).comp w hn₀))
        ?_ ?_
      · exact congrArg (fun z => z.comp w hn₀) hnat
      · exact hassoc3



open SSGRoute.PTExt CategoryTheory Limits

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G)
  [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]

noncomputable def coindTraceNat :
    NatTrans (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype) (𝟭 (Rep Coeff G)) where
  app A := coindTrace S A
  naturality A B φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    show traceLin S B ((Representation.coindMap S.subtype
        ((Rep.resFunctor S.subtype).map φ).hom) f) = φ.hom (traceLin S A f)
    rw [traceLin_apply, traceLin_apply, map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Representation.coindMap_coe_apply_apply, Rep.resMap_hom_apply]
    exact (Rep.hom_comm_apply φ (Quotient.out q)⁻¹ (f.1 (Quotient.out q))).symm



/-- `Ext.mk₀` is `ℕ`-linear. -/
lemma mk₀_nsmul_aux {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{0} C]
    {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    Abelian.Ext.mk₀ (n • f) = n • Abelian.Ext.mk₀ f := by
  induction n with
  | zero => simp [Abelian.Ext.mk₀_zero]
  | succ k ih => rw [succ_nsmul', Abelian.Ext.mk₀_add, ih, succ_nsmul']

/-- `(n • α).comp β h = n • (α.comp β h)`. -/
lemma nsmul_comp_aux {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{0} C]
    {X Y Z : C} {a b c : ℕ} (n : ℕ) (α : Abelian.Ext X Y a) (β : Abelian.Ext Y Z b)
    (h : a + b = c) :
    (n • α).comp β h = n • (α.comp β h) := by
  have h1 : (n • α).comp β h = (Abelian.Ext.bilinearComp X Y Z a b c h (n • α)) β := rfl
  rw [h1, map_nsmul]
  rfl

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G)
  [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]

/-- The corestriction map on `Ext`, before the identity is proved. -/
noncomputable def extCor (M A : Rep Coeff G) (n : ℕ) :
    (Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) n) →+ (Abelian.Ext M A n) :=
  (Abelian.Ext.postcomp (Abelian.Ext.mk₀ (coindTrace S A)) M (add_zero n)).comp
    ((Abelian.Ext.precomp (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M))
      (Rep.coind S.subtype (Rep.res S.subtype A)) (zero_add n)).comp
      ((Rep.coindFunctor Coeff S.subtype).mapExtAddHom (Rep.res S.subtype M)
        (Rep.res S.subtype A) n))

lemma extCor_apply (M A : Rep Coeff G) (n : ℕ)
    (y : Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) n) :
    extCor S M A n y
      = ((Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M)).comp
          (y.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)) (zero_add n)).comp
        (Abelian.Ext.mk₀ (coindTrace S A)) (add_zero n) := rfl

/-- **Corestriction on the derived `Ext`.** For a finite group `G` and a subgroup `S ≤ G` there is a
family of additive maps `cor : Extⁿ_S(res M, res A) → Extⁿ_G(M, A)` whose composite with the
restriction map `extRes S.subtype` is multiplication by the index `[G : S]`.

The infrastructure is already in place (import it):
* `Submission.Work.SSGRoute.ext_coind_exact` — `Rep.coindFunctor Coeff S.subtype` is `Additive`,
  preserves zero morphisms and (after `Rep.indCoindNatIso`) finite colimits, so
  `Abelian.Ext.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)` is available.
* `Submission.Work.SSGRoute.ext_cor` — the trace `Work.SSGRoute.coindTrace S A` over
  `Coeff = ULift ℤ` and the adjunction identity
  `Work.SSGRoute.unit_comp_coindTrace : η ≫ coindTrace = S.index • 𝟙`, where `η` is the unit of
  `Rep.resCoindAdjunction Coeff S.subtype`.

Suggested construction: `cor M A n y :=
((Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M)).comp
    (y.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)) rfl).comp
  (Abelian.Ext.mk₀ (Work.SSGRoute.coindTrace S A)) rfl`.
For the identity: `extRes S.subtype x` is `x.mapExactFunctor (Rep.resFunctor S.subtype)`, so one
needs the functor-composition lemma `(x.mapExactFunctor F).mapExactFunctor G =
x.mapExactFunctor (F ⋙ G)` (provable from `Abelian.Ext.mapExactFunctor_hom` and the functoriality of
`Functor.mapDerivedCategory`), then the naturality of `unit`/`coindTrace` (as natural
transformations `Id ⟹ Res ⋙ Coind` and `Res ⋙ Coind ⟹ Id`, giving
`tr ≫ (Res ⋙ Coind)(x) = x ≫ tr` at the `Ext` level) and finally
`Work.SSGRoute.unit_comp_coindTrace`.  Additivity of `cor` follows from
`Abelian.Ext.mapExactFunctor_add` and `Abelian.Ext.comp_add`. -/
theorem ext_corestriction {G : Type} [Group G] [Fintype G] (S : Subgroup G) :
    ∃ cor : (M A : Rep Coeff G) → (n : ℕ) →
        (Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) n) →+ (Abelian.Ext M A n),
      ∀ (M A : Rep Coeff G) (n : ℕ) (x : Abelian.Ext M A n),
        cor M A n (extRes S.subtype x) = S.index • x := by
  classical
  haveI hdec : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  haveI hfin : Fintype (G ⧸ S) := Fintype.ofFinite _
  refine ⟨fun M A n => extCor S M A n, ?_⟩
  intro M A n x
  have hnat : (x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype)).comp
        (Abelian.Ext.mk₀ (coindTrace S A)) (add_zero n)
      = (Abelian.Ext.mk₀ (coindTrace S M)).comp x (zero_add n) :=
    ext_mapExactFunctor_naturality_aux (C := Rep Coeff G)
      (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype) (coindTraceNat S) n M A x
  have hlast : (S.index • Abelian.Ext.mk₀ (𝟙 M)).comp x (zero_add n) = S.index • x := by
    rw [nsmul_comp_aux, Abelian.Ext.mk₀_id_comp x]
  have hmk : (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M)).comp
        (Abelian.Ext.mk₀ (coindTrace S M)) (add_zero 0) = S.index • Abelian.Ext.mk₀ (𝟙 M) := by
    rw [Abelian.Ext.mk₀_comp_mk₀, Work.SSGRoute.unit_comp_coindTrace S M, mk₀_nsmul_aux]
  have hcomp := ext_mapExactFunctor_comp_functor_aux (C := Rep Coeff G) (D := Rep Coeff S)
    (E := Rep Coeff G) (Rep.resFunctor S.subtype) (Rep.coindFunctor Coeff S.subtype) n M A x
  rw [extCor_apply]
  change ((Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M)).comp
      ((x.mapExactFunctor (Rep.resFunctor S.subtype)).mapExactFunctor
        (Rep.coindFunctor Coeff S.subtype)) (zero_add n)).comp
      (Abelian.Ext.mk₀ (coindTrace S A)) (add_zero n) = S.index • x
  rw [hcomp, Abelian.Ext.comp_assoc_of_third_deg_zero, hnat,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, hmk, hlast]


end Work.SSGRoute
