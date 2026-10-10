import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Tactic.Have
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.local_ext_h1_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory

universe u v w w'

/-- In positive degrees, `Ext P Y n` vanishes when `P` is projective. -/
lemma ext_subsingleton_of_projective_pos {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (P Y : C) [Projective P] {n : ℕ} (hn : 1 ≤ n) :
    Subsingleton (Abelian.Ext.{w} P Y n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact Abelian.Ext.subsingleton_of_projective P Y m

/-- **The connecting map `Ext^n(X₁,Y) → Ext^{n+1}(X₃,Y)` of a short exact sequence with
projective middle term is a bijection in degrees `n ≥ 1`.** This is the classical "syzygy shift":
the long exact sequence degenerates because both `Ext^n(X₂,Y)` and `Ext^{n+1}(X₂,Y)` vanish. -/
lemma bijective_extClass_precomp {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂] (Y : C)
    {n : ℕ} (hn1 : 1 ≤ n) (h : 1 + n = n + 1) :
    Function.Bijective (hS.extClass.precomp Y h :
      Abelian.Ext.{w} S.X₁ Y n → Abelian.Ext.{w} S.X₃ Y (n + 1)) := by
  haveI : Subsingleton (Abelian.Ext.{w} S.X₂ Y n) :=
    ext_subsingleton_of_projective_pos S.X₂ Y hn1
  constructor
  · intro x y hxy
    have hxy' : hS.extClass.precomp Y h (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzero : hS.extClass.comp (x - y) h = 0 := hxy'
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y (x - y) h hzero
    have hx₂0 : x₂ = 0 := Subsingleton.elim x₂ 0
    rw [hx₂0] at hx₂
    simp at hx₂
    exact sub_eq_zero.mp hx₂.symm
  · intro y
    haveI : Subsingleton (Abelian.Ext.{w} S.X₂ Y (n + 1)) :=
      Abelian.Ext.subsingleton_of_projective S.X₂ Y n
    have hy : (Abelian.Ext.mk₀ S.g).comp y (zero_add (n + 1)) = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hy h
    exact ⟨x, hx⟩

/-- **The connecting map of a short exact sequence with projective middle term, transported
along an exact functor `F`.** Both the source and target connecting maps are bijections, and
they are compatible with `Ext.mapExactFunctor F`. -/
lemma bijective_extClass_precomp_map {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{w} D]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂] (Y : C)
    {n : ℕ} (hn1 : 1 ≤ n) (h : 1 + n = n + 1) (x : Abelian.Ext.{w} S.X₁ Y n) :
    (hS.extClass.comp x h).mapExactFunctor F =
      (hS.map_of_exact F).extClass.comp (x.mapExactFunctor F) h := by
  rw [Abelian.Ext.mapExactFunctor_comp F hS.extClass x h,
    Abelian.Ext.mapExactFunctor_extClass F hS]
  try rfl

/-- **Naturality of the syzygy shift under restriction to a subgroup.**  For a short exact
sequence `0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` with projective middle term, a subgroup
`D ≤ G`, a coefficient `Y` and a degree `n ≥ 1`, there are degree shifts
`e : Ext^n(X₁,Y) ≅ Ext^{n+1}(X₃,Y)` and `eD : Ext^n(res X₁, res Y) ≅ Ext^{n+1}(res X₃, res Y)`
for the restricted sequence which are compatible with the restriction map `extRes D.subtype`.
This is the "restriction of the canonical resolution" step: it lets the `Ext`-side dictionary of
`E1a` be compared with its localisation at the decomposition groups `D_w`, which is what the
coherence of the global and local dictionaries needs. -/
theorem ext_shift_natural_res {G : Type} [Group G] (D : Subgroup G)
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) [CategoryTheory.Projective S.X₂]
    (Y : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) (hn1 : 1 ≤ n) :
    ∃ (e : CategoryTheory.Abelian.Ext.{0} S.X₁ Y n ≃+
        CategoryTheory.Abelian.Ext.{0} S.X₃ Y (n + 1))
      (eD : CategoryTheory.Abelian.Ext.{0} (Rep.res D.subtype S.X₁) (Rep.res D.subtype Y) n ≃+
        CategoryTheory.Abelian.Ext.{0} (Rep.res D.subtype S.X₃) (Rep.res D.subtype Y) (n + 1)),
      ∀ x : CategoryTheory.Abelian.Ext.{0} S.X₁ Y n,
        SSGRoute.PTExt.extRes D.subtype (e x) = eD (SSGRoute.PTExt.extRes D.subtype x) := by
  have h : 1 + n = n + 1 := by omega
  have hbij : Function.Bijective (hS.extClass.precomp Y h :
      Abelian.Ext.{0} S.X₁ Y n → Abelian.Ext.{0} S.X₃ Y (n + 1)) :=
    bijective_extClass_precomp hS Y hn1 h
  let F : Rep.{0} SSGRoute.PTExt.Coeff G ⥤ Rep.{0} SSGRoute.PTExt.Coeff ↥D :=
    Rep.resFunctor D.subtype
  haveI : Projective (S.map F).X₂ := Functor.projective_obj F S.X₂
  have hSD : (S.map F).ShortExact := hS.map_of_exact F
  have hbijD : Function.Bijective (hSD.extClass.precomp (F.obj Y) h :
      Abelian.Ext.{0} (F.obj S.X₁) (F.obj Y) n →
        Abelian.Ext.{0} (F.obj S.X₃) (F.obj Y) (n + 1)) :=
    bijective_extClass_precomp hSD (F.obj Y) hn1 h
  let φ : Abelian.Ext.{0} (Rep.res D.subtype S.X₁) (Rep.res D.subtype Y) n →+
      Abelian.Ext.{0} (Rep.res D.subtype S.X₃) (Rep.res D.subtype Y) (n + 1) :=
    hSD.extClass.precomp (F.obj Y) h
  have hφ : Function.Bijective ⇑φ := hbijD
  refine ⟨AddEquiv.ofBijective (hS.extClass.precomp Y h) hbij,
          AddEquiv.ofBijective φ hφ, ?_⟩
  intro x
  rw [AddEquiv.ofBijective_apply, AddEquiv.ofBijective_apply]
  show (hS.extClass.comp x h).mapExactFunctor F =
    hSD.extClass.comp (x.mapExactFunctor F) h
  exact bijective_extClass_precomp_map F hS Y hn1 h x

end Work.SSGRoute.ExtChain
