import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.smallSpan_inf
import Submission.Work.SingMV.injective_map_inclTop
import Submission.Work.SingMV.SdAux

/-!
# The Mayer–Vietoris comparison map is a monomorphism

For a topological space `X` and subsets `U V ⊆ X`, the canonical map

`pushoutMap X U V : pushout (C(U∩V) → C(U)) (C(U∩V) → C(V)) ⟶ C(X)`

from the pushout of the inclusions of the singular chains of `U ∩ V` into those of `U` and `V`
to the singular chains of `X` is a monomorphism of chain complexes.

This is the "easy half" of the small-simplices Mayer–Vietoris theorem (Hatcher,
Proposition 2.21): its image is the subcomplex of `(U,V)`-small chains.

## Route

Monomorphisms of chain complexes of `ℤ`-modules are detected degreewise
(`HomologicalComplex.mono_of_mono_f`), so it suffices to show that for every `n` the map

`(pushoutMap X U V).f n : (pushout (C_n(U∩V) → C_n(U)) (C_n(U∩V) → C_n(V))) ⟶ C_n(X)`

is injective.  The evaluation functor to `ModuleCat ℤ` preserves the pushout
(`pushoutComparison`), so this reduces to the following statement in `ModuleCat ℤ`: if `p`, `q`
are the maps on `n`-chains induced by the inclusions `U ⊆ X`, `V ⊆ X` and `f`, `g` those induced
by `U ∩ V ⊆ U`, `U ∩ V ⊆ V`, then the canonical map from `C_n(U ∩ V)` to the pullback of `p`
and `q` is an isomorphism.

That pullback statement is `moduleCat_isPullback_of_range_inf` below; its hypothesis is the
computation of `range (C_n(U∩V) → C_n(U) → C_n(X))` as the intersection of the ranges of
`C_n(U) → C_n(X)` and `C_n(V) → C_n(X)`, which is `range_singC_map_inclTop` combined with
`smallSpan_inf`: the chains carried by `U ∩ V` are exactly those carried by both `U` and `V`.
The identification `range (C_n(U) → C_n(X)) = smallSpan X n U` is proved here in two steps:
`smallSpan_le_range` (a chain carried by `U` is a sum of generators of simplices lying in `U`,
each of which is pushed forward from `C_n(U)`) and `range_le_smallSpan` (the converse, via the
naturality `eLin_map` of the identification of `C_n(X)` with the free module on the singular
`n`-simplices).
-/

open CategoryTheory Limits
open Submission.Blueprint

noncomputable section

namespace Work.SingMV

open Work.SingMV.SmallSpanAux

/-! ## The range of the map induced on chains by the inclusion of a subspace -/

/-- The singular `n`-chains of `X` are spanned by the generators attached to its singular
`n`-simplices, i.e. `smallSpan` of the whole space is everything. -/
theorem smallSpan_univ (X : TopCat) (n : ℕ) : smallSpan X n (Set.univ : Set X) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  rw [mem_smallSpan_iff]
  exact fun _ _ _ => trivial

/-- A chain carried by `U` is the image of a chain of `U` under `C_n(U) → C_n(X)`: each generator
of `smallSpan X n U` is the pushforward of the generator of the corresponding simplex of `U`. -/
theorem smallSpan_le_range (X : TopCat) (n : ℕ) (U : Set X) :
    smallSpan X n U ≤ LinearMap.range ((singC.map (inclTop U)).f n).hom := by
  rw [smallSpan, Submodule.span_le]
  rintro y ⟨σ, rfl⟩
  refine ⟨gen (TopCat.of U) n ⟨fun z => ⟨σ.1 z, σ.2 z⟩, by fun_prop⟩, ?_⟩
  rw [gen_map (TopCat.of U) X n (inclTop U)]
  congr 1

/-- The image in `C_n(X)` of a chain of `U` is a sum of generators of simplices lying in `U`:
the generators of the chains of `U` are pushed forward to generators of simplices of `U`. -/
theorem range_le_smallSpan (X : TopCat) (n : ℕ) (U : Set X) :
    LinearMap.range ((singC.map (inclTop U)).f n).hom ≤ smallSpan X n U := by
  have hspan : Submodule.map ((singC.map (inclTop U)).f n).hom
      (smallSpan (TopCat.of U) n (Set.univ : Set (TopCat.of U))) ≤ smallSpan X n U := by
    rw [smallSpan, Submodule.map_span, Submodule.span_le]
    rintro y ⟨x, ⟨σ, rfl⟩, rfl⟩
    rw [gen_map (TopCat.of U) X n (inclTop U) σ.1]
    exact Submodule.subset_span ⟨⟨(inclTop U).hom.comp σ.1, fun z => (σ.1 z).2⟩, rfl⟩
  rwa [LinearMap.range_eq_map, ← smallSpan_univ (TopCat.of U) n]

/-- **The range of `C_n(U) → C_n(X)`.**  The singular `n`-chains of `X` that are pushforwards of
chains of `U` are exactly the chains carried by `U`. -/
theorem range_singC_map_inclTop (X : TopCat) (n : ℕ) (U : Set X) :
    LinearMap.range ((singC.map (inclTop U)).f n).hom = smallSpan X n U :=
  le_antisymm (range_le_smallSpan X n U) (smallSpan_le_range X n U)

/-! ## A pullback criterion in `ModuleCat ℤ` -/

/-- If a commutative square of `ℤ`-modules

`A --f--> B --p--> E`, `A --g--> D --q--> E`

with `f ≫ p = g ≫ q` satisfies `range (f ≫ p) = range p ⊓ range q`, with `p`, `q` and `f ≫ p`
injective, then it is a pullback square. -/
theorem moduleCat_isPullback_of_range_inf {A B D E : ModuleCat ℤ} (f : A ⟶ B) (g : A ⟶ D)
    (p : B ⟶ E) (q : D ⟶ E) (w : f ≫ p = g ≫ q) [Mono p] [Mono q] [Mono (f ≫ p)]
    (h : LinearMap.range (f ≫ p).hom = LinearMap.range p.hom ⊓ LinearMap.range q.hom) :
    IsPullback f g p q := by
  have hp : Function.Injective ⇑p.hom := (ModuleCat.mono_iff_injective p).mp inferInstance
  have hq : Function.Injective ⇑q.hom := (ModuleCat.mono_iff_injective q).mp inferInstance
  have hfp : Function.Injective ⇑(f ≫ p).hom :=
    (ModuleCat.mono_iff_injective (f ≫ p)).mp inferInstance
  have hf : Function.Injective ⇑f.hom := by
    intro x y hxy
    apply hfp
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  letI : Module ℤ ↥((f ≫ p).hom.range) := ((f ≫ p).hom.range).module
  let e := LinearEquiv.ofInjective (f ≫ p).hom hfp
  refine IsPullback.mk' w ?_ ?_
  · intro T φ φ' h₁ _
    apply ModuleCat.hom_ext
    ext x
    apply hf
    have hx := congrArg (fun u : T ⟶ B => (u.hom : ↑T → ↑B) x) h₁
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using hx
  · intro T a b hab
    have hb : ∀ t : ↑T, p.hom (a.hom t) = q.hom (b.hom t) := fun t => by
      have ht := congrArg (fun u : T ⟶ E => (u.hom : ↑T → ↑E) t) hab
      simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using ht
    let Ψ := LinearMap.codRestrict ((f ≫ p).hom.range) (p.hom.comp a.hom) fun t => by
      rw [h]
      exact ⟨⟨a.hom t, rfl⟩, ⟨b.hom t, (hb t).symm⟩⟩
    let L := e.symm.toLinearMap.comp Ψ
    have hL : ∀ t : ↑T, (f ≫ p).hom (L t) = p.hom (a.hom t) := fun t => by
      have h1 : e (L t) = Ψ t := LinearEquiv.apply_symm_apply e (Ψ t)
      have h2 : ((e (L t) : (f ≫ p).hom.range) : E) = p.hom (a.hom t) := by
        rw [h1]
        rfl
      exact h2
    refine ⟨ModuleCat.ofHom L, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      ext t
      change f.hom (L t) = a.hom t
      apply hp
      change (f ≫ p).hom (L t) = p.hom (a.hom t)
      exact hL t
    · apply ModuleCat.hom_ext
      ext t
      change g.hom (L t) = b.hom t
      apply hq
      change (g ≫ q).hom (L t) = q.hom (b.hom t)
      rw [← w, hL t, hb t]

/-! ## The square of chain complexes -/

variable (X : TopCat) (U V : Set X)

theorem incl_comp_inclTop :
    incl (Set.inter_subset_left : U ∩ V ⊆ U) ≫ inclTop U = inclTop (U ∩ V : Set X) := by
  ext x
  rfl

theorem incl_comp_inclTop' :
    incl (Set.inter_subset_right : U ∩ V ⊆ V) ≫ inclTop V = inclTop (U ∩ V : Set X) := by
  ext x
  rfl

theorem map_incl_comp_map_inclTop (n : ℕ) :
    ((singC.map (incl (Set.inter_subset_left : U ∩ V ⊆ U))).f n) ≫
        ((singC.map (inclTop U)).f n)
      = (singC.map (inclTop (U ∩ V : Set X))).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, incl_comp_inclTop X U V]

theorem map_incl_comp_map_inclTop' (n : ℕ) :
    ((singC.map (incl (Set.inter_subset_right : U ∩ V ⊆ V))).f n) ≫
        ((singC.map (inclTop V)).f n)
      = (singC.map (inclTop (U ∩ V : Set X))).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, incl_comp_inclTop' X U V]

/-- The square of spaces (and hence of chain complexes) is commutative. -/
theorem map_incl_comp_inclTop_eq :
    (singC.map (incl (Set.inter_subset_left : U ∩ V ⊆ U))) ≫ (singC.map (inclTop U)) =
      (singC.map (incl (Set.inter_subset_right : U ∩ V ⊆ V))) ≫ (singC.map (inclTop V)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, incl_comp_inclTop X U V, incl_comp_inclTop' X U V]

/-- **The intersection square is a pullback square**, in every degree. -/
theorem isPullback_degree (n : ℕ) :
    IsPullback
      ((singC.map (incl (Set.inter_subset_left : U ∩ V ⊆ U))).f n)
      ((singC.map (incl (Set.inter_subset_right : U ∩ V ⊆ V))).f n)
      ((singC.map (inclTop U)).f n)
      ((singC.map (inclTop V)).f n) := by
  haveI hp : Mono ((singC.map (inclTop U)).f n) :=
    (ModuleCat.mono_iff_injective _).mpr (injective_map_inclTop X n U)
  haveI hq : Mono ((singC.map (inclTop V)).f n) :=
    (ModuleCat.mono_iff_injective _).mpr (injective_map_inclTop X n V)
  haveI hfp : Mono (((singC.map (incl (Set.inter_subset_left : U ∩ V ⊆ U))).f n) ≫
      ((singC.map (inclTop U)).f n)) := by
    rw [map_incl_comp_map_inclTop X U V n]
    exact (ModuleCat.mono_iff_injective _).mpr (injective_map_inclTop X n (U ∩ V))
  refine moduleCat_isPullback_of_range_inf _ _ _ _ ?_ ?_
  · rw [map_incl_comp_map_inclTop X U V n, map_incl_comp_map_inclTop' X U V n]
  · rw [map_incl_comp_map_inclTop X U V n, range_singC_map_inclTop X n (U ∩ V),
      range_singC_map_inclTop X n U, range_singC_map_inclTop X n V]
    exact (smallSpan_inf X n U V).symm

/-! ## The main theorem -/

theorem mono_pushout_desc (X : TopCat) (U V : Set X) :
    CategoryTheory.Mono (Work.SingMV.pushoutMap X U V) := by
  refine HomologicalComplex.mono_of_mono_f _ (fun n => ?_)
  let G := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
  show CategoryTheory.Mono (G.map (pushoutMap X U V))
  let tt := singC.map (incl (Set.inter_subset_left : U ∩ V ⊆ U))
  let ll := singC.map (incl (Set.inter_subset_right : U ∩ V ⊆ V))
  let uu := singC.map (inclTop U)
  let vv := singC.map (inclTop V)
  have hInl : pushout.inl tt ll ≫ pushoutMap X U V = uu := by
    unfold pushoutMap
    exact pushout.inl_desc _ _ _
  have hInr : pushout.inr tt ll ≫ pushoutMap X U V = vv := by
    unfold pushoutMap
    exact pushout.inr_desc _ _ _
  haveI hpu : Mono (G.map uu) :=
    (ModuleCat.mono_iff_injective _).mpr (injective_map_inclTop X n U)
  let φ : pushout (G.map tt) (G.map ll) ⟶ G.obj (singC.obj X) :=
    pushout.desc (G.map uu) (G.map vv)
      (by rw [← G.map_comp, ← G.map_comp]; exact congrArg G.map (map_incl_comp_inclTop_eq X U V))
  have hpush : IsPushout (G.map tt) (G.map ll)
      (pushout.inl (G.map tt) (G.map ll)) (pushout.inr (G.map tt) (G.map ll)) :=
    IsPushout.mk ⟨pushout.condition⟩ ⟨pushoutIsPushout (G.map tt) (G.map ll)⟩
  have hpull : IsPullback (G.map tt) (G.map ll) (G.map uu) (G.map vv) :=
    isPullback_degree X U V n
  have hk : CategoryTheory.Mono φ :=
    IsPushout.mono_of_isPullback_of_mono hpush hpull φ (pushout.inl_desc _ _ _)
      (pushout.inr_desc _ _ _)
  have hEq : pushoutComparison G tt ll ≫ G.map (pushoutMap X U V) = φ := by
    apply pushout.hom_ext
    · rw [← Category.assoc, inl_comp_pushoutComparison, ← G.map_comp, hInl]
      exact (pushout.inl_desc (G.map uu) (G.map vv) _).symm
    · rw [← Category.assoc, inr_comp_pushoutComparison, ← G.map_comp, hInr]
      exact (pushout.inr_desc (G.map uu) (G.map vv) _).symm
  haveI : Mono (pushoutComparison G tt ll ≫ G.map (pushoutMap X U V)) := hEq ▸ hk
  have hkey : (PreservesPushout.iso G tt ll).inv ≫
      (pushoutComparison G tt ll ≫ G.map (pushoutMap X U V)) = G.map (pushoutMap X U V) := by
    rw [← Category.assoc, ← PreservesPushout.iso_hom, Iso.inv_hom_id, Category.id_comp]
  rw [← hkey]
  infer_instance

end Work.SingMV
