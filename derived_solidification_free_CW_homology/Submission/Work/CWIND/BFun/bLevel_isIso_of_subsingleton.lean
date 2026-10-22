import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.BFun.underlyingBijective
import Submission.Work.CWIND.BFun.sigmaIotaApplyInjective
import Submission.Work.CWIND.BFun.thePointBijective

/-!
# CWIND/T2 — the levelwise comparison is an isomorphism for a space with at most one point

For a topological space `X` with `Subsingleton ↥X` (so `X` is the empty space or the one-point
space) and `n : ℕ`, the level-`n` comparison map
`bLevel X n : ℤ[Singₙ X] ⟶ ℤ[X^{Δⁿ}]`
of `Basic.lean` is an isomorphism of light condensed abelian groups.

## Strategy

Write `T = X^{Δⁿ}` (the compact-open mapping space, a light condensed set) and `J = Singₙ X`, and
let `B = ℤ[X^{Δⁿ}] = freeLightCondAbOfTop T` be the free light condensed abelian group on `T`. By
definition `bLevel X n` is the transpose, under the adjunction `discrete ⊣ underlying`, of the map

`g : ℤ^{(J)} ⟶ Γ(ℤ[T])`,  `e_j ↦ theGen X n j`,

where `Γ = underlying` is evaluation at the one-point light profinite set and `theGen X n j` is the
generator of `ℤ[T]` at the point of `T` corresponding to the simplex `j`.

Every ingredient of the statement is *degenerate* because `X` has at most one point:

* `J = C(Δⁿ,X)` is empty (if `X = ∅`) or a singleton;
* `T(S) = C(S, C(Δⁿ,X))` is a subsingleton for every light profinite set `S`, so `T` is either the
  initial or the terminal light condensed set; in particular `Γ T` is a subsingleton, and every
  morphism `t : T ⟶ F` is determined by the function `Γ t : Γ T ⟶ Γ F` (`underlyingBijective`).

Concretely, for a fixed test object `A` we compare the two identifications

* `eB : (B ⟶ A) ≃ (Γ T ⟶ Γ A)`, `u ↦ Γ(unit ≫ forget u)` — bijective by the free–forget
  adjunction together with `underlyingBijective`;
* `eD : (ℤ^{(J)} ⟶ A) → (J → Γ A)`, `w ↦ (j ↦ (β w)(e_j))` — where `β` is the transpose of the
  discrete–underlying adjunction; injective because a morphism out of `ℤ^{(J)}` is determined by
  its values on the generators (`sigmaIotaApplyInjective`).

The key computation (`eD_apply`) is that these two identifications intertwine `bLevel X n` with
precomposition along the canonical identification `thePoint X n : J → Γ T`
(`thePointBijective`), which is a bijection because `J` and `Γ T` are both empty or both a
singleton. The Yoneda criterion `isIso_iff_coyoneda_map_bijective` then finishes the proof: `eB`
is bijective with inverse `eD`-style, so `bLevel X n` is an isomorphism. -/

namespace Work.CWIND.BFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The abelian group `Γ(ℤ[X^{Δⁿ}])` of sections of the free light condensed abelian group on
`X^{Δⁿ}` at the point. -/
abbrev gB (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  (LightCondensed.underlying (ModuleCat ℤ)).obj (freeLightCondAbOfTop (singSpace X n))

/-- The module `ℤ^{(Singₙ X)}` (the source of `bLevel X n`). -/
abbrev gM (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  ∐ fun _ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) => ModuleCat.of ℤ ℤ

/-- The set `Singₙ X` of singular `n`-simplices of `X`. -/
abbrev gJ (X : TopCat.{0}) (n : ℕ) : Type := (TopCat.toSSet.obj X).obj (op ⦋n⦌)

/-- `Γ A = A(∗)`, the underlying abelian group of `A`. -/
abbrev gGA (A : LightCondAb) : ModuleCat.{0} ℤ := (LightCondensed.underlying (ModuleCat ℤ)).obj A

/-- `Γ T` for `T = X^{Δⁿ}`, a light condensed set. -/
abbrev gO (X : TopCat.{0}) (n : ℕ) : Type :=
  (LightCondSet.underlying).obj (topCatToLightCondSet.obj (singSpace X n))

/-- The underlying type of `Γ A` viewed through the forgetful functor of light condensed sets. -/
abbrev gUA (A : LightCondAb) : Type :=
  (LightCondSet.underlying).obj ((LightCondensed.forget ℤ).obj A)

/-- The identification `(ℤ[X^{Δⁿ}] ⟶ A) → (Γ T ⟶ Γ A)` induced by the free–forget adjunction. -/
abbrev eB (X : TopCat.{0}) (n : ℕ) (A : LightCondAb) :
    (freeLightCondAbOfTop (singSpace X n) ⟶ A) → (gO X n ⟶ gUA A) :=
  fun u => (LightCondSet.underlying).map (((LightCondensed.freeForgetAdjunction ℤ).homEquiv
      (topCatToLightCondSet.obj (singSpace X n)) A) u)

/-- The identification `(ℤ^{(Singₙ X)} ⟶ A) → (Singₙ X → Γ A)` given by evaluating the transpose of
a morphism at the canonical generators. -/
abbrev eD (X : TopCat.{0}) (n : ℕ) (A : LightCondAb) :
    ((LightCondensed.discrete (ModuleCat ℤ)).obj (gM X n) ⟶ A) → (gJ X n → gUA A) :=
  fun w => fun y => (((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv (gM X n) A) w)
      (Limits.Sigma.ι (fun _ : gJ X n => ModuleCat.of ℤ ℤ) y 1)

/-- The map `g` underlying `bLevel X n`: the transpose of `bLevel X n` under `discrete ⊣ underlying`,
with components the generators `theGen X n j`. -/
def gL (X : TopCat.{0}) (n : ℕ) : gM X n ⟶ gB X n :=
  Sigma.desc (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (theGen X n x)))

/-- The defining property of `gL`: on the generator indexed by `y` it is `theGen X n y`. -/
lemma gL_apply (X : TopCat.{0}) (n : ℕ) (y : gJ X n) :
    (gL X n) (Limits.Sigma.ι (fun _ : gJ X n => ModuleCat.of ℤ ℤ) y 1) = theGen X n y := by
  rw [← ConcreteCategory.comp_apply]
  have h : Limits.Sigma.ι (fun _ : gJ X n => ModuleCat.of ℤ ℤ) y ≫ gL X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (theGen X n y)) :=
    Limits.Sigma.ι_comp_desc _ y
  rw [h, ModuleCat.ofHom_apply, LinearMap.toSpanSingleton_apply_one]

/-- The two ways of computing the underlying map of a morphism of light condensed abelian groups
agree (the forgetful functors commute, definitionally). -/
lemma underlying_map_apply {A B : LightCondAb} (u : A ⟶ B)
    (x : (LightCondSet.underlying).obj ((LightCondensed.forget ℤ).obj A)) :
    ((LightCondensed.underlying (ModuleCat ℤ)).map u) x
      = ((LightCondSet.underlying).map ((LightCondensed.forget ℤ).map u)) x := rfl

/-- `bLevel X n` is the transpose of `gL X n`. -/
lemma beta_bLevel_mul (X : TopCat.{0}) (n : ℕ) (A : LightCondAb)
    (u : freeLightCondAbOfTop (singSpace X n) ⟶ A) :
    ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv (gM X n) A)
      (bLevel X n ≫ u)
    = gL X n ≫ (LightCondensed.underlying (ModuleCat ℤ)).map u := by
  have hβ : ∀ (A' : LightCondAb) (f : (LightCondensed.discrete (ModuleCat ℤ)).obj (gM X n) ⟶ A'),
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ A') f =
        (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app _ ≫
          (LightCondensed.underlying (ModuleCat ℤ)).map f :=
    fun A' f => Adjunction.homEquiv_apply _ _ _ f
  have h1 : ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _) (bLevel X n)
      = gL X n := by
    rw [show bLevel X n = ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _
      ).symm (gL X n) from rfl, Equiv.apply_symm_apply]
  rw [hβ A (bLevel X n ≫ u), Functor.map_comp, ← Category.assoc,
    ← hβ (freeLightCondAbOfTop (singSpace X n)) (bLevel X n), h1]

/-- **The key square.** The identification `eD` intertwines `bLevel X n` with precomposition along
`thePoint X n`: for every `u` and every simplex `y`, the `y`-component of `eD (bLevel X n ≫ u)` is
the value of `eB u` at the point of `X^{Δⁿ}` classified by `y`. -/
lemma eD_apply (X : TopCat.{0}) (n : ℕ) (A : LightCondAb)
    (u : freeLightCondAbOfTop (singSpace X n) ⟶ A) :
    eD X n A (bLevel X n ≫ u) = fun y => ConcreteCategory.hom (eB X n A u)
      (Work.CWIND.thePoint X n y) := by
  funext y
  rw [show eD X n A (bLevel X n ≫ u) y =
      (((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv (gM X n) A)
        (bLevel X n ≫ u))
        (Limits.Sigma.ι (fun _ : gJ X n => ModuleCat.of ℤ ℤ) y 1) from rfl,
    beta_bLevel_mul X n A u, ConcreteCategory.comp_apply, gL_apply]
  simp only [theGen]
  erw [underlying_map_apply, ← types_comp_apply, ← Functor.map_comp, ← Adjunction.homEquiv_apply]

/-- **CWIND/T2.** For a space with at most one point (the point, or the empty space) the level-`n`
comparison map `bLevel X n : ℤ[Singₙ X] ⟶ ℤ[X^{Δⁿ}]` of `Basic.lean` is an isomorphism of light
condensed abelian groups: `Singₙ X` is a subsingleton set and every continuous map `Δⁿ → X` is the
unique one, so both sides are free on at most one point and the comparison is the canonical
isomorphism. -/
theorem bLevel_isIso_of_subsingleton (X : TopCat.{0}) [Subsingleton ↥X] (n : ℕ) :
    IsIso (bLevel X n) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro A
  -- `eB` is bijective: it is the free–forget adjunction composed with `t ↦ Γ t`.
  have h1 : Function.Bijective (eB X n A) := by
    have hb := underlyingBijective X n ((LightCondensed.forget ℤ).obj A)
    constructor
    · intro u u' h
      refine Equiv.injective ((LightCondensed.freeForgetAdjunction ℤ).homEquiv
        (topCatToLightCondSet.obj (singSpace X n)) A) ?_
      exact hb.injective (show
        (LightCondSet.underlying).map (((LightCondensed.freeForgetAdjunction ℤ).homEquiv
          (topCatToLightCondSet.obj (singSpace X n)) A) u) =
        (LightCondSet.underlying).map (((LightCondensed.freeForgetAdjunction ℤ).homEquiv
          (topCatToLightCondSet.obj (singSpace X n)) A) u') from h)
    · intro a
      obtain ⟨t, ht⟩ := hb.surjective a
      exact ⟨((LightCondensed.freeForgetAdjunction ℤ).homEquiv
        (topCatToLightCondSet.obj (singSpace X n)) A).symm t, by
          show (LightCondSet.underlying).map (((LightCondensed.freeForgetAdjunction ℤ).homEquiv
            (topCatToLightCondSet.obj (singSpace X n)) A)
            (((LightCondensed.freeForgetAdjunction ℤ).homEquiv
              (topCatToLightCondSet.obj (singSpace X n)) A).symm t)) = a
          rw [Equiv.apply_symm_apply]
          exact ht⟩
  -- `eD` is injective: a morphism out of `ℤ^{(Singₙ X)}` is determined by its values on generators.
  have h2 : Function.Injective (eD X n A) :=
    (sigmaIotaApplyInjective (gJ X n) (gGA A)).comp (Equiv.injective _)
  have hp : Function.Bijective (fun y : gJ X n => Work.CWIND.thePoint X n y) :=
    thePointBijective X n
  let pe := Equiv.ofBijective (fun y : gJ X n => Work.CWIND.thePoint X n y) hp
  have hpe : ∀ q, pe q = Work.CWIND.thePoint X n q := fun q => Equiv.ofBijective_apply _ _ q
  refine ⟨?_, ?_⟩
  · -- injectivity of `bLevel X n ≫ ·`
    intro u u' huv
    have huv' : bLevel X n ≫ u = bLevel X n ≫ u' := huv
    have hcomp : (fun y : gJ X n => ConcreteCategory.hom (eB X n A u)
        (Work.CWIND.thePoint X n y))
        = fun y => ConcreteCategory.hom (eB X n A u') (Work.CWIND.thePoint X n y) := by
      rw [← eD_apply X n A u, ← eD_apply X n A u', huv']
    have hmor : eB X n A u = eB X n A u' := by
      apply ConcreteCategory.hom_injective
      apply TypeCat.Fun.ext
      funext q
      obtain ⟨y, hy⟩ := hp.surjective q
      rw [← hy]
      exact congrFun hcomp y
    exact h1.injective hmor
  · -- surjectivity of `bLevel X n ≫ ·`
    intro w
    obtain ⟨a, ha⟩ : ∃ (a : gO X n ⟶ gUA A),
        ∀ y : gJ X n, ConcreteCategory.hom a (Work.CWIND.thePoint X n y) = eD X n A w y :=
      ⟨TypeCat.ofHom (fun q => eD X n A w (pe.symm q)), by
        intro y
        rw [TypeCat.ofHom_apply, ← hpe y, Equiv.symm_apply_apply]⟩
    obtain ⟨u, hu⟩ := h1.surjective a
    refine ⟨u, ?_⟩
    apply h2
    rw [eD_apply X n A u, hu]
    funext y
    exact ha y

end

end Work.CWIND.BFun
