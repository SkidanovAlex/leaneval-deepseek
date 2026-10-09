import Mathlib
import Submission.NK.LocalCFT.Brauer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `LocalH2Nonvanishing` versus the cohomology of the full Galois group

The definitions in `Submission/Work/LocalCFT/Brauer/Basic.lean` present the local Brauer input
`H²(G_κ, ℤ/p) ≠ 0` (`NK.LocalCFT.LocalH2Nonvanishing`) as a statement about the *colimit*
`NK.BrauerHasse.H2Profinite p ⊤ = colim_L H²(Gal(L/κ), ℤ/p)` over the finite Galois intermediate
fields `L` of `κ'/κ`, and separately as a statement about `H²(Gal(κ'/κ), ℤ/p)`, written
`NK.BrauerHasse.H2 p (κ' ≃ₐ[κ] κ')`.

This file proves that, whenever `κ'/κ` is *finite* — `[FiniteDimensional κ κ']`, together with
`[IsSepClosure κ κ']` so that the colimit is the one attached to a Galois extension — the two
statements agree:

`NK.LocalCFT.LocalH2Nonvanishing p κ κ' ↔ ∃ x : H²(Gal(κ'/κ), ℤ/p), x ≠ 0`.

This is the degenerate (but genuinely non-vacuous) case of the general principle "non-vanishing is
detected at the top level": under the hypotheses, the finite Galois intermediate fields have a
*top* element `κ'` itself.  Indeed, the normal closure of a finite separable extension of a
separably closed field is again a finite separable extension of that field, hence trivial, so
`κ'/κ` is Galois and `⊤` is a level of the colimit; the inflation maps out of `⊤` are the
identifications (`⊤ ≤ M` forces `M = ⊤`), so `ofLevel ⊤` is a bijection between the single level
`H²(Gal(κ'/κ), ℤ/p)` and the whole colimit.

Everything needed for the general (infinite) case — that the colimit really is the profinite
cohomology `H²(G_κ, ℤ/p)` — is not required: the argument below uses only the explicit colimit
description of `NK.BrauerHasse.H2Profinite` and the identification of the level at `⊤` with the
Galois group `Gal(κ'/κ)`.
-/

open CategoryTheory

universe u

namespace NK.LocalCFT.Brauer

/-! ## Two elementary transfers of the property `∃ x ≠ 0` -/

namespace Aux

/-- `∃ x ≠ 0` transfers across a bijection that maps `0` to `0`. -/
lemma exists_ne_zero_of_equiv {α β : Type*} [Zero α] [Zero β] (e : α ≃ β) (h0 : e 0 = 0) :
    (∃ x : α, x ≠ 0) ↔ ∃ y : β, y ≠ 0 := by
  have h0' : e.symm 0 = 0 := by
    apply e.injective
    simp [h0]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, fun h => hx ?_⟩
    have : e.symm (e x) = e.symm 0 := by rw [h]
    simpa [h0'] using this
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, fun h => hy ?_⟩
    have : e (e.symm y) = e 0 := by rw [h]
    simpa [h0] using this

/-- `∃ x ≠ 0` in `H²(·, ℤ/p)` transfers along an isomorphism of groups: `H²` is contravariantly
functorial in the group, and `H2.map` of a group isomorphism is an isomorphism of `ℤ/p`-modules
because `H2.map_comp` and `H2.map_id` exhibit `H2.map e` and `H2.map e.symm` as mutually inverse. -/
lemma H2_ne_zero_iff_of_mulEquiv {p : ℕ} {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    (∃ x : NK.BrauerHasse.H2 p G, x ≠ 0) ↔
      ∃ y : NK.BrauerHasse.H2 p H, y ≠ 0 := by
  have hid1 : ((e.symm : H →* G)).comp (e : G →* H) = MonoidHom.id G := by ext x; simp
  have hid2 : ((e : G →* H)).comp (e.symm : H →* G) = MonoidHom.id H := by ext x; simp
  have h1 : (NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)) ≫
      (NK.BrauerHasse.H2.map (p := p) (e : G →* H)) = 𝟙 (NK.BrauerHasse.H2 p G) := by
    rw [← NK.BrauerHasse.H2.map_comp (f := (e.symm : H →* G)) (g := (e : G →* H)), hid1,
      NK.BrauerHasse.H2.map_id]
  have h2 : (NK.BrauerHasse.H2.map (p := p) (e : G →* H)) ≫
      (NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)) = 𝟙 (NK.BrauerHasse.H2 p H) := by
    rw [← NK.BrauerHasse.H2.map_comp (f := (e : G →* H)) (g := (e.symm : H →* G)), hid2,
      NK.BrauerHasse.H2.map_id]
  have keyG : ∀ z : NK.BrauerHasse.H2 p G,
      (NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom
        ((NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)).hom z) = z := by
    intro z
    have := congrArg (fun (f : NK.BrauerHasse.H2 p G ⟶ NK.BrauerHasse.H2 p G) => f.hom z) h1
    simpa using this
  have keyH : ∀ z : NK.BrauerHasse.H2 p H,
      (NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)).hom
        ((NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom z) = z := by
    intro z
    have := congrArg (fun (f : NK.BrauerHasse.H2 p H ⟶ NK.BrauerHasse.H2 p H) => f.hom z) h2
    simpa using this
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)).hom x, fun h => hx ?_⟩
    have hz : (NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom
        ((NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)).hom x) = 0 := by rw [h]; simp
    rw [keyG x] at hz; exact hz
  · rintro ⟨y, hy⟩
    refine ⟨(NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom y, fun h => hy ?_⟩
    have hz : (NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)).hom
        ((NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom y) = 0 := by rw [h]; simp
    rw [keyH y] at hz; exact hz

end Aux

/-! ## The top level of the colimit -/

/-- Inflation along a reflexive inclusion is the identity at the level of elements. -/
lemma levelMap_refl_apply {F : Type u} {F' : Type u} [Field F] [Field F'] [Algebra F F']
    [IsSepClosure F F'] (p : ℕ) (U : Subgroup Gal(F'/F)) (L : FiniteGaloisIntermediateField F F')
    (a : NK.BrauerHasse.LevelH2 p U L) :
    (NK.BrauerHasse.levelMap p (U := U) (le_refl L)) a = a := by
  have h : NK.BrauerHasse.levelMap p (U := U) (le_refl L) =
      𝟙 (NK.BrauerHasse.LevelH2 p U L) := by
    have hq : NK.BrauerHasse.levelQuotHom (U := U) (le_refl L) =
        MonoidHom.id (NK.BrauerHasse.LevelGroup U L) := by
      simp only [NK.BrauerHasse.levelQuotHom, QuotientGroup.map_id]
    simp only [NK.BrauerHasse.levelMap]
    rw [hq, NK.BrauerHasse.H2.map_id]
  have := congrArg (fun (f : NK.BrauerHasse.LevelH2 p U L ⟶ NK.BrauerHasse.LevelH2 p U L) =>
    f.hom a) h
  simpa using this

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
  [FiniteDimensional F F']

/-- **The top finite Galois intermediate field**, namely `F'` itself.  It exists because
`IsSepClosure F F'` provides `IsGalois F F'`. -/
noncomputable def topLev : FiniteGaloisIntermediateField F F' where
  toIntermediateField := ⊤
  finiteDimensional := inferInstance
  isGalois := isGalois_iff_isGalois_top.mpr inferInstance

/-- Every finite Galois intermediate field is contained in the top one. -/
lemma le_topLev (L : FiniteGaloisIntermediateField F F') : L ≤ topLev (F:=F) (F':=F') :=
  (FiniteGaloisIntermediateField.le_iff L topLev).mpr le_top

/-- **Every class of the colimit comes from the top level.** -/
lemma ofLevel_topLev_surjective (p : ℕ) (y : NK.BrauerHasse.H2Profinite (K:=F) (K':=F') p ⊤) :
    ∃ a : NK.BrauerHasse.LevelH2 (K:=F) (K':=F') p ⊤ (topLev (F:=F) (F':=F')),
      NK.BrauerHasse.H2Profinite.ofLevel (topLev (F:=F) (F':=F')) a = y := by
  obtain ⟨L, a, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective y
  exact ⟨NK.BrauerHasse.levelMap p (U := ⊤) (le_topLev L) a, by
    rw [NK.BrauerHasse.H2Profinite.ofLevel_levelMap]⟩

/-- **The structure map of the colimit at the top level is injective.**  Two classes of the top
level that become equal in the colimit already agree on a common dominating level `M`; but
`⊤ ≤ M` forces `M = ⊤`, and there the inflation is the identity. -/
lemma ofLevel_topLev_injective (p : ℕ) :
    Function.Injective
      (fun a : NK.BrauerHasse.LevelH2 (K:=F) (K':=F') p ⊤ (topLev (F:=F) (F':=F')) =>
        NK.BrauerHasse.H2Profinite.ofLevel (topLev (F:=F) (F':=F')) a) := by
  intro a b hab
  obtain ⟨M, h1, h2, he⟩ := (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := ⊤) a b).mp hab
  have hM : M = topLev (F:=F) (F':=F') := by
    apply FiniteGaloisIntermediateField.val_injective
    exact le_antisymm le_top (show (⊤ : IntermediateField F F') ≤ M.toIntermediateField from h1)
  subst M
  have hh1 : h1 = le_refl (topLev (F:=F) (F':=F')) := Subsingleton.elim _ _
  have hh2 : h2 = le_refl (topLev (F:=F) (F':=F')) := Subsingleton.elim _ _
  rw [hh1] at he
  rw [hh2] at he
  rw [levelMap_refl_apply (p:=p) (U:=⊤) (topLev (F:=F) (F':=F')) a,
      levelMap_refl_apply (p:=p) (U:=⊤) (topLev (F:=F) (F':=F')) b] at he
  exact he

/-- The level group at the top level is the full Galois group: the fixing subgroup of `⊤ = F'`
is trivial, so no quotient is taken. -/
lemma topLev_fixingSubgroup : (topLev (F:=F) (F':=F')).fixingSubgroup = ⊥ := by
  show IntermediateField.fixingSubgroup (topLev (F:=F) (F':=F')).toIntermediateField = ⊥
  rw [show (topLev (F:=F) (F':=F')).toIntermediateField = (⊤ : IntermediateField F F') from rfl,
    IntermediateField.fixingSubgroup_top]

/-- **The level group at the top level is `Gal(F'/F)`.** -/
noncomputable def levelGroupTopEquiv :
    NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(F'/F)) (topLev (F:=F) (F':=F')) ≃* Gal(F'/F) :=
  ((QuotientGroup.quotientMulEquivOfEq (by rw [topLev_fixingSubgroup, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot).trans Subgroup.topEquiv

/-! ## The theorem -/

/-- **The local Brauer non-vanishing is non-vanishing of the second cohomology of the full Galois
group, in the finite case.**  When `F'/F` is finite, the colimit of `H²(Gal(L/F), ℤ/p)` over the
finite Galois intermediate fields has a top element `⊤ = F'`, so `H²(G_F, ℤ/p)` is the (single)
top level of the colimit, and both descriptions of non-vanishing coincide. -/
theorem localH2Nonvanishing_iff_finite {F F' : Type u} [Field F] [Field F'] [Algebra F F']
    [IsSepClosure F F'] [FiniteDimensional F F'] (p : ℕ) :
    NK.LocalCFT.LocalH2Nonvanishing p F F' ↔
      ∃ x : NK.BrauerHasse.H2 p (F' ≃ₐ[F] F'), x ≠ 0 := by
  have hbio : Function.Bijective
      (fun a : NK.BrauerHasse.LevelH2 (K:=F) (K':=F') p ⊤ (topLev (F:=F) (F':=F')) =>
        NK.BrauerHasse.H2Profinite.ofLevel (topLev (F:=F) (F':=F')) a) :=
    ⟨ofLevel_topLev_injective (F:=F) (F':=F') p,
      fun y => ofLevel_topLev_surjective (F:=F) (F':=F') p y⟩
  -- Step 1: `H²(G_F, ℤ/p)` (the colimit) is bijective to the single top level.
  have hbij : (∃ x : NK.BrauerHasse.H2Profinite (K:=F) (K':=F') p ⊤, x ≠ 0) ↔
      ∃ a : NK.BrauerHasse.LevelH2 (K:=F) (K':=F') p ⊤ (topLev (F:=F) (F':=F')), a ≠ 0 := by
    refine (Aux.exists_ne_zero_of_equiv (Equiv.ofBijective _ hbio) ?_).symm
    show (fun a : NK.BrauerHasse.LevelH2 (K:=F) (K':=F') p ⊤ (topLev (F:=F) (F':=F')) =>
        NK.BrauerHasse.H2Profinite.ofLevel (topLev (F:=F) (F':=F')) a) 0 = 0
    exact NK.BrauerHasse.ofLevel_zero _
  -- Step 2: the top level is `H²(Gal(F'/F), ℤ/p)`.
  have hstep2 : (∃ a : NK.BrauerHasse.LevelH2 (K:=F) (K':=F') p ⊤ (topLev (F:=F) (F':=F')),
        a ≠ 0) ↔ ∃ x : NK.BrauerHasse.H2 p (F' ≃ₐ[F] F'), x ≠ 0 :=
    Aux.H2_ne_zero_iff_of_mulEquiv (p := p) (levelGroupTopEquiv (F:=F) (F':=F'))
  show (∃ x : NK.BrauerHasse.H2Profinite (K:=F) (K':=F') p ⊤, x ≠ 0) ↔
      ∃ x : NK.BrauerHasse.H2 p (F' ≃ₐ[F] F'), x ≠ 0
  exact hbij.trans hstep2

end NK.LocalCFT.Brauer
