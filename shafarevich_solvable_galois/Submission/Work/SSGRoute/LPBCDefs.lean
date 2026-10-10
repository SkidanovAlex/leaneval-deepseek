import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.sylow_in_defs

/-!
# Base change for the local level pairing: transport infrastructure

Vocabulary for `Work.SSGRoute.levelPair_baseChange_in` (Y3).  Everything here is abstract
`Rep`/`Ext` algebra: transport of `Ext`-classes along isomorphisms of the two coefficient
representations, along an isomorphism of the acting group, and the compatibility of these
transports with the level pairing `SSGRoute.PTExt.levelPair`.

## Contents

* `extCongrIso` — `Ext X Y n ≃+ Ext X' Y' n` from isomorphisms `X ≅ X'`, `Y ≅ Y'`;
  `extCongrIso_apply`, `extCongrIso_mk₀`, `extCongrIso_comp11` (naturality in `Ext.comp`, in the
  degrees `1`, `1`, `2` that occur in the level pairing).
* `extCongrIso_mapExactFunctor` — the transports commute with an exact functor.
* `extResEquiv` — `Ext X Y n ≃+ Ext (res_e X) (res_e Y) n` for a group isomorphism `e`.
* `unitResIso` — the identity `ℤ → ℤ` as an isomorphism `res_f (unitRep G) ≅ unitRep H`.
* `extHMapEquiv` — restriction of `Hⁿ` along a group isomorphism as an additive equivalence.
* `levelPair_Hstep`, `levelPair_iso` — the two steps of the base-change comparison of the level
  pairing (the `H₂ → H₁` restriction step and the group-isomorphism step).
-/

namespace Work.SSGRoute.LPBC

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 4000000

attribute [local instance 100000] Rep.hV2 Rep.hV1 Submodule.module

/-! ## 1. `Ext` transport along isomorphisms of both variables -/

section Congr

variable {G : Type} [Group G] {n : ℕ}

/-- Transport of `Extⁱ`-classes along isomorphisms of both coefficient representations. -/
def extCongrHom {X X' Y Y' : Rep.{0} Coeff G} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Abelian.Ext.{0} X Y n →+ Abelian.Ext.{0} X' Y' n where
  toFun x :=
    (Abelian.Ext.mk₀ eX.inv).comp (x.comp (Abelian.Ext.mk₀ eY.hom) (add_zero n)) (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp [Abelian.Ext.comp_add, Abelian.Ext.add_comp]

@[simp] lemma extCongrHom_apply {X X' Y Y' : Rep.{0} Coeff G} (eX : X ≅ X') (eY : Y ≅ Y')
    (n : ℕ) (x : Abelian.Ext.{0} X Y n) :
    extCongrHom eX eY n x =
      (Abelian.Ext.mk₀ eX.inv).comp (x.comp (Abelian.Ext.mk₀ eY.hom) (add_zero n))
        (zero_add n) := rfl

/-- **Transport of `Extⁱ` along isomorphisms of both coefficient representations**: the additive
equivalence `Ext X Y n ≃+ Ext X' Y' n` induced by `eX : X ≅ X'` and `eY : Y ≅ Y'`. -/
def extCongrIso {X X' Y Y' : Rep.{0} Coeff G} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Abelian.Ext.{0} X Y n ≃+ Abelian.Ext.{0} X' Y' n where
  toFun := (extCongrHom eX eY n : Abelian.Ext.{0} X Y n → Abelian.Ext.{0} X' Y' n)
  invFun := fun y => (Abelian.Ext.mk₀ eX.hom).comp
    (y.comp (Abelian.Ext.mk₀ eY.inv) (add_zero n)) (zero_add n)
  left_inv x := by
    show (Abelian.Ext.mk₀ eX.hom).comp
        (((Abelian.Ext.mk₀ eX.inv).comp (x.comp (Abelian.Ext.mk₀ eY.hom) (add_zero n))
          (zero_add n)).comp (Abelian.Ext.mk₀ eY.inv) (add_zero n)) (zero_add n) = x
    rw [Abelian.Ext.comp_assoc]
    rw [← Abelian.Ext.comp_assoc]
    rw [Abelian.Ext.mk₀_comp_mk₀, eX.hom_inv_id, Abelian.Ext.mk₀_id_comp]
    rw [Abelian.Ext.comp_assoc]
    rw [Abelian.Ext.mk₀_comp_mk₀, eY.hom_inv_id, Abelian.Ext.comp_mk₀_id]
    all_goals try omega
  right_inv y := by
    show (Abelian.Ext.mk₀ eX.inv).comp
        (((Abelian.Ext.mk₀ eX.hom).comp (y.comp (Abelian.Ext.mk₀ eY.inv) (add_zero n))
          (zero_add n)).comp (Abelian.Ext.mk₀ eY.hom) (add_zero n)) (zero_add n) = y
    rw [Abelian.Ext.comp_assoc]
    rw [← Abelian.Ext.comp_assoc]
    rw [Abelian.Ext.mk₀_comp_mk₀, eX.inv_hom_id, Abelian.Ext.mk₀_id_comp]
    rw [Abelian.Ext.comp_assoc]
    rw [Abelian.Ext.mk₀_comp_mk₀, eY.inv_hom_id, Abelian.Ext.comp_mk₀_id]
    all_goals try omega
  map_add' x y := (extCongrHom eX eY n).map_add x y

@[simp] lemma extCongrIso_apply {X X' Y Y' : Rep.{0} Coeff G} (eX : X ≅ X') (eY : Y ≅ Y')
    (n : ℕ) (x : Abelian.Ext.{0} X Y n) :
    extCongrIso eX eY n x =
      (Abelian.Ext.mk₀ eX.inv).comp (x.comp (Abelian.Ext.mk₀ eY.hom) (add_zero n))
        (zero_add n) := rfl

/-- `extCongrIso` on degree-`0` classes is composition of morphisms. -/
lemma extCongrIso_mk₀ {X X' Y Y' : Rep.{0} Coeff G} (eX : X ≅ X') (eY : Y ≅ Y')
    (γ : X ⟶ Y) :
    extCongrIso eX eY 0 (Abelian.Ext.mk₀ γ) = Abelian.Ext.mk₀ (eX.inv ≫ γ ≫ eY.hom) := by
  rw [extCongrIso_apply]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [Abelian.Ext.mk₀_comp_mk₀]

/-- **Naturality of the `Ext`-transport in `Ext.comp`**, in the degrees `1 + 1 = 2` occurring in
the level pairing. -/
lemma extCongrIso_comp11 {X X' Y Y' Z Z' : Rep.{0} Coeff G} (eX : X ≅ X') (eY : Y ≅ Y')
    (eZ : Z ≅ Z') (h : Abelian.Ext.{0} X Y 1) (P : Abelian.Ext.{0} Y Z 1) :
    extCongrIso eX eZ 2 (h.comp P rfl) =
      (extCongrIso eX eY 1 h).comp (extCongrIso eY eZ 1 P) rfl := by
  simp only [extCongrIso_apply, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc_of_second_deg_zero, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]
  rw [eY.hom_inv_id]
  rw [Abelian.Ext.comp_mk₀_id]
  rw [← Abelian.Ext.comp_assoc]
  omega

/-- `extCongrIso` with identity isomorphisms is the identity. -/
@[simp] lemma extCongrIso_refl_apply {X Y : Rep.{0} Coeff G} (n : ℕ)
    (x : Abelian.Ext.{0} X Y n) :
    extCongrIso (Iso.refl X) (Iso.refl Y) n x = x := by
  rw [extCongrIso_apply]
  simp

end Congr

/-! ## 2. `Ext` transport along a group isomorphism -/

section ResEquiv

/-- **Transport of `Extⁱ` along a group isomorphism.**  `Rep.res` along a group isomorphism is an
equivalence of categories, so applying it to an `Ext`-class is a bijection. -/
noncomputable def extResEquiv {G₁ G₂ : Type} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (X Y : Rep.{0} Coeff G₂) (n : ℕ) :
    Abelian.Ext.{0} X Y n ≃+
      Abelian.Ext.{0} (Rep.res e.toMonoidHom X) (Rep.res e.toMonoidHom Y) n := by
  haveI hE : (Rep.resFunctor (k := Coeff) e.toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence e.symm
  exact AddEquiv.ofBijective ((Rep.resFunctor e.toMonoidHom).mapExtAddHom X Y n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects _ X Y n)

@[simp] lemma extResEquiv_apply {G₁ G₂ : Type} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (X Y : Rep.{0} Coeff G₂) (n : ℕ) (x : Abelian.Ext.{0} X Y n) :
    extResEquiv e X Y n x = extRes e.toMonoidHom x := rfl

end ResEquiv

/-! ## 3. The unit `ℤ → ℤ` as an isomorphism of representations -/

section UnitRes

/-- The identity `ℤ → ℤ`, as an isomorphism from the restriction of the trivial representation
`ℤ` of `G` to the trivial representation `ℤ` of `H` along `f : H →* G`. -/
def unitResIso {H G : Type} [Group H] [Group G] (f : H →* G) :
    Rep.res f (unitRep G) ≅ unitRep H where
  hom := trivResInv f Coeff
  inv := unitRes f
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

@[simp] lemma unitResIso_inv {H G : Type} [Group H] [Group G] (f : H →* G) :
    (unitResIso f).inv = unitRes f := rfl

end UnitRes

/-! ## 4. Commutation of the transports with an exact functor -/

section ExactFunctor

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

/-- **The `Ext`-transport commutes with restriction along a group homomorphism.** -/
lemma extCongrIso_mapExactFunctor (φ : G₁ →* G₂) {X X' Y Y' : Rep.{0} Coeff G₂}
    (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) (w : Abelian.Ext.{0} X Y n) :
    extCongrIso ((Rep.resFunctor φ).mapIso eX) ((Rep.resFunctor φ).mapIso eY) n (extRes φ w)
      = extRes φ (extCongrIso eX eY n w) := by
  simp only [extRes, extCongrIso_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Functor.mapIso_hom, Functor.mapIso_inv]

end ExactFunctor

/-! ## 5. Restriction of `Hⁿ` along a group isomorphism -/

section HMap

variable {H₁ H₂ : Type} [Group H₁] [Group H₂]

/-- Restriction of `Hⁿ` along a group isomorphism, as an additive equivalence. -/
noncomputable def extHMapEquiv (j : H₁ ≃* H₂) (A : Rep.{0} Coeff H₂) (n : ℕ) :
    extH A n ≃+ extH (Rep.res j.toMonoidHom A) n :=
  (extResEquiv j (unitRep H₂) A n).trans (extCongrIso (unitResIso j.toMonoidHom) (Iso.refl _) n)

/-- `extHMapEquiv` is the restriction map `extHMap j 𝟙` on elements. -/
lemma extHMapEquiv_apply (j : H₁ ≃* H₂) (A : Rep.{0} Coeff H₂) (n : ℕ)
    (y : extH A n) :
    extHMapEquiv j A n y = extHMap j.toMonoidHom (𝟙 (Rep.res j.toMonoidHom A)) y := by
  simp only [extHMapEquiv, AddEquiv.trans_apply, extResEquiv_apply, extCongrIso_apply,
    unitResIso_inv, extHMap]
  rfl

end HMap

/-! ## 6. The two steps of the base-change comparison -/

section Steps

variable {G : Type} [Group G] {H₁ H₂ : Type} [Group H₁] [Group H₂]

/-- **The `H₂ → H₁` restriction step of the base-change comparison.**  Pushing the value of the
level pairing at a level `f : H₂ →* G` down to the smaller group `H₁` along `j : H₁ ≃* H₂` (and
then transporting the coefficient module along `eB`) is the level pairing at the restricted level
`f ∘ j`, paired with the restriction of the `H¹`-class. -/
lemma levelPair_Hstep (j : H₁ ≃* H₂) (f : H₂ →* G) {M A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H₂} {B₁ : Rep.{0} Coeff H₁} (ι : Rep.res f A ⟶ B)
    (eB : Rep.res j.toMonoidHom B ≅ B₁) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) :
    extCongrIso (Iso.refl (unitRep H₁)) eB (s + r) (extHMapEquiv j B (s + r) (levelPair f ι x h)) =
      extCongrIso (Iso.refl (unitRep H₁)) eB (s + r)
        (levelPair (f.comp j.toMonoidHom) (Rep.resMap j.toMonoidHom ι) x
          (extHMapEquiv j (Rep.res f M) s h)) := by
  rw [extHMapEquiv_apply, extHMapEquiv_apply]
  rw [Work.SSGRoute.SylowIn.levelPair_restrict f j.toMonoidHom ι (𝟙 (Rep.res j.toMonoidHom B))
    (Rep.resMap j.toMonoidHom ι) x h rfl]

end Steps

/-- **Additive isomorphisms preserve the cardinality of the `p`-torsion.** -/
lemma card_pTorsion_addEquiv {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (p : ℕ)
    (e : X ≃+ Y) :
    Nat.card {x : X // p • x = 0} = Nat.card {y : Y // p • y = 0} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => ?_))
  show p • x = 0 ↔ p • e x = 0
  constructor
  · intro hx
    rw [← map_nsmul e p x, hx, map_zero]
  · intro hx
    rw [show p • e x = e (p • x) from (map_nsmul e p x).symm,
      show (0 : Y) = e 0 from (map_zero e).symm] at hx
    exact e.injective hx

end

end Work.SSGRoute.LPBC

namespace Work.SSGRoute.LPBC

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-! ## 7. The action on places and the restriction of decomposition groups -/

section DecompK

/-- **The action on places only sees the underlying function.**  For a tower `k ⊆ k' ⊆ K` and
`σ : K ≃ₐ[k'] K`, forgetting the `k'`-linearity does not change the action on the places of `K`. -/
theorem place_smul_restrictScalarsHom (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k k'] [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' K] (σ : K ≃ₐ[k'] K) (w : NK.GlobalCFT.Place K) :
    (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K) σ) • w = σ • w := by
  cases w <;> rfl

/-- The restriction map on decomposition groups attached to a change of base field `k ⊆ k'`. -/
def decompKRestrictScalarsHom (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k']
    [IsScalarTower k k' K] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K]
    [IsGalois k' K] (w : NK.GlobalCFT.Place K) :
    decompK (k := k') w →* decompK (k := k) w :=
  MonoidHom.codRestrict
    ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)).comp (decompK (k := k') w).subtype)
    (decompK (k := k) w)
    (fun d => by
      have hd : (d : K ≃ₐ[k'] K) • w = w := MulAction.mem_stabilizer_iff.mp d.2
      show ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) (d : K ≃ₐ[k'] K)) • w = w
      rw [place_smul_restrictScalarsHom k k' K (d : K ≃ₐ[k'] K) w]
      exact hd)

@[simp] theorem decompKRestrictScalarsHom_apply (k k' K : Type) [Field k] [NumberField k]
    [Field k'] [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K]
    [Algebra k k'] [IsScalarTower k k' K] [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k' K] [IsGalois k' K] (w : NK.GlobalCFT.Place K)
    (d : decompK (k := k') w) :
    ((decompKRestrictScalarsHom k k' K w d : decompK (k := k) w) : K ≃ₐ[k] K)
      = AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K) (d : K ≃ₐ[k'] K) := rfl

/-- The same restriction at the level of stabilizers in `Gal(L/k')` and `Gal(L/k)`. -/
def stabilizerRestrictScalarsHom (k k' L : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field L] [NumberField L] [Algebra k L] [Algebra k' L] [Algebra k k']
    [IsScalarTower k k' L] (w : NK.GlobalCFT.Place L) :
    MulAction.stabilizer (L ≃ₐ[k'] L) w →* MulAction.stabilizer (L ≃ₐ[k] L) w :=
  MonoidHom.codRestrict
    ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L)).comp
      (MulAction.stabilizer (L ≃ₐ[k'] L) w).subtype)
    (MulAction.stabilizer (L ≃ₐ[k] L) w)
    (fun d => by
      have hd : (d : L ≃ₐ[k'] L) • w = w := MulAction.mem_stabilizer_iff.mp d.2
      show ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L)) (d : L ≃ₐ[k'] L)) • w = w
      rw [place_smul_restrictScalarsHom k k' L (d : L ≃ₐ[k'] L) w]
      exact hd)

@[simp] theorem stabilizerRestrictScalarsHom_apply (k k' L : Type) [Field k] [NumberField k]
    [Field k'] [NumberField k'] [Field L] [NumberField L] [Algebra k L] [Algebra k' L]
    [Algebra k k'] [IsScalarTower k k' L] (w : NK.GlobalCFT.Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w) :
    ((stabilizerRestrictScalarsHom k k' L w σ : MulAction.stabilizer (L ≃ₐ[k] L) w) :
        L ≃ₐ[k] L)
      = AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L) (σ : L ≃ₐ[k'] L) := rfl

end DecompK


end

end Work.SSGRoute.LPBC

namespace Work.SSGRoute.LPBC

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-- `eqToHom` of any proof of `X = X` is the identity. -/
lemma eqToHom_self_eq_id {C : Type*} [Category* C] {X : C} (h : X = X) :
    eqToHom h = 𝟙 X := by
  rw [Subsingleton.elim h rfl, eqToHom_refl]

/-! ## 8. The group-isomorphism step of the base-change comparison -/

/-- Two isomorphisms of representations with the same values on elements are equal. -/
lemma ext_of_pointwise {G : Type} [Group G] {X Y : Rep.{0} Coeff G} (e₁ e₂ : X ≅ Y)
    (h : ∀ x : X.V, e₁.hom x = e₂.hom x) : e₁ = e₂ := by
  letI := X.hV1
  letI := X.hV2
  letI := Y.hV1
  letI := Y.hV2
  apply Iso.ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact h x

section IsoStep

variable {G₁ G₂ H : Type} [Group G₁] [Group G₂] [Group H]

/-- **The group-isomorphism step of the base-change comparison of the level pairing.**  Suppose a
level over the base field `k'` (group `G₁`, level map `f`) is obtained from a level over the base
field `k` (group `G₂`, level map `g`) by the group isomorphism `e : G₁ ≃* G₂` and compatible
coefficient isomorphisms (`eMg`, `eAg` being the canonical ones, given by their values on
elements).  Then the level pairings correspond. -/
theorem levelPair_iso (e : G₁ ≃* G₂) (f : H →* G₁) (g : H →* G₂)
    (hg : g = e.toMonoidHom.comp f)
    {M₂ A₂ : Rep.{0} Coeff G₂} {M₁ A₁ : Rep.{0} Coeff G₁}
    (eM : Rep.res e.toMonoidHom M₂ ≅ M₁) (eA : Rep.res e.toMonoidHom A₂ ≅ A₁)
    {B₂ B₁ : Rep.{0} Coeff H} (eB : B₂ ≅ B₁)
    (eMg : Rep.res g M₂ ≅ Rep.res f M₁) (eAg : Rep.res g A₂ ≅ Rep.res f A₁)
    (hM : ∀ x : M₂.V, eMg.hom x = ((Rep.resFunctor f).mapIso eM).hom x)
    (hA : ∀ x : A₂.V, eAg.hom x = ((Rep.resFunctor f).mapIso eA).hom x)
    (ι₂ : Rep.res g A₂ ⟶ B₂) (ι₁ : Rep.res f A₁ ⟶ B₁)
    (hι : eAg.hom ≫ ι₁ = ι₂ ≫ eB.hom)
    (z : Abelian.Ext.{0} M₂ A₂ 1) (h : extH (Rep.res g M₂) 1) :
    levelPair f ι₁ (extCongrIso eM eA 1 (extRes e.toMonoidHom z))
        (extCongrIso (Iso.refl (unitRep H)) eMg 1 h)
      = extCongrIso (Iso.refl (unitRep H)) eB 2 (levelPair g ι₂ z h) := by
  subst hg
  have hMe : eMg = (show Rep.res (e.toMonoidHom.comp f) M₂ ≅ Rep.res f M₁ from
      (Rep.resFunctor f).mapIso eM) :=
    ext_of_pointwise _ _ (fun x => hM x)
  have hAe : eAg = (show Rep.res (e.toMonoidHom.comp f) A₂ ≅ Rep.res f A₁ from
      (Rep.resFunctor f).mapIso eA) :=
    ext_of_pointwise _ _ (fun x => hA x)
  rw [hMe] at ⊢
  rw [hAe] at hι
  -- Step 1: the `Ext¹`-factor of the `k`-side equals the image of the `k'`-side factor.
  have hE : extRes f (extCongrIso eM eA 1 (extRes e.toMonoidHom z))
      = extCongrIso ((Rep.resFunctor f).mapIso eM) ((Rep.resFunctor f).mapIso eA) 1
          (extRes (e.toMonoidHom.comp f) z) := by
    rw [← extCongrIso_mapExactFunctor f eM eA 1 (extRes e.toMonoidHom z)]
    rw [Work.SSGRoute.SylowDesc.extRes_comp_aux e.toMonoidHom f z]
  -- Step 2: the coefficient morphism factor.
  have hP : extCongrIso ((Rep.resFunctor f).mapIso eM) eB 1
        ((extRes (e.toMonoidHom.comp f) z).comp (Abelian.Ext.mk₀ ι₂) (add_zero 1))
      = (extRes f (extCongrIso eM eA 1 (extRes e.toMonoidHom z))).comp
          (Abelian.Ext.mk₀ ι₁) (add_zero 1) := by
    rw [hE, extCongrIso_apply, extCongrIso_apply]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
    rw [Abelian.Ext.mk₀_comp_mk₀]
    rw [Abelian.Ext.comp_assoc]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
    rw [Abelian.Ext.mk₀_comp_mk₀]
    rw [hι]
    all_goals try omega
  -- Assembly.
  rw [levelPair]
  rw [levelPair]
  rw [extCongrIso_comp11 (Iso.refl (unitRep H)) ((Rep.resFunctor f).mapIso eM) eB h
    ((extRes (e.toMonoidHom.comp f) z).comp (Abelian.Ext.mk₀ ι₂) (add_zero 1))]
  rw [hP]

end IsoStep


end

end Work.SSGRoute.LPBC
