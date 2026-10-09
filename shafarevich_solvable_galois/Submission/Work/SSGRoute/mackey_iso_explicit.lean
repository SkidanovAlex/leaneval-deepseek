import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.ext_coind_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Mackey isomorphism `Res_f ∘ Coind_S ≅ Coind_{S'} ∘ Res_{f|}` for a surjection, explicit

For a surjection `f : G →* D`, a subgroup `S ≤ D` and `S' = S.comap f`, the two functors
`Rep ↥S ⤳ Rep G` given by `X ↦ Rep.res f (Rep.coind S.subtype X)` and
`X ↦ Rep.coind S'.subtype (Rep.res (f.subgroupComap S) X)` are naturally isomorphic; the component
at `X` is the map `φ ↦ φ ∘ f` on the underlying function spaces (a bijection because `f` is onto).

Here the isomorphism is built explicitly, together with its compatibility with the units of the
adjunctions `Rep.resCoindAdjunction Coeff S.subtype` and `Rep.resCoindAdjunction Coeff S'.subtype`
and with the traces `Work.SSGRoute.coindTrace`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

namespace MackeyIso

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

variable {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]

/-- The underlying map `φ ↦ φ ∘ f` of the Mackey isomorphism. -/
noncomputable def toFun (f : G →* D) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) (φ : (Rep.coind S.subtype X).V) :
    (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V :=
  ⟨fun x => φ.1 (f x), by
    intro r y
    have h := (Representation.mem_coindV (φ := S.subtype) (σ := X.ρ) φ.1).mp φ.2
      ⟨f r, r.2⟩ (f y)
    show φ.1 (f (r * y)) = (Rep.res (f.subgroupComap S) X).ρ r (φ.1 (f y))
    rw [map_mul]
    exact h
  ⟩

/-- `φ ↦ φ ∘ f` as a linear map. -/
noncomputable def toLin (f : G →* D) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) :
    (Rep.coind S.subtype X).V →ₗ[SSGRoute.PTExt.Coeff]
      (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V where
  toFun := toFun f S X
  map_add' φ ψ := by apply Subtype.ext; funext x; rfl
  map_smul' a φ := by apply Subtype.ext; funext x; rfl

/-- The morphism `Rep.res f (Rep.coind S.subtype X) ⟶
Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)`. -/
noncomputable def hom (f : G →* D) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) :
    (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f).obj X ⟶
      (Rep.resFunctor (f.subgroupComap S) ⋙
        Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype).obj X :=
  Rep.ofHom ⟨toLin f S X, by
    intro x
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext y
    show φ.1 (f y * f x) = φ.1 (f (y * x))
    rw [map_mul]
  ⟩

/-- A chosen preimage of `d` under the surjection `f`. -/
noncomputable def sec (f : G →* D) (hf : Function.Surjective f) (d : D) : G :=
  Classical.choose (hf d)

lemma sec_spec (f : G →* D) (hf : Function.Surjective f) (d : D) :
    f (sec f hf d) = d := Classical.choose_spec (hf d)

/-- `f : S' → S` is onto. -/
lemma surj_subgroupComap (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    Function.Surjective (f.subgroupComap S) := by
  intro s
  obtain ⟨x, hx⟩ := hf (s : D)
  refine ⟨⟨x, ?_⟩, ?_⟩
  · show f x ∈ S
    rw [hx]
    exact s.2
  · apply Subtype.ext
    show f x = (s : D)
    rw [hx]

/-- An `S'`-equivariant function `ψ : G → X.V` is constant on the fibres of `f`. -/
lemma eq_of_f_eq (f : G →* D) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V)
    {x y : G} (hxy : f x = f y) : ψ.1 x = ψ.1 y := by
  have hr : (x * y⁻¹) ∈ S.comap f := by
    show f (x * y⁻¹) ∈ S
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact S.one_mem
  have h := (Representation.mem_coindV (φ := (S.comap f).subtype)
      (σ := (Rep.res (f.subgroupComap S) X).ρ) ψ.1).mp ψ.2 ⟨x * y⁻¹, hr⟩ y
  have hx : ((S.comap f).subtype ⟨x * y⁻¹, hr⟩) * y = x := by
    show x * y⁻¹ * y = x
    group
  rw [hx] at h
  rw [Rep.coe_res_obj_ρ'] at h
  have hg : (f.subgroupComap S) ⟨x * y⁻¹, hr⟩ = 1 := by
    apply Subtype.ext
    show f (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  rw [hg] at h
  simpa using h

/-- The underlying map of the inverse of the Mackey isomorphism: descend `ψ` along `f`. -/
noncomputable def invFun (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V) :
    (Rep.coind S.subtype X).V :=
  ⟨fun d => ψ.1 (sec f hf d), by
    intro s d
    show ψ.1 (sec f hf ((s : D) * d)) = X.ρ s (ψ.1 (sec f hf d))
    obtain ⟨r, hr⟩ := surj_subgroupComap f hf S s
    have hfe : f (r : G) = (s : D) := congrArg Subtype.val hr
    have h1 : ψ.1 (sec f hf ((s : D) * d)) = ψ.1 ((r : G) * sec f hf d) := by
      apply eq_of_f_eq f S X ψ
      rw [sec_spec, map_mul, hfe, sec_spec]
    rw [h1]
    have h2 := (Representation.mem_coindV (φ := (S.comap f).subtype)
      (σ := (Rep.res (f.subgroupComap S) X).ρ) ψ.1).mp ψ.2 r (sec f hf d)
    simp only [Subgroup.coe_subtype] at h2
    rw [h2]
    rw [Rep.coe_res_obj_ρ']
    show X.ρ ((f.subgroupComap S) r) (ψ.1 (sec f hf d)) = X.ρ s (ψ.1 (sec f hf d))
    rw [hr]
  ⟩

/-- The inverse map as a linear map. -/
noncomputable def invLin (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) :
    (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V →ₗ[SSGRoute.PTExt.Coeff]
      (Rep.coind S.subtype X).V where
  toFun := invFun f hf S X
  map_add' φ ψ := by apply Subtype.ext; funext x; rfl
  map_smul' a φ := by apply Subtype.ext; funext x; rfl

/-- The inverse morphism `Rep.coind S'.subtype (Rep.res (f.subgroupComap S) X) ⟶
Rep.res f (Rep.coind S.subtype X)`. -/
noncomputable def inv (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) :
    (Rep.resFunctor (f.subgroupComap S) ⋙
        Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype).obj X ⟶
      (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f).obj X :=
  Rep.ofHom ⟨invLin f hf S X, by
    intro x
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    funext y
    show ψ.1 (sec f hf y * x) = ψ.1 (sec f hf (y * f x))
    apply eq_of_f_eq f S X ψ
    rw [map_mul, sec_spec, sec_spec]
  ⟩

/-- `hom` and `inv` are inverse to each other. -/
lemma hom_comp_inv (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) :
    hom f S X ≫ inv f hf S X = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ψ
  apply Subtype.ext
  funext y
  show ψ.1 (f (sec f hf y)) = ψ.1 y
  rw [sec_spec]

lemma inv_comp_hom (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep.{0} SSGRoute.PTExt.Coeff ↥S) :
    inv f hf S X ≫ hom f S X = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext d
  show φ.1 (sec f hf (f d)) = φ.1 d
  apply eq_of_f_eq f S X φ
  rw [sec_spec]

/-- The forward natural transformation. -/
noncomputable def homNat (f : G →* D) (S : Subgroup D) :
    (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f) ⟶
      (Rep.resFunctor (f.subgroupComap S) ⋙
        Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype) where
  app X := hom f S X
  naturality {X Y} φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    funext x
    show (φ.hom) (ψ.1 (f x)) = (φ.hom) (ψ.1 (f x))
    rfl

/-- The inverse natural transformation. -/
noncomputable def invNat (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    (Rep.resFunctor (f.subgroupComap S) ⋙
        Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype) ⟶
      (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f) where
  app X := inv f hf S X
  naturality {X Y} φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    funext d
    show (φ.hom) (ψ.1 (sec f hf d)) = (φ.hom) (ψ.1 (sec f hf d))
    rfl

/-- **The Mackey isomorphism** `Rep.res f ∘ Coind_S ≅ Coind_{S'} ∘ Rep.res (f.subgroupComap S)`. -/
noncomputable def iso (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype ⋙ Rep.resFunctor f) ≅
      (Rep.resFunctor (f.subgroupComap S) ⋙
        Rep.coindFunctor SSGRoute.PTExt.Coeff (S.comap f).subtype) where
  hom := homNat f S
  inv := invNat f hf S
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    exact hom_comp_inv f hf S X
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    exact inv_comp_hom f hf S X

/-- **Compatibility of the Mackey isomorphism with the adjunction units.** -/
theorem unit_compat (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (M : Rep.{0} SSGRoute.PTExt.Coeff D) :
    (Rep.resFunctor f).map ((Rep.resCoindAdjunction SSGRoute.PTExt.Coeff S.subtype).unit.app M) ≫
        (iso f hf S).hom.app (Rep.res S.subtype M)
      = (Rep.resCoindAdjunction SSGRoute.PTExt.Coeff (S.comap f).subtype).unit.app
          (Rep.res f M) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  funext x
  show M.ρ (f x) m = (Rep.res f M).ρ x m
  rfl

/-- The map on cosets induced by `f`: `Quotient (rightRel S') → Quotient (rightRel S)`. -/
noncomputable def quotientMap (f : G →* D) (S : Subgroup D) :
    Quotient (QuotientGroup.rightRel (S.comap f)) → Quotient (QuotientGroup.rightRel S) :=
  Quotient.map f (fun x y h => by
    refine QuotientGroup.rightRel_apply.2 ?_
    have hh : y * x⁻¹ ∈ S.comap f := QuotientGroup.rightRel_apply.1 h
    show f y * (f x)⁻¹ ∈ S
    simpa [map_mul, map_inv] using hh)

lemma quotientMap_mk (f : G →* D) (S : Subgroup D) (x : G) :
    quotientMap f S (Quotient.mk (QuotientGroup.rightRel (S.comap f)) x)
      = Quotient.mk (QuotientGroup.rightRel S) (f x) := rfl

lemma quotientMap_surjective (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    Function.Surjective (quotientMap f S) := by
  intro q
  induction q using Quotient.inductionOn with
  | h d =>
    obtain ⟨x, hx⟩ := hf d
    exact ⟨Quotient.mk (QuotientGroup.rightRel (S.comap f)) x, by
      rw [quotientMap_mk, hx]⟩

lemma quotientMap_injective (f : G →* D) (S : Subgroup D) :
    Function.Injective (quotientMap f S) := by
  intro q q' h
  induction q using Quotient.inductionOn with
  | h x =>
    induction q' using Quotient.inductionOn with
    | h y =>
      have h1 : Quotient.mk (QuotientGroup.rightRel S) (f x)
          = Quotient.mk (QuotientGroup.rightRel S) (f y) := h
      have h2 : f y * (f x)⁻¹ ∈ S :=
        QuotientGroup.rightRel_apply.1 (Quotient.exact h1)
      refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
      show f (y * x⁻¹) ∈ S
      simpa [map_mul, map_inv] using h2

/-- The summands of the two traces agree along the coset bijection. -/
lemma trace_term (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (A : Rep.{0} SSGRoute.PTExt.Coeff D)
    (ψ : (Rep.coind (S.comap f).subtype
      (Rep.res (f.subgroupComap S) (Rep.res S.subtype A))).V)
    (q' : Quotient (QuotientGroup.rightRel (S.comap f))) :
    A.ρ (Quotient.out (quotientMap f S q'))⁻¹
        (ψ.1 (sec f hf (Quotient.out (quotientMap f S q'))))
      = A.ρ (f (Quotient.out q'))⁻¹ (ψ.1 (Quotient.out q')) := by
  have hmap : quotientMap f S q'
      = Quotient.mk (QuotientGroup.rightRel S) (f (Quotient.out q')) := by
    conv_lhs => rw [← Quotient.out_eq' q']
    rw [quotientMap_mk]
  have hfin : Quotient.mk (QuotientGroup.rightRel S)
        (Quotient.out (quotientMap f S q'))
      = Quotient.mk (QuotientGroup.rightRel S) (f (Quotient.out q')) :=
    (Quotient.out_eq' (quotientMap f S q')).trans hmap
  have hs : f (Quotient.out q') * (Quotient.out (quotientMap f S q'))⁻¹ ∈ S :=
    QuotientGroup.rightRel_apply.1 (Quotient.exact hfin)
  obtain ⟨r, hr⟩ := hf (f (Quotient.out q') * (Quotient.out (quotientMap f S q'))⁻¹)
  have hmem : r ∈ S.comap f := by
    show f r ∈ S
    rw [hr]
    exact hs
  have hfe : f (Quotient.out q')
      = f ((S.comap f).subtype ⟨r, hmem⟩
          * sec f hf (Quotient.out (quotientMap f S q'))) := by
    rw [map_mul, sec_spec]
    show f (Quotient.out q')
      = f ((S.comap f).subtype ⟨r, hmem⟩) * Quotient.out (quotientMap f S q')
    rw [show f ((S.comap f).subtype ⟨r, hmem⟩) = f r from rfl, hr]
    group
  have hpsi : ψ.1 (Quotient.out q')
      = ((Rep.res (f.subgroupComap S) (Rep.res S.subtype A)).ρ ⟨r, hmem⟩)
          (ψ.1 (sec f hf (Quotient.out (quotientMap f S q')))) := by
    have h2 := eq_of_f_eq f S (Rep.res S.subtype A) ψ hfe
    rw [h2]
    exact (Representation.mem_coindV (φ := (S.comap f).subtype)
      (σ := (Rep.res (f.subgroupComap S) (Rep.res S.subtype A)).ρ) ψ.1).mp ψ.2
      ⟨r, hmem⟩ (sec f hf (Quotient.out (quotientMap f S q')))
  rw [hpsi]
  have hρ : (Rep.res (f.subgroupComap S) (Rep.res S.subtype A)).ρ ⟨r, hmem⟩
      = A.ρ (f r) := by
    rw [Rep.coe_res_obj_ρ', Rep.coe_res_obj_ρ']
    rfl
  rw [hρ]
  rw [← Module.End.mul_apply, ← map_mul]
  rw [show (f (Quotient.out q'))⁻¹ * f r = (Quotient.out (quotientMap f S q'))⁻¹ from by
    rw [hr]
    group]

/-- **Compatibility of the explicit Mackey isomorphism with the traces `coindTrace`.** -/
theorem trace_compat (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (A : Rep.{0} SSGRoute.PTExt.Coeff D) :
    CategoryTheory.CategoryStruct.comp ((iso f hf S).inv.app (Rep.res S.subtype A))
      ((Rep.resFunctor f).map (coindTrace S A)) = coindTrace (S.comap f) (Rep.res f A) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ψ
  show traceLin S A (invFun f hf S (Rep.res S.subtype A) ψ)
      = traceLin (S.comap f) (Rep.res f A) ψ
  rw [traceLin_apply, traceLin_apply]
  simp only [Rep.coe_res_obj_ρ', invFun]
  exact (Fintype.sum_bijective (quotientMap f S)
    ⟨quotientMap_injective f S, quotientMap_surjective f hf S⟩ _ _
    (fun q' => by
      simpa only [MonoidHom.comp_apply, map_inv] using (trace_term f hf S A ψ q').symm)).symm

end MackeyIso

end Work.SSGRoute
