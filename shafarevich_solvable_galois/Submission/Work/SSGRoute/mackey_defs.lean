import Mathlib
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.ext_coind_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Mackey isomorphism `Res_f (Coind_S X) ≅ Coind_{S.comap f} (Res_{S'} X)` for a surjection

For a surjective group homomorphism `f : G →* D` and a subgroup `S ≤ D` with `S' := S.comap f`,
the restriction of the coinduced representation `Coind_S^D X` of `X : Rep k S` along `f` is the
coincidence of the coinduction of `X` along `f| : S' → S`, i.e.

`Res_f (Coind_S X) ≅ Coind_{S'} (Res_{S'} X)`,

with component at `X` given by `φ ↦ φ ∘ f` on the underlying function spaces.

This file contains the definitions and the elementary lemmas (equivariance, naturality, the
two inverse identities) used by `Submission.Work.SSGRoute.coind_res_mackey`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

noncomputable section

variable {G D : Type} [Group G] [Group D]

/-! ## The forward map `φ ↦ φ ∘ f` -/

/-- Precomposition with `f` on the coinduced function spaces. -/
def mackeyToLin (f : G →* D) (S : Subgroup D) (X : Rep Coeff S) :
    (Rep.coind S.subtype X).V →ₗ[Coeff]
      (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V where
  toFun φ := ⟨fun x => φ.1 (f x), by
    intro g h
    have h2 : S.subtype ((f.subgroupComap S) g) = f (g : G) := rfl
    have hh := (Representation.mem_coindV (φ := S.subtype) (σ := X.ρ) φ.1).mp φ.2
      ((f.subgroupComap S) g) (f h)
    rw [h2] at hh
    show φ.1 (f ((g : G) * h)) = X.ρ ((f.subgroupComap S) g) (φ.1 (f h))
    rw [map_mul]
    exact hh⟩
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by ext x; simp

lemma mackeyToLin_apply (f : G →* D) (S : Subgroup D) (X : Rep Coeff S)
    (φ : (Rep.coind S.subtype X).V) (x : G) :
    (mackeyToLin f S X φ).1 x = φ.1 (f x) := rfl

lemma mackeyToLin_equivariant (f : G →* D) (S : Subgroup D) (X : Rep Coeff S) (g : G)
    (φ : (Rep.coind S.subtype X).V) :
    mackeyToLin f S X (((Rep.res f (Rep.coind S.subtype X)).ρ g) φ) =
      ((Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).ρ g)
        (mackeyToLin f S X φ) := by
  ext x
  rw [show (((Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).ρ g)
        (mackeyToLin f S X φ)).1 x = (mackeyToLin f S X φ).1 (x * g) from rfl]
  rw [mackeyToLin_apply, mackeyToLin_apply]
  rw [show (((Rep.res f (Rep.coind S.subtype X)).ρ g) φ).1 (f x) = φ.1 (f x * f g) from rfl]
  rw [map_mul]

/-- The `G`-equivariant map `Res_f (Coind_S X) ⟶ Coind_{S'} (Res_{S'} X)`, `φ ↦ φ ∘ f`. -/
def mackeyHom (f : G →* D) (S : Subgroup D) (X : Rep Coeff S) :
    Rep.res f (Rep.coind S.subtype X) ⟶
      Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X) :=
  Rep.ofHom ⟨mackeyToLin f S X, fun g => LinearMap.ext (mackeyToLin_equivariant f S X g)⟩

lemma mackeyHom_apply_apply (f : G →* D) (S : Subgroup D) (X : Rep Coeff S)
    (φ : (Rep.coind S.subtype X).V) (x : G) :
    (((mackeyHom f S X).hom φ).1 x) = φ.1 (f x) := rfl

/-! ## The inverse -/

/-- An `S'`-equivariant function on `G` is constant on the fibres of `f`. -/
lemma coind_welldef (f : G →* D) (S : Subgroup D) (X : Rep Coeff S)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V)
    {x y : G} (h : f x = f y) : ψ.1 x = ψ.1 y := by
  have hmem : x * y⁻¹ ∈ S.comap f := by
    rw [Subgroup.mem_comap]
    show f (x * y⁻¹) ∈ S
    rw [map_mul, map_inv, h, mul_inv_cancel]
    exact S.one_mem
  have hcond := (Representation.mem_coindV (φ := (S.comap f).subtype)
      (σ := X.ρ.comp (f.subgroupComap S)) ψ.1).mp ψ.2 ⟨x * y⁻¹, hmem⟩ y
  rw [show ((S.comap f).subtype ⟨x * y⁻¹, hmem⟩ : G) = x * y⁻¹ from rfl] at hcond
  rw [show x * y⁻¹ * y = x from by group] at hcond
  rw [hcond]
  have h1 : (f.subgroupComap S) ⟨x * y⁻¹, hmem⟩ = 1 := by
    ext
    show f (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [show (X.ρ.comp (f.subgroupComap S)) ⟨x * y⁻¹, hmem⟩
      = X.ρ ((f.subgroupComap S) ⟨x * y⁻¹, hmem⟩) from rfl, h1]
  simp

/-- The inverse: an `S'`-equivariant `ψ : G → X` gives a well defined `φ : D → X` with
`φ (f x) = ψ x`. -/
def mackeyInvLin (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) (X : Rep Coeff S) :
    (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V →ₗ[Coeff]
      (Rep.res f (Rep.coind S.subtype X)).V where
  toFun ψ := ⟨fun d => ψ.1 (Function.surjInv hf d), by
    intro s d
    change ψ.1 (Function.surjInv hf (S.subtype s * d)) = X.ρ s (ψ.1 (Function.surjInv hf d))
    set x₀ := Function.surjInv hf d with hx0def
    set x₁ := Function.surjInv hf (S.subtype s) with hx1def
    have hx0 : f x₀ = d := Function.surjInv_eq hf d
    have hx1 : f x₁ = S.subtype s := Function.surjInv_eq hf (S.subtype s)
    have hmem : x₁ ∈ S.comap f := by
      rw [Subgroup.mem_comap, hx1]; exact s.2
    have hcond := (Representation.mem_coindV (φ := (S.comap f).subtype)
      (σ := X.ρ.comp (f.subgroupComap S)) ψ.1).mp ψ.2 ⟨x₁, hmem⟩ x₀
    rw [show ((S.comap f).subtype ⟨x₁, hmem⟩ : G) = x₁ from rfl] at hcond
    have hfa : f (x₁ * x₀) = S.subtype s * d := by rw [map_mul, hx1, hx0]
    have key : ψ.1 (Function.surjInv hf (S.subtype s * d)) = ψ.1 (x₁ * x₀) :=
      coind_welldef f S X ψ (by rw [Function.surjInv_eq hf (S.subtype s * d), hfa])
    rw [key, hcond]
    have ht : (f.subgroupComap S) ⟨x₁, hmem⟩ = s := by
      apply Subtype.ext
      show f x₁ = (s : D)
      exact hx1
    rw [show (X.ρ.comp (f.subgroupComap S)) ⟨x₁, hmem⟩
        = X.ρ ((f.subgroupComap S) ⟨x₁, hmem⟩) from rfl, ht]⟩
  map_add' ψ χ := by ext d; simp
  map_smul' c ψ := by ext d; simp

lemma mackeyInvLin_apply (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V) (d : D) :
    (mackeyInvLin f hf S X ψ).1 d = ψ.1 (Function.surjInv hf d) := rfl

lemma mackeyInvLin_equivariant (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S) (g : G)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V) :
    mackeyInvLin f hf S X
        (((Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).ρ g) ψ) =
      ((Rep.res f (Rep.coind S.subtype X)).ρ g) (mackeyInvLin f hf S X ψ) := by
  ext d
  rw [mackeyInvLin_apply]
  rw [show (((Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).ρ g) ψ).1
        (Function.surjInv hf d) = ψ.1 (Function.surjInv hf d * g) from rfl]
  rw [show (((Rep.res f (Rep.coind S.subtype X)).ρ g) (mackeyInvLin f hf S X ψ)).1 d
        = (mackeyInvLin f hf S X ψ).1 (d * f g) from rfl]
  rw [mackeyInvLin_apply]
  exact coind_welldef f S X ψ (by rw [map_mul, Function.surjInv_eq hf, Function.surjInv_eq hf])

/-- The inverse morphism `Coind_{S'} (Res_{S'} X) ⟶ Res_f (Coind_S X)`. -/
def mackeyInv (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) (X : Rep Coeff S) :
    Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X) ⟶
      Rep.res f (Rep.coind S.subtype X) :=
  Rep.ofHom ⟨mackeyInvLin f hf S X, fun g => LinearMap.ext (mackeyInvLin_equivariant f hf S X g)⟩

lemma mackeyInv_apply_apply (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)).V) (d : D) :
    (((mackeyInv f hf S X).hom ψ).1 d) = ψ.1 (Function.surjInv hf d) := rfl

lemma mackeyHom_inv (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S) :
    mackeyHom f S X ≫ mackeyInv f hf S X = 𝟙 (Rep.res f (Rep.coind S.subtype X)) := by
  ext φ d
  simp only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_id, LinearMap.id_apply,
    Representation.IntertwiningMap.toLinearMap_apply]
  rw [mackeyInv_apply_apply, mackeyHom_apply_apply, Function.surjInv_eq hf]

lemma mackeyInv_hom (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S) :
    mackeyInv f hf S X ≫ mackeyHom f S X =
      𝟙 (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) X)) := by
  ext ψ x
  simp only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_id, LinearMap.id_apply,
    Representation.IntertwiningMap.toLinearMap_apply]
  rw [mackeyHom_apply_apply, mackeyInv_apply_apply]
  exact coind_welldef f S X ψ (Function.surjInv_eq hf (f x))

/-! ## The natural isomorphism of functors -/

/-- The component at `X` of the Mackey isomorphism. -/
def mackeyIso (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) (X : Rep Coeff S) :
    (Rep.coindFunctor Coeff S.subtype ⋙ Rep.resFunctor f).obj X ≅
      (Rep.resFunctor (f.subgroupComap S) ⋙
        Rep.coindFunctor Coeff (S.comap f).subtype).obj X where
  hom := mackeyHom f S X
  inv := mackeyInv f hf S X
  hom_inv_id := mackeyHom_inv f hf S X
  inv_hom_id := mackeyInv_hom f hf S X

lemma mackeyHom_naturality (f : G →* D) (S : Subgroup D) (X Y : Rep Coeff S) (α : X ⟶ Y) :
    (Rep.coindFunctor Coeff S.subtype ⋙ Rep.resFunctor f).map α ≫ mackeyHom f S Y
      = mackeyHom f S X ≫
        (Rep.resFunctor (f.subgroupComap S) ⋙
          Rep.coindFunctor Coeff (S.comap f).subtype).map α := by
  ext φ x
  show (α.hom (φ.1 (f x))) = (α.hom (φ.1 (f x)))
  rfl

/-- **The Mackey isomorphism for a surjection**, as an isomorphism of functors
`Rep k S ⥤ Rep k G`. -/
def mackeyNatIso (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    (Rep.coindFunctor Coeff S.subtype ⋙ Rep.resFunctor f) ≅
      (Rep.resFunctor (f.subgroupComap S) ⋙ Rep.coindFunctor Coeff (S.comap f).subtype) :=
  NatIso.ofComponents (fun X => mackeyIso f hf S X)
    (fun {X Y} α => mackeyHom_naturality f S X Y α)

lemma mackeyNatIso_hom_app (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S) :
    (mackeyNatIso f hf S).hom.app X = mackeyHom f S X := rfl

lemma mackeyNatIso_inv_app (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (X : Rep Coeff S) :
    (mackeyNatIso f hf S).inv.app X = mackeyInv f hf S X := rfl

/-! ## The bijection `G ⧸ S' ≃ D ⧸ S` and the termwise comparison of the two traces -/

/-- The map `G ⧸ S.comap f → D ⧸ S` induced by `f : G →* D`. -/
def comapQuotMap (f : G →* D) (S : Subgroup D) :
    Quotient (QuotientGroup.rightRel (S.comap f)) → Quotient (QuotientGroup.rightRel S) :=
  @Quotient.map G D (QuotientGroup.rightRel (S.comap f)) (QuotientGroup.rightRel S) f
    (fun a b (h : QuotientGroup.rightRel (S.comap f) a b) => by
      refine QuotientGroup.rightRel_apply.2 ?_
      have h' : b * a⁻¹ ∈ S.comap f := QuotientGroup.rightRel_apply.1 h
      rwa [Subgroup.mem_comap, map_mul, map_inv] at h')

lemma comapQuotMap_mk (f : G →* D) (S : Subgroup D) (x : G) :
    comapQuotMap f S (Quotient.mk'' (s₁ := QuotientGroup.rightRel (S.comap f)) x)
      = Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (f x) :=
  Quotient.map_mk _ _ x

/-- For a surjection `f`, the map `G ⧸ S.comap f → D ⧸ S` is a bijection. -/
lemma comapQuotMap_bijective (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    Function.Bijective (comapQuotMap f S) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      simp only [comapQuotMap_mk] at hab
      have h : (QuotientGroup.rightRel S) (f x) (f y) := Quotient.exact hab
      have h' : f y * (f x)⁻¹ ∈ S := QuotientGroup.rightRel_apply.1 h
      refine Quotient.sound' ?_
      refine QuotientGroup.rightRel_apply.2 ?_
      rwa [Subgroup.mem_comap, map_mul, map_inv]
  · intro b
    induction b using Quotient.inductionOn with
    | h d =>
      refine ⟨Quotient.mk'' (s₁ := QuotientGroup.rightRel (S.comap f)) (Function.surjInv hf d), ?_⟩
      rw [comapQuotMap_mk, Function.surjInv_eq hf]

/-- The representatives of corresponding cosets differ by an element of `S`. -/
lemma comapQuotMap_out_mem (f : G →* D) (S : Subgroup D)
    (q : Quotient (QuotientGroup.rightRel (S.comap f))) :
    f (Quotient.out q) * (Quotient.out (comapQuotMap f S q))⁻¹ ∈ S := by
  have h1 : Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (Quotient.out (comapQuotMap f S q))
      = comapQuotMap f S q := Quotient.out_eq' _
  have h2 : comapQuotMap f S q
      = comapQuotMap f S (Quotient.mk'' (s₁ := QuotientGroup.rightRel (S.comap f))
          (Quotient.out q)) := by rw [Quotient.out_eq']
  have h3 : comapQuotMap f S (Quotient.mk'' (s₁ := QuotientGroup.rightRel (S.comap f))
        (Quotient.out q)) = Quotient.mk'' (s₁ := QuotientGroup.rightRel S) (f (Quotient.out q)) :=
    comapQuotMap_mk f S (Quotient.out q)
  have h : (QuotientGroup.rightRel S) (Quotient.out (comapQuotMap f S q)) (f (Quotient.out q)) :=
    Quotient.exact (h1.trans (h2.trans h3))
  exact QuotientGroup.rightRel_apply.1 h

/-- **The termwise comparison of the two traces.** For an `S'`-equivariant `ψ : G → A` the
`q`-th summand of the trace of the `S`-equivariant function `φ` with `φ (f x) = ψ x`, taken with
representatives of the *`S`-cosets*, equals the summand of the trace of `ψ` over the corresponding
`S'`-coset. -/
lemma mackeyInv_summand (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (A : Rep Coeff D)
    (ψ : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) (Rep.res S.subtype A))).V)
    (q : Quotient (QuotientGroup.rightRel (S.comap f))) :
    A.ρ (Quotient.out (comapQuotMap f S q))⁻¹
        (ψ.1 (Function.surjInv hf (Quotient.out (comapQuotMap f S q))))
      = A.ρ (f (Quotient.out q))⁻¹ (ψ.1 (Quotient.out q)) := by
  set d := Quotient.out (comapQuotMap f S q) with hd
  set y := Quotient.out q with hy
  have hrel : f y * d⁻¹ ∈ S := comapQuotMap_out_mem f S q
  set s : S := ⟨f y * d⁻¹, hrel⟩ with hs_def
  have hs : (s : D) * d = f y := by
    show f y * d⁻¹ * d = f y
    group
  set z := Function.surjInv hf d with hz
  have hz' : f z = d := Function.surjInv_eq hf d
  set xs := Function.surjInv hf (s : D) with hxs
  have hxs' : f xs = (s : D) := Function.surjInv_eq hf (s : D)
  have hmem : xs ∈ S.comap f := by
    rw [Subgroup.mem_comap, hxs']; exact s.2
  have hwelldef : ψ.1 y = ψ.1 (xs * z) :=
    coind_welldef f S (Rep.res S.subtype A) ψ (by rw [map_mul, hxs', hz', hs])
  have hcond := (Representation.mem_coindV (φ := (S.comap f).subtype)
      (σ := (Rep.res (f.subgroupComap S) (Rep.res S.subtype A)).ρ) ψ.1).mp ψ.2
      (⟨xs, hmem⟩ : S.comap f) z
  have heq : ((Rep.res (f.subgroupComap S) (Rep.res S.subtype A)).ρ (⟨xs, hmem⟩ : S.comap f))
      = A.ρ (s : D) := by
    have h1 : S.subtype ((f.subgroupComap S) ⟨xs, hmem⟩) = (s : D) := hxs'
    rw [show ((Rep.res (f.subgroupComap S) (Rep.res S.subtype A)).ρ (⟨xs, hmem⟩ : S.comap f))
        = A.ρ (S.subtype ((f.subgroupComap S) ⟨xs, hmem⟩)) from rfl, h1]
  have hsz : ψ.1 (xs * z) = A.ρ (s : D) (ψ.1 z) := by
    rw [show ((S.comap f).subtype ⟨xs, hmem⟩ : G) = xs from rfl] at hcond
    rw [heq] at hcond
    exact hcond
  have hy_eq : ψ.1 y = A.ρ (s : D) (ψ.1 z) := hwelldef.trans hsz
  have hz_eq : ψ.1 z = A.ρ ((s : D)⁻¹) (ψ.1 y) := by
    rw [hy_eq, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel]
    simp
  rw [hz_eq, ← Module.End.mul_apply, ← map_mul]
  have hmul : d⁻¹ * (s : D)⁻¹ = (f y)⁻¹ := by
    rw [← mul_inv_rev, hs]
  rw [hmul]

/-- The bijection `G ⧸ S.comap f ≃ D ⧸ S` induced by a surjection `f`. -/
noncomputable def comapQuotEquiv (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D) :
    Quotient (QuotientGroup.rightRel (S.comap f)) ≃ Quotient (QuotientGroup.rightRel S) :=
  Equiv.ofBijective (comapQuotMap f S) (comapQuotMap_bijective f hf S)

lemma comapQuotEquiv_apply (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    (q : Quotient (QuotientGroup.rightRel (S.comap f))) :
    comapQuotEquiv f hf S q = comapQuotMap f S q := rfl

/-- **The traces agree on the descent.** For an `S'`-equivariant `ψ : G → A.V`, with `φ` the
corresponding `S`-equivariant function `D → A.V` (i.e. `φ (f x) = ψ x`), the `S`-trace of `φ`
equals the `S'`-trace of `ψ`. This is the underlying identity for the trace compatibility. -/
theorem mackeyInv_traceLin {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]
    (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (A : Rep Coeff D)
    (ψ : (Rep.coind (S.comap f).subtype
      (Rep.res (f.subgroupComap S) (Rep.res S.subtype A))).V) :
    traceLin S A (mackeyInvLin f hf S (Rep.res S.subtype A) ψ)
      = traceLin (S.comap f) (Rep.res f A) ψ := by
  have h1 : traceLin S A (mackeyInvLin f hf S (Rep.res S.subtype A) ψ)
      = ∑ q : Quotient (QuotientGroup.rightRel S),
          A.ρ (Quotient.out q)⁻¹ (ψ.1 (Function.surjInv hf (Quotient.out q))) := by
    rw [traceLin_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    exact congrArg (fun v => A.ρ (Quotient.out q)⁻¹ v)
      (mackeyInvLin_apply f hf S (Rep.res S.subtype A) ψ (Quotient.out q))
  have hsum := (Fintype.sum_equiv (comapQuotEquiv f hf S)
      (fun q' : Quotient (QuotientGroup.rightRel (S.comap f)) =>
        A.ρ (f (Quotient.out q'))⁻¹ (ψ.1 (Quotient.out q')))
      (fun q : Quotient (QuotientGroup.rightRel S) =>
        A.ρ (Quotient.out q)⁻¹ (ψ.1 (Function.surjInv hf (Quotient.out q))))
      (fun q' => (mackeyInv_summand f hf S A ψ q').symm)).symm
  have h3 : (∑ q : Quotient (QuotientGroup.rightRel (S.comap f)),
        A.ρ (f (Quotient.out q))⁻¹ (ψ.1 (Quotient.out q)))
      = ∑ q : Quotient (QuotientGroup.rightRel (S.comap f)),
          (Rep.res f A).ρ (Quotient.out q)⁻¹ (ψ.1 (Quotient.out q)) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [MonoidHom.comp_apply, map_inv]
  exact h1.trans (hsum.trans (h3.trans
    (traceLin_apply (S.comap f) (Rep.res f A) ψ).symm))

/-- **Compatibility of the Mackey isomorphism with the traces.** -/
theorem mackey_trace_compat {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]
    (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (A : Rep Coeff D) :
    CategoryTheory.CategoryStruct.comp ((mackeyNatIso f hf S).inv.app (Rep.res S.subtype A))
      ((Rep.resFunctor f).map (coindTrace S A))
    = coindTrace (S.comap f) (Rep.res f A) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ψ
  show traceLin S A (mackeyInvLin f hf S (Rep.res S.subtype A) ψ)
     = traceLin (S.comap f) (Rep.res f A) ψ
  exact mackeyInv_traceLin f hf S A ψ

/-- **Compatibility of the Mackey isomorphism with the units of the adjunctions.** -/
theorem mackey_unit_compat {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]
    (f : G →* D) (hf : Function.Surjective f) (S : Subgroup D)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (G ⧸ S.comap f)]
    (M : Rep Coeff D) :
    CategoryTheory.CategoryStruct.comp
      ((Rep.resFunctor f).map ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M))
      ((mackeyNatIso f hf S).hom.app (Rep.res S.subtype M))
    = (Rep.resCoindAdjunction Coeff (S.comap f).subtype).unit.app (Rep.res f M) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  funext x
  show (((Rep.resCoindAdjunction Coeff S.subtype).unit.app M).hom m).1 (f x)
     = (((Rep.resCoindAdjunction Coeff (S.comap f).subtype).unit.app
          (Rep.res f M)).hom m).1 x
  exact (resCoind_unit_apply_coe S M m (f x)).trans
    (resCoind_unit_apply_coe (S.comap f) (Rep.res f M) m x).symm

end

end Work.SSGRoute
