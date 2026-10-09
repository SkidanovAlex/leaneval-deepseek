import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.Sha2Lib.extH_class_of_character
import Submission.Work.SSGRoute.mapExactFunctor_id
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-! ## Scalar multiples in a module killed by `p`

Two elementary facts about `ℕ`-scalar multiples: in a module killed by `p`, the multiple `n • m`
only depends on `n % p` (equivalently on the image of `n` in `ZMod p`). -/

/-- In a module killed by `p`, `n • m = (n % p) • m`. -/
theorem nsmul_eq_mod_nsmul {M : Type*} [AddCommMonoid M] (p n : ℕ) {m : M}
    (hm : p • m = 0) : n • m = (n % p) • m := by
  conv_lhs => rw [← Nat.div_add_mod n p]
  rw [add_nsmul, mul_nsmul, hm, nsmul_zero, zero_add]

/-- In a module killed by `p`, `a • m = b • m` whenever `a` and `b` agree in `ZMod p`. -/
theorem nsmul_eq_of_natCast_eq {M : Type*} [AddCommMonoid M] (p : ℕ) {m : M}
    (hm : p • m = 0) {a b : ℕ} (h : (a : ZMod p) = (b : ZMod p)) : a • m = b • m := by
  have hab : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rw [nsmul_eq_mod_nsmul p a hm, nsmul_eq_mod_nsmul p b hm, hab]

/-! ## The `1`-cocycle of the invariant case -/

/-- **The `1`-cocycle of the invariant case.**  Let `G` be a group, `A` a `G`-module over the
coefficient ring `Coeff = ULift ℤ` which is killed by `p`, `f : Additive G →+ ZMod p` an additive
character, and `m ∈ A` a `G`-fixed element.  Then the function `g ↦ (f g).val • m` is a
`1`-cocycle of `A`: the cocycle identity
`(f (g*h)).val • m = A.ρ g ((f h).val • m) + (f g).val • m`
follows from additivity of `f` (so that `(f (g*h)).val` and `(f h).val + (f g).val` have the same
image in `ZMod p`), from `G`-invariance of `m`, and from `p • m = 0`. -/
theorem invariantCocycle {G : Type} [Group G] (A : Rep.{0} Coeff G) (p : ℕ) [NeZero p]
    (hA : ∀ x : A, p • x = 0) (f : Additive G →+ ZMod p) (m : A)
    (hm : ∀ g : G, A.ρ g m = m) :
    (fun g : G => (f (Additive.ofMul g)).val • m) ∈ groupCohomology.cocycles₁ A := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro g h
  show (f (Additive.ofMul (g * h))).val • m
      = A.ρ g ((f (Additive.ofMul h)).val • m) + (f (Additive.ofMul g)).val • m
  rw [map_nsmul, hm g]
  rw [← add_nsmul]
  refine nsmul_eq_of_natCast_eq p (hA m) ?_
  rw [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ofMul_mul, map_add]
  exact add_comm _ _

/-! ## The `Ext`-algebra of restriction followed by a coefficient map -/

/-- **(D)** `extHMap` as a post-composition: `extHMap g ι x = (extHMap g 𝟙 x).comp (mk₀ ι) _`.
(A local copy of `dass_extHMap_eq_comp` of
`Submission/Work/SSGRoute/detectAbove_sub_step_new.lean`, kept here to avoid importing that file.) -/
theorem extHMap_eq_comp_aux {G₁ G : Type} [Group G₁] [Group G]
    (g : G →* G₁) {B₁ : Rep.{0} Coeff G₁} {B : Rep.{0} Coeff G}
    (ι : Rep.res g B₁ ⟶ B) (s : ℕ) (x : extH B₁ s) :
    extHMap g ι x = (extHMap g (𝟙 (Rep.res g B₁)) x).comp
      (Abelian.Ext.mk₀ ι) (add_zero s) := by
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]

/-- The identity `ℤ → ℤ` gives the identity change of coefficients: `extHMap` at the identity group
map is postcomposition with `mk₀ φ`. -/
theorem extHMap_id_apply_aux {G : Type} [Group G] {A B : Rep.{0} Coeff G} (φ : A ⟶ B) {n : ℕ}
    (y : extH A n) : extHMap (MonoidHom.id G) φ y = y.comp (Abelian.Ext.mk₀ φ) (add_zero n) := by
  unfold extHMap extRes
  rw [show y.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = y from
        Work.SSGRoute.mapExactFunctor_id y,
      show unitRes (MonoidHom.id G) = 𝟙 (unitRep G) from rfl]
  exact Abelian.Ext.mk₀_id_comp _

/-- **Naturality of the `E0b` bridge in the coefficient morphism.**  Postcomposition with `mk₀ φ`
of the class of a `1`-cocycle `z` is the class of the coefficientwise image cocycle `z'`.  (Local
copy of `Work.SSGRoute.E7cOmega.eCoh_one_comp_mk0`.) -/
theorem eCoh_one_comp_mk0_aux {G : Type} [Group G] {A B : Rep.{0} Coeff G} (φ : A ⟶ B)
    (z : ↥(groupCohomology.cocycles₁ A)) (z' : ↥(groupCohomology.cocycles₁ B))
    (hz : ∀ g : G, (z' : G → ↥B) g = φ.hom ((z : G → ↥A) g)) :
    (eCoh 1 G A ((groupCohomology.H1π A).hom z)).comp
        (Abelian.Ext.mk₀ φ) (add_zero 1) =
      eCoh 1 G B ((groupCohomology.H1π B).hom z') := by
  have hzz : groupCohomology.mapCocycles₁ (MonoidHom.id G) φ z = z' := by
    apply Subtype.ext
    funext g
    first
      | (rw [groupCohomology.coe_mapCocycles₁]; exact (hz g).symm)
      | (show (groupCohomology.cochainsMap₁ (MonoidHom.id G) φ (z : G → ↥A)) g
            = (z' : G → ↥B) g
         exact (hz g).symm)
      | exact (hz g).symm
  rw [← extHMap_id_apply_aux φ (eCoh 1 G A ((groupCohomology.H1π A).hom z)),
    ← Work.SSGRoute.eCoh_map 1 G G (MonoidHom.id G) A B φ ((groupCohomology.H1π A).hom z),
    groupCohomology.H1π_comp_map_apply, hzz]

/-- **Restriction to a subgroup followed by a coefficient morphism, computed on cocycles.**
Let `A` be a `G`-module, `D ≤ G`, `φ : res_D A ⟶ B` a morphism of `D`-modules, `z` a `1`-cocycle of
`A` and `z'` a `1`-cocycle of `B` whose values are the `φ`-images of the values of `z`.  Then the
class of `z` in `H¹(G, A)`, restricted to `D` and pushed forward along `φ`, is the class of `z'` in
`H¹(D, B)`. -/
theorem eCoh_restrict_comp_mk0 {G : Type} [Group G] (D : Subgroup G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff ↥D) (φ : Rep.res D.subtype A ⟶ B)
    (z : ↥(groupCohomology.cocycles₁ A)) (z' : ↥(groupCohomology.cocycles₁ B))
    (hz : ∀ d : ↥D, (z' : ↥D → ↥B) d = φ.hom ((z : G → ↥A) (d : G))) :
    (extHRestrict D (eCoh 1 G A ((groupCohomology.H1π A).hom z))).comp
        (Abelian.Ext.mk₀ φ) (add_zero 1) =
      eCoh 1 ↥D B ((groupCohomology.H1π B).hom z') := by
  have hzz : groupCohomology.mapCocycles₁ D.subtype φ z = z' := by
    apply Subtype.ext
    funext d
    first
      | (rw [groupCohomology.coe_mapCocycles₁]; exact (hz d).symm)
      | (show (groupCohomology.cochainsMap₁ D.subtype φ (z : G → ↥A)) d
            = (z' : ↥D → ↥B) d
         exact (hz d).symm)
      | exact (hz d).symm
  have h1 : (extHRestrict D (eCoh 1 G A ((groupCohomology.H1π A).hom z))).comp
        (Abelian.Ext.mk₀ φ) (add_zero 1) =
      extHMap D.subtype φ (eCoh 1 G A ((groupCohomology.H1π A).hom z)) := by
    show (extHMap D.subtype (𝟙 (Rep.res D.subtype A))
        (eCoh 1 G A ((groupCohomology.H1π A).hom z))).comp
          (Abelian.Ext.mk₀ φ) (add_zero 1) =
      extHMap D.subtype φ (eCoh 1 G A ((groupCohomology.H1π A).hom z))
    exact (extHMap_eq_comp_aux D.subtype φ 1 _).symm
  rw [h1, ← Work.SSGRoute.eCoh_map 1 G ↥D D.subtype A B φ ((groupCohomology.H1π A).hom z),
    groupCohomology.H1π_comp_map_apply, hzz]

/-! ## The invariant case of the unramified detector -/

theorem detectorInvariantCase (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (f : Additive (L ≃ₐ[k] L) →+ ZMod p)
    (hf : ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' σ → f (Additive.ofMul σ) = 0)
    (hfne : ∃ σ : L ≃ₐ[k] L,
      σ ∈ SSGRoute.PTExt.decompK (NK.GlobalCFT.Place.ofFinite q') ∧ f (Additive.ofMul σ) ≠ 0)
    (π : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Rep.trivial SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k) (K := K) w) (ZMod p))
    (m : M) (hm : ∀ σ : K ≃ₐ[k] K, M.ρ σ m = m) (hmπ : π.hom m ≠ 0) :
    ∃ h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1,
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      (SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q')) h).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap
          (Work.SSGRoute.decompKRestrict k K L w
            (NK.GlobalCFT.Place.ofFinite q') hq') π)) (add_zero 1) ≠ 0 := by
  classical
  -- The `Gal(L/k)`-module `res M` and its `1`-cocycle `σ ↦ f(σ) • m`.
  let A : Rep.{0} SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) :=
    Rep.res (SSGRoute.PTExt.galRes k K L) M
  have hA : ∀ x : A, p • x = 0 := fun x => hM x
  have hfix : ∀ σ : L ≃ₐ[k] L, A.ρ σ m = m := fun σ => hm (SSGRoute.PTExt.galRes k K L σ)
  have hzm : (fun σ : L ≃ₐ[k] L => (f (Additive.ofMul σ)).val • m) ∈
      groupCohomology.cocycles₁ A := invariantCocycle A p hA f m hfix
  let z : groupCohomology.cocycles₁ A := ⟨_, hzm⟩
  have hzval : ∀ σ : L ≃ₐ[k] L,
      (z : (L ≃ₐ[k] L) → ↥A) σ = (f (Additive.ofMul σ)).val • m := fun σ => rfl
  set h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1 :=
    SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A ((groupCohomology.H1π A).hom z) with hh
  refine ⟨h, ?_, ?_⟩
  · -- Unramifiedness: the cocycle vanishes on the inertia group of `q'`.
    intro D hD
    rw [hh]
    refine (Work.SSGRoute.e9_caseB_cocycle A D z).mpr ⟨0, ?_⟩
    intro d hd
    rw [hzval d, hf d (hD d hd)]
    simp
  · -- Non-vanishing on the decomposition group of `q'`.
    let D' : Subgroup (L ≃ₐ[k] L) :=
      SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q')
    let c : ZMod p := π.hom m
    have hcne : c ≠ 0 := hmπ
    -- Multiplication of the character `f` on `D'` by the non-zero constant `c`.
    let gchar : Additive ↥D' →+ ZMod p :=
      { toFun := fun a => f (Additive.ofMul ((Additive.toMul a : ↥D') : L ≃ₐ[k] L)) * c
        map_zero' := by
          change f (Additive.ofMul ((1 : ↥D') : L ≃ₐ[k] L)) * c = 0
          simp
        map_add' := by
          intro a b
          show f (Additive.ofMul ((Additive.toMul (a + b) : ↥D') : L ≃ₐ[k] L)) * c
            = f (Additive.ofMul ((Additive.toMul a : ↥D') : L ≃ₐ[k] L)) * c
              + f (Additive.ofMul ((Additive.toMul b : ↥D') : L ≃ₐ[k] L)) * c
          rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl,
            Subgroup.coe_mul, ofMul_mul, map_add, add_mul] }
    have hg_ne : gchar ≠ 0 := by
      obtain ⟨σ, hσ, hσne⟩ := hfne
      intro hg0
      have h1 : gchar (Additive.ofMul (⟨σ, hσ⟩ : ↥D')) = 0 := by rw [hg0]; rfl
      rw [show gchar (Additive.ofMul (⟨σ, hσ⟩ : ↥D'))
            = f (Additive.ofMul σ) * c from rfl] at h1
      exact mul_ne_zero hσne hcne h1
    -- The class of the character `gchar` on `D'`, and its identification with the pushed-forward
    -- restricted cocycle.
    let zt : ↥(groupCohomology.cocycles₁ (Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p))) :=
      ⟨gchar ∘ Additive.ofMul,
        groupCohomology.mem_cocycles₁_of_addMonoidHom
          (A := Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p)) gchar⟩
    have hzid : ∀ d : ↥D',
        (zt : ↥D' → ZMod p) d
          = (Rep.resMap (Work.SSGRoute.decompKRestrict k K L w
              (NK.GlobalCFT.Place.ofFinite q') hq') π).hom
              ((z : (L ≃ₐ[k] L) → ↥A) (d : L ≃ₐ[k] L)) := by
      intro d
      rw [hzval (d : L ≃ₐ[k] L)]
      show gchar (Additive.ofMul d)
        = (Rep.resMap (Work.SSGRoute.decompKRestrict k K L w
            (NK.GlobalCFT.Place.ofFinite q') hq') π).hom
            ((f (Additive.ofMul ((d : ↥D') : L ≃ₐ[k] L))).val • m)
      rw [show gchar (Additive.ofMul d)
            = f (Additive.ofMul ((d : ↥D') : L ≃ₐ[k] L)) * c from rfl,
        Rep.resMap_hom_apply, map_nsmul]
      rw [show π.hom m = c from rfl, nsmul_eq_mul, ZMod.natCast_zmod_val]
    have key : (SSGRoute.PTExt.extHRestrict D'
          (SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A ((groupCohomology.H1π A).hom z))).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (Work.SSGRoute.decompKRestrict k K L w
            (NK.GlobalCFT.Place.ofFinite q') hq') π)) (add_zero 1) =
        SSGRoute.PTExt.eCoh 1 ↥D' (Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p))
          ((groupCohomology.H1π (Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p))).hom zt) :=
      eCoh_restrict_comp_mk0 D' A (Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p))
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K L w
          (NK.GlobalCFT.Place.ofFinite q') hq') π) z zt hzid
    rw [hh]
    show (SSGRoute.PTExt.extHRestrict D'
        (SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A
          ((groupCohomology.H1π A).hom z))).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (Work.SSGRoute.decompKRestrict k K L w
            (NK.GlobalCFT.Place.ofFinite q') hq') π)) (add_zero 1) ≠ 0
    rw [key]
    intro h0
    have h1 : (groupCohomology.H1π (Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p))).hom zt
        = 0 :=
      (SSGRoute.PTExt.eCoh 1 ↥D'
        (Rep.trivial SSGRoute.PTExt.Coeff ↥D' (ZMod p))).map_eq_zero_iff.mp h0
    exact H1pi_character_ne_zero ↥D' p gchar hg_ne h1

end Work.SSGRoute.Sha2Lib
