import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.extHRestrict_comp
import Submission.Work.SSGRoute.phiTriv_mk0_eq
import Submission.Work.SSGRoute.unitsMap_mem_localUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped RestrictedProduct
open NK.GlobalCFT (Idele Place IdeleClassGroup)

set_option linter.unusedSectionVars false

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## `𝔽_p`-valued morphisms of representations -/

section ZmodHom

variable {A : Type} [AddCommGroup A]

/-- Associativity of `Ext.comp` with a degree-`0` first factor. -/
theorem comp_assoc_first_deg_zero {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z T : C} {a₂ a₃ : ℕ} (α : Abelian.Ext X Y 0) (β : Abelian.Ext Y Z a₂)
    (γ : Abelian.Ext Z T a₃) :
    (α.comp β (zero_add a₂)).comp γ rfl = α.comp (β.comp γ rfl) (zero_add (a₂ + a₃)) :=
  Abelian.Ext.comp_assoc α β γ (zero_add a₂) rfl (by omega)

/-- The additive homomorphism `ℤ →+ A` given by multiplication by `x`. -/
noncomputable def zmodScalarHom (x : A) : ℤ →+ A where
  toFun := fun m => m • x
  map_zero' := zero_zsmul x
  map_add' := fun a b => add_zsmul x a b

/-- The additive homomorphism `𝔽_p →+ A` sending the generator `1` to a `p`-torsion point `x`. -/
noncomputable def zmodToAdd (x : A) (hx : (p : ℤ) • x = 0) : ZMod p →+ A :=
  ZMod.lift p ⟨zmodScalarHom x, by simpa [zmodScalarHom] using hx⟩

@[simp] lemma zmodToAdd_coe (x : A) (hx : (p : ℤ) • x = 0) (m : ℤ) :
    zmodToAdd p x hx (m : ZMod p) = m • x := by
  simp [zmodToAdd, zmodScalarHom, ZMod.lift_coe]

@[simp] lemma zmodToAdd_one (x : A) (hx : (p : ℤ) • x = 0) :
    zmodToAdd p x hx 1 = x := by
  rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from by simp, zmodToAdd_coe, one_zsmul]

/-- `zmodToAdd` is fixed by any additive endomorphism fixing `x`. -/
lemma zmodToAdd_map (x : A) (hx : (p : ℤ) • x = 0) (f : A →+ A) (hf : f x = x) (n : ZMod p) :
    f (zmodToAdd p x hx n) = zmodToAdd p x hx n := by
  have hgen : ∀ m : ℤ, f (zmodToAdd p x hx ((m : ℤ) : ZMod p)) =
      zmodToAdd p x hx ((m : ℤ) : ZMod p) := by
    intro m
    rw [zmodToAdd_coe, map_zsmul, hf]
  have hn : n = ((n.val : ℤ) : ZMod p) := by
    rw [← ZMod.natCast_zmod_val n]
    simp
  rw [hn]
  exact hgen _

end ZmodHom

/-- `𝔽_p`-valued morphisms of representations out of the trivial representation are determined by
the image of the generator `1`. -/
lemma zmod_trivial_hom_ext {G : Type} [Group G] {P : ℕ} [Fact P.Prime] {B : Rep Coeff G}
    (f g : Rep.trivial Coeff G (ZMod P) ⟶ B) (h : f.hom (1 : ZMod P) = g.hom (1 : ZMod P)) :
    f = g := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro n
  have hn : n = (n : ZMod P).val • (1 : ZMod P) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (n : ZMod P)]
    rw [nsmul_one]
  rw [hn, map_nsmul, map_nsmul, h]

/-! ## The `μ_p`-idèle `(ζ^{a v})_v` of a number field -/

section MuIdeles

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (ζ : k) (hζ : IsPrimitiveRoot ζ p)

/-- The image of a primitive `p`-th root of unity `ζ ∈ k` in `Kˣ`. -/
noncomputable def zetaUnitK : Kˣ :=
  Units.mk0 (algebraMap k K ζ)
    ((hζ.map_of_injective (algebraMap k K).injective).ne_zero (Fact.out : p.Prime).ne_zero)

@[simp] lemma zetaUnitK_coe : ((zetaUnitK p k K ζ hζ : Kˣ) : K) = algebraMap k K ζ := rfl

@[simp] lemma zetaUnitK_pow : zetaUnitK p k K ζ hζ ^ p = 1 := by
  ext
  simp [zetaUnitK, ← map_pow, hζ.pow_eq_one]

/-- **The `μ_p`-idèle of `K` attached to `a : Place K → ZMod p`**: the idèle whose component at
the place `v` is `ζ^{a v}` (a local unit, since `ζ` is a root of unity). -/
noncomputable def muIdeles (a : Place K → ZMod p) : Idele K :=
  RestrictedProduct.mk
    (fun v => (Units.map ((algebraMap K (Place.localField K v)).toMonoidHom) (zetaUnitK p k K ζ hζ))
      ^ (a v).val)
    (Filter.Eventually.of_forall fun v =>
      Subgroup.pow_mem _ (unitsMap_mem_localUnits (zetaUnitK p k K ζ hζ)
        (Fact.out : p.Prime).ne_zero (zetaUnitK_pow p k K ζ hζ) v) (a v).val)

@[simp] lemma muIdeles_apply (a : Place K → ZMod p) (v : Place K) :
    muIdeles p k K ζ hζ a v =
      (Units.map ((algebraMap K (Place.localField K v)).toMonoidHom) (zetaUnitK p k K ζ hζ))
        ^ (a v).val :=
  rfl

lemma muIdeles_pow (a : Place K → ZMod p) : muIdeles p k K ζ hζ a ^ p = 1 := by
  apply Idele.ext
  intro v
  have h1 : (muIdeles p k K ζ hζ a ^ p) v = (muIdeles p k K ζ hζ a v) ^ p :=
    MonoidHom.map_pow (Idele.eval v) _ p
  rw [h1, muIdeles_apply]
  have h2 : (Units.map ((algebraMap K (Place.localField K v)).toMonoidHom)
      (zetaUnitK p k K ζ hζ)) ^ p = 1 := by
    rw [← map_pow, zetaUnitK_pow, map_one]
  rw [← pow_mul, mul_comm, pow_mul, h2, one_pow, Idele.one_apply]

lemma muIdeles_smul (a : Place K → ZMod p) (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w)
    (σ : K ≃ₐ[k] K) : σ • muIdeles p k K ζ hζ a = muIdeles p k K ζ hζ a := by
  apply Idele.ext
  intro v
  rw [Idele.smul_apply, muIdeles_apply, muIdeles_apply]
  have key : (Units.map (Place.localRingEquiv σ⁻¹ v).symm.toMonoidHom)
      (Units.map ((algebraMap K (Place.localField K (σ⁻¹ • v))).toMonoidHom)
        (zetaUnitK p k K ζ hζ))
      = Units.map ((algebraMap K (Place.localField K v)).toMonoidHom) (zetaUnitK p k K ζ hζ) := by
    apply Units.ext
    rw [Units.coe_map, Units.coe_map]
    change (Place.localRingEquiv σ⁻¹ v).symm
        ((algebraMap K (Place.localField K (σ⁻¹ • v))) (zetaUnitK p k K ζ hζ : K)) =
      (algebraMap K (Place.localField K v)) (zetaUnitK p k K ζ hζ : K)
    rw [zetaUnitK_coe,
      NK.GlobalCFT.Galois.globalCFT_localRingEquiv_symm_algebraMap σ v (algebraMap k K ζ),
      σ.commutes ζ]
  rw [map_pow, key, ← ha σ⁻¹ v]

/-- The class of the `μ_p`-idèle in `C_K`, as a `p`-torsion point. -/
noncomputable def muClass (a : Place K → ZMod p) : Additive (IdeleClassGroup K) :=
  Additive.ofMul (IdeleClassGroup.mk K (muIdeles p k K ζ hζ a))

lemma muClass_p (a : Place K → ZMod p) : (p : ℤ) • muClass p k K ζ hζ a = 0 := by
  have h1 : (p : ℤ) • Additive.ofMul (IdeleClassGroup.mk K (muIdeles p k K ζ hζ a)) =
      Additive.ofMul ((IdeleClassGroup.mk K (muIdeles p k K ζ hζ a)) ^ p) := by
    rw [natCast_zsmul]
    rfl
  rw [muClass, h1, show (IdeleClassGroup.mk K (muIdeles p k K ζ hζ a)) ^ p = 1 from by
    rw [← map_pow, muIdeles_pow, map_one]]
  simp

lemma muClass_smul (a : Place K → ZMod p) (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w)
    (σ : K ≃ₐ[k] K) : σ • muClass p k K ζ hζ a = muClass p k K ζ hζ a := by
  show Additive.ofMul (σ • IdeleClassGroup.mk K (muIdeles p k K ζ hζ a)) =
    Additive.ofMul (IdeleClassGroup.mk K (muIdeles p k K ζ hζ a))
  rw [IdeleClassGroup.smul_mk, muIdeles_smul p k K ζ hζ a ha σ]

end MuIdeles

/-! ## The `𝔽_p`-valued coefficient morphisms -/

section Level

variable (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]

/-- The morphism of `Gal(L/k)`-representations `𝔽_p ⟶ C_L` with a prescribed `p`-torsion
`Gal(L/k)`-fixed class at `1`. -/
noncomputable def zmodToClassesRep (x : Additive (IdeleClassGroup L)) (hx : (p : ℤ) • x = 0)
    (hfix : ∀ σ : L ≃ₐ[k] L, σ • x = x) :
    Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ classesK k L :=
  Rep.ofHom
    { toFun := (zmodToAdd p x hx : ZMod p → Additive (IdeleClassGroup L))
      map_add' := fun a b => (zmodToAdd p x hx).map_add a b
      map_smul' := fun n v => by
        obtain ⟨m⟩ := n
        exact AddMonoidHom.map_zsmul (zmodToAdd p x hx) m v
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro n
        show zmodToAdd p x hx ((Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)).ρ σ n) =
          (classesK k L).ρ σ (zmodToAdd p x hx n)
        rw [Rep.trivial_ρ_apply]
        exact (zmodToAdd_map p x hx
          (DistribSMul.toAddMonoidHom (Additive (IdeleClassGroup L)) σ) (hfix σ) n).symm }

@[simp] lemma zmodToClassesRep_apply (x : Additive (IdeleClassGroup L)) (hx : (p : ℤ) • x = 0)
    (hfix : ∀ σ : L ≃ₐ[k] L, σ • x = x) (n : ZMod p) :
    (zmodToClassesRep p k L x hx hfix).hom n = zmodToAdd p x hx n := rfl

@[simp] lemma zmodToClassesRep_apply_one (x : Additive (IdeleClassGroup L))
    (hx : (p : ℤ) • x = 0) (hfix : ∀ σ : L ≃ₐ[k] L, σ • x = x) :
    (zmodToClassesRep p k L x hx hfix).hom 1 = x := by
  rw [zmodToClassesRep_apply, zmodToAdd_one]

/-- The morphism of `Gal(L/k)`-representations `𝔽_p ⟶ 𝕀_L` with a prescribed `p`-torsion
`Gal(L/k)`-fixed idèle at `1`. -/
noncomputable def zmodToIdelesRep (e : Idele L) (he : (p : ℤ) • Additive.ofMul e = 0)
    (hfix : ∀ σ : L ≃ₐ[k] L, σ • Additive.ofMul e = Additive.ofMul e) :
    Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ idelesK k L :=
  Rep.ofHom
    { toFun := (zmodToAdd p (Additive.ofMul e) he : ZMod p → Additive (Idele L))
      map_add' := fun a b => (zmodToAdd p (Additive.ofMul e) he).map_add a b
      map_smul' := fun n v => by
        obtain ⟨m⟩ := n
        exact AddMonoidHom.map_zsmul (zmodToAdd p (Additive.ofMul e) he) m v
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro n
        show zmodToAdd p (Additive.ofMul e) he
            ((Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)).ρ σ n) =
          (idelesK k L).ρ σ (zmodToAdd p (Additive.ofMul e) he n)
        rw [Rep.trivial_ρ_apply]
        exact (zmodToAdd_map p (Additive.ofMul e) he
          (DistribSMul.toAddMonoidHom (Additive (Idele L)) σ) (hfix σ) n).symm }

@[simp] lemma zmodToIdelesRep_apply (e : Idele L) (he : (p : ℤ) • Additive.ofMul e = 0)
    (hfix : ∀ σ : L ≃ₐ[k] L, σ • Additive.ofMul e = Additive.ofMul e) (n : ZMod p) :
    (zmodToIdelesRep p k L e he hfix).hom n = zmodToAdd p (Additive.ofMul e) he n := rfl

@[simp] lemma zmodToIdelesRep_apply_one (e : Idele L) (he : (p : ℤ) • Additive.ofMul e = 0)
    (hfix : ∀ σ : L ≃ₐ[k] L, σ • Additive.ofMul e = Additive.ofMul e) :
    (zmodToIdelesRep p k L e he hfix).hom 1 = Additive.ofMul e := by
  rw [zmodToIdelesRep_apply, zmodToAdd_one]

end Level

/-! ## `Ext`-calculus helpers -/

/-- `n`-fold addition commutes with `Ext.comp` in the second variable. -/
lemma Ext.comp_nsmul {C : Type*} [Category* C] [Abelian C] [HasExt C] {X Y Z : C} {a b c : ℕ}
    (n : ℕ) (α : Abelian.Ext X Y a) (β : Abelian.Ext Y Z b) (h : a + b = c) :
    n • (α.comp β h) = α.comp (n • β) h := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.comp_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, ih, Abelian.Ext.comp_add]

/-- The `ℕ`-scalar action on intertwining maps is pointwise. -/
lemma IntertwiningMap.nsmul_apply_aux {A G V W : Type*} [Semiring A] [Monoid G] [AddCommMonoid V]
    [AddCommMonoid W] [Module A V] [Module A W] {ρ : Representation A G V}
    {σ : Representation A G W} (n : ℕ) (f : ρ.IntertwiningMap σ) (x : V) :
    (n • f) x = n • f x := rfl

/-- The `ℕ`-scalar action on morphisms of representations is pointwise. -/
lemma Rep.nsmul_apply_aux {G : Type} [Group G] {A B : Rep Coeff G} (n : ℕ) (f : A ⟶ B)
    (x : A) : (n • f) x = n • f x := rfl

/-- Morphisms out of a restricted trivial representation on `𝔽_p` are determined by the image of
the generator `1`. -/
lemma res_trivial_zmod_hom_ext {G H : Type} [Group G] [Group H] (f : H →* G) {P : ℕ}
    [Fact P.Prime] {B : Rep Coeff H} (u v : Rep.res f (Rep.trivial Coeff G (ZMod P)) ⟶ B)
    (h : u.hom (1 : ZMod P) = v.hom (1 : ZMod P)) : u = v := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro n
  have hn : n = (n : ZMod P).val • (1 : ZMod P) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (n : ZMod P)]
    rw [nsmul_one]
  rw [hn, map_nsmul, map_nsmul, h]

/-- The value of the trivially-acting `trivRes` on the generator. -/
@[simp] lemma trivRes_hom_one {G H : Type} [Group G] [Group H] (f : H →* G) (P : ℕ) :
    (trivRes f (ZMod P)).hom (1 : ZMod P) = (1 : ZMod P) := rfl

/-! ## Computation rules for the localisation maps -/

/-- The `w`-component of an idèle, as the value of `ideleToLocalUnits`. -/
@[simp] lemma ideleToLocalUnits_apply {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : Place L) (y : Idele L) :
    (NK.HassePrinciple.ideleToLocalUnits k L w).hom (Additive.ofMul y) =
      Additive.ofMul (y w) := rfl

/-- The `ζ`-unit of `K` mapped to the `ζ`-unit of `L`. -/
lemma zetaUnitK_map (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (ζ : k)
    (hζ : IsPrimitiveRoot ζ p) :
    Units.map (algebraMap K L).toMonoidHom (zetaUnitK p k K ζ hζ) = zetaUnitK p k L ζ hζ := by
  apply Units.ext
  rw [Units.coe_map]
  show algebraMap K L ((zetaUnitK p k K ζ hζ : Kˣ) : K) = algebraMap k L ζ
  rw [zetaUnitK_coe, IsScalarTower.algebraMap_apply k K L]

/-- The image of the `ζ`-unit in the local units at a place. -/
lemma unitsToLocalUnitsHom_zetaUnitK {k L : Type} [Field k] [Field L] [NumberField L]
    [Algebra k L] (ζ : k) (hζ : IsPrimitiveRoot ζ p) (w : Place L) :
    NK.HassePrinciple.unitsToLocalUnitsHom w (zetaUnitK p k L ζ hζ) =
      Units.map ((algebraMap L (Place.localField L w)).toMonoidHom) (zetaUnitK p k L ζ hζ) :=
  rfl

/-! ## The `μ_p`-class at the level `K`: `c₀` -/

/-! ## The localisation morphisms with pinned universes -/

section LocHom

variable (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- The `w`-component map `𝕀_L → L_wˣ` with its universes pinned. -/
abbrev ideleLocHom (w : Place L) :
    Rep.res (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype (idelesK k L) ⟶
      NK.HassePrinciple.localUnitsRep k L w :=
  NK.HassePrinciple.ideleToLocalUnits k L w

/-- The localisation `Lˣ → L_wˣ` with its universes pinned. -/
abbrev unitsLocHom (w : Place L) :
    Rep.res (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype (unitsK k L) ⟶
      NK.HassePrinciple.localUnitsRep k L w :=
  NK.HassePrinciple.unitsToLocalUnits k L w

@[simp] lemma ideleLocHom_apply (w : Place L) (y : Idele L) :
    (ideleLocHom k L w).hom (Additive.ofMul y) = Additive.ofMul (y w) := rfl

@[simp] lemma unitsLocHom_apply (w : Place L) (u : Lˣ) :
    (unitsLocHom k L w).hom (Additive.ofMul u) =
      Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w u) := rfl

end LocHom

section MuClassHom

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (ζ : k) (hζ : IsPrimitiveRoot ζ p)

/-- **The class `c₀` of the `μ_p`-idèle `(ζ^{a v})_v`** of `K`: the morphism of
`Gal(K/k)`-representations `𝔽_p ⟶ C_K` with `1 ↦ [ (ζ^{a v})_v ]`. -/
noncomputable def muClassHom (a : Place K → ZMod p)
    (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w) :
    Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K :=
  zmodToClassesRep p k K (muClass p k K ζ hζ a) (muClass_p p k K ζ hζ a)
    (muClass_smul p k K ζ hζ a ha)

@[simp] lemma muClassHom_apply_one (a : Place K → ZMod p)
    (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w) :
    (muClassHom p k K ζ hζ a ha).hom (1 : ZMod p) = muClass p k K ζ hζ a :=
  zmodToClassesRep_apply_one p k K _ _ _

end MuClassHom


/-- **E4Ω-R2 (the `μ_p`-idèle and the local–global cup formula).** With `μ_p ⊆ k`, for every
`Gal(K/k)`-invariant `a : Place K → ZMod p` there is `c₀ ∈ Hom_G(𝔽_p, C_K)` (the class of the idèle
`(ζ^{a w})_w`) whose pairing with `h ∈ H²(Gal(L/k), 𝔽_p)` at every level `L` is the image in `C_L`
of an idèle-valued class `y` with `w'`-component `a w • loc_{w'}(κ h)` for `w' ∣ w`. -/
theorem zeta_idele_class_pairing (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (a : NK.GlobalCFT.Place K → ZMod p) (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w) :
    ∃ c₀ : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K,
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ unitsK k L)
        (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
        (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
        ∃ y : extH (idelesK k L) 2,
          (∀ (w' : NK.GlobalCFT.Place L) (w : NK.GlobalCFT.Place K),
            NK.GlobalCFT.Place.LiesOver w' w →
            (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') y).comp
                (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w')) (add_zero 2) =
              (a w).val • (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
                  (h.comp (Abelian.Ext.mk₀ z) (add_zero 2))).comp
                (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w')) (add_zero 2)) ∧
          phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c₀) h =
            y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) := by
  classical
  refine ⟨muClassHom p k K ζ hζ a ha, ?_⟩
  intro L _instNF _instFD _instGal z hz h
  -- the canonical idèle-level inclusion `𝕀_K → 𝕀_L` underlying `classIncl k K L`
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k K L
  let eK : Idele K := muIdeles p k K ζ hζ a
  let eL : Idele L := φ eK
  have heK_pow : eK ^ p = 1 := muIdeles_pow p k K ζ hζ a
  have heL_pow : eL ^ p = 1 := by
    rw [show eL = φ eK from rfl, ← map_pow, heK_pow, map_one]
  haveI : FiniteDimensional K L := NK.GlobalCFT.Inclusion.globalCFT_finiteDimensional_of_numberField
  -- `eL` is fixed by `Gal(L/k)`
  have hgal : ∀ σ : L ≃ₐ[k] L, σ • eL = eL := by
    intro σ
    have h1 : σ • φ eK = φ ((AlgEquiv.restrictNormalHom K σ) • eK) :=
      NK.HassePrinciple.ideleInclusion_smul_of_restrict (K := k) (F := K) (L := L) u hu φ hφ σ eK
    rw [show eL = φ eK from rfl, h1]
    congr 1
    exact muIdeles_smul p k K ζ hζ a ha (AlgEquiv.restrictNormalHom K σ)
  have heL_tor : (p : ℤ) • Additive.ofMul eL = 0 := by
    rw [natCast_zsmul, ← ofMul_pow, heL_pow]
    rfl
  have hfix : ∀ σ : L ≃ₐ[k] L, σ • Additive.ofMul eL = Additive.ofMul eL := by
    intro σ
    show Additive.ofMul (σ • eL) = Additive.ofMul eL
    rw [hgal σ]
  -- the `𝔽_p → 𝕀_L` coefficient morphism of the idèle class `[eL]`
  let ψ : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ idelesK k L :=
    zmodToIdelesRep p k L eL heL_tor hfix
  refine ⟨h.comp (Abelian.Ext.mk₀ ψ) (add_zero 2), ?_, ?_⟩
  · -- local components
    intro w' w hw
    have huw : u w' = w := NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu w') hw
    -- the `w'`-component of `eL` is `ζ^{a w}`
    have hcomp : eL w' = (NK.HassePrinciple.unitsToLocalUnitsHom w'
        (zetaUnitK p k L ζ hζ)) ^ (a w).val := by
      have key : eL w' = (NK.HassePrinciple.unitsToLocalUnitsHom w'
          (zetaUnitK p k L ζ hζ)) ^ (a (u w')).val := by
        rw [hφ eK w']
        rw [show eK (u w') = (Units.map
              ((algebraMap K (Place.localField K (u w'))).toMonoidHom) (zetaUnitK p k K ζ hζ))
              ^ (a (u w')).val from muIdeles_apply p k K ζ hζ a (u w')]
        rw [map_pow,
          NK.NUV2.LC.RouteB.localAlgebraMapUnits_algebraMap_units (L := K) (M := L)
            (hu w') (zetaUnitK p k K ζ hζ)]
        rw [zetaUnitK_map p k K L ζ hζ]
        rfl
      have hval : (a w).val = (a (u w')).val := congrArg ZMod.val (by rw [huw])
      rw [hval]
      exact key
    -- the morphism identity (A)
    have hz10 : Additive.toMul (z.hom (1 : ZMod p)) = zetaUnitK p k L ζ hζ :=
      Units.ext (hz.trans (zetaUnitK_coe p k L ζ hζ).symm)
    have hz1' : z.hom (1 : ZMod p) = Additive.ofMul (zetaUnitK p k L ζ hζ) := by
      rw [← hz10]
      exact (ofMul_toMul (z.hom (1 : ZMod p))).symm
    have hψ1 : ψ.hom (1 : ZMod p) = Additive.ofMul eL :=
      zmodToIdelesRep_apply_one p k L eL heL_tor hfix
    have hlocψ : ((ideleLocHom k ↥L w')).hom (Additive.ofMul eL)
        = Additive.ofMul (eL w') := ideleToLocalUnits_apply w' eL
    have hlocz : ((unitsLocHom k ↥L w')).hom
          (Additive.ofMul (zetaUnitK p k L ζ hζ))
        = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w' (zetaUnitK p k L ζ hζ)) :=
      NK.HassePrinciple.unitsToLocalUnits_apply (K := k) (L := ↥L) w' (zetaUnitK p k L ζ hζ)
    have hA : (Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ ≫
        (ideleLocHom k ↥L w')
        = (a w).val • ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z ≫
            (unitsLocHom k ↥L w')) := by
      apply res_trivial_zmod_hom_ext (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype
      have e1 : (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ) ≫
            (ideleLocHom k ↥L w')).hom (1 : ZMod p)
          = ((ideleLocHom k ↥L w')).hom
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ)
                (1 : ZMod p)) := rfl
      have e2 : ((ideleLocHom k ↥L w')).hom
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ)
                (1 : ZMod p))
          = ((ideleLocHom k ↥L w')).hom (ψ.hom (1 : ZMod p)) := rfl
      have e3 : ((ideleLocHom k ↥L w')).hom (ψ.hom (1 : ZMod p))
          = ((ideleLocHom k ↥L w')).hom (Additive.ofMul eL) :=
        congrArg (fun y => ((ideleLocHom k ↥L w')).hom y) hψ1
      have e4 : ((ideleLocHom k ↥L w')).hom (Additive.ofMul eL)
          = Additive.ofMul (eL w') := hlocψ
      have e5 : Additive.ofMul (eL w')
          = Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ)) ^ (a w).val) := congrArg (fun y => Additive.ofMul y) hcomp
      have e6 : Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ)) ^ (a w).val)
          = (a w).val • Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ)) :=
        ofMul_pow (a w).val (NK.HassePrinciple.unitsToLocalUnitsHom w' (zetaUnitK p k L ζ hζ))
      have e7 : (a w).val • Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ))
          = (a w).val • (((unitsLocHom k ↥L w')).hom
              (Additive.ofMul (zetaUnitK p k L ζ hζ))) :=
        congrArg (fun y => (a w).val • y) hlocz.symm
      have e8 : (a w).val • (((unitsLocHom k ↥L w')).hom
              (Additive.ofMul (zetaUnitK p k L ζ hζ)))
          = (a w).val • (((unitsLocHom k ↥L w')).hom (z.hom (1 : ZMod p))) :=
        (congrArg (fun y => (a w).val • ((unitsLocHom k ↥L w')).hom y)
          hz1').symm
      have e9 : (a w).val • (((unitsLocHom k ↥L w')).hom (z.hom (1 : ZMod p)))
          = (a w).val • (((unitsLocHom k ↥L w'))
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z)
                (1 : ZMod p))) := rfl
      have e10 : (a w).val • (((unitsLocHom k ↥L w'))
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) (1 : ZMod p)))
          = (a w).val • ((((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) ≫
              (unitsLocHom k ↥L w')) (1 : ZMod p)) := rfl
      have e11 : (a w).val • ((((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) ≫
              (unitsLocHom k ↥L w')) (1 : ZMod p))
          = ((a w).val • (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) ≫
              (unitsLocHom k ↥L w'))).hom (1 : ZMod p) := by
        rw [Rep.nsmul_hom, IntertwiningMap.nsmul_apply_aux]
      exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans
        (e9.trans (e10.trans e11)))))))))
    -- the `Ext` computation
    have hL' : (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (h.comp (Abelian.Ext.mk₀ ψ) (add_zero 2))).comp
        (Abelian.Ext.mk₀ ((ideleLocHom k ↥L w'))) (add_zero 2)
        = (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ ≫
            (ideleLocHom k ↥L w'))) (add_zero 2) := by
      rw [extHRestrict_comp, Abelian.Ext.comp_assoc_of_third_deg_zero,
        Abelian.Ext.mk₀_comp_mk₀]
    have hR' : (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (h.comp (Abelian.Ext.mk₀ z) (add_zero 2))).comp
        (Abelian.Ext.mk₀ ((unitsLocHom k ↥L w'))) (add_zero 2)
        = (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z ≫
            (unitsLocHom k ↥L w'))) (add_zero 2) := by
      rw [extHRestrict_comp, Abelian.Ext.comp_assoc_of_third_deg_zero,
        Abelian.Ext.mk₀_comp_mk₀]
    rw [hL', hR', Ext.comp_nsmul, ← mk₀_nsmul_aux, ← hA]
  · -- the pairing identity
    have hc0' : (muClassHom p k K ζ hζ a ha).hom (1 : ZMod p) = muClass p k K ζ hζ a :=
      muClassHom_apply_one p k K ζ hζ a ha
    have hcl : (classIncl k K L).hom (muClass p k K ζ hζ a)
        = Additive.ofMul (IdeleClassGroup.mk L (φ (muIdeles p k K ζ hζ a))) := by
      show (classIncl k K L).hom
          (Additive.ofMul (IdeleClassGroup.mk K (muIdeles p k K ζ hζ a))) = _
      exact hι (muIdeles p k K ζ hζ a)
    have hLHS : (trivRes (galRes k K L) (ZMod p) ≫
        (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫ classIncl k K L).hom
          (1 : ZMod p) = Additive.ofMul (IdeleClassGroup.mk L eL) := by
      have e1 : (trivRes (galRes k K L) (ZMod p) ≫
            (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫
            classIncl k K L).hom (1 : ZMod p)
          = (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom
                ((trivRes (galRes k K L) (ZMod p)).hom (1 : ZMod p))) := rfl
      have e2 : (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom ((trivRes (galRes k K L) (ZMod p)).hom (1 : ZMod p)))
          = (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom (1 : ZMod p)) := by
        rw [trivRes_hom_one]
      have e3 : (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom (1 : ZMod p))
          = (classIncl k K L).hom ((muClassHom p k K ζ hζ a ha).hom (1 : ZMod p)) := rfl
      have e4 : (classIncl k K L).hom ((muClassHom p k K ζ hζ a ha).hom (1 : ZMod p))
          = (classIncl k K L).hom (muClass p k K ζ hζ a) :=
        congrArg (fun y => (classIncl k K L).hom y) hc0'
      have e5 : (classIncl k K L).hom (muClass p k K ζ hζ a)
          = Additive.ofMul (IdeleClassGroup.mk L (φ (muIdeles p k K ζ hζ a))) := hcl
      have e6 : Additive.ofMul (IdeleClassGroup.mk L (φ (muIdeles p k K ζ hζ a)))
          = Additive.ofMul (IdeleClassGroup.mk L eL) := rfl
      exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
    have hRHS : (ψ ≫ NK.HassePrinciple.classGroupMap k L).hom (1 : ZMod p)
        = Additive.ofMul (IdeleClassGroup.mk L eL) := by
      have hψ1 : ψ.hom (1 : ZMod p) = Additive.ofMul eL :=
        zmodToIdelesRep_apply_one p k L eL heL_tor hfix
      have e1 : (ψ ≫ NK.HassePrinciple.classGroupMap k L).hom (1 : ZMod p)
          = (NK.HassePrinciple.classGroupMap k L).hom (ψ.hom (1 : ZMod p)) := rfl
      have e2 : (NK.HassePrinciple.classGroupMap k L).hom (ψ.hom (1 : ZMod p))
          = (NK.HassePrinciple.classGroupMap k L).hom (Additive.ofMul eL) :=
        congrArg (fun y => (NK.HassePrinciple.classGroupMap k L).hom y) hψ1
      have e3 : (NK.HassePrinciple.classGroupMap k L).hom (Additive.ofMul eL)
          = Additive.ofMul (IdeleClassGroup.mk L eL) :=
        NK.HassePrinciple.classGroupMap_apply k L eL
      exact e1.trans (e2.trans e3)
    have hB : trivRes (galRes k K L) (ZMod p) ≫
        (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫ classIncl k K L
        = ψ ≫ NK.HassePrinciple.classGroupMap k L :=
      zmod_trivial_hom_ext _ _ (hLHS.trans hRHS.symm)
    have hphi : phiTriv (k := k) (K := K) (L := L) (ZMod p)
        (Abelian.Ext.mk₀ (muClassHom p k K ζ hζ a ha)) h
        = h.comp (Abelian.Ext.mk₀ (trivRes (galRes k K L) (ZMod p) ≫
            (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫
            classIncl k K L)) (add_zero 2) :=
      phiTriv_mk0_eq (k := k) (K := K) (L := L) (ZMod p) (muClassHom p k K ζ hζ a ha) h
    rw [hphi, hB, Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

end

end Work.SSGRoute
