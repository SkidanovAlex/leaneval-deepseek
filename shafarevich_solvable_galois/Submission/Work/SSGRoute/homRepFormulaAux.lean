import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.homCoindDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for `Work.SSGRoute.homRep_unitsK_formula`

The two sides of the identification

`Hom_Rep(M, Kˣ) ≅ (Hom_ℤ(M.V, Ωˣ))^Γ`   (`Γ = Gal(Ω/k)`)

used in `Work.SSGRoute.homRep_unitsK_formula`:

* the *forward* map sends `f` to the `Γ`-invariant map `x ↦ algebraMap (f x)`;
* the *inverse* map sends a `Γ`-invariant `φ` to `x ↦ u x`, where `u x ∈ Kˣ` is the unit with
  `algebraMap (u x) = φ x`; the existence of `u x` is the fixed-field statement
  `InfiniteGalois.fixedField_fixingSubgroup`: an element of `Ω` fixed by `Gal(Ω/K)` lies in `K`.

Implementation notes.  `Coeff = ULift ℤ`, the `Additive` type tag is a *transparent* synonym and
`(unitsK k K).V` is definitionally `↥Kˣ`.  Consequently every use of `Additive.toMul` on an
element of `(unitsK k K).V` is written with the explicit `(α := (↥K)ˣ)` ascription (and likewise
`(α := Ωˣ)` on the `Ω` side), and the bookkeeping lemmas are stated in exactly those shapes, so
that rewriting is stable.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt

noncomputable section

attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-! ## Bookkeeping -/

/-- The algebra map on units, `Kˣ → Ωˣ`.  (An `abbrev`, so definitionally the expression appearing
in the statement of the main theorem.) -/
abbrev unitsMapK : (↥K)ˣ →* Ωˣ :=
  Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom

/-- The Galois action on `Ωˣ`, for `σ : Gal(Ω/k)`. -/
abbrev unitsMapΩ (σ : Ω ≃ₐ[k] Ω) : Ωˣ →* Ωˣ :=
  Units.map σ.toAlgHom.toRingHom.toMonoidWithZeroHom

/-- The Galois action on `Kˣ`, for `γ : Gal(K/k)`. -/
abbrev unitsMapOf (γ : K ≃ₐ[k] K) : (↥K)ˣ →* (↥K)ˣ :=
  Units.map γ.toAlgHom.toRingHom.toMonoidWithZeroHom

@[simp] theorem unitsMapK_apply_coe (u : (↥K)ˣ) :
    ((unitsMapK u : Ωˣ) : Ω) = algebraMap ↥K Ω (u : ↥K) := rfl

@[simp] theorem unitsMapΩ_apply_coe (σ : Ω ≃ₐ[k] Ω) (a : Ωˣ) :
    ((unitsMapΩ σ a : Ωˣ) : Ω) = σ (a : Ω) := rfl

@[simp] theorem unitsMapOf_apply_coe (γ : K ≃ₐ[k] K) (u : (↥K)ˣ) :
    ((unitsMapOf γ u : (↥K)ˣ) : ↥K) = γ (u : ↥K) := rfl

/-- The `Γ`-action on `Ωˣ`, in terms of the named map `homCoind.smulHom`. -/
theorem toMul_smulHom (σ : Ω ≃ₐ[k] Ω) (a : Additive Ωˣ) :
    Additive.toMul (α := Ωˣ) (homCoind.smulHom (k := k) (Ω := Ω) σ a)
      = unitsMapΩ σ (Additive.toMul (α := Ωˣ) a) := rfl

/-- The action of `σ` on `homCoind`, in terms of `homCoind.smulHom`. -/
theorem smul_homCoind_apply (M : Rep Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (Φ : homCoind k Ω K M) (x : M.V) :
    (σ • Φ) x = homCoind.smulHom (k := k) (Ω := Ω) σ (Φ (M.ρ (SSGRoute.res k K σ)⁻¹ x)) := rfl

/-- The `Coeff`-scalar action of a representation is the canonical `ℤ`-action. -/
theorem inst_smul_ulift_eq_int {X : Type*} [AddCommGroup X] (instM : Module (ULift ℤ) X)
    (n : ℤ) (x : X) : instM.smul (ULift.up n) x = n • x := by
  let f : ℤ →+* ULift ℤ :=
    { toFun := fun m => ULift.up m
      map_one' := rfl
      map_mul' := fun a b => rfl
      map_zero' := rfl
      map_add' := fun a b => rfl }
  exact int_smul_eq_zsmul (@Module.compHom (ULift ℤ) ℤ X _ _ instM _ f) n x

theorem rep_coeff_smul_eq (G : Type) [Group G] (M : Rep Coeff G) (c : Coeff) (x : M.V) :
    M.hV2.smul c x = c.down • x := by
  rw [show c = ULift.up c.down from rfl]
  exact inst_smul_ulift_eq_int (X := M.V) M.hV2 c.down x

/-- The unit of `Kˣ` underlying an element of `(unitsK k K).V`, in the `Additive`-free form. -/
theorem toMul_zero_K : Additive.toMul (α := (↥K)ˣ) (0 : (unitsK k K).V) = 1 :=
  toMul_zero (α := (↥K)ˣ)

theorem toMul_add_K (a b : (unitsK k K).V) :
    Additive.toMul (α := (↥K)ˣ) (a + b)
      = Additive.toMul (α := (↥K)ˣ) a * Additive.toMul (α := (↥K)ˣ) b :=
  toMul_add (α := (↥K)ˣ) a b

theorem toMul_ofMul_K (u : (↥K)ˣ) :
    Additive.toMul (α := (↥K)ˣ) (Additive.ofMul u) = u :=
  toMul_ofMul u

theorem rho_unitsK_ofMul (γ : K ≃ₐ[k] K) (u : (↥K)ˣ) :
    (unitsK k K).ρ γ (Additive.ofMul u) = Additive.ofMul (unitsMapOf γ u) := rfl

/-- The `Γ`-action on `Additive Ωˣ`, in terms of the named map `homCoind.smulHom`. -/
theorem smulHom_ofMul (σ : Ω ≃ₐ[k] Ω) (v : Ωˣ) :
    homCoind.smulHom (k := k) (Ω := Ω) σ (Additive.ofMul v)
      = Additive.ofMul (unitsMapΩ σ v) := rfl

theorem toMul_rho_unitsK (γ : K ≃ₐ[k] K) (a : (unitsK k K).V) :
    Additive.toMul (α := (↥K)ˣ) ((unitsK k K).ρ γ a)
      = unitsMapOf γ (Additive.toMul (α := (↥K)ˣ) a) := by
  rw [show (unitsK k K).ρ γ a
      = Additive.ofMul (unitsMapOf γ (Additive.toMul (α := (↥K)ˣ) a)) from
    rho_unitsK_ofMul γ (Additive.toMul (α := (↥K)ˣ) a)]
  exact toMul_ofMul (unitsMapOf γ (Additive.toMul (α := (↥K)ˣ) a))

theorem unitsMapK_injective : Function.Injective (unitsMapK (k := k) (Ω := Ω) (K := K)) := by
  intro u v h
  apply Units.ext
  have h' : algebraMap ↥K Ω (u : ↥K) = algebraMap ↥K Ω (v : ↥K) := by
    simpa using congrArg (fun w : Ωˣ => (w : Ω)) h
  exact RingHom.injective (algebraMap ↥K Ω) h'

theorem unitsMapOf_mul (γ δ : K ≃ₐ[k] K) (u : (↥K)ˣ) :
    unitsMapOf γ (unitsMapOf δ u) = unitsMapOf (γ * δ) u := by
  ext
  rw [unitsMapOf_apply_coe, unitsMapOf_apply_coe, unitsMapOf_apply_coe, AlgEquiv.mul_apply]

theorem unitsMapOf_one (u : (↥K)ˣ) : unitsMapOf (1 : K ≃ₐ[k] K) u = u := by
  ext
  rw [unitsMapOf_apply_coe, AlgEquiv.one_apply]

theorem unitsMapOf_res_inv (σ : Ω ≃ₐ[k] Ω) (u : (↥K)ˣ) :
    unitsMapOf (SSGRoute.res k K σ) (unitsMapOf (SSGRoute.res k K σ⁻¹) u) = u := by
  rw [unitsMapOf_mul, ← map_mul, mul_inv_cancel, map_one, unitsMapOf_one]

theorem unitsMapΩ_unitsMapK (σ : Ω ≃ₐ[k] Ω) (v : (↥K)ˣ) :
    unitsMapΩ σ (unitsMapK v) = unitsMapK (unitsMapOf (SSGRoute.res k K σ) v) := by
  ext
  rw [unitsMapΩ_apply_coe, unitsMapK_apply_coe, unitsMapK_apply_coe, unitsMapOf_apply_coe]
  exact (AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ (v : ↥K)).symm

/-! ## The forward map -/

/-- **The value map** `f ↦ (x ↦ algebraMap (f x))` from `Hom_Rep(M, Kˣ)` to `Hom_ℤ(M.V, Ωˣ)`. -/
def toCoindFun (M : Rep Coeff (K ≃ₐ[k] K)) (f : M ⟶ unitsK k K) : homCoind k Ω K M where
  toFun x := Additive.ofMul (unitsMapK (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x)))
  map_zero' := by
    rw [map_zero, toMul_zero_K, map_one, ofMul_one]
  map_add' := by
    intro x y
    rw [map_add, toMul_add_K, map_mul, ofMul_mul]

@[simp] theorem toCoindFun_apply (M : Rep Coeff (K ≃ₐ[k] K)) (f : M ⟶ unitsK k K) (x : M.V) :
    toCoindFun M f x
      = Additive.ofMul (unitsMapK (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x))) := rfl

theorem toCoindFun_zero (M : Rep Coeff (K ≃ₐ[k] K)) : toCoindFun M 0 = 0 := by
  apply AddMonoidHom.ext
  intro x
  have h0 : Rep.Hom.hom (0 : M ⟶ unitsK k K) x = (0 : (unitsK k K).V) := by
    rw [Rep.zero_hom]
    exact Pi.zero_apply x
  rw [toCoindFun_apply, h0, toMul_zero_K, map_one, ofMul_one]
  rw [show (0 : homCoind k Ω K M) x = (0 : Additive Ωˣ) from rfl]

theorem toCoindFun_add (M : Rep Coeff (K ≃ₐ[k] K)) (f g : M ⟶ unitsK k K) :
    toCoindFun M (f + g) = toCoindFun M f + toCoindFun M g := by
  apply AddMonoidHom.ext
  intro x
  rw [toCoindFun_apply, Rep.add_hom]
  rw [show ((Rep.Hom.hom f + Rep.Hom.hom g) : M.ρ.IntertwiningMap (unitsK k K).ρ) x
      = Rep.Hom.hom f x + Rep.Hom.hom g x from rfl]
  rw [toMul_add_K, map_mul, ofMul_mul]
  rw [show (toCoindFun M f + toCoindFun M g) x = toCoindFun M f x + toCoindFun M g x from rfl]
  rw [toCoindFun_apply, toCoindFun_apply]

/-- The value map as an additive homomorphism. -/
def toCoindHom (M : Rep Coeff (K ≃ₐ[k] K)) :
    (M ⟶ unitsK k K) →+ homCoind k Ω K M :=
  { toFun := toCoindFun M
    map_zero' := toCoindFun_zero M
    map_add' := toCoindFun_add M }

@[simp] theorem toCoindHom_apply (M : Rep Coeff (K ≃ₐ[k] K)) (f : M ⟶ unitsK k K) :
    toCoindHom M f = toCoindFun M f := rfl

/-- The forward map takes values in the `Γ`-invariants. -/
theorem toCoindFun_mem_H0 (M : Rep Coeff (K ≃ₐ[k] K)) (f : M ⟶ unitsK k K) :
    toCoindFun M f ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M) := by
  intro σ
  apply AddMonoidHom.ext
  intro x
  rw [show (σ • toCoindFun M f) x
      = homCoind.smulHom (k := k) (Ω := Ω) σ (toCoindFun M f (M.ρ (SSGRoute.res k K σ)⁻¹ x))
      from rfl]
  rw [show (SSGRoute.res k K σ)⁻¹ = SSGRoute.res k K σ⁻¹ from by simp]
  rw [toCoindFun_apply, toCoindFun_apply]
  rw [show Rep.Hom.hom f (M.ρ (SSGRoute.res k K σ⁻¹) x)
      = (unitsK k K).ρ (SSGRoute.res k K σ⁻¹) (Rep.Hom.hom f x) from
    Rep.hom_comm_apply f _ x]
  rw [toMul_rho_unitsK]
  rw [show homCoind.smulHom (k := k) (Ω := Ω) σ
        (Additive.ofMul (unitsMapK (unitsMapOf (SSGRoute.res k K σ⁻¹)
          (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x)))))
      = Additive.ofMul (unitsMapΩ σ (unitsMapK (unitsMapOf (SSGRoute.res k K σ⁻¹)
          (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x))))) from smulHom_ofMul σ _]
  rw [show unitsMapΩ σ (unitsMapK (unitsMapOf (SSGRoute.res k K σ⁻¹)
        (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x))))
      = unitsMapK (unitsMapOf (SSGRoute.res k K σ) (unitsMapOf (SSGRoute.res k K σ⁻¹)
          (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x)))) from unitsMapΩ_unitsMapK σ _]
  rw [unitsMapOf_res_inv]

/-- **The forward map** `Hom_Rep(M, Kˣ) → (Hom_ℤ(M.V, Ωˣ))^Γ`, as an additive map into the
subgroup of invariants. -/
def toCoindH0 (M : Rep Coeff (K ≃ₐ[k] K)) :
    (M ⟶ unitsK k K) →+ ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M)) :=
  (toCoindHom M).codRestrict _ (toCoindFun_mem_H0 M)

@[simp] theorem toCoindH0_apply_coe (M : Rep Coeff (K ≃ₐ[k] K)) (f : M ⟶ unitsK k K) :
    ((toCoindH0 M f : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M)))
      : homCoind k Ω K M) = toCoindFun M f := rfl

/-- The formula of the forward map, pointwise (in the shape required by the main theorem). -/
theorem toCoindH0_apply (M : Rep Coeff (K ≃ₐ[k] K)) (f : M ⟶ unitsK k K) (x : M.V) :
    ((toCoindH0 M f : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M)))
      : homCoind k Ω K M) x =
      Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
        (Additive.toMul (Rep.Hom.hom f x))) :=
  toCoindFun_apply M f x

/-! ## Injectivity of the forward map -/

theorem toCoindH0_injective (M : Rep Coeff (K ≃ₐ[k] K)) :
    Function.Injective (toCoindH0 M) := by
  intro f g h
  have h1 : toCoindFun M f = toCoindFun M g := by
    simpa using congrArg (fun z : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))
      => (z : homCoind k Ω K M)) h
  apply Rep.hom_ext
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_)
  have h2 : toCoindFun M f x = toCoindFun M g x := congrArg (fun ψ : homCoind k Ω K M => ψ x) h1
  rw [toCoindFun_apply, toCoindFun_apply] at h2
  have h3 : unitsMapK (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom f x))
      = unitsMapK (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom g x)) :=
    Additive.ofMul.injective h2
  exact Additive.toMul.injective (unitsMapK_injective h3)

/-! ## The inverse map -/

/-- **The fixed-field input.** A `Γ`-invariant element of `Hom_ℤ(M.V, Ωˣ)` has values in `Kˣ`. -/
theorem exists_unitsMap_toMul_of_mem_H0 (M : Rep Coeff (K ≃ₐ[k] K))
    {φ : homCoind k Ω K M}
    (hφ : φ ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M)) (x : M.V) :
    ∃ u : (↥K)ˣ, unitsMapK u = Additive.toMul (α := Ωˣ) (φ x) := by
  have hmem : (((Additive.toMul (α := Ωˣ) (φ x) : Ωˣ)) : Ω)
      ∈ IntermediateField.fixedField K.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσ1 : SSGRoute.res k K σ = 1 := by
      have hker : σ ∈ (SSGRoute.res k K).ker := by
        rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
          IntermediateField.restrictNormalHom_ker K]
        exact hσ
      exact hker
    have hρ : M.ρ (SSGRoute.res k K σ)⁻¹ (M.ρ (SSGRoute.res k K σ) x) = x := by
      have h3 : M.ρ (SSGRoute.res k K σ)⁻¹ * M.ρ (SSGRoute.res k K σ) = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      have h4 : (M.ρ (SSGRoute.res k K σ)⁻¹ * M.ρ (SSGRoute.res k K σ)) x = x := by
        rw [h3]
        rfl
      simpa only [Module.End.mul_apply] using h4
    have hρ2 : M.ρ (SSGRoute.res k K σ) x = x := by
      rw [hσ1, map_one]
      rfl
    have h : (σ • φ) (M.ρ (SSGRoute.res k K σ) x) = φ (M.ρ (SSGRoute.res k K σ) x) := by
      rw [hφ σ]
    rw [smul_homCoind_apply, hρ, hρ2] at h
    have h2 : Additive.toMul (α := Ωˣ) (homCoind.smulHom (k := k) (Ω := Ω) σ (φ x))
        = Additive.toMul (α := Ωˣ) (φ x) := congrArg (Additive.toMul (α := Ωˣ)) h
    have h3 : unitsMapΩ σ (Additive.toMul (α := Ωˣ) (φ x))
        = Additive.toMul (α := Ωˣ) (φ x) :=
      (toMul_smulHom σ (φ x)).symm.trans h2
    show σ (((Additive.toMul (α := Ωˣ) (φ x) : Ωˣ)) : Ω)
        = (((Additive.toMul (α := Ωˣ) (φ x) : Ωˣ)) : Ω)
    exact congrArg (fun w : Ωˣ => (w : Ω)) h3
  have hfix : (((Additive.toMul (α := Ωˣ) (φ x) : Ωˣ)) : Ω) ∈ K :=
    (le_of_eq (InfiniteGalois.fixedField_fixingSubgroup K) : _ ≤ K) hmem
  let a : ↥K := ⟨((Additive.toMul (α := Ωˣ) (φ x) : Ωˣ) : Ω), hfix⟩
  have ha : a ≠ 0 := by
    intro h0
    apply Units.ne_zero (Additive.toMul (α := Ωˣ) (φ x))
    exact congrArg (fun z : ↥K => (z : Ω)) h0
  refine ⟨Units.mk0 a ha, ?_⟩
  refine Units.ext ?_
  show algebraMap ↥K Ω ((Units.mk0 a ha : (↥K)ˣ) : ↥K)
      = (((Additive.toMul (α := Ωˣ) (φ x) : Ωˣ)) : Ω)
  rw [Units.val_mk0]
  rfl

/-- The unit of `Kˣ` attached to an invariant `φ` and `x : M.V`. -/
def unitsOfCoind (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) (x : M.V) : (↥K)ˣ :=
  Classical.choose (exists_unitsMap_toMul_of_mem_H0 M φ.2 x)

/-- Characterising property of `unitsOfCoind`. -/
theorem unitsMap_unitsOfCoind (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) (x : M.V) :
    unitsMapK (unitsOfCoind M φ x) = Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) x) :=
  Classical.choose_spec (exists_unitsMap_toMul_of_mem_H0 M φ.2 x)

theorem ofMul_unitsOfCoind_zero (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) :
    Additive.ofMul (unitsOfCoind M φ 0) = 0 := by
  have h : unitsOfCoind M φ 0 = 1 := by
    apply unitsMapK_injective
    rw [unitsMap_unitsOfCoind, map_zero, toMul_zero (α := Ωˣ), map_one]
  rw [h, ofMul_one]

theorem ofMul_unitsOfCoind_add (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) (x y : M.V) :
    Additive.ofMul (unitsOfCoind M φ (x + y)) =
      Additive.ofMul (unitsOfCoind M φ x) + Additive.ofMul (unitsOfCoind M φ y) := by
  have h : unitsOfCoind M φ (x + y) = unitsOfCoind M φ x * unitsOfCoind M φ y := by
    apply unitsMapK_injective
    rw [unitsMap_unitsOfCoind, map_add]
    rw [show Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) x + (φ : homCoind k Ω K M) y)
        = Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) x)
          * Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) y) from
      toMul_add (α := Ωˣ) _ _]
    rw [map_mul, unitsMap_unitsOfCoind, unitsMap_unitsOfCoind]
  rw [h, ofMul_mul]

theorem ofMul_unitsOfCoind_smul (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) (n : ℤ) (x : M.V) :
    Additive.ofMul (unitsOfCoind M φ (n • x)) =
      n • Additive.ofMul (unitsOfCoind M φ x) := by
  have h : unitsOfCoind M φ (n • x) = (unitsOfCoind M φ x) ^ n := by
    apply unitsMapK_injective
    rw [unitsMap_unitsOfCoind]
    rw [show Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) (n • x))
        = Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) x) ^ n from
      (congrArg (Additive.toMul (α := Ωˣ))
        (AddMonoidHom.map_zsmul (φ : homCoind k Ω K M) n x)).trans
        (toMul_zsmul (α := Ωˣ) n ((φ : homCoind k Ω K M) x))]
    rw [map_zpow, unitsMap_unitsOfCoind]
  rw [h, ofMul_zpow]

theorem ofMul_unitsOfCoind_intertwining (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) (γ : K ≃ₐ[k] K)
    (x : M.V) :
    Additive.ofMul (unitsOfCoind M φ (M.ρ γ x)) =
      (unitsK k K).ρ γ (Additive.ofMul (unitsOfCoind M φ x)) := by
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥K) Ω γ
  have h := DFunLike.congr_fun (φ.2 σ) (M.ρ γ x)
  have hρ : M.ρ (SSGRoute.res k K σ)⁻¹ (M.ρ γ x) = x := by
    have h3 : M.ρ (SSGRoute.res k K σ)⁻¹ * M.ρ γ
        = M.ρ ((SSGRoute.res k K σ)⁻¹ * γ) := by
      rw [← map_mul]
    have h4 : (M.ρ (SSGRoute.res k K σ)⁻¹ * M.ρ γ) x = x := by
      rw [h3, hσ, inv_mul_cancel, map_one]
      rfl
    simpa only [Module.End.mul_apply] using h4
  rw [smul_homCoind_apply, hρ] at h
  have h2 : Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) (M.ρ γ x))
      = unitsMapΩ σ (Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) x)) :=
    (congrArg (Additive.toMul (α := Ωˣ)) h).symm.trans
      (toMul_smulHom σ ((φ : homCoind k Ω K M) x))
  have h5 : unitsOfCoind M φ (M.ρ γ x) = unitsMapOf γ (unitsOfCoind M φ x) := by
    apply unitsMapK_injective
    rw [unitsMap_unitsOfCoind, h2, ← unitsMap_unitsOfCoind M φ x]
    rw [show unitsMapΩ σ (unitsMapK (unitsOfCoind M φ x))
        = unitsMapK (unitsMapOf (SSGRoute.res k K σ) (unitsOfCoind M φ x)) from
      unitsMapΩ_unitsMapK σ _]
    rw [hσ]
  rw [h5, rho_unitsK_ofMul]

/-- **The inverse map** `(Hom_ℤ(M.V, Ωˣ))^Γ → Hom_Rep(M, Kˣ)`.  The underlying `Coeff`-linear map
is built directly inside the intertwining map (with the scalar structures of the representations
`M` and `unitsK k K` pinned by `letI`). -/
def ofCoindHom (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) : M ⟶ unitsK k K :=
  letI instS : Module Coeff M.V := M.hV2
  letI instT : Module Coeff (unitsK k K).V := (unitsK k K).hV2
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (unitsOfCoind M φ x)
          map_add' := fun x y => ofMul_unitsOfCoind_add M φ x y
          map_smul' := fun c x => by
            show Additive.ofMul (unitsOfCoind M φ (instS.smul c x)) =
              (RingHom.id Coeff) c • Additive.ofMul (unitsOfCoind M φ x)
            rw [show instS.smul c x = c.down • x from by
              rw [show (c : Coeff) = ULift.up c.down from rfl]
              exact inst_smul_ulift_eq_int (X := M.V) instS c.down x]
            exact ofMul_unitsOfCoind_smul M φ c.down x }
      isIntertwining' := fun γ => by
        apply LinearMap.ext
        intro x
        exact ofMul_unitsOfCoind_intertwining M φ γ x }

theorem toCoindFun_ofCoindHom (M : Rep Coeff (K ≃ₐ[k] K))
    (φ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K M))) :
    toCoindFun M (ofCoindHom M φ) = φ := by
  apply AddMonoidHom.ext
  intro x
  rw [toCoindFun_apply]
  have h3 : Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom (ofCoindHom M φ) x)
      = unitsOfCoind M φ x := by
    rw [show Rep.Hom.hom (ofCoindHom M φ) x = Additive.ofMul (unitsOfCoind M φ x) from rfl]
    exact toMul_ofMul (unitsOfCoind M φ x)
  rw [h3, unitsMap_unitsOfCoind]
  rw [show Additive.ofMul (Additive.toMul (α := Ωˣ) ((φ : homCoind k Ω K M) x))
      = (φ : homCoind k Ω K M) x from ofMul_toMul _]

/-! ## Assembly -/

theorem toCoindH0_bijective (M : Rep Coeff (K ≃ₐ[k] K)) :
    Function.Bijective (toCoindH0 M) := by
  refine ⟨toCoindH0_injective M, fun φ => ⟨ofCoindHom M φ, ?_⟩⟩
  exact Subtype.ext (toCoindFun_ofCoindHom M φ)

end

end Work.SSGRoute
