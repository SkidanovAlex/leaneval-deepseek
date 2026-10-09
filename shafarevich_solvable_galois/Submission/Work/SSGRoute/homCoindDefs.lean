import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Gal(Ω/k)`-module `Hom_ℤ(M, Ωˣ)` used in `E1c`

For `K/k` a finite extension inside an algebraic closure `Ω`, `G = K ≃ₐ[k] K` and a `Rep Coeff G`
`M`, this file defines

* `homCoind k Ω K M := M.V →+ Additive Ωˣ`, the additive maps from `M` to `Ωˣ` (equivalently the
  `Coeff = ULift ℤ`-linear ones),

with the *conjugation* action `(σ · φ) x = σ · (φ (σ⁻¹ · x))` of `Γ = Ω ≃ₐ[k] Ω` (the action on
`M.V` being through `res k K : Γ → G`).

The vanishing `H¹(Γ, homCoind k Ω K M) = 0` for `M = Rep.free Coeff G ι` (Shapiro + Hilbert 90 over
`K`) and the identification `Hom_Rep(M, Kˣ) ≅ (homCoind k Ω K M)^Γ` are the two algebraic inputs of
the bridge `H¹(k,E) ≅ Ext¹_G(E', Kˣ)`.
-/

universe u

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

attribute [local instance 10000] Rep.hV1 Rep.hV2

variable (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]

/-- The additive group `Hom_ℤ(M.V, Ωˣ)`; the conjugation action of `Γ = Ω ≃ₐ[k] Ω` is in the
`homCoind` namespace below. -/
abbrev homCoind (M : Rep.{0} Coeff (K ≃ₐ[k] K)) : Type := M.V →+ Additive Ωˣ

namespace homCoind

variable {k Ω K}

/-- The action of `σ` on `Ωˣ` as an additive homomorphism. -/
def smulHom (σ : Ω ≃ₐ[k] Ω) : Additive Ωˣ →+ Additive Ωˣ where
  toFun a := σ • a
  map_zero' := smul_zero σ
  map_add' a b := smul_add σ a b

@[simp] theorem smulHom_apply (σ : Ω ≃ₐ[k] Ω) (a : Additive Ωˣ) :
    smulHom (k := k) (Ω := Ω) σ a = σ • a := rfl

theorem smulHom_one : smulHom (k := k) (Ω := Ω) (1 : Ω ≃ₐ[k] Ω) = AddMonoidHom.id _ := by
  ext a; simp

instance (M : Rep.{0} Coeff (K ≃ₐ[k] K)) : AddCommGroup (homCoind k Ω K M) :=
  inferInstanceAs (AddCommGroup (M.V →+ Additive Ωˣ))

instance (M : Rep.{0} Coeff (K ≃ₐ[k] K)) : SMul (Ω ≃ₐ[k] Ω) (homCoind k Ω K M) where
  smul σ φ := (smulHom (k := k) (Ω := Ω) σ).comp
    (φ.comp ((M.ρ (SSGRoute.res k K σ)⁻¹).toAddMonoidHom))

@[simp] theorem smul_apply {M : Rep.{0} Coeff (K ≃ₐ[k] K)} (σ : Ω ≃ₐ[k] Ω)
    (φ : homCoind k Ω K M) (x : M.V) :
    (σ • φ) x = σ • φ (M.ρ (SSGRoute.res k K σ)⁻¹ x) := rfl

theorem smul_smul {M : Rep.{0} Coeff (K ≃ₐ[k] K)} (σ τ : Ω ≃ₐ[k] Ω) (φ : homCoind k Ω K M) :
    σ • (τ • φ) = (σ * τ) • φ := by
  ext x
  simp only [smul_apply, mul_inv_rev, map_mul, Module.End.mul_apply, mul_smul]

instance (M : Rep.{0} Coeff (K ≃ₐ[k] K)) : DistribMulAction (Ω ≃ₐ[k] Ω) (homCoind k Ω K M) where
  one_smul φ := by
    show (smulHom (k := k) (Ω := Ω) (1 : Ω ≃ₐ[k] Ω)).comp
      (φ.comp ((M.ρ (SSGRoute.res k K 1)⁻¹).toAddMonoidHom)) = φ
    rw [smulHom_one, map_one, inv_one, map_one]
    exact AddMonoidHom.id_comp _
  mul_smul σ τ φ := (smul_smul σ τ φ).symm
  smul_zero σ := by
    show (smulHom (k := k) (Ω := Ω) σ).comp
      ((0 : homCoind k Ω K M).comp ((M.ρ (SSGRoute.res k K σ)⁻¹).toAddMonoidHom)) = 0
    rw [AddMonoidHom.zero_comp, AddMonoidHom.comp_zero]
  smul_add σ φ ψ := by
    show (smulHom (k := k) (Ω := Ω) σ).comp
      ((φ + ψ).comp ((M.ρ (SSGRoute.res k K σ)⁻¹).toAddMonoidHom)) =
        (smulHom (k := k) (Ω := Ω) σ).comp (φ.comp _) +
          (smulHom (k := k) (Ω := Ω) σ).comp (ψ.comp _)
    rw [AddMonoidHom.add_comp, AddMonoidHom.comp_add]

end homCoind

section UnitsOmega

variable (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

/-- The Galois action on `Ωˣ`. -/
def algEquivUnitsMapΩ (σ : Ω ≃ₐ[k] Ω) : Ωˣ →* Ωˣ :=
  Units.map σ.toAlgHom.toRingHom.toMonoidWithZeroHom

@[simp] theorem algEquivUnitsMapΩ_coe (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ) :
    ((algEquivUnitsMapΩ k Ω σ u : Ωˣ) : Ω) = σ (u : Ω) := rfl

@[simp] theorem algEquivUnitsMapΩ_one (u : Ωˣ) : algEquivUnitsMapΩ k Ω 1 u = u := by
  ext; simp [algEquivUnitsMapΩ]

@[simp] theorem algEquivUnitsMapΩ_mul (σ τ : Ω ≃ₐ[k] Ω) (u : Ωˣ) :
    algEquivUnitsMapΩ k Ω (σ * τ) u
      = algEquivUnitsMapΩ k Ω σ (algEquivUnitsMapΩ k Ω τ u) := by
  ext; simp [algEquivUnitsMapΩ]

instance instDistribMulActionAddUnitsΩ : DistribMulAction (Ω ≃ₐ[k] Ω) (Additive Ωˣ) where
  smul σ a := Additive.ofMul (algEquivUnitsMapΩ k Ω σ (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (algEquivUnitsMapΩ k Ω 1 (Additive.toMul a)) = a
    rw [algEquivUnitsMapΩ_one]; rfl
  mul_smul σ τ a := by
    show Additive.ofMul (algEquivUnitsMapΩ k Ω (σ * τ) (Additive.toMul a)) =
      Additive.ofMul (algEquivUnitsMapΩ k Ω σ (algEquivUnitsMapΩ k Ω τ (Additive.toMul a)))
    rw [algEquivUnitsMapΩ_mul]
  smul_zero σ := by
    show Additive.ofMul (algEquivUnitsMapΩ k Ω σ 1) = 0
    rw [map_one]; rfl
  smul_add σ a b := by
    show Additive.ofMul (algEquivUnitsMapΩ k Ω σ (Additive.toMul a * Additive.toMul b)) =
      Additive.ofMul (algEquivUnitsMapΩ k Ω σ (Additive.toMul a)) +
        Additive.ofMul (algEquivUnitsMapΩ k Ω σ (Additive.toMul b))
    rw [map_mul]; rfl

@[simp] theorem addUnits_smul_toMulΩ (σ : Ω ≃ₐ[k] Ω) (a : Additive Ωˣ) :
    Additive.toMul (σ • a) = algEquivUnitsMapΩ k Ω σ (Additive.toMul a) := rfl

theorem stabilizer_addUnits_ofMulΩ (u : Ωˣ) :
    (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (Additive.ofMul u) : Set (Ω ≃ₐ[k] Ω)) =
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (u : Ω) : Set (Ω ≃ₐ[k] Ω)) := by
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h0 : Additive.ofMul (algEquivUnitsMapΩ k Ω σ u) = Additive.ofMul u := h
    have h2 : algEquivUnitsMapΩ k Ω σ u = u := Additive.ofMul.injective h0
    have h3 := congrArg (fun w : Ωˣ => (w : Ω)) h2
    rwa [algEquivUnitsMapΩ_coe] at h3
  · intro h
    show Additive.ofMul (algEquivUnitsMapΩ k Ω σ u) = Additive.ofMul u
    rw [show algEquivUnitsMapΩ k Ω σ u = u from Units.ext (by rw [algEquivUnitsMapΩ_coe]; exact h)]

theorem isDiscreteModule_addUnitsΩ [IsAlgClosure k Ω] :
    Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (Additive Ωˣ) := by
  intro a
  show IsOpen (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (Additive.ofMul (Additive.toMul a)) :
    Set (Ω ≃ₐ[k] Ω))
  rw [stabilizer_addUnits_ofMulΩ k Ω (Additive.toMul a)]
  exact stabilizer_isOpen_of_isIntegral _

end UnitsOmega

/-! ## The coinduced module `Maps(Gal(K/k), Ωˣ)` -/

/-- The coinduced module: functions `Gal(K/k) → Ωˣ` with the `Gal(Ω/k)`-action
`(σ • φ) x = σ (φ ((σ|_K)⁻¹ * x))`.  It is isomorphic to the induced module
`ℤ[Gal(Ω/k)] ⊗_{ℤ[Gal(Ω/K)]} Ωˣ`. -/
def CoindU (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) : Type := (K ≃ₐ[k] K) → Additive Ωˣ

namespace CoindU

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
  [Normal k K] [FiniteDimensional k K]

instance instAddCommGroup : AddCommGroup (CoindU k Ω K) :=
  inferInstanceAs (AddCommGroup ((K ≃ₐ[k] K) → Additive Ωˣ))

noncomputable instance instDistribMulAction : DistribMulAction (Ω ≃ₐ[k] Ω) (CoindU k Ω K) where
  smul σ φ := fun x => σ • φ ((SSGRoute.res k K σ)⁻¹ * x)
  one_smul φ := by
    funext x
    change (1 : Ω ≃ₐ[k] Ω) • φ ((SSGRoute.res k K 1)⁻¹ * x) = φ x
    simp
  mul_smul σ τ φ := by
    funext x
    change (σ * τ) • φ ((SSGRoute.res k K (σ * τ))⁻¹ * x) =
      σ • (τ • φ ((SSGRoute.res k K τ)⁻¹ * ((SSGRoute.res k K σ)⁻¹ * x)))
    rw [map_mul]
    rw [show (((SSGRoute.res k K) σ * (SSGRoute.res k K) τ)⁻¹ * x) =
      ((SSGRoute.res k K) τ)⁻¹ * (((SSGRoute.res k K) σ)⁻¹ * x) by group]
    rw [mul_smul]
  smul_zero σ := by
    funext x
    change σ • (0 : Additive Ωˣ) = 0
    simp
  smul_add σ φ ψ := by
    funext x
    change σ • (φ ((SSGRoute.res k K σ)⁻¹ * x) + ψ ((SSGRoute.res k K σ)⁻¹ * x)) =
      σ • φ ((SSGRoute.res k K σ)⁻¹ * x) + σ • ψ ((SSGRoute.res k K σ)⁻¹ * x)
    rw [smul_add]

/-- The `Gal(Ω/k)`-equivariant "sum over `Gal(K/k)`" map `Maps(Gal(K/k), Ωˣ) → Ωˣ`. -/
noncomputable def normMap (φ : CoindU k Ω K) : Additive Ωˣ :=
  ∑ x : K ≃ₐ[k] K, φ x

theorem isDiscreteModule_coindU [IsAlgClosure k Ω] :
    Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (CoindU k Ω K) := by
  intro φ
  have hUmem : (1 : Ω ≃ₐ[k] Ω) ∈ ⋂ x : K ≃ₐ[k] K,
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (φ x) : Set (Ω ≃ₐ[k] Ω)) :=
    Set.mem_iInter.mpr fun x => MulAction.mem_stabilizer_iff.mpr rfl
  have hU : IsOpen (⋂ x : K ≃ₐ[k] K,
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (φ x) : Set (Ω ≃ₐ[k] Ω))) :=
    isOpen_iInter_of_finite fun x => isDiscreteModule_addUnitsΩ _ _ (φ x)
  have h1ker : (1 : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
    rw [MonoidHom.mem_ker]; exact map_one _
  have hker : IsOpen (((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    have h : (SSGRoute.res k K).ker = K.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker K
    rw [h]
    exact IntermediateField.fixingSubgroup_isOpen K
  have hsub : (⋂ x : K ≃ₐ[k] K,
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (φ x) : Set (Ω ≃ₐ[k] Ω))) ∩
        (((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) ⊆
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) φ : Set (Ω ≃ₐ[k] Ω)) := by
    intro σ hσ
    obtain ⟨hσ1, hσ2⟩ := hσ
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    funext x
    change σ • φ ((SSGRoute.res k K σ)⁻¹ * x) = φ x
    have hσU : σ • (φ x) = φ x :=
      MulAction.mem_stabilizer_iff.mp (Set.mem_iInter.mp hσ1 x)
    rw [show SSGRoute.res k K σ = 1 from MonoidHom.mem_ker.mp hσ2, inv_one, one_mul]
    exact hσU
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset ((hU.inter hker).mem_nhds ⟨hUmem, h1ker⟩) hsub)

end CoindU

section CoindAux
variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
  [Normal k K] [FiniteDimensional k K]

/-- **Discreteness of a finite product of coinduced modules.** -/
theorem isDiscreteModule_pi_coindU [IsAlgClosure k Ω] {ι : Type*} [Fintype ι] :
    Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (ι → CoindU k Ω K) := by
  intro φ
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (φ i) : Set (Ω ≃ₐ[k] Ω))) :=
    isOpen_iInter_of_finite fun i => CoindU.isDiscreteModule_coindU (K := K) (φ i)
  have h1 : (1 : Ω ≃ₐ[k] Ω) ∈ ⋂ i,
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (φ i) : Set (Ω ≃ₐ[k] Ω)) :=
    Set.mem_iInter.mpr fun i => MulAction.mem_stabilizer_iff.mpr (one_smul _ _)
  have hsub : (⋂ i, (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (φ i) : Set (Ω ≃ₐ[k] Ω))) ⊆
      (MulAction.stabilizer (Ω ≃ₐ[k] Ω) φ : Set (Ω ≃ₐ[k] Ω)) := by
    intro σ hσ
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    funext i
    have := Set.mem_iInter.mp hσ i
    rwa [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at this
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset ((hU).mem_nhds h1) hsub)

end CoindAux

/-! ## The action of `K`-automorphisms of `Ω` on `Ωˣ`

`umap` is the map on units induced by a field automorphism; it is the multiplicative form of the
`Γ`-action on `Additive Ωˣ` used above. -/

section Umap

variable (KF : Type) [Field KF] (ΩF : Type) [Field ΩF] [Algebra KF ΩF]

/-- The action of a `KF`-automorphism of `ΩF` on `ΩFˣ`. -/
def umap (σ : ΩF ≃ₐ[KF] ΩF) : ΩFˣ →* ΩFˣ :=
  Units.map σ.toAlgHom.toRingHom.toMonoidWithZeroHom

@[simp] theorem umap_coe (σ : ΩF ≃ₐ[KF] ΩF) (u : ΩFˣ) :
    ((umap KF ΩF σ u : ΩFˣ) : ΩF) = σ (u : ΩF) := rfl
@[simp] theorem umap_one (u : ΩFˣ) : umap KF ΩF 1 u = u := by ext; simp [umap]
@[simp] theorem umap_mul (σ τ : ΩF ≃ₐ[KF] ΩF) (u : ΩFˣ) :
    umap KF ΩF (σ * τ) u = umap KF ΩF σ (umap KF ΩF τ u) := by ext; simp [umap]

end Umap

end

end Work.SSGRoute
