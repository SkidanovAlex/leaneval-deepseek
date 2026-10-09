import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! The base-field change `(k, Ω, K) ↝ (↥L, Ω, K)` for `L : IntermediateField k K`:
`K` is re-read as an intermediate field of `Ω` over `↥L`, and the composite instances needed to
instantiate a field-generic chapter at the base field `↥L` are provided explicitly
(`inferInstance` does not find them). -/

namespace Work.SSGRoute.E1aClean

open IntermediateField

section BaseFieldChange

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- `K` viewed as an intermediate field of `Ω` over the subfield `L : IntermediateField k K`:
the top field of the base-changed extension `K / L`. -/
def Kover (L : IntermediateField k K) : IntermediateField ↥L Ω where
  carrier := (K : Set Ω)
  mul_mem' := fun hx hy => K.mul_mem' hx hy
  one_mem' := K.one_mem'
  add_mem' := fun hx hy => K.add_mem' hx hy
  zero_mem' := K.zero_mem'
  inv_mem' := fun hx => K.inv_mem' hx
  algebraMap_mem' := fun x => by
    show algebraMap ↥L Ω x ∈ (K : Set Ω)
    rw [IsScalarTower.algebraMap_apply ↥L ↥K Ω]
    exact (algebraMap ↥L ↥K x).2

variable (L : IntermediateField k K)

/-- `Ω` is torsion free over the subfield `↥L` (explicit: the field instance). -/
instance isTorsionFree_Kover : Module.IsTorsionFree ↥L Ω where
  isSMulRegular r hr m₁ m₂ hm := by
    have h := congrArg (fun x => r⁻¹ • x) hm
    simpa [inv_smul_smul₀ hr.ne_zero] using h

/-- `Ω` is algebraic over the subfield `↥L` (tower transfer). -/
theorem isAlgebraic_Kover [Algebra.IsAlgebraic k Ω] : Algebra.IsAlgebraic ↥L Ω :=
  Algebra.IsAlgebraic.tower_top (K := k) (L := ↥L) (A := Ω)

/-- **`Ω` is an algebraic closure of the base field `↥L`.**  This is the instance that
`inferInstance` cannot find and that the base-changed field-generic instantiation needs. -/
instance isAlgClosure_Kover [IsAlgClosure k Ω] : IsAlgClosure ↥L Ω where
  isAlgClosed := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
  isAlgebraic := isAlgebraic_Kover L

/-- The `↥L`-algebra structure on the base-changed top field. -/
example : Algebra ↥L (Kover L) := inferInstance

/-- `↥L` is a number field (from `k` and finiteness of `K` over `k`). -/
example [NumberField k] [FiniteDimensional k K] : NumberField ↥L :=
  NumberField.of_module_finite (K := k) (L := ↥L)

/-! ### The two inclusions of the base-changed groups

The level-change naturality square compares the dictionary over `Gal(K/k)` with the one over
`Gal(K/L)`; the latter group sits inside the former as the fixing subgroup of `L` (in `K`,
respectively in `Ω`).  These are the two group inclusions and the membership facts the square
needs. -/

/-- `L`, viewed as an intermediate field of `Ω` (through `K ⊆ Ω`). -/
def LOmega (L : IntermediateField k K) : IntermediateField k Ω :=
  L.map (IntermediateField.val K)

/-- The group `Gal(K/L)` inside `Gal(K/k)`. -/
def galKIncl (L : IntermediateField k K) : (K ≃ₐ[↥L] K) →* (K ≃ₐ[k] K) where
  toFun σ := AlgEquiv.restrictScalars k σ
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- The group `Gal(Ω/L)` inside `Gal(Ω/k)`. -/
def galOIncl (L : IntermediateField k K) : (Ω ≃ₐ[↥L] Ω) →* (Ω ≃ₐ[k] Ω) where
  toFun σ := AlgEquiv.restrictScalars k σ
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- The image of `galKIncl` is the fixing subgroup of `L` in `Gal(K/k)`. -/
theorem galKIncl_mem_fixingSubgroup (L : IntermediateField k K) (σ : K ≃ₐ[↥L] K) :
    galKIncl L σ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact AlgEquiv.commutes σ ⟨x, hx⟩

/-- The image of `galOIncl` is the fixing subgroup of `LOmega L` in `Gal(Ω/k)`. -/
theorem galOIncl_mem_fixingSubgroup (L : IntermediateField k K) (σ : Ω ≃ₐ[↥L] Ω) :
    galOIncl L σ ∈ (LOmega L).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro x ⟨y, hy, rfl⟩
  exact AlgEquiv.commutes σ ⟨y, hy⟩

/-- The scalar map `↥L → ↥K` lands in `L`. -/
theorem algebraMap_mem_L (L : IntermediateField k K) (x : ↥L) :
    algebraMap ↥L ↥K x ∈ L :=
  x.2

/-- The scalar map `↥L → Ω` lands in `LOmega L`. -/
theorem algebraMap_mem_LOmega (L : IntermediateField k K) (x : ↥L) :
    algebraMap ↥L Ω x ∈ LOmega L :=
  (IntermediateField.mem_map (S := L) (f := IntermediateField.val K)).mpr
    ⟨x.1, x.2, rfl⟩

/-- **`Gal(K/L) ≃* L.fixingSubgroup`**: an element of `Gal(K/k)` fixing `L` pointwise is
`↥L`-linear, and conversely. -/
noncomputable def galKMulEquiv (L : IntermediateField k K) :
    (K ≃ₐ[↥L] K) ≃* L.fixingSubgroup where
  toFun σ := ⟨galKIncl L σ, galKIncl_mem_fixingSubgroup L σ⟩
  invFun τ := AlgEquiv.ofRingEquiv (f := (τ.1 : K ≃+* K)) fun x =>
    (IntermediateField.mem_fixingSubgroup_iff L τ.1).mp τ.2 _
      (algebraMap_mem_L L x)
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- **Coherence of the two inclusions**: `galKIncl` after the inverse of `galKMulEquiv` is the
coercion of the subgroup.  This is what turns the `Rep.res`-identifications of the transport into
`rfl`. -/
theorem galKIncl_galKMulEquiv_symm (L : IntermediateField k K) (τ : L.fixingSubgroup) :
    galKIncl L ((galKMulEquiv L).symm τ) = τ.1 := by
  ext x
  rfl

/-- **`Gal(Ω/L) ≃* (LOmega L).fixingSubgroup`** (the `Ω`-side twin). -/
noncomputable def galOMulEquiv (L : IntermediateField k K) :
    (Ω ≃ₐ[↥L] Ω) ≃* (LOmega L).fixingSubgroup where
  toFun σ := ⟨galOIncl L σ, galOIncl_mem_fixingSubgroup L σ⟩
  invFun τ := AlgEquiv.ofRingEquiv (f := (τ.1 : Ω ≃+* Ω)) fun x =>
    (IntermediateField.mem_fixingSubgroup_iff (LOmega L) τ.1).mp τ.2 _
      (algebraMap_mem_LOmega L x)
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- **Coherence of the two inclusions** (the `Ω`-side twin). -/
theorem galOIncl_galOMulEquiv_symm (L : IntermediateField k K) (τ : (LOmega L).fixingSubgroup) :
    galOIncl L ((galOMulEquiv L).symm τ) = τ.1 := by
  ext x
  rfl

end BaseFieldChange

end Work.SSGRoute.E1aClean
