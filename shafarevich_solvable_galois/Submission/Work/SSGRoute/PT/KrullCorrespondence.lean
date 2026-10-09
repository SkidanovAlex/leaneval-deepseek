import Mathlib
import Submission.AbsoluteKummer
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Work.SSGRoute.PT.H1Transfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Krull correspondence for *open* subgroups of an absolute Galois group

Mathlib's Galois correspondence `IntermediateField.fixingSubgroup_fixedField` is stated for a
*finite-dimensional* extension; for the absolute Galois group `Gal(Ω/k)` of an infinite extension
it is not available.  This file proves the missing case: for an **open** subgroup `U` of
`Gal(Ω/k)` (Krull topology),

  `(IntermediateField.fixedField U).fixingSubgroup = U`.

This is Milne, *ADT*, the reduction that carries the class-formation axiom 1.1a (Hilbert 90) from
the absolute target `Gal(Ω/F)` to an arbitrary open subgroup — the last step of the chain
`H1Transfer` → `hilbert90_H1_eq_zero_of_isAlgClosure` → open subgroups.

## Proof plan (hard direction `(fixedField U).fixingSubgroup ≤ U`)

Let `σ` fix `L := fixedField U` pointwise.

1. `U` is open and `1 ∈ U`, so by `krullTopology_mem_nhds_one_iff` there is a
   **finite** intermediate field `E` with `E.fixingSubgroup ⊆ U`.
2. Let `M := IntermediateField.normalClosure k ↥E Ω`; then `E ≤ M`
   (`IntermediateField.le_normalClosure`), `M/k` is finite (`normalClosure.is_finiteDimensional`)
   and normal — the latter is the universal property `AlgHom.fieldRange_le_normalClosure` — so
   `ρ := AlgEquiv.restrictNormalHom (K₁ := Ω) ↥M : Gal(Ω/k) →* Gal(M/k)` is defined.
   Also `M.fixingSubgroup ≤ E.fixingSubgroup ≤ U` since `E ≤ M`.
3. Let `H := U.map ρ ≤ Gal(M/k)`.  Then, inside `M`, `fixedField H = (fixedField U).comap _`
   — for `x : ↥M`, `(ρτ) x = τ x` (`AlgEquiv.restrictNormalHom_apply`), so `x` is fixed by
   `ρ(U) = H` iff `↑x` is fixed by `U`.
4. `ρ σ ∈ H`: `IntermediateField.fixingSubgroup_fixedField H` (finite case, `M/k`) identifies
   `H` with `fixingSubgroup (fixedField H)`, and `ρ σ` fixes `fixedField H = (fixedField U).comap`
   because `σ` fixes `fixedField U`.
5. `Subgroup.mem_map` gives `τ ∈ U` with `ρ τ = ρ σ`; then `σ * τ⁻¹ ∈ ker ρ = M.fixingSubgroup ⊆ U`
   (the kernel computation uses `AlgEquiv.restrictNormalHom_apply` and
   `IntermediateField.mem_fixingSubgroup_iff`), so `σ = (σ * τ⁻¹) * τ ∈ U`.

## Status

The easy direction `U ≤ (fixedField U).fixingSubgroup` is proved below (it is the Galois
connection `IntermediateField.le_iff_le`); the hard direction is `sorry` and is the item recorded
in `Submission/Work/SSGRoute/PT/localTatePairing_deg02.lean` (roadmap, step 3a).
-/

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false

open Filter

/-!
## Status (updated)

All four items of this file are now proved (`lake build` clean):

* `le_fixingSubgroup_fixedField`, `fixingSubgroup_fixedField_of_isOpen` — Krull correspondence at an
  open subgroup;
* `finiteDimensional_fixedField_of_isOpen` — the fixed field of an open subgroup is finite over `k`
  (the missing half of `InfiniteGalois.isOpen_iff_finite`);
* `continuous_fixingSubgroupEquiv`, `isHomeomorph_fixingSubgroupEquiv` — the isomorphism
  `K.fixingSubgroup ≃* Gal(Ω/↥K)` is a homeomorphism for the Krull topologies;
* **`hilbert90_H1_eq_zero_openSubgroup`** — Milne, *ADT*, class-formation axiom **1.1a** for the
  class module `\bar k^×`: `H¹(U, Ωˣ) = 0` for **every open** subgroup `U ≤ Gal(Ω/k)`, obtained from
  the absolute case `hilbert90_H1_eq_zero_of_isAlgClosure` by the `H¹`-transfer along the
  homeomorphism above.

This is the first of the two class-formation inputs in the roadmap of
`Submission/Work/SSGRoute/PT/localTatePairing_deg02.lean`; the second is the invariant map
`H²(U, \bar k^×) ≅ ℚ/ℤ` (Milne 1.1b), and together with Milne's Theorem 1.8 they give the target.
-/

/-- The easy half of the Krull correspondence: `U` fixes `fixedField U` pointwise. -/
theorem le_fixingSubgroup_fixedField {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (U : Subgroup (Ω ≃ₐ[k] Ω)) :
    U ≤ (IntermediateField.fixedField U).fixingSubgroup :=
  (IntermediateField.le_iff_le U (IntermediateField.fixedField U)).mp le_rfl

/-- **The Krull correspondence for an open subgroup** of an absolute Galois group:
`(fixedField U).fixingSubgroup = U`. -/
theorem fixingSubgroup_fixedField_of_isOpen {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] (U : Subgroup (Ω ≃ₐ[k] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[k] Ω))) :
    (IntermediateField.fixedField U).fixingSubgroup = U := by
  refine le_antisymm ?_ (le_fixingSubgroup_fixedField U)
  intro σ hσ
  -- Krull basis: a finite intermediate field whose fixing subgroup lies in `U`
  obtain ⟨E, hEfin, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff k Ω (U : Set (Ω ≃ₐ[k] Ω))).mp
      (hU.mem_nhds U.one_mem)
  -- the normal closure of `E` is finite and normal over `k`
  let M : IntermediateField k Ω := IntermediateField.normalClosure k ↥E Ω
  haveI hMfin : FiniteDimensional k ↥M := inferInstance
  haveI hMnorm : Normal k ↥M := inferInstance
  have hE_le_M : E ≤ M := IntermediateField.le_normalClosure E
  have hMfix_le : M.fixingSubgroup ≤ U := fun τ hτ =>
    hEU ((IntermediateField.mem_fixingSubgroup_iff E τ).mpr fun y hy =>
      (IntermediateField.mem_fixingSubgroup_iff M τ).mp hτ y (hE_le_M hy))
  -- the restriction map `Gal(Ω/k) →* Gal(M/k)`
  set ρ := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M with hρ
  set H : Subgroup (↥M ≃ₐ[k] ↥M) := U.map ρ with hH
  -- its kernel is the fixing subgroup of `M`
  have hker : ∀ γ : Ω ≃ₐ[k] Ω, ρ γ = 1 → γ ∈ M.fixingSubgroup := by
    intro γ hγ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h2 : (ρ γ) ⟨x, hx⟩ = (1 : ↥M ≃ₐ[k] ↥M) ⟨x, hx⟩ := by rw [hγ]
    have h3 := congrArg (fun (y : ↥M) => (y : Ω)) h2
    simpa [hρ, AlgEquiv.restrictNormalHom_apply] using h3
  -- `fixedField H = (fixedField U).comap`
  have hfix : IntermediateField.fixedField H
      = (IntermediateField.fixedField U).comap (IsScalarTower.toAlgHom k ↥M Ω) := by
    ext x
    change x ∈ IntermediateField.fixedField H ↔
      (IsScalarTower.toAlgHom k ↥M Ω) x ∈ IntermediateField.fixedField U
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
    constructor
    · intro h τ hτ
      have h2 : (ρ τ) x = x := h (ρ τ) (Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩)
      have h3 := congrArg (fun (y : ↥M) => (y : Ω)) h2
      simpa [hρ, AlgEquiv.restrictNormalHom_apply] using h3
    · intro h φ hφ
      obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hφ
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      exact h τ hτ
  -- `ρ σ` lies in the image of `U`
  have hρσ : ρ σ ∈ H := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : (IsScalarTower.toAlgHom k ↥M Ω) y ∈ IntermediateField.fixedField U := by
      rw [hfix] at hy
      exact hy
    have h4 : σ ((IsScalarTower.toAlgHom k ↥M Ω) y) = (IsScalarTower.toAlgHom k ↥M Ω) y :=
      ((IntermediateField.mem_fixingSubgroup_iff (IntermediateField.fixedField U) σ).mp hσ)
        ((IsScalarTower.toAlgHom k ↥M Ω) y) hy'
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact h4
  obtain ⟨τ, hτU, hτρ⟩ := Subgroup.mem_map.mp hρσ
  have hτker : σ * τ⁻¹ ∈ M.fixingSubgroup := by
    refine hker (σ * τ⁻¹) ?_
    rw [map_mul, map_inv, hτρ, mul_inv_cancel]
  have hmem : σ * τ⁻¹ ∈ U := hMfix_le hτker
  have hστ : σ = (σ * τ⁻¹) * τ := by group
  rw [hστ]
  exact U.mul_mem hmem hτU

/-- **The fixed field of an open subgroup is finite over the base.**  For `U ≤ Gal(Ω/k)` open,
`Ω^{U}/k` is finite: this is the missing half of the Krull correspondence (Mathlib only has the
finite-extension direction `InfiniteGalois.isOpen_iff_finite`). -/
theorem finiteDimensional_fixedField_of_isOpen {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] (U : Subgroup (Ω ≃ₐ[k] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[k] Ω))) :
    FiniteDimensional k ↥(IntermediateField.fixedField U) :=
  (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField U)).mp (by
    rw [InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω)
      ⟨U, Subgroup.isClosed_of_isOpen U hU⟩]
    exact hU)

section FixingSubgroupHomeomorph

variable (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [CharZero k]
  (K : IntermediateField k Ω)

/-- **The isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is continuous.** -/
theorem continuous_fixingSubgroupEquiv [FiniteDimensional k K] :
    Continuous ((IntermediateField.fixingSubgroupEquiv K).toMonoidHom :
      ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω)) := by
  let f : ↥(K.fixingSubgroup) →* (Ω ≃ₐ[↥K] Ω) :=
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥K Ω] at hU
  obtain ⟨N, hNfin, hNU⟩ := hU
  haveI : FiniteDimensional ↥K N := hNfin
  haveI hMfin : FiniteDimensional k ↥(N.restrictScalars k) :=
    FiniteDimensional.trans k ↥K ↥N
  have hopen : IsOpen ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen (N.restrictScalars k)
  have hmem : (Subtype.val ⁻¹' ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) ∈
      nhds (1 : ↥(K.fixingSubgroup)) :=
    (hopen.preimage continuous_subtype_val).mem_nhds (by simp)
  refine Filter.mem_of_superset hmem ?_
  intro x hx
  show (IntermediateField.fixingSubgroupEquiv K x) ∈ U
  apply hNU
  change (IntermediateField.fixingSubgroupEquiv K x) ∈ N.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hyM : y ∈ (N.restrictScalars k : IntermediateField k Ω) := hy
  rw [IntermediateField.mem_restrictScalars] at hyM
  have hx' : (x : Ω ≃ₐ[k] Ω) ∈ (N.restrictScalars k).fixingSubgroup := hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hx'
  exact hx' y hyM

/-- **The isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is a homeomorphism** for the Krull
topologies (a continuous bijection from a compact space to a Hausdorff space).  The finiteness
`FiniteDimensional k K` is needed: without it the statement is false. -/
theorem isHomeomorph_fixingSubgroupEquiv [FiniteDimensional k K] [IsAlgClosure k Ω] :
    IsHomeomorph
      ((IntermediateField.fixingSubgroupEquiv K : ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω))) := by
  haveI : CompactSpace ↥(K.fixingSubgroup) := by
    have hclosed : IsClosed ((K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      IntermediateField.fixingSubgroup_isClosed K
    haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space (Ω ≃ₐ[↥K] Ω) := krullTopology_t2 (K := ↥K) (L := Ω)
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨continuous_fixingSubgroupEquiv k Ω K, (IntermediateField.fixingSubgroupEquiv K).bijective⟩

end FixingSubgroupHomeomorph

/-- **Hilbert 90 at an open subgroup** (Milne, *ADT*, class formation axiom 1.1a for the class
module `\bar k^×`): for an open subgroup `U` of an absolute Galois group `Gal(Ω/k)` of
characteristic `0`, `H¹(U, Ωˣ) = 0`.

Proof: transport `hilbert90_H1_eq_zero_of_isAlgClosure ↥L Ω` (Hilbert 90 at the absolute group
`Gal(Ω/L)`, `L = fixedField U`) along the homeomorphic group isomorphism
`IntermediateField.fixingSubgroupEquiv L`, using `(fixedField U).fixingSubgroup = U` (Krull
correspondence for open `U`). -/
theorem hilbert90_H1_eq_zero_openSubgroup {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsAlgClosure k Ω] [CharZero k] (U : Subgroup (Ω ≃ₐ[k] Ω))
    (hU : IsOpen (U : Set (Ω ≃ₐ[k] Ω))) :
    Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) := by
  let L : IntermediateField k Ω := IntermediateField.fixedField U
  have hL : L.fixingSubgroup = U := fixingSubgroup_fixedField_of_isOpen U hU
  haveI : FiniteDimensional k ↥L := finiteDimensional_fixedField_of_isOpen U hU
  haveI : IsAlgClosure ↥L Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥L] Ω) (Additive (Units Ω))) :=
    ⟨fun a b => by
      rw [Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure ↥L Ω a,
        Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure ↥L Ω b]⟩
  have hΦ : IsHomeomorph ((IntermediateField.fixingSubgroupEquiv L :
      ↥(L.fixingSubgroup) → (Ω ≃ₐ[↥L] Ω))) := isHomeomorph_fixingSubgroupEquiv k Ω L
  have h := Work.SSGRoute.PT.h1Transfer (G := Ω ≃ₐ[↥L] Ω) (G' := ↥(L.fixingSubgroup))
    (M := Additive (Units Ω)) (M' := Additive (Units Ω))
    (IntermediateField.fixingSubgroupEquiv L) hΦ (AddEquiv.refl (Additive (Units Ω)))
    (fun g' m' => rfl)
  rw [← hL]
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩
