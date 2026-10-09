/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The embedding `G_0/G_1 ↪ (A/𝔪_A)^×`

For a discretely valued extension with uniformizer `π`
(`NK.RamificationDeep.UniformizerData`), the classical map `σ ↦ σ(π)/π` gives, for `i = 0`
this time, a homomorphism `G_0 → (A/𝔪_A)^×` with kernel `G_1`.  Consequently
`#(G_0/G_1) ∣ #(A/𝔪_A)^× = q - 1`; in particular, if the residue field has `p^f` elements then
`G_0/G_1` has order prime to `p`.

Formalisation: for `σ ∈ G_0` the element `σ π - π` lies in `𝔪_A = (π)`, so
`σ π - π = π b_σ`; then `σ ↦ 1 + b_σ` is multiplicative modulo `𝔪_A`
(`unitCoord_mul_sub_mem`) and its kernel is `G_1` (`unitHom_ker`).
-/
import Mathlib
import Submission.NK.RamificationDeep.QuotientEmbed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {A : ValuationSubring L} [IsDiscreteValuationRing A] {π : A} {E : IntermediateField K L}

/-! ## The unit coordinate of `σ ∈ G_0` -/

/-- The element `1 + b_σ = σ(π)/π` attached to `σ ∈ G_0`. -/
def unitCoord (D : UniformizerData (K := K) A π E)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) : A :=
  1 + coord D 0 σ

/-- `π`-relation: `(1 + b_σ) π = σ π`. -/
theorem unitCoord_mul_pi (D : UniformizerData (K := K) A π E)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) :
    unitCoord D σ * π = (σ : A.decompositionSubgroup K) • π := by
  have h := coord_spec (K := K) D 0 σ
  rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one] at h
  rw [unitCoord, add_mul, one_mul, h]
  ring

/-- **`1 + b_σ` is a unit of `A`.**  Indeed `1 + b_σ = σ(π)/π`, and since `σ⁻¹ π = a π` with
`a ∈ A`, we get `π = (σ • a)(σ • π) = ε · ε' π`; cancelling `π` exhibits the inverse of
`1 + b_σ`. -/
theorem isUnit_unitCoord (D : UniformizerData (K := K) A π E)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) :
    IsUnit (unitCoord D σ) := by
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
    rw [D.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  have hxmem : (σ : A.decompositionSubgroup K)⁻¹ • π ∈ IsLocalRing.maximalIdeal A := by
    have h := NK.Ramification.smul_mem_maximalIdeal_pow (K := K) A
      (σ : A.decompositionSubgroup K)⁻¹ 1 (show π ∈ IsLocalRing.maximalIdeal A ^ 1 by
        rwa [pow_one])
    simpa using h
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton').mp (by rw [← D.maximalIdeal_eq]; exact hxmem)
  have h1 : ((σ : A.decompositionSubgroup K) • a) * unitCoord D σ = 1 := by
    refine mul_right_cancel₀ (pi_ne_zero (K := K) D) ?_
    rw [one_mul]
    calc ((σ : A.decompositionSubgroup K) • a) * unitCoord D σ * π
        = ((σ : A.decompositionSubgroup K) • a) * (unitCoord D σ * π) := by ring
      _ = ((σ : A.decompositionSubgroup K) • a) * ((σ : A.decompositionSubgroup K) • π) := by
            rw [unitCoord_mul_pi]
      _ = (σ : A.decompositionSubgroup K) • (a * π) := (smul_mul' _ _ _).symm
      _ = (σ : A.decompositionSubgroup K) • ((σ : A.decompositionSubgroup K)⁻¹ • π) := by rw [ha]
      _ = π := by rw [← mul_smul, mul_inv_cancel, one_smul]
  exact ⟨⟨unitCoord D σ, (σ : A.decompositionSubgroup K) • a, (mul_comm _ _).trans h1, h1⟩, rfl⟩

/-! ## Multiplicativity of `σ ↦ 1 + b_σ` modulo `𝔪_A` -/

/-- The exact identity `1 + b_{στ} = σ(1 + b_τ)·(1 + b_σ)`, obtained by multiplying by `π`. -/
theorem unitCoord_mul_eq (D : UniformizerData (K := K) A π E)
    (σ τ : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) :
    unitCoord D (σ * τ) =
      (σ : A.decompositionSubgroup K) • (unitCoord D τ) * unitCoord D σ := by
  have hcoe : ((σ * τ : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) :
      A.decompositionSubgroup K) = (σ : A.decompositionSubgroup K) *
        (τ : A.decompositionSubgroup K) := rfl
  have h1 : unitCoord D (σ * τ) * π =
      (σ : A.decompositionSubgroup K) • (unitCoord D τ * π) := by
    calc unitCoord D (σ * τ) * π
        = ((σ : A.decompositionSubgroup K) * (τ : A.decompositionSubgroup K)) • π := by
          rw [unitCoord_mul_pi, hcoe]
      _ = (σ : A.decompositionSubgroup K) • ((τ : A.decompositionSubgroup K) • π) :=
          mul_smul _ _ _
      _ = (σ : A.decompositionSubgroup K) • (unitCoord D τ * π) := by rw [unitCoord_mul_pi]
  have h2 : (σ : A.decompositionSubgroup K) • (unitCoord D τ * π) =
      ((σ : A.decompositionSubgroup K) • (unitCoord D τ) * unitCoord D σ) * π := by
    have hπ : (σ : A.decompositionSubgroup K) • π = unitCoord D σ * π :=
      (unitCoord_mul_pi (K := K) D σ).symm
    rw [smul_mul', hπ]
    ring
  exact mul_right_cancel₀ (pi_ne_zero (K := K) D) (h1.trans h2)

/-- **Multiplicativity modulo `𝔪_A`**: `(1 + b_{στ}) ≡ (1 + b_σ)(1 + b_τ)  (mod 𝔪_A)`. -/
theorem unitCoord_mul_sub_mem (D : UniformizerData (K := K) A π E)
    (σ τ : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) :
    unitCoord D (σ * τ) - unitCoord D σ * unitCoord D τ ∈ IsLocalRing.maximalIdeal A := by
  have hmem : (σ : A.decompositionSubgroup K) • (unitCoord D τ) - unitCoord D τ ∈
      IsLocalRing.maximalIdeal A := by
    have h := σ.2 (unitCoord D τ)
    rwa [show (0 : ℕ) + 1 = 1 from rfl, pow_one] at h
  have hkey : unitCoord D (σ * τ) - unitCoord D σ * unitCoord D τ =
      ((σ : A.decompositionSubgroup K) • (unitCoord D τ) - unitCoord D τ) * unitCoord D σ := by
    rw [unitCoord_mul_eq]
    ring
  rw [hkey]
  exact Ideal.mul_mem_right _ _ hmem

/-! ## The monoid homomorphism `G_0 → (A/𝔪_A)^×` -/

/-- **The coordinate homomorphism** `G_0 → (A/𝔪_A)^×`, `σ ↦ 1 + b_σ`.  Its kernel is `G_1`. -/
def unitHom (D : UniformizerData (K := K) A π E) :
    ↥(NK.Ramification.ramificationSubgroup (K := K) A 0) →*
      (A ⧸ IsLocalRing.maximalIdeal A)ˣ where
  toFun σ := ((isUnit_unitCoord (K := K) D σ).map
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).unit
  map_one' := by
    refine Units.ext ?_
    rw [IsUnit.unit_spec, Units.val_one]
    have hc : coord D 0 (1 : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) = 0 := by
      refine (coord_unique (K := K) D ?_).symm
      rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one]
      rw [zero_mul, show ((1 : ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)) :
        A.decompositionSubgroup K) = 1 from rfl, one_smul, sub_self]
    rw [unitCoord, hc, add_zero, map_one]
  map_mul' σ τ := by
    refine Units.ext ?_
    rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    rw [show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (unitCoord D σ) *
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (unitCoord D τ) =
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (unitCoord D σ * unitCoord D τ) from
      (map_mul _ _ _).symm]
    rw [Ideal.Quotient.eq]
    have h := unitCoord_mul_sub_mem (K := K) D σ τ
    have : unitCoord D (σ * τ) - unitCoord D σ * unitCoord D τ =
        unitCoord D (σ * τ) - unitCoord D σ * unitCoord D τ := rfl
    exact h

/-- The kernel of `σ ↦ 1 + b_σ` is `G_1`: `1 + b_σ ≡ 1 (mod 𝔪_A)` iff `b_σ ∈ 𝔪_A` iff
`σ π - π ∈ 𝔪_A^2` iff `σ ∈ G_1` (the uniformizer criterion). -/
theorem unitHom_ker (D : UniformizerData (K := K) A π E) :
    (unitHom (K := K) D).ker =
      (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0) := by
  ext σ
  rw [MonoidHom.mem_ker]
  show ((isUnit_unitCoord (K := K) D σ).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).unit = (1 : (A ⧸
        IsLocalRing.maximalIdeal A)ˣ) ↔ _
  rw [Units.ext_iff, IsUnit.unit_spec, Units.val_one, Subgroup.mem_subgroupOf]
  rw [succ_mem_iff (K := K) D σ σ.2]
  rw [show (0 : ℕ) + 2 = 2 from rfl]
  rw [show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (unitCoord D σ) = 1 ↔
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (unitCoord D σ) =
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) 1 from Iff.rfl]
  rw [Ideal.Quotient.eq, show unitCoord D σ - 1 = coord D 0 σ from by rw [unitCoord]; ring]
  constructor
  · -- `b_σ ∈ 𝔪_A` implies `σ π - π ∈ 𝔪_A^2`
    intro hb
    have hx : (σ : A.decompositionSubgroup K) • π - π = coord D 0 σ * π := by
      have h := coord_spec (K := K) D 0 σ
      rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one] at h
      exact h.symm
    rw [D.maximalIdeal_eq] at hb ⊢
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton').mp hb
    rw [hx, show coord D 0 σ = c * π from hc.symm]
    rw [show c * π * π = c * π ^ 2 by ring, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩
  · -- `σ π - π ∈ 𝔪_A^2` implies `b_σ ∈ 𝔪_A`
    intro h
    have hx : (σ : A.decompositionSubgroup K) • π - π = coord D 0 σ * π := by
      have h := coord_spec (K := K) D 0 σ
      rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one] at h
      exact h.symm
    rw [D.maximalIdeal_eq] at h ⊢
    rw [Ideal.span_singleton_pow] at h
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton').mp h
    rw [hx] at hc
    rw [show c * π ^ 2 = (c * π) * π by ring] at hc
    have hb : coord D 0 σ = c * π :=
      mul_right_cancel₀ (pi_ne_zero (K := K) D) hc.symm
    rw [hb]
    exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩

/-- **The embedding `G_0/G_1 ↪ (A/𝔪_A)^×`** in cardinality form. -/
theorem natCard_quotient_zero_dvd_units (D : UniformizerData (K := K) A π E) :
    Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := K) A 0)) ∣
      Nat.card (A ⧸ IsLocalRing.maximalIdeal A)ˣ := by
  have hnormal : ((NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
      (NK.Ramification.ramificationSubgroup (K := K) A 0)).Normal :=
    (NK.Ramification.ramificationSubgroup_normal (K := K) A 1).subgroupOf _
  haveI := hnormal
  set φ := unitHom (K := K) D with hφ
  have hker : φ.ker = (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
      (NK.Ramification.ramificationSubgroup (K := K) A 0) := unitHom_ker (K := K) D
  have hcard : Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A 0) ⧸
      (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)) = Nat.card ↥φ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [hcard]
  exact ⟨φ.range.index, (Subgroup.card_mul_index φ.range).symm⟩

end

end NK.RamificationDeep
