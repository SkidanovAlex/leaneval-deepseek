/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The embedding `G_i/G_{i+1} ↪ 𝔪_A^i/𝔪_A^{i+1}` and the structure of `G_1`

For a discretely valued extension `L/K` with valuation ring `A` of uniformizer `π`
(`NK.RamificationDeep.UniformizerData`), Serre (*Local Fields*, IV §2, Cor. 2) proves that for
`i ≥ 1` the map

  `σ ↦ σ(π)/π = 1 + b_σ`,   where `σ π - π = π^{i+1} b_σ`,

induces a **group homomorphism** `G_i → 𝔪_A^i/𝔪_A^{i+1}` with kernel `G_{i+1}`; since
`𝔪_A^i/𝔪_A^{i+1} ≅ A/𝔪_A` has `q = #(A/𝔪_A)` elements, this gives `#(G_i/G_{i+1}) ∣ q`.

The formalisation below avoids the identification `𝔪_A^i/𝔪_A^{i+1} ≅ A/𝔪_A` by landing the map
directly in the additive group of the *residue ring*: the coordinate `b_σ` is defined from
`σ π - π ∈ 𝔪_A^{i+1} = (π^{i+1})` as `σ π - π = π^{i+1} b_σ`, and the map is `σ ↦ b_σ mod 𝔪_A`.
Its additivity is the congruence

  `b_{στ} - b_σ - b_τ ∈ 𝔪_A`,

which follows from `(σ τ) π - π = σ(τ π - π) + (σ π - π)` together with
`σ x - x ∈ 𝔪_A^{i+j}` for `x ∈ 𝔪_A^j`, `i ≥ 1`
(`NK.Ramification.smul_sub_mem_maximalIdeal_pow`), and its kernel is `G_{i+1}` by the
uniformizer criterion (`NK.Ramification.ramificationSubgroup_succ_eq_of_uniformizer`).

The same construction with `i = 0` and the multiplicative target `(A/𝔪_A)^×` gives the embedding
`G_0/G_1 ↪ (A/𝔪_A)^×` (`unitMap`, `natCard_quotient_zero_dvd_units`), whence `G_0/G_1` has order
prime to `p` when the residue field has `p^f` elements.
-/
import Mathlib
import Submission.NK.RamificationDeep.Defs
import Submission.NK.Ramification.smul_sub_mem_maximalIdeal_pow

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {A : ValuationSubring L} [IsDiscreteValuationRing A] {π : A} {E : IntermediateField K L}

/-! ## The uniformizer coordinate of `σ ∈ G_i` -/

/-- For `σ ∈ G_i` the element `σ π - π` lies in `𝔪_A^{i+1} = (π^{i+1})`, so it can be written
`π^{i+1} b_σ`.  This is Serre's `b_σ = σ(π)/π - 1`. -/
theorem exists_coord (D : UniformizerData (K := K) A π E) (i : ℕ)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
    ∃ b : A, b * π ^ (i + 1) =
      (σ : A.decompositionSubgroup K) • π - π := by
  have hmem : (σ : A.decompositionSubgroup K) • π - π ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
    σ.2 π
  rw [D.maximalIdeal_eq, Ideal.span_singleton_pow] at hmem
  exact (Ideal.mem_span_singleton').mp hmem

/-- The uniformizer coordinate `b_σ` of `σ ∈ G_i`, defined by `σ π - π = π^{i+1} b_σ`. -/
def coord (D : UniformizerData (K := K) A π E) (i : ℕ)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) : A :=
  Classical.choose (exists_coord (K := K) D i σ)

/-- The defining property of the uniformizer coordinate. -/
theorem coord_spec (D : UniformizerData (K := K) A π E) (i : ℕ)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
    coord D i σ * π ^ (i + 1) = (σ : A.decompositionSubgroup K) • π - π :=
  Classical.choose_spec (exists_coord (K := K) D i σ)

/-- The uniformizer coordinate is determined by the congruence `σ π - π = π^{i+1} b`. -/
theorem coord_unique (D : UniformizerData (K := K) A π E) {i : ℕ}
    {σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)} {b : A}
    (hb : b * π ^ (i + 1) = (σ : A.decompositionSubgroup K) • π - π) :
    b = coord D i σ := by
  have h := coord_spec (K := K) D i σ
  have h' : b * π ^ (i + 1) = coord D i σ * π ^ (i + 1) := by rw [hb, h]
  exact mul_right_cancel₀ (pow_ne_zero _ (pi_ne_zero (K := K) D)) h'

/-- **The coordinate map** `G_i → A/𝔪_A`, `σ ↦ b_σ mod 𝔪_A`.  Its kernel is `G_{i+1}`; for
`i ≥ 1` it is additive, so `G_i/G_{i+1}` sits inside the additive group of the residue ring. -/
def residueMap (D : UniformizerData (K := K) A π E) (i : ℕ)
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
    A ⧸ IsLocalRing.maximalIdeal A :=
  Ideal.Quotient.mk _ (coord D i σ)

/-! ## The key congruence: `b_{στ} ≡ b_σ + b_τ  (mod 𝔪_A)` -/

/-- **Serre's congruence** (*Local Fields* IV §2, proof of Cor. 2): for `i ≥ 1` and `σ, τ ∈ G_i`,

  `b_{στ} - b_σ - b_τ ∈ 𝔪_A`. -/
theorem coord_mul_sub_mem (D : UniformizerData (K := K) A π E) {i : ℕ} (hi : 1 ≤ i)
    (σ τ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
    coord D i (σ * τ) - coord D i σ - coord D i τ ∈ IsLocalRing.maximalIdeal A := by
  have hcoe : ((σ * τ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
      A.decompositionSubgroup K) = (σ : A.decompositionSubgroup K) *
        (τ : A.decompositionSubgroup K) := rfl
  have hστ : π ^ (i + 1) * coord D i (σ * τ) = (σ : A.decompositionSubgroup K) •
      ((τ : A.decompositionSubgroup K) • π) - π := by
    rw [mul_comm, coord_spec, hcoe, mul_smul]
  have hσ : π ^ (i + 1) * coord D i σ = (σ : A.decompositionSubgroup K) • π - π := by
    rw [mul_comm, coord_spec]
  have hτ : π ^ (i + 1) * coord D i τ = (τ : A.decompositionSubgroup K) • π - π := by
    rw [mul_comm, coord_spec]
  -- The key identity: `(σ τ) π - π = σ(τ π - π) + (σ π - π)`.
  have hkey : (σ : A.decompositionSubgroup K) • ((τ : A.decompositionSubgroup K) • π) - π =
      (σ : A.decompositionSubgroup K) • ((τ : A.decompositionSubgroup K) • π - π) +
        ((σ : A.decompositionSubgroup K) • π - π) := by
    rw [smul_sub]
    ring
  -- Multiply the difference of the coordinates by `π^{i+1}`.
  have hmul : π ^ (i + 1) * (coord D i (σ * τ) - coord D i σ - coord D i τ) =
      (σ : A.decompositionSubgroup K) • ((τ : A.decompositionSubgroup K) • π - π) -
        ((τ : A.decompositionSubgroup K) • π - π) := by
    rw [mul_sub, mul_sub, hστ, hσ, hτ, hkey]
    ring
  have hmem : (σ : A.decompositionSubgroup K) • ((τ : A.decompositionSubgroup K) • π - π) -
      ((τ : A.decompositionSubgroup K) • π - π) ∈ IsLocalRing.maximalIdeal A ^ (i + 2) :=
    Ideal.pow_le_pow_right (by omega)
      (NK.Ramification.smul_sub_mem_maximalIdeal_pow (K := K) A π D.maximalIdeal_eq hi
        (σ : A.decompositionSubgroup K) σ.2 (τ.2 π))
  have hmem' : π ^ (i + 1) * (coord D i (σ * τ) - coord D i σ - coord D i τ) ∈
      Ideal.span ({π ^ (i + 2)} : Set A) := by
    rw [← Ideal.span_singleton_pow, ← D.maximalIdeal_eq, hmul]
    exact hmem
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton').mp hmem'
  -- `hc : c * π^{i+2} = π^{i+1} * (b_{στ} - b_σ - b_τ)`; cancel `π^{i+1}`.
  have hc' : coord D i (σ * τ) - coord D i σ - coord D i τ = c * π := by
    have h2 : π ^ (i + 1) * (coord D i (σ * τ) - coord D i σ - coord D i τ) =
        π ^ (i + 1) * (c * π) := by
      rw [hc.symm]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ (pi_ne_zero (K := K) D)) h2
  rw [D.maximalIdeal_eq, hc']
  exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩

/-- The coordinate map is additive modulo `𝔪_A`, i.e. it descends to the additive group of the
residue ring. -/
theorem residueMap_mul (D : UniformizerData (K := K) A π E) {i : ℕ} (hi : 1 ≤ i)
    (σ τ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
    residueMap (K := K) D i (σ * τ) = residueMap (K := K) D i σ + residueMap (K := K) D i τ := by
  have hsum : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (coord D i σ) +
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (coord D i τ) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (coord D i σ + coord D i τ) :=
    (map_add (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) _ _).symm
  rw [residueMap, residueMap, residueMap, hsum, Ideal.Quotient.eq]
  have h := coord_mul_sub_mem (K := K) D hi σ τ
  have : coord D i (σ * τ) - (coord D i σ + coord D i τ) =
      coord D i (σ * τ) - coord D i σ - coord D i τ := by ring
  rw [this]
  exact h

/-! ## The kernel of the coordinate map is `G_{i+1}` -/

/-- **The kernel of the coordinate map is `G_{i+1}`**: `b_σ ∈ 𝔪_A` iff `σ π - π ∈ 𝔪_A^{i+2}` iff
`σ ∈ G_{i+1}` (the last equivalence is the uniformizer criterion). -/
theorem residueMap_eq_zero_iff (D : UniformizerData (K := K) A π E) {i : ℕ}
    (σ : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
    residueMap (K := K) D i σ = 0 ↔
      (σ : A.decompositionSubgroup K) ∈
        NK.Ramification.ramificationSubgroup (K := K) A (i + 1) := by
  have hx : (σ : A.decompositionSubgroup K) • π - π = coord D i σ * π ^ (i + 1) :=
    (coord_spec (K := K) D i σ).symm
  rw [succ_mem_iff (K := K) D σ σ.2]
  rw [residueMap, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · -- `b_σ ∈ 𝔪_A` gives `σ π - π ∈ (π^{i+2})`
    intro hb
    rw [D.maximalIdeal_eq] at hb ⊢
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton').mp hb
    rw [hx, hc.symm]
    rw [show c * π * π ^ (i + 1) = c * π ^ (i + 2) by ring, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩
  · -- `σ π - π ∈ (π^{i+2})` gives `b_σ ∈ 𝔪_A`
    intro h
    rw [D.maximalIdeal_eq] at h ⊢
    rw [Ideal.span_singleton_pow] at h
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton').mp h
    rw [hx] at hc
    have h2 : π ^ (i + 1) * coord D i σ = π ^ (i + 1) * (c * π) := by
      rw [mul_comm (π ^ (i + 1)) (coord D i σ), ← hc]
      ring
    have hb : coord D i σ = c * π :=
      mul_left_cancel₀ (pow_ne_zero _ (pi_ne_zero (K := K) D)) h2
    rw [hb]
    exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩

/-- **The coordinate map as a group homomorphism** `G_i → (A/𝔪_A, +)` for `i ≥ 1`, with the
target written multiplicatively. -/
def residueHom (D : UniformizerData (K := K) A π E) {i : ℕ} (hi : 1 ≤ i) :
    ↥(NK.Ramification.ramificationSubgroup (K := K) A i) →*
      Multiplicative (A ⧸ IsLocalRing.maximalIdeal A) where
  toFun σ := Multiplicative.ofAdd (residueMap (K := K) D i σ)
  map_one' := by
    have hb : (0 : A) * π ^ (i + 1) = ((1 : ↥(NK.Ramification.ramificationSubgroup
        (K := K) A i)) : A.decompositionSubgroup K) • π - π := by
      rw [zero_mul, show ((1 : ↥(NK.Ramification.ramificationSubgroup (K := K) A i)) :
        A.decompositionSubgroup K) = 1 from rfl, one_smul, sub_self]
    have hcoord : coord D i 1 = 0 := (coord_unique (K := K) D hb).symm
    show Multiplicative.ofAdd (residueMap (K := K) D i 1) = 1
    rw [residueMap, hcoord, map_zero]
    rfl
  map_mul' σ τ := by
    show Multiplicative.ofAdd (residueMap (K := K) D i (σ * τ)) =
      Multiplicative.ofAdd (residueMap (K := K) D i σ) *
        Multiplicative.ofAdd (residueMap (K := K) D i τ)
    rw [← ofAdd_add, residueMap_mul (K := K) D hi]

/-- The kernel of the coordinate homomorphism is `G_{i+1}` (viewed inside `G_i`). -/
theorem residueHom_ker (D : UniformizerData (K := K) A π E) {i : ℕ} (hi : 1 ≤ i) :
    (residueHom (K := K) D hi).ker =
      (NK.Ramification.ramificationSubgroup (K := K) A (i + 1)).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A i) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    ← residueMap_eq_zero_iff (K := K) D σ]
  rfl

/-- **The embedding `G_i/G_{i+1} ↪ A/𝔪_A`** in cardinality form: for `i ≥ 1` the order of the
quotient `G_i/G_{i+1}` divides the order `q` of the residue field. -/
theorem natCard_quotient_dvd_residue (D : UniformizerData (K := K) A π E) {i : ℕ} (hi : 1 ≤ i) :
    Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A i) ⧸
        (NK.Ramification.ramificationSubgroup (K := K) A (i + 1)).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := K) A i)) ∣
      Nat.card (A ⧸ IsLocalRing.maximalIdeal A) := by
  have hnormal : ((NK.Ramification.ramificationSubgroup (K := K) A (i + 1)).subgroupOf
      (NK.Ramification.ramificationSubgroup (K := K) A i)).Normal :=
    (NK.Ramification.ramificationSubgroup_normal (K := K) A (i + 1)).subgroupOf _
  haveI := hnormal
  set φ := residueHom (K := K) D hi with hφ
  have hker : φ.ker = (NK.Ramification.ramificationSubgroup (K := K) A (i + 1)).subgroupOf
      (NK.Ramification.ramificationSubgroup (K := K) A i) := residueHom_ker (K := K) D hi
  have hcard : Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A i) ⧸
      (NK.Ramification.ramificationSubgroup (K := K) A (i + 1)).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A i)) = Nat.card ↥φ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [hcard]
  exact ⟨φ.range.index, (Subgroup.card_mul_index φ.range).symm⟩

end

end NK.RamificationDeep
