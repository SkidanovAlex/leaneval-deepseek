/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The higher ramification filtration in lower numbering

Mathlib defines, for a field extension `L/K` and a valuation subring `A` of `L`, the
*decomposition subgroup* `A.decompositionSubgroup K ≤ L ≃ₐ[K] L` and the *inertia subgroup*
`A.inertiaSubgroup K` (the kernel of the action on the residue field of `A`), and records
`TODO: Define higher ramification groups in lower numbering`.

This file supplies that missing definition and its elementary theory.  For `i : ℕ` the `i`-th
higher ramification subgroup is

  `G_i = { σ ∈ A.decompositionSubgroup K | ∀ x : A, σ • x - x ∈ 𝔪_A ^ (i+1) }`,

where `𝔪_A` is the maximal ideal of `A`.  Equivalently — and this is the classical definition —
`G_i` consists of the `σ` acting trivially on `A/𝔪_A^{i+1}`.

The classical dictionary (for `L/K` a finite Galois extension of local fields and `A` the
valuation ring, which is `Galois`-stable) is

* `G_{-1} = Gal(L/K)` (not formalised here, we index from `0`);
* `G_0 = I` — the inertia subgroup (`ramificationSubgroup_zero`);
* `G_1 = V` — the wild inertia, the maximal pro-`p` subgroup;
* the `G_i` are normal in the decomposition subgroup, decrease with `i`, and become trivial
  for `i` large (`iInf_ramificationSubgroup_eq_bot`, `exists_ramificationSubgroup_eq_bot`).

The chapter continues in `NK.Ramification.Herbrand` (the Herbrand function and the upper
numbering), `NK.Ramification.Tower` (multiplicativity in towers), `NK.Ramification.Adic`
(the `p`-adic case, reconciliation with the infinite-level vocabulary of
`NK.LocalTame`/`NK.LocalAnabelian`) and `NK.Ramification.Determined` (what the filtration
determines).
-/
import Mathlib
import Mathlib.RingTheory.Valuation.RamificationGroup

open scoped Pointwise

namespace NK.Ramification

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## The action of the decomposition subgroup on the valuation ring -/

/-- An element of the decomposition subgroup `A.decompositionSubgroup K` acts on the valuation
ring `A` by a ring automorphism.  This is the structure through which the higher ramification
subgroups are defined. -/
def smulRingEquiv (A : ValuationSubring L) (σ : A.decompositionSubgroup K) : A ≃+* A :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ

@[simp]
theorem smulRingEquiv_apply (A : ValuationSubring L) (σ : A.decompositionSubgroup K) (x : A) :
    smulRingEquiv A σ x = σ • x := rfl

/-- The underlying element of the field of the action of the decomposition subgroup. -/
@[simp]
theorem coe_smul (A : ValuationSubring L) (σ : A.decompositionSubgroup K) (x : A) :
    ((σ • x : A) : L) = (σ : L ≃ₐ[K] L) (x : L) := rfl

/-- The action of the decomposition subgroup on `A` preserves the maximal ideal. -/
@[simp]
theorem map_smulRingEquiv_maximalIdeal (A : ValuationSubring L) (σ : A.decompositionSubgroup K) :
    (IsLocalRing.maximalIdeal A).map (smulRingEquiv A σ : A →+* A) = IsLocalRing.maximalIdeal A :=
  IsLocalRing.map_ringEquiv_maximalIdeal _

/-- The action of the decomposition subgroup on `A` preserves every power of the maximal
ideal. -/
theorem smul_mem_maximalIdeal_pow (A : ValuationSubring L) (σ : A.decompositionSubgroup K)
    (n : ℕ) {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A ^ n) :
    σ • x ∈ IsLocalRing.maximalIdeal A ^ n := by
  have h1 : (smulRingEquiv A σ) x ∈ (IsLocalRing.maximalIdeal A ^ n).map
      (smulRingEquiv A σ : A →+* A) := Ideal.mem_map_of_mem _ hx
  rwa [Ideal.map_pow, map_smulRingEquiv_maximalIdeal] at h1

/-! ## The higher ramification subgroups -/

/-- **The `i`-th higher ramification subgroup in lower numbering**, for `i : ℕ`:

`G_i = { σ ∈ A.decompositionSubgroup K | σ x ≡ x  (mod 𝔪_A^{i+1}) for all x ∈ A }`.

For `i = 0` this is the inertia subgroup (`ramificationSubgroup_zero`).  Classically one also
sets `G_{-1} = Gal(L/K)`; we index from `0` and work inside the decomposition subgroup. -/
noncomputable def ramificationSubgroup (A : ValuationSubring L) (i : ℕ) :
    Subgroup (A.decompositionSubgroup K) where
  carrier := {σ | ∀ x : A, σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1)}
  mul_mem' := by
    intro σ τ hσ hτ x
    have h1 : σ • (τ • x) - σ • x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := by
      have h : (smulRingEquiv A σ) (τ • x - x) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
        smul_mem_maximalIdeal_pow A σ (i + 1) (hτ x)
      rw [map_sub] at h
      simp only [smulRingEquiv_apply] at h
      exact h
    have h2 : σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hσ x
    have h3 : (σ * τ) • x - x = (σ • (τ • x) - σ • x) + (σ • x - x) := by
      rw [mul_smul]; abel
    rw [h3]
    exact add_mem h1 h2
  one_mem' := by
    intro x
    rw [one_smul, sub_self]
    exact zero_mem _
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ • x)
    rw [show σ • (σ⁻¹ • x) = x from by rw [← mul_smul, mul_inv_cancel, one_smul]] at h
    have h' := neg_mem h
    rwa [neg_sub] at h'

theorem mem_ramificationSubgroup_iff (A : ValuationSubring L) (i : ℕ)
    (σ : A.decompositionSubgroup K) :
    σ ∈ ramificationSubgroup A i ↔
      ∀ x : A, σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
  Iff.rfl

/-! ## Basic properties: monotonicity and normality -/

/-- The ramification filtration is decreasing in the lower numbering. -/
theorem ramificationSubgroup_antitone (A : ValuationSubring L) :
    Antitone (ramificationSubgroup (K := K) A) := by
  intro i j hij σ hσ x
  exact Ideal.pow_le_pow_right (Nat.succ_le_succ hij) (hσ x)

/-- The ramification filtration is decreasing in the lower numbering. -/
theorem ramificationSubgroup_le_ramificationSubgroup (A : ValuationSubring L) {i j : ℕ}
    (hij : i ≤ j) : ramificationSubgroup (K := K) A j ≤ ramificationSubgroup A i :=
  ramificationSubgroup_antitone A hij

/-- The higher ramification subgroups are normal in the decomposition subgroup. -/
theorem ramificationSubgroup_normal (A : ValuationSubring L) (i : ℕ) :
    (ramificationSubgroup (K := K) A i).Normal := by
  refine ⟨fun σ hσ τ x => ?_⟩
  have h2 : τ • (σ • (τ⁻¹ • x)) - τ • (τ⁻¹ • x) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := by
    have h : (smulRingEquiv A τ) (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈
        IsLocalRing.maximalIdeal A ^ (i + 1) :=
      smul_mem_maximalIdeal_pow A τ (i + 1) (hσ (τ⁻¹ • x))
    rw [map_sub] at h
    simp only [smulRingEquiv_apply] at h
    exact h
  have hx : τ • (τ⁻¹ • x) = x := by rw [← mul_smul, mul_inv_cancel, one_smul]
  have hgoal : (τ * σ * τ⁻¹) • x - x = τ • (σ • (τ⁻¹ • x)) - τ • (τ⁻¹ • x) := by
    rw [hx, ← mul_smul, ← mul_smul]
  rw [hgoal]
  exact h2

instance ramificationSubgroup_normal_inst (A : ValuationSubring L) (i : ℕ) :
    (ramificationSubgroup (K := K) A i).Normal :=
  ramificationSubgroup_normal A i

/-! ## The zeroth subgroup is the inertia subgroup -/

/-- **`G_0` is the inertia subgroup**: the automorphisms acting trivially modulo `𝔪_A` are
exactly those acting trivially on the residue field of `A`. -/
theorem ramificationSubgroup_zero (A : ValuationSubring L) :
    ramificationSubgroup (K := K) A 0 = A.inertiaSubgroup K := by
  ext σ
  rw [mem_ramificationSubgroup_iff, ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker,
    pow_one]
  constructor
  · intro h
    refine RingEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have h2 : σ • IsLocalRing.residue A x = IsLocalRing.residue A x := by
      rw [← IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup K) σ x]
      exact (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A)).mpr (h x)
    simpa using h2
  · intro h x
    have h2 : σ • IsLocalRing.residue A x = IsLocalRing.residue A x := by
      have h1 := DFunLike.congr_fun h (IsLocalRing.residue A x)
      simpa using h1
    rw [← IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup K) σ x] at h2
    exact (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A)).mp h2

/-! ## Triviality of the filtration -/

/-- **The intersection of the higher ramification subgroups is trivial**, provided the
intersection of the powers of the maximal ideal is trivial (Krull's intersection theorem, which
holds for instance for a Noetherian local ring — in particular for a discrete valuation ring). -/
theorem iInf_ramificationSubgroup_eq_bot (A : ValuationSubring L)
    (hA : (⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n) = ⊥) :
    (⨅ i : ℕ, ramificationSubgroup (K := K) A i) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [Subgroup.mem_iInf] at hσ
  have hfix : ∀ x : A, σ • x = x := by
    intro x
    have hmem : σ • x - x ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n) := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n => exact (mem_ramificationSubgroup_iff A n σ).mp (hσ n) x
    rw [hA] at hmem
    simpa using sub_eq_zero.mp hmem
  have hfixL : ∀ x : A, (σ : L ≃ₐ[K] L) (x : L) = (x : L) := by
    intro x
    rw [← coe_smul, hfix x]
  have h1 : (σ : L ≃ₐ[K] L) = 1 := by
    ext y
    change (σ : L ≃ₐ[K] L) y = y
    by_cases hy : y ∈ A
    · exact hfixL ⟨y, hy⟩
    · have hinv : y⁻¹ ∈ A := (A.mem_or_inv_mem y).resolve_left hy
      have h2 := hfixL ⟨y⁻¹, hinv⟩
      calc (σ : L ≃ₐ[K] L) y = (σ : L ≃ₐ[K] L) (y⁻¹)⁻¹ := by rw [inv_inv]
        _ = ((σ : L ≃ₐ[K] L) y⁻¹)⁻¹ := by rw [map_inv₀]
        _ = (y⁻¹)⁻¹ := by rw [h2]
        _ = y := by rw [inv_inv]
  exact Subtype.ext h1

/-- **Every higher ramification subgroup is contained in the inertia subgroup** `G_0`. -/
theorem ramificationSubgroup_le_inertiaSubgroup (A : ValuationSubring L) (i : ℕ) :
    ramificationSubgroup (K := K) A i ≤ A.inertiaSubgroup K := by
  rw [← ramificationSubgroup_zero A]
  exact ramificationSubgroup_antitone A (Nat.zero_le i)

/-- **Membership in `G_i` through the quotient `A ⧸ 𝔪_A^{i+1}`**: `σ ∈ G_i` iff `σ` acts
trivially on `A/𝔪_A^{i+1}`.  This is the definition used in the classical literature. -/
theorem mem_ramificationSubgroup_iff_quotient (A : ValuationSubring L) (i : ℕ)
    (σ : A.decompositionSubgroup K) :
    σ ∈ ramificationSubgroup A i ↔
      ∀ x : A,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (i + 1)) (σ • x) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (i + 1)) x := by
  rw [mem_ramificationSubgroup_iff]
  exact forall_congr' fun x =>
    (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A ^ (i + 1))).symm

end

end NK.Ramification
