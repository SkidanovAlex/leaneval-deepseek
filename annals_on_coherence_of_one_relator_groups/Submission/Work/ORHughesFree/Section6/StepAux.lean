/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary lemmas for the construction of the induction environment `Thm61Step`

* `normal_conj_zpow`: conjugation of `N ⊴ H` by the powers of `t`;
* `decomp_of_sup`: from `H = N ⊔ ⟨t⟩` to the normal form `h = n t^k`;
* `uUnitN`: the unit `φ(t)` of `U_N`, and the formula for the twist `τ` on `U_N` in terms of its
  powers (the hypothesis `hact` of `exists_theta`, and the equivariance input for the
  coefficientwise map `K[N][t^{±1};τ] → U_N[t^{±1};τ]`).
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.ConjKN
import Submission.Work.Section6.StepA
import Submission.Work.ORHughesFree.Section6.StarSkewL
import Submission.Work.ORHughesFree.Section6.skewMonoidAlgebra_mapRingHom

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree
open Work.Section6

variable {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H} {t : H}
variable {U : Type} [Ring U] [StarRing U] [IsStarRegular U]

/-- Conjugation by the powers of `t` preserves a normal subgroup `N ⊴ H`. -/
theorem normal_conj_zpow (hN : N.Normal) (k : ℤ) (n : N) :
    t ^ k * (n : H) * t ^ (-k) ∈ N := by
  induction k using Int.induction_on with
  | zero => simpa using n.2
  | succ i ih =>
      have heq : t ^ ((i : ℤ) + 1) * (n : H) * t ^ (-((i : ℤ) + 1)) =
          t * (t ^ (i : ℤ) * (n : H) * t ^ (-(i : ℤ))) * t⁻¹ := by
        rw [zpow_add_one, zpow_neg, zpow_add_one]
        group
      rw [heq]
      exact hN.conj_mem _ ih t
  | pred i ih =>
      have heq : t ^ (-(i : ℤ) - 1) * (n : H) * t ^ (-(-(i : ℤ) - 1)) =
          t⁻¹ * (t ^ (-(i : ℤ)) * (n : H) * t ^ (-(-(i : ℤ)))) * t := by
        group
      rw [heq]
      exact hN.conj_mem' _ ih t

/-- The normal form `h = n t^k` of the elements of `H = N ⊔ ⟨t⟩` for `N ⊴ H`. -/
theorem decomp_of_sup (hN : N.Normal)
    (htop : (⊤ : Subgroup H) = N ⊔ Subgroup.closure ({t} : Set H)) :
    ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k := by
  intro h
  have hmem : h ∈ N ⊔ Subgroup.closure ({t} : Set H) := by rw [← htop]; exact Subgroup.mem_top h
  -- the set of normal forms is a subgroup
  let S : Subgroup H :=
    { carrier := {x : H | ∃ (n : N) (k : ℤ), x = (n : H) * t ^ k}
      one_mem' := ⟨1, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨n₁, k₁, rfl⟩ ⟨n₂, k₂, rfl⟩
        refine ⟨n₁ * ⟨t ^ k₁ * (n₂ : H) * t ^ (-k₁), normal_conj_zpow hN k₁ n₂⟩, k₁ + k₂, ?_⟩
        simp only [Subgroup.coe_mul]
        group
      inv_mem' := by
        rintro x ⟨n, k, rfl⟩
        refine ⟨⟨t ^ (-k) * (n : H)⁻¹ * t ^ (-(-k)), normal_conj_zpow hN (-k) n⁻¹⟩, -k, ?_⟩
        simp only [Subgroup.coe_mul, Subtype.coe_mk, mul_inv_rev, ← zpow_neg]
        group }
  have hNle : N ≤ S := fun n hn => ⟨⟨n, hn⟩, 0, by simp⟩
  have htle : Subgroup.closure ({t} : Set H) ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨1, 1, by simp⟩
  have := sup_le hNle htle hmem
  exact this

/-- The powers of the inner automorphism `conjUN` are conjugation by the powers of `φ(t)`. -/
theorem conjUN_zpow_apply (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (k : ℤ) (x : UNty φ H N) :
    (((conjUN φ H N hN t hstar) ^ k) x : U) =
      ((uUnit φ H t ^ k : Uˣ) : U) * (x : U) * (((uUnit φ H t ^ (-k) : Uˣ)) : U) := by
  have hbase : ∀ x : UNty φ H N,
      (((conjUN φ H N hN t hstar) ^ (0 : ℤ)) x : U) =
        ((uUnit φ H t ^ (0 : ℤ) : Uˣ) : U) * (x : U) *
          (((uUnit φ H t) ^ (-(0 : ℤ)) : Uˣ)) := by
    intro x
    rw [zpow_zero]
    simp
  have hsucc : ∀ (i : ℕ), (∀ x : UNty φ H N,
      (((conjUN φ H N hN t hstar) ^ (i : ℤ)) x : U) =
        ((uUnit φ H t ^ (i : ℤ) : Uˣ) : U) * (x : U) *
          (((uUnit φ H t) ^ (-(i : ℤ)) : Uˣ))) →
      ∀ x : UNty φ H N,
        (((conjUN φ H N hN t hstar) ^ ((i : ℤ) + 1)) x : U) =
          ((uUnit φ H t ^ ((i : ℤ) + 1) : Uˣ) : U) * (x : U) *
            (((uUnit φ H t) ^ (-((i : ℤ) + 1)) : Uˣ)) := by
    intro i ih x
    rw [zpow_add_one (conjUN φ H N hN t hstar) (i : ℤ)]
    show (((conjUN φ H N hN t hstar) ^ (i : ℤ))
      ((conjUN φ H N hN t hstar) x) : U) = _
    rw [ih ((conjUN φ H N hN t hstar) x), conjUN_apply]
    have h1 : (uUnit φ H t) ^ ((i : ℤ) + 1) = (uUnit φ H t) ^ (i : ℤ) * uUnit φ H t :=
      zpow_add_one _ _
    have h2 : (uUnit φ H t) ^ (-((i : ℤ) + 1)) =
        (uUnit φ H t)⁻¹ * (uUnit φ H t) ^ (-(i : ℤ)) := by
      rw [show -((i : ℤ) + 1) = (-1) + (-(i : ℤ)) from by ring, zpow_add, zpow_neg_one]
    rw [h1, h2, Units.val_mul, Units.val_mul]
    group
  have hpred : ∀ (i : ℕ), (∀ x : UNty φ H N,
      (((conjUN φ H N hN t hstar) ^ (-(i : ℤ))) x : U) =
        ((uUnit φ H t ^ (-(i : ℤ)) : Uˣ) : U) * (x : U) *
          (((uUnit φ H t) ^ (-(-(i : ℤ))) : Uˣ))) →
      ∀ x : UNty φ H N,
        (((conjUN φ H N hN t hstar) ^ (-(i : ℤ) - 1)) x : U) =
          ((uUnit φ H t ^ (-(i : ℤ) - 1) : Uˣ) : U) * (x : U) *
            (((uUnit φ H t) ^ (-(-(i : ℤ) - 1)) : Uˣ)) := by
    intro i ih x
    rw [zpow_sub_one (conjUN φ H N hN t hstar) (-(i : ℤ))]
    show (((conjUN φ H N hN t hstar) ^ (-(i : ℤ)))
      (((conjUN φ H N hN t hstar)⁻¹) x) : U) = _
    rw [show (((conjUN φ H N hN t hstar)⁻¹) x : UNty φ H N) =
        (conjUN φ H N hN t hstar).symm x from rfl]
    rw [ih ((conjUN φ H N hN t hstar).symm x), conjUN_symm_apply]
    have h1 : (uUnit φ H t) ^ (-(i : ℤ) - 1) = (uUnit φ H t) ^ (-(i : ℤ)) * (uUnit φ H t)⁻¹ :=
      zpow_sub_one _ _
    have h2 : (uUnit φ H t) ^ (-(-(i : ℤ) - 1)) = uUnit φ H t * (uUnit φ H t) ^ (i : ℤ) := by
      rw [show -(-(i : ℤ) - 1) = (1 : ℤ) + (i : ℤ) from by ring, zpow_add, zpow_one]
    rw [h1, h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, neg_neg]
    group
  revert x
  refine Int.induction_on k ?_ ?_ ?_
  · exact hbase
  · intro i ih
    exact hsucc i ih
  · intro i ih
    exact hpred i ih

/-- The twist on `U_N` is conjugation by the powers of `φ(t)`, at the level of `U`. -/
theorem tauAction_smulU (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (N : Subgroup H)
    (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (k : ℤ) (x : UNty φ H N) :
    letI := tauAction φ H N hN t hstar
    (((Multiplicative.ofAdd k) • x : UNty φ H N) : U) =
      ((uUnit φ H t ^ k : Uˣ) : U) * (x : U) * (((uUnit φ H t) ^ (-k) : Uˣ) : U) := by
  letI := tauAction φ H N hN t hstar
  rw [tauAction_smul_eq φ H N hN t hstar k x, conjUN_zpow_apply φ H N hN t hstar k x]

end Work.ORHughesFree.Section6
