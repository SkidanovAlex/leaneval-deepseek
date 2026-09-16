/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.AExpansion
import Submission.ZagierHoffmanProof.CarlitzAT
import Submission.Commons.Algebra.BigOperators.prod_range_ite

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Psi

/-- The specialisation `t ↦ θ^q` of `A[t] = (F[X])[X]` into `A = F[X]` (`θ ↦ θ`, `t ↦ θ^q`). -/
noncomputable def psi : (F[X])[X] →+* F[X] :=
  Polynomial.eval₂RingHom (RingHom.id (F[X])) ((Polynomial.X : F[X]) ^ Nat.card F)

lemma psi_apply (p : (F[X])[X]) :
    psi F p = Polynomial.eval₂ (RingHom.id (F[X])) ((Polynomial.X : F[X]) ^ Nat.card F) p :=
  rfl

@[simp] lemma psi_C (p : F[X]) : psi F (Polynomial.C p) = p := by
  rw [psi_apply, Polynomial.eval₂_C, RingHom.id_apply]

@[simp] lemma psi_X : psi F (Polynomial.X : (F[X])[X]) = (Polynomial.X : F[X]) ^ Nat.card F := by
  rw [psi_apply, Polynomial.eval₂_X]

lemma psi_natCast (n : ℕ) : psi F (n : (F[X])[X]) = (n : F[X]) := by
  rw [show ((n : (F[X])[X])) = Polynomial.C (n : F[X]) by simp, psi_C]

/-- `ψ` sends `θ^k` (the constant `X^k`) to itself. -/
lemma psi_theta (k : ℕ) : psi F (Polynomial.C ((Polynomial.X : F[X]) ^ k)) =
    (Polynomial.X : F[X]) ^ k := by
  rw [psi_C]

/-- The polynomial model of `γ_j = ∏_{ℓ=1}^{j}(θ ^ (q^j) - t ^ (q^ℓ))`. -/
noncomputable def atGammaPoly (j : ℕ) : (F[X])[X] :=
  ∏ l ∈ Finset.Icc 1 j,
    (Polynomial.C ((Polynomial.X : F[X]) ^ (Nat.card F ^ j)) -
      (Polynomial.X : (F[X])[X]) ^ (Nat.card F ^ l))

lemma atTheta_pow (k : ℕ) :
    (atTheta F) ^ k =
      algebraMap ((F[X])[X]) (atQ F) (Polynomial.C ((Polynomial.X : F[X]) ^ k)) := by
  rw [atTheta, ← map_pow, ← Polynomial.C_pow]

lemma atT_pow (k : ℕ) :
    (atT F) ^ k =
      algebraMap ((F[X])[X]) (atQ F) ((Polynomial.X : (F[X])[X]) ^ k) := by
  rw [atT, ← map_pow]

/-- `γ_j` is the image of `atGammaPoly j` in `F(θ,t)`. -/
lemma atGamma_eq_algebraMap (j : ℕ) :
    atGamma F j = algebraMap ((F[X])[X]) (atQ F) (atGammaPoly F j) := by
  rw [atGammaPoly, atGamma, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_sub, ← atTheta_pow, ← atT_pow]

/-- The polynomial model of the Carlitz factorial `D_j`. -/
noncomputable def atDpoly (j : ℕ) : (F[X])[X] := Polynomial.C (carlitzFact F j)

lemma atD_eq_algebraMap (j : ℕ) :
    atD F j = algebraMap ((F[X])[X]) (atQ F) (atDpoly F j) := rfl

lemma atDpoly_ne_zero (j : ℕ) : atDpoly F j ≠ 0 :=
  Polynomial.C_ne_zero.mpr (carlitzFact_ne_zero F j)

@[simp] lemma atDpoly_zero : atDpoly F 0 = 1 := by
  rw [atDpoly, carlitzFact_zero, Polynomial.C_1]

@[simp] lemma psi_atDpoly (j : ℕ) : psi F (atDpoly F j) = carlitzFact F j := by
  rw [atDpoly, psi_C]

@[simp] lemma psi_atGammaPoly_zero : psi F (atGammaPoly F 0) = 1 := by
  rw [atGammaPoly]; simp

lemma psi_atGammaPoly_one : psi F (atGammaPoly F 1) = -(carlitzOne F) ^ Nat.card F := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  rw [atGammaPoly, pow_one, Finset.Icc_self, Finset.prod_singleton, map_sub, psi_C, map_pow,
    psi_X, pow_one]
  rw [carlitzOne, sub_pow_card]
  ring

lemma psi_atGammaPoly_eq_zero (j : ℕ) (hj : 2 ≤ j) : psi F (atGammaPoly F j) = 0 := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  rw [atGammaPoly, map_prod]
  refine Finset.prod_eq_zero
    (Finset.mem_Icc.mpr ⟨Nat.le_sub_one_of_lt (show 1 < j by omega), Nat.sub_le j 1⟩) ?_
  rw [map_sub, psi_C, map_pow, psi_X]
  have hmul : Nat.card F * Nat.card F ^ (j - 1) = Nat.card F ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  have hpow : ((Polynomial.X : F[X]) ^ Nat.card F) ^ (Nat.card F ^ (j - 1)) =
      (Polynomial.X : F[X]) ^ (Nat.card F ^ j) := by
    rw [← pow_mul, hmul]
  rw [hpow, sub_self]

end Psi


section Clearing

private lemma prod_range_ite'' {M : Type*} [CommMonoid M] (f : ℕ → M) (m N : ℕ) (h : m ≤ N) :
    (∏ i ∈ Finset.range N, (if i < m then f i else 1)) = ∏ i ∈ Finset.range m, f i := by
  rw [Commons.Algebra.BigOperators.prod_range_ite f m N, Nat.min_eq_left h]

/-- The clearing factor `Λ_n = ∏_{i ≤ n} D_i^(n+1)`. -/
noncomputable def LamPoly (n : ℕ) : (F[X])[X] :=
  ∏ i ∈ Finset.range (n + 1), (atDpoly F i) ^ (n + 1)

/-- The quotient `Λ_n / (Λ_{n-q^j} · D_j)`, written as a product of powers. -/
noncomputable def Mpoly (n j : ℕ) : (F[X])[X] :=
  ∏ i ∈ Finset.range (n + 1),
    (atDpoly F i) ^ ((if i < n - Nat.card F ^ j + 1 then Nat.card F ^ j else n + 1) -
      (if i = j then 1 else 0))

lemma card_pow_pos (j : ℕ) : 0 < Nat.card F ^ j := pow_pos (by have := card_ge_two F; omega) j

lemma card_pow_le_one_add (j : ℕ) : Nat.card F ^ j ≥ j + 1 := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  calc Nat.card F ^ j ≥ 2 ^ j := Nat.pow_le_pow_left hq j
    _ ≥ j + 1 := by
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ]; omega

lemma le_of_card_pow_le {j n : ℕ} (h : Nat.card F ^ j ≤ n) : j ≤ n :=
  le_trans (Nat.le_succ j |>.trans (card_pow_le_one_add F j)) h

private lemma pow_ite {R : Type*} [Monoid R] (D : R) (c : Prop) [Decidable c] (a : ℕ) :
    (if c then D ^ a else 1) = D ^ (if c then a else 0) := by
  by_cases h : c <;> simp [h]

private lemma ite_pow_one {R : Type*} [Monoid R] (D : R) (c : Prop) [Decidable c] :
    (if c then D else 1) = D ^ (if c then 1 else 0) := by
  by_cases h : c <;> simp [h]

private lemma eq_prod_ite {M : Type*} [CommMonoid M] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b : ι → M) (a : ι) (ha : a ∈ s) :
    b a = ∏ x ∈ s, (if x = a then b x else 1) := by
  rw [Finset.prod_ite_eq' s a b, if_pos ha]

private lemma exp_key (n j i : ℕ) (hj : Nat.card F ^ j ≤ n) (hq1 : 1 ≤ Nat.card F ^ j) :
    (if i < n - Nat.card F ^ j + 1 then n - Nat.card F ^ j + 1 else 0) +
        (if i = j then 1 else 0) +
        ((if i < n - Nat.card F ^ j + 1 then Nat.card F ^ j else n + 1) -
          (if i = j then 1 else 0)) = n + 1 := by
  split_ifs <;> omega

/-- ★ The clearing factorisation: `Λ_n = Λ_{n-q^j} · D_j · M(n,j)` for `q^j ≤ n`. -/
lemma LamPoly_eq_mul (n j : ℕ) (hj : Nat.card F ^ j ≤ n) :
    LamPoly F n = LamPoly F (n - Nat.card F ^ j) * atDpoly F j * Mpoly F n j := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hq1 : 1 ≤ Nat.card F ^ j := card_pow_pos F j
  have hmem : j ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (by have := le_of_card_pow_le F hj; omega)
  have hmN : n - Nat.card F ^ j + 1 ≤ n + 1 := by omega
  unfold LamPoly Mpoly
  rw [← prod_range_ite'' _ _ _ hmN,
    eq_prod_ite (Finset.range (n + 1)) (fun i => atDpoly F i) j hmem,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_ite, ite_pow_one, ← pow_add, ← pow_add, exp_key F n j i hj hq1]

end Clearing


section CPoly

/-- The cleared Anderson–Thakur coefficients: `CPoly n = Λ_n · c_n`, defined by the same
recursion as `atCoeff` with the denominators cleared. -/
noncomputable def CPoly (n : ℕ) : (F[X])[X] :=
  Nat.strongRecOn n fun m ih =>
    if hm : m = 0 then 1 else
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m),
        atGammaPoly F j * Mpoly F m j * ih (m - Nat.card F ^ j) (by
          have h1 : 0 < Nat.card F ^ j := card_pow_pos F j
          exact Nat.sub_lt (Nat.pos_of_ne_zero hm) h1)

lemma CPoly_zero : CPoly F 0 = 1 := by
  rw [CPoly, Nat.strongRecOn_eq]
  simp

lemma CPoly_succ {m : ℕ} (hm : m ≠ 0) :
    CPoly F m =
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m),
        atGammaPoly F j * Mpoly F m j * CPoly F (m - Nat.card F ^ j) := by
  conv_lhs => rw [CPoly, Nat.strongRecOn_eq]
  simp only [dif_neg hm]
  rfl

/-- ★★ `CPoly n` is the clearing of `atCoeff n`: `↑(CPoly n) = ↑(Λ n) · c_n` in `F(θ,t)`. -/
lemma algebraMap_CPoly_eq (n : ℕ) :
    algebraMap ((F[X])[X]) (atQ F) (CPoly F n) =
      algebraMap ((F[X])[X]) (atQ F) (LamPoly F n) * atCoeff F n := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [CPoly_zero, atCoeff_zero, map_one]
      rw [show LamPoly (F := F) 0 = 1 by
        rw [LamPoly, Finset.range_one, Finset.prod_singleton, atDpoly_zero, one_pow]]
      rw [map_one, one_mul]
    · have hm : m ≠ 0 := Nat.pos_iff_ne_zero.mp h
      rw [CPoly_succ F hm, map_sum, atCoeff_succ F hm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨-, hjq⟩ := hj
      have hD0 : algebraMap ((F[X])[X]) (atQ F) (atDpoly F j) ≠ 0 := by
        rw [← atD_eq_algebraMap]; exact atD_ne_zero F j
      have hfac := congrArg (algebraMap ((F[X])[X]) (atQ F)) (LamPoly_eq_mul F m j hjq)
      simp only [map_mul] at hfac
      rw [map_mul, map_mul, ih (m - Nat.card F ^ j) (by
        have h1 : 0 < Nat.card F ^ j := card_pow_pos F j
        exact Nat.sub_lt (Nat.pos_of_ne_zero hm) h1), hfac, ← atGamma_eq_algebraMap F j]
      rw [atD_eq_algebraMap F j]
      field_simp

end CPoly

section Bspec

variable [DecidableEq (RatFunc F)]

/-- The specialisation of the Anderson–Thakur coefficient sequence: `b_n = (-1)^(n+1) A_(n+1)`. -/
noncomputable def bspec (n : ℕ) : F[X] := (-1 : F[X]) ^ (n + 1) * A F (n + 1)

@[simp] lemma bspec_zero : bspec F 0 = 1 := by
  rw [bspec, pow_one, A_one_eq_neg_one F]
  ring

/-- `(-1)^q = -1` in `F[X]` for a finite field `F` of cardinality `q`. -/
lemma neg_one_pow_card : (-1 : F[X]) ^ Nat.card F = -1 := by
  have hF : (-1 : F) ^ Nat.card F = -1 := by
    letI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card (-1)
  rw [show (-1 : F[X]) = Polynomial.C (-1 : F) by simp, ← Polynomial.C_pow, hF]

/-- ★ The recursion satisfied by the specialisation: for `m ≥ q`,
`b_m = b_(m-1) - [1]^(q-1) b_(m-q)`. -/
lemma bspec_succ (m : ℕ) (hm : Nat.card F ≤ m) :
    bspec F m = bspec F (m - 1) - (carlitzOne F) ^ (Nat.card F - 1) * bspec F (m - Nat.card F) := by
  have hneg := neg_one_pow_card F
  have hm1q : 1 ≤ m := le_trans (by have := card_ge_two F; omega) hm
  have hd : (-1 : F[X]) ^ (m + 1 - Nat.card F) = -((-1 : F[X]) ^ (m + 1)) := by
    have hsum : (m + 1 - Nat.card F) + Nat.card F = m + 1 :=
      Nat.sub_add_cancel (by omega)
    have h : (-1 : F[X]) ^ (m + 1 - Nat.card F) * (-1) ^ Nat.card F = (-1) ^ (m + 1) := by
      rw [← pow_add, hsum]
    rw [hneg, mul_neg_one] at h
    have h2 := congrArg Neg.neg h
    rwa [neg_neg] at h2
  have hm1 : (-1 : F[X]) ^ m = -((-1 : F[X]) ^ (m + 1)) := by
    rw [pow_succ]
    ring
  rw [bspec, bspec, bspec,
    show m - 1 + 1 = m by omega, show m - Nat.card F + 1 = m + 1 - Nat.card F by omega, hd, hm1]
  have hA := A_recursion F (m + 1) (by omega)
  rw [show m + 1 - 1 = m by omega] at hA
  linear_combination ((-1 : F[X]) ^ (m + 1)) * hA

/-- For `1 ≤ m < q` the recursion degenerates to `b_m = b_(m-1)`. -/
lemma bspec_low (m : ℕ) (hm1 : 1 ≤ m) (hmq : m < Nat.card F) :
    bspec F m = bspec F (m - 1) := by
  have h1 : A F (m + 1) = (-1 : F[X]) ^ (m + 1) :=
    A_eq_neg_one_pow F (m + 1) (by omega) (by omega)
  have h2 : A F m = (-1 : F[X]) ^ m := A_eq_neg_one_pow F m hm1 (by omega)
  rw [bspec, bspec, show m - 1 + 1 = m by omega, h1, h2,
    show (-1 : F[X]) ^ (m + 1) = -(-1) ^ m by rw [pow_succ]; ring]
  ring

end Bspec

section Bridge

variable [DecidableEq (RatFunc F)]

/-- The composite of the specialisation `ψ` with the coercion into the fraction field. -/
noncomputable def Psi : (F[X])[X] →+* RatFunc F :=
  (algebraMap F[X] (RatFunc F)).comp (psi F)

lemma Psi_apply (p : (F[X])[X]) : Psi F p = algebraMap F[X] (RatFunc F) (psi F p) := rfl

lemma carlitzOne_ne_zero : carlitzOne F ≠ 0 := by
  intro h
  have hd := carlitzOne_natDegree F
  rw [h, Polynomial.natDegree_zero] at hd
  have := card_ge_two F
  omega

lemma carlitzFact_one : carlitzFact F 1 = carlitzOne F := by
  rw [carlitzFact_succ F 0, carlitzFact_zero, one_pow, one_mul, Nat.zero_add,
    show carlitzBracket F 1 = carlitzOne F by rw [carlitzBracket, carlitzOne, pow_one]]

lemma Psi_atGammaPoly_zero : Psi F (atGammaPoly F 0) = 1 := by
  rw [Psi_apply, psi_atGammaPoly_zero, map_one]

lemma Psi_atDpoly_zero : Psi F (atDpoly F 0) = 1 := by
  rw [Psi_apply, psi_atDpoly, carlitzFact_zero, map_one]

lemma Psi_atGammaPoly_eq_zero (j : ℕ) (hj : 2 ≤ j) : Psi F (atGammaPoly F j) = 0 := by
  rw [Psi_apply, psi_atGammaPoly_eq_zero F j hj, map_zero]

lemma Psi_atDpoly_ne_zero (j : ℕ) : Psi F (atDpoly F j) ≠ 0 := by
  rw [Psi_apply, psi_atDpoly]
  exact fun h => carlitzFact_ne_zero F j (RatFunc.algebraMap_injective F (by rw [h, map_zero]))

/-- The `j = 1` factor of the specialisation: `ψ(γ_1)/ψ(D_1) = -[1]^(q-1)`. -/
lemma key_one :
    Psi F (atGammaPoly F 1) * (Psi F (atDpoly F 1))⁻¹ =
      -algebraMap F[X] (RatFunc F) ((carlitzOne F) ^ (Nat.card F - 1)) := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hAne : algebraMap F[X] (RatFunc F) (carlitzOne F) ≠ 0 := by
    intro h
    exact carlitzOne_ne_zero F (RatFunc.algebraMap_injective F (by rw [h, map_zero]))
  rw [Psi_apply, psi_atGammaPoly_one, Psi_apply, psi_atDpoly, carlitzFact_one,
    map_neg, map_pow, map_pow]
  have hq : Nat.card F = (Nat.card F - 1) + 1 := by omega
  conv_lhs => rw [hq, pow_succ']
  field_simp

/-- The `j = 0` factor of the specialisation: `ψ(γ_0)/ψ(D_0) = 1`. -/
lemma key_zero :
    Psi F (atGammaPoly F 0) * (Psi F (atDpoly F 0))⁻¹ = 1 := by
  rw [Psi_atGammaPoly_zero, Psi_atDpoly_zero, inv_one, mul_one]

/-- ★ `ψ(M(n,j)) · ψ(Λ_(n-q^j)) = ψ(Λ_n)/ψ(D_j)`. -/
lemma Psi_Mpoly_mul (m j : ℕ) (hjq : Nat.card F ^ j ≤ m) :
    Psi F (Mpoly F m j) * Psi F (LamPoly F (m - Nat.card F ^ j)) =
      Psi F (LamPoly F m) * (Psi F (atDpoly F j))⁻¹ := by
  have hfac := congrArg (Psi F) (LamPoly_eq_mul F m j hjq)
  simp only [map_mul] at hfac
  rw [eq_mul_inv_iff_mul_eq₀ (Psi_atDpoly_ne_zero F j), hfac]
  ring

end Bridge

section MainBridge

variable [DecidableEq (RatFunc F)]

/-- ★★★ The specialisation of the cleared Anderson–Thakur coefficients is Carlitz's
power-sum sequence: `ψ(CPoly n) = (-1)^(n+1) A_(n+1) · ψ(Λ n)` in `F(θ,t)`'s fraction field. -/
theorem psi_CPoly (n : ℕ) :
    Psi F (CPoly F n) = algebraMap F[X] (RatFunc F) (bspec F n) * Psi F (LamPoly F n) := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [CPoly_zero, bspec_zero]
      rw [show LamPoly (F := F) 0 = 1 from by
        rw [LamPoly, Finset.range_one, Finset.prod_singleton, atDpoly_zero, one_pow]]
      simp
    · have hm : m ≠ 0 := Nat.pos_iff_ne_zero.mp h
      have hstep : Psi F (CPoly F m) =
          ∑ j ∈ (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m),
            (Psi F (atGammaPoly F j) * (Psi F (atDpoly F j))⁻¹ *
              algebraMap F[X] (RatFunc F) (bspec F (m - Nat.card F ^ j))) *
            Psi F (LamPoly F m) := by
        rw [CPoly_succ F hm, map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_filter, Finset.mem_range] at hj
        obtain ⟨-, hjq⟩ := hj
        rw [map_mul, map_mul, ih (m - Nat.card F ^ j)
            (Nat.sub_lt (Nat.pos_of_ne_zero hm) (card_pow_pos F j))]
        have h1 := Psi_Mpoly_mul F m j hjq
        linear_combination (Psi F (atGammaPoly F j) *
          algebraMap F[X] (RatFunc F) (bspec F (m - Nat.card F ^ j))) * h1
      rw [hstep, ← Finset.sum_mul]
      congr 1
      by_cases hmq : Nat.card F ≤ m
      · have hsub : ({0, 1} : Finset ℕ) ⊆
            (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m) := by
          intro x hx
          rw [Finset.mem_filter, Finset.mem_range]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨by omega, by rw [pow_zero]; omega⟩
          · exact ⟨by omega, by rw [pow_one]; exact hmq⟩
        rw [← Finset.sum_subset hsub (fun x hx hxnot => by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
              rw [Psi_atGammaPoly_eq_zero F x (by omega), zero_mul, zero_mul]),
            Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
        rw [pow_zero, pow_one, key_zero, key_one, one_mul, bspec_succ F m hmq,
          map_sub, map_mul, neg_mul]
        ring
      · have hS : (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m) = {0} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨-, hxq⟩
            by_contra hx0
            have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
            have hle : Nat.card F ≤ Nat.card F ^ x := by
              conv_lhs => rw [← pow_one (Nat.card F)]
              exact Nat.pow_le_pow_right (by have := card_ge_two F; omega) hx1
            omega
          · rintro rfl
            exact ⟨by omega, by rw [pow_zero]; omega⟩
        rw [hS, Finset.sum_singleton, pow_zero, key_zero, one_mul,
          bspec_low F m h (by omega)]

/-- ★★★ The bridge in `F[X]`. -/
theorem psi_CPoly' (n : ℕ) :
    psi F (CPoly F n) = bspec F n * psi F (LamPoly F n) := by
  refine RatFunc.algebraMap_injective F ?_
  rw [map_mul]
  simpa [Psi] using psi_CPoly F n

@[simp] lemma LamPoly_zero : LamPoly F 0 = 1 := by
  rw [LamPoly, Finset.range_one, Finset.prod_singleton, atDpoly_zero, one_pow]

/-- ★★★ The bridge, stated for the Anderson–Thakur coefficients themselves: the clearing
`Λ_n · c_n` of `c_n` specialises to `(-1)^(n+1) A_(n+1) · ψ(Λ_n)`. -/
theorem psi_cleared_atCoeff (n : ℕ) :
    psi F (CPoly F n) = (-1 : F[X]) ^ (n + 1) * A F (n + 1) * psi F (LamPoly F n) :=
  psi_CPoly' F n

/-- `Λ_n · c_n` is the image of the polynomial `CPoly n`. -/
theorem LamPoly_mul_atCoeff (n : ℕ) :
    (algebraMap ((F[X])[X]) (atQ F) (LamPoly F n)) * atCoeff F n =
      algebraMap ((F[X])[X]) (atQ F) (CPoly F n) :=
  (algebraMap_CPoly_eq F n).symm

/-- `ψ(Λ_n) ≠ 0`: the clearing factor does not vanish under the specialisation. -/
lemma psi_LamPoly_ne_zero (n : ℕ) : psi F (LamPoly F n) ≠ 0 := by
  rw [LamPoly, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [map_pow, psi_atDpoly]
  exact pow_ne_zero _ (carlitzFact_ne_zero F i)

end MainBridge

end ZagierHoffmanPositiveChar
