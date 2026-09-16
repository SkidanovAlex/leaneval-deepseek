/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ATBridge
import Submission.ZagierHoffmanProof.AFormulaDegree
import Submission.ZagierHoffmanProof.DepthTwo
import Submission.ZagierHoffmanProof.ATIntegral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# Consequences of the Anderson–Thakur ↔ power-sum bridge

The bridge (`ATBridge.psi_CPoly'`) identifies the specialisation of the cleared Anderson–Thakur
coefficients with Carlitz's power-sum sequence.  Two consequences are recorded here:

* the **exact θ-degree** of the specialisation: by `AFormulaDegree.natDegree_A` the degree of
  `A_(n+1)` is `(q-1)q·m*`, where `m* = mStar (n+1)` is the largest index whose binomial coefficient
  does not vanish — so the degree of `ψ(CPoly n)` is `(q-1)q m* + deg ψ(Λ_n)`;
* the bridge in `K∞ = F((1/t))`, using `A_n = [1]^n P_1(n)` (`AExpansion.polyToK_A_eq`), i.e. the
  statement in terms of the depth-one power sums `P_1(n) = ∑_{c∈F}(X+c)^{-n}`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma A_ne_zero (m : ℕ) (hm : 1 ≤ m) : A F m ≠ 0 := by
  intro h
  have h1 := polyToK_A_eq F m hm
  rw [h, map_zero] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h3
  · exact pow_ne_zero m (polyToK_ne_zero F (carlitzOne_ne_zero F)) h2
  · exact P_one_ne_zero F ⟨m, hm⟩ h3

lemma bspec_ne_zero (n : ℕ) : bspec F n ≠ 0 := by
  rw [bspec]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : F[X]) ≠ 0)) (A_ne_zero F (n + 1) (by omega))

lemma natDegree_bspec (n : ℕ) :
    (bspec F n).natDegree = (Nat.card F - 1) * Nat.card F * mStar F (n + 1) := by
  rw [bspec,
    Polynomial.natDegree_mul (pow_ne_zero _ (by norm_num : (-1 : F[X]) ≠ 0))
      (A_ne_zero F (n + 1) (by omega)),
    natDegree_A F (n + 1) (by omega)]
  have h0 : ((-1 : F[X]) ^ (n + 1)).natDegree = 0 := by
    rw [show (-1 : F[X]) = Polynomial.C (-1 : F) by simp, ← Polynomial.C_pow]
    exact Polynomial.natDegree_C _
  rw [h0, zero_add]

/-- ★ The exact degree of the specialisation of the cleared Anderson–Thakur coefficients. -/
theorem natDegree_psi_CPoly (n : ℕ) :
    (psi F (CPoly F n)).natDegree =
      (Nat.card F - 1) * Nat.card F * mStar F (n + 1) + (psi F (LamPoly F n)).natDegree := by
  rw [psi_CPoly' F n,
    Polynomial.natDegree_mul (bspec_ne_zero F n) (psi_LamPoly_ne_zero F n), natDegree_bspec F n]

/-- ★ The bridge in `K∞ = F((1/t))`: the specialisation of the cleared Anderson–Thakur coefficients
is `(-1)^(n+1) [1]^(n+1) P_1(n+1) ψ(Λ_n)`, where `P_1(m) = ∑_{c∈F}(X+c)^{-m}` is the depth-one
power sum. -/
theorem polyToK_psi_CPoly (n : ℕ) :
    polyToK F (psi F (CPoly F n)) =
      (-1 : RatFunc.CompletionAtInfty F) ^ (n + 1) *
        (polyToK F (carlitzOne F)) ^ (n + 1) * P F 1 ⟨n + 1, by omega⟩ *
          polyToK F (psi F (LamPoly F n)) := by
  rw [psi_CPoly' F n, bspec, map_mul, map_mul, map_pow, map_neg, map_one,
    polyToK_A_eq F (n + 1) (by omega)]
  ring

/-- ★★★ The bridge at the special (Chen-)integral indices: for the Anderson–Thakur polynomial
`α_m` at `m = atIndex n N + 1` with `∑_{i<n} N_i ≤ q-1` (the range where Chen's theorem gives
integrality, `ATIntegral.atAlpha_atIndex_mem`), there is an integrality witness `P ∈ A[t]` whose
specialisation at `t ↦ θ^q` is `(-1)^m Γ_m A_m` — Carlitz's power-sum polynomial. -/
theorem atAlpha_atIndex_spec (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    ∃ P : (F[X])[X],
      atAlpha F (atIndex F n N + 1) = algebraMap ((F[X])[X]) (atQ F) P ∧
      psi F P = (-1 : F[X]) ^ (atIndex F n N + 1) *
        carlitzGamma F (atIndex F n N + 1) * A F (atIndex F n N + 1) := by
  obtain ⟨P, hP⟩ := atAlpha_atIndex_mem F n hn N hsum
  refine ⟨P, hP, ?_⟩
  have hm1 : 1 ≤ atIndex F n N + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hA : algebraMap ((F[X])[X]) (atQ F) (LamPoly F (atIndex F n N + 1 - 1) * P) =
      algebraMap ((F[X])[X]) (atQ F)
        (Polynomial.C (carlitzGamma F (atIndex F n N + 1)) *
          CPoly F (atIndex F n N + 1 - 1)) := by
    rw [map_mul, map_mul, ← hP, atAlpha, algebraMap_CPoly_eq F (atIndex F n N + 1 - 1)]
    ring
  have hB : LamPoly F (atIndex F n N + 1 - 1) * P =
      Polynomial.C (carlitzGamma F (atIndex F n N + 1)) *
        CPoly F (atIndex F n N + 1 - 1) :=
    IsFractionRing.injective ((F[X])[X]) (atQ F) hA
  have hC : psi F (LamPoly F (atIndex F n N + 1 - 1)) * psi F P =
      carlitzGamma F (atIndex F n N + 1) *
        (bspec F (atIndex F n N + 1 - 1) * psi F (LamPoly F (atIndex F n N + 1 - 1))) := by
    rw [← map_mul, hB, map_mul, psi_CPoly' F (atIndex F n N + 1 - 1), psi_C]
  have hD : psi F P * psi F (LamPoly F (atIndex F n N + 1 - 1)) =
      (carlitzGamma F (atIndex F n N + 1) * bspec F (atIndex F n N + 1 - 1)) *
        psi F (LamPoly F (atIndex F n N + 1 - 1)) := by
    rw [mul_comm (psi F P), hC, ← mul_assoc]
  have hE := mul_right_cancel₀ (psi_LamPoly_ne_zero F (atIndex F n N + 1 - 1)) hD
  rw [hE, bspec, Nat.sub_add_cancel hm1]
  ring

end ZagierHoffmanPositiveChar

namespace BridgeConsequencesRegression

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

/-- The exact degree of `ψ(CPoly n)` over `F₂` at `n = 1`. -/
example : (psi (ZMod 2) (CPoly (ZMod 2) 1)).natDegree =
    (Nat.card (ZMod 2) - 1) * Nat.card (ZMod 2) * mStar (ZMod 2) 2 +
      (psi (ZMod 2) (LamPoly (ZMod 2) 1)).natDegree :=
  natDegree_psi_CPoly (ZMod 2) 1

/-- The `K∞`-form of the bridge over `F₃` at `n = 2`. -/
example : polyToK (ZMod 3) (psi (ZMod 3) (CPoly (ZMod 3) 2)) =
    (-1 : RatFunc.CompletionAtInfty (ZMod 3)) ^ 3 *
      (polyToK (ZMod 3) (carlitzOne (ZMod 3))) ^ 3 * P (ZMod 3) 1 ⟨3, by norm_num⟩ *
        polyToK (ZMod 3) (psi (ZMod 3) (LamPoly (ZMod 3) 2)) :=
  polyToK_psi_CPoly (ZMod 3) 2

/-- The bridge at the special index `n = 2, N = 0` over `F₂` (`m = 4`). -/
example : ∃ P : ((ZMod 2)[X])[X],
    atAlpha (ZMod 2) (atIndex (ZMod 2) 2 (fun _ => 0) + 1) =
      algebraMap (((ZMod 2)[X])[X]) (atQ (ZMod 2)) P ∧
    psi (ZMod 2) P = (-1 : (ZMod 2)[X]) ^ (atIndex (ZMod 2) 2 (fun _ => 0) + 1) *
      carlitzGamma (ZMod 2) (atIndex (ZMod 2) 2 (fun _ => 0) + 1) *
        A (ZMod 2) (atIndex (ZMod 2) 2 (fun _ => 0) + 1) :=
  atAlpha_atIndex_spec (ZMod 2) 2 (by norm_num) (fun _ => 0) (by simp)

end BridgeConsequencesRegression
