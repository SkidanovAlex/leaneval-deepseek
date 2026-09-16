/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.StepL201
import Submission.ZagierHoffmanProof.ShuffleGen
import Submission.ZagierHoffmanProof.StepL193

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
open scoped BigOperators WithZero

/-!
# The MZV space is stable under Frobenius

`StepL201` proves Thakur's Frobenius relation at level one, `ζ_A(q·𝔰) = ζ_A(𝔰)^q` (the `q`-th
power map, `q = |F|`, is the Frobenius of `K∞ = F_q((1/t))`).  This module upgrades it to the whole
weight space:

  ★★★ `frobenius_mem_Z (hx : x ∈ 𝒵 w) : x ^ q ∈ 𝒵 (w · q)`.

Equivalently: the Frobenius map `x ↦ x^q` sends the weight-`w` MZV space into the weight-`wq` one,
i.e. it multiplies the weight by `q`.  (The spaces are *not* Frobenius-invariant: the Frobenius
changes the weight, so the MZV algebra is an `F_q`-algebra with a "twisted" Frobenius action.)

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The weight of the `q`-scaled tuple is `q` times the weight. -/
lemma weight_scaleTuple {r : ℕ} (𝔰 : Fin r → ℕ+) :
    weight r (scaleTuple F 𝔰) = Nat.card F * weight r 𝔰 := by
  rw [weight, weight, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact PNat.mul_coe _ _

/-- ★★★ **Frobenius stability of the MZV space**: `x ↦ x^q` maps the weight-`w` space into the
weight-`wq` space. -/
theorem frobenius_mem_Z {w : ℕ} {x : RatFunc.CompletionAtInfty F} (hx : x ∈ 𝒵 F w) :
    x ^ Nat.card F ∈ 𝒵 F (w * Nat.card F) := by
  classical
  have hq : Nat.card F ≠ 0 := by have := card_ge_two F; omega
  rw [𝒵] at hx
  refine Submodule.span_induction
    (p := fun x _ => x ^ Nat.card F ∈ 𝒵 F (w * Nat.card F)) ?_ ?_ ?_ ?_ hx
  · rintro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨r, hxr⟩ := hx
    rw [ζ_A_weight_mem_iff F w r] at hxr
    obtain ⟨𝔰, h𝔰w, rfl⟩ := hxr
    have hw : weight r 𝔰 = w := h𝔰w
    rcases Nat.eq_zero_or_pos r with h0 | hr
    · subst h0
      rw [zeta_A_fin_zero F 𝔰, one_pow]
      have hw0 : w = 0 := by
        have h : weight 0 𝔰 = 0 := by simp [weight]
        exact hw.symm.trans h
      rw [hw0, Nat.zero_mul, ← zeta_A_fin_zero F 𝔰]
      exact zeta_mem_Z F 𝔰 rfl
    · rw [← zeta_frobenius F hr 𝔰]
      refine zeta_mem_Z F (scaleTuple F 𝔰) ?_
      rw [weight_scaleTuple, hw, Nat.mul_comm]
  · rw [zero_pow hq]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [add_pow_natCard]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have hpow : (c • a) ^ Nat.card F = (c ^ Nat.card F) • (a ^ Nat.card F) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow]
    rw [hpow]
    exact Submodule.smul_mem _ _ ha

/-- Iterating Frobenius: `x ^ (q^k) ∈ 𝒵 (w · q^k)`. -/
theorem frobenius_iter_mem_Z (k : ℕ) {w : ℕ} {x : RatFunc.CompletionAtInfty F}
    (hx : x ∈ 𝒵 F w) : x ^ (Nat.card F ^ k) ∈ 𝒵 F (w * Nat.card F ^ k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      have h := frobenius_mem_Z F ih
      rw [← pow_mul, ← pow_succ, mul_assoc, ← pow_succ] at h
      exact h

/-- The Frobenius action on the Hoffman spanning sets. -/
theorem frobenius_mem_span_T {w : ℕ} (hw : 1 ≤ w) {x : RatFunc.CompletionAtInfty F}
    (hx : x ∈ Submodule.span (RatFunc F) (𝒯 F w)) :
    x ^ Nat.card F ∈ Submodule.span (RatFunc F) (𝒯 F (w * Nat.card F)) := by
  rw [← theoremA_span_amb F w hw] at hx
  rw [← theoremA_span_amb F (w * Nat.card F) (Nat.mul_pos (by omega) (by have := card_ge_two F; omega))]
  exact frobenius_mem_Z F hx

end ZagierHoffmanPositiveChar