/-
Copyright (c) 2024. All rights reserved.

# A lower bound for the size of a non-zero invariant subspace

If `σ` is semiregular on `V ∖ {0}` and has order `2 ^ n - 1`, then every non-zero `σ`-invariant
subspace `U` contains the `2 ^ n - 1` distinct non-zero elements `σ ^ k u` (`k < 2 ^ n - 1`) of the
orbit of a non-zero `u ∈ U`, together with `0`; hence `2 ^ n ≤ |U|`.
-/

import Mathlib
import Submission.Work.Higman.Layers.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman.Layers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- If `orderOf σ = 2 ^ n - 1` then `σ ^ (2 ^ n - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hord : orderOf σ = 2 ^ n - 1) :
    σ ^ (2 ^ n - 1) = 1 := by
  rw [← hord]
  exact pow_orderOf_eq_one σ

/-- `(σ ^ (a + b)) x = (σ ^ a) ((σ ^ b) x)`. -/
theorem pow_apply_add {σ : V →ₗ[ZMod 2] V} (a b : ℕ) (x : V) :
    (σ ^ (a + b)) x = (σ ^ a) ((σ ^ b) x) := by
  rw [pow_add]
  rfl

/-- Iterated invariance. -/
theorem inv_pow_mem {σ : V →ₗ[ZMod 2] V} {U : Submodule (ZMod 2) V} (hU : IsInv σ U) :
    ∀ k : ℕ, ∀ x : V, x ∈ U → (σ ^ k) x ∈ U := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ']
      exact hU _ (ih x hx)

/-- A non-zero `σ`-invariant subspace has at least `2 ^ n` elements when `orderOf σ = 2 ^ n - 1`
and `σ` is semiregular. -/
theorem pow_le_card {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hord : orderOf σ = 2 ^ n - 1) (hn : 1 ≤ n)
    (hsr : Semiregular σ) {U : Submodule (ZMod 2) V} (hU : IsInv σ U) (hne : U ≠ ⊥) :
    2 ^ n ≤ Nat.card U := by
  classical
  have hpow : σ ^ (2 ^ n - 1) = 1 := pow_card_sub_one_eq_one hord
  have hfix : ∀ x : V, (σ ^ (2 ^ n - 1)) x = x := by
    intro x; rw [hpow]; rfl
  -- `σ ^ k u ≠ 0` for `u ≠ 0` and `k ≤ 2 ^ n - 1`
  have hne0 : ∀ k : ℕ, k ≤ 2 ^ n - 1 → ∀ u : V, u ≠ 0 → (σ ^ k) u ≠ 0 := by
    intro k hk u hu h0
    have h2 : u = (σ ^ (2 ^ n - 1 - k)) ((σ ^ k) u) := by
      rw [← pow_apply_add, Nat.sub_add_cancel hk, hfix]
    have : u = 0 := by rw [h2, h0, map_zero]
    exact hu this
  -- distinctness of the orbit elements
  have hstep : ∀ a b : ℕ, a < b → b < 2 ^ n - 1 → ∀ u : V, u ≠ 0 →
      (σ ^ a) u ≠ (σ ^ b) u := by
    intro a b hab hb u hu hcon
    have h3 : (σ ^ (b - a)) ((σ ^ a) u) = (σ ^ a) u := by
      rw [← pow_apply_add, Nat.sub_add_cancel (le_of_lt hab)]
      exact hcon.symm
    have ha : a ≤ 2 ^ n - 1 := le_of_lt (lt_trans hab hb)
    have h1 := hsr (b - a) ((σ ^ a) u) (hne0 a ha u hu) h3
    have h2 : 2 ^ n - 1 ∣ b - a := by
      rw [← hord]
      exact orderOf_dvd_iff_pow_eq_one.mpr h1
    have h5 : 0 < b - a := Nat.sub_pos_of_lt hab
    have h6 : b - a < 2 ^ n - 1 := lt_of_le_of_lt (Nat.sub_le b a) hb
    exact (not_le.mpr h6) (Nat.le_of_dvd h5 h2)
  obtain ⟨u, huU, hu0⟩ : ∃ u : V, u ∈ U ∧ u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (le_antisymm (fun x hx => by simpa using hcon x hx) bot_le)
  have horb : Function.Injective
      (fun p : Fin (2 ^ n - 1) ⊕ Fin 1 =>
        (Sum.elim (fun k : Fin (2 ^ n - 1) => (⟨(σ ^ (k : ℕ)) u, inv_pow_mem hU _ u huU⟩ : U))
          (fun _ => (⟨0, U.zero_mem⟩ : U)) p)) := by
    intro p q hpq
    rcases p with k₁ | k₁ <;> rcases q with k₂ | k₂
    · simp only [Sum.elim_inl] at hpq
      have h1 : (σ ^ (k₁ : ℕ)) u = (σ ^ (k₂ : ℕ)) u := by
        have := congrArg (fun x : U => (x : V)) hpq
        simpa using this
      by_cases hlt : (k₁ : ℕ) < (k₂ : ℕ)
      · exact absurd h1 (hstep _ _ hlt k₂.isLt u hu0)
      · have hle : (k₂ : ℕ) ≤ (k₁ : ℕ) := by omega
        rcases lt_or_eq_of_le hle with hlt2 | heq2
        · exact absurd h1.symm (hstep _ _ hlt2 k₁.isLt u hu0)
        · exact congrArg Sum.inl (Fin.ext heq2.symm)
    · simp only [Sum.elim_inl, Sum.elim_inr] at hpq
      have h1 : (σ ^ (k₁ : ℕ)) u = 0 := by
        have := congrArg (fun x : U => (x : V)) hpq
        simpa using this
      exact absurd h1 (hne0 _ (le_of_lt k₁.isLt) u hu0)
    · simp only [Sum.elim_inl, Sum.elim_inr] at hpq
      have h1 : (σ ^ (k₂ : ℕ)) u = 0 := by
        have := congrArg (fun x : U => (x : V)) hpq
        simpa using this.symm
      exact absurd h1 (hne0 _ (le_of_lt k₂.isLt) u hu0)
    · exact congrArg Sum.inr (Subsingleton.elim k₁ k₂)
  have hle := Nat.card_le_card_of_injective _ horb
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin] at hle
  have hsub : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel (Nat.one_le_two_pow (n := n))
  omega

end Work.Higman.Layers
