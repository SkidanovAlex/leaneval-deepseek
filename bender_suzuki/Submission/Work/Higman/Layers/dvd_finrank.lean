/-
Copyright (c) 2024. All rights reserved.

# The dimension of a non-zero invariant subspace is divisible by `n`

If `orderOf σ = 2 ^ n - 1` and `σ` acts semiregularly on `V ∖ {0}`, then the `⟨σ⟩`-orbits on
`U ∖ {0}` (for `U ≠ ⊥` a `σ`-invariant subspace) have size `2 ^ n - 1`; hence
`2 ^ n - 1 ∣ |U| - 1 = 2 ^ d - 1` where `d = finrank U`, and therefore `n ∣ d`.
-/

import Mathlib
import Submission.Work.Higman.Layers.Defs
import Submission.Work.Higman.Layers.pow_le_card
import Submission.Work.Higman.Q3.orderOf_dvd_ncard_of_semiregular
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Layers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The dimension of a non-zero `σ`-invariant subspace is divisible by `n`, when
`orderOf σ = 2 ^ n - 1` and `σ` is semiregular. -/
theorem dvd_finrank {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hord : orderOf σ = 2 ^ n - 1) (hn : 1 ≤ n)
    (hsr : Semiregular σ) {U : Submodule (ZMod 2) V} (hU : IsInv σ U) (hne : U ≠ ⊥) :
    n ∣ Module.finrank (ZMod 2) U := by
  classical
  have hpow : σ ^ (2 ^ n - 1) = 1 := pow_card_sub_one_eq_one hord
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hinv : σ ^ (2 ^ n - 2) * σ = 1 := by
    rw [← pow_succ, show 2 ^ n - 2 + 1 = 2 ^ n - 1 by omega, hpow]
  have hinj : Function.Injective σ := by
    intro x y hxy
    calc x = (σ ^ (2 ^ n - 2) * σ) x := by rw [hinv]; rfl
      _ = (σ ^ (2 ^ n - 2)) (σ x) := rfl
      _ = (σ ^ (2 ^ n - 2)) (σ y) := by rw [hxy]
      _ = (σ ^ (2 ^ n - 2) * σ) y := rfl
      _ = y := by rw [hinv]; rfl
  let τ : V ≃ V := Equiv.ofBijective σ ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hτ : ∀ x : V, τ x = σ x := fun x => Equiv.ofBijective_apply _ _ x
  have hτpow : ∀ (k : ℕ) (x : V), (τ ^ k) x = (σ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        have h1 : (τ ^ (k + 1)) x = (τ ^ k) (τ x) := by rw [pow_succ]; rfl
        have h2 : (σ ^ (k + 1)) x = (σ ^ k) (σ x) := by rw [pow_succ]; rfl
        rw [h1, h2, hτ, ih]
  have horder : orderOf τ = orderOf σ := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]
      ext x
      rw [hτpow, pow_orderOf_eq_one]
      rfl
    · rw [orderOf_dvd_iff_pow_eq_one]
      ext x
      rw [← hτpow, pow_orderOf_eq_one]
      rfl
  -- the orbits of `⟨σ⟩` on `U ∖ {0}` are free
  set S : Set V := {x | x ∈ U ∧ x ≠ 0} with hSdef
  have hS : ∀ x ∈ S, τ x ∈ S := by
    rintro x ⟨hxU, hx0⟩
    refine ⟨?_, ?_⟩
    · rw [hτ]; exact hU x hxU
    · rw [hτ]; exact fun h => hx0 (hinj (by rw [h, map_zero]))
  have hfree : ∀ k : ℕ, ∀ x ∈ S, (τ ^ k) x = x → τ ^ k = 1 := by
    intro k x hx hkx
    have h1 : (σ ^ k) x = x := by
      rw [← hτpow k x]; exact hkx
    have h2 : σ ^ k = 1 := hsr k x hx.2 h1
    ext y
    rw [hτpow, h2]
    rfl
  have hdiv := Work.Higman.Q3.orderOf_dvd_ncard_of_semiregular τ S hS hfree
  rw [horder, hord] at hdiv
  -- `S.ncard = |U| - 1`
  have hSnc : S.ncard = Nat.card U - 1 := by
    have h1 : S = (U : Set V) \ {0} := by
      ext x
      simp [hSdef]
    rw [h1]
    have h2 := Set.ncard_sdiff_singleton_add_one (a := (0 : V)) (s := (U : Set V))
        (by simp)
    have h3 : (U : Set V).ncard = Nat.card U := (Nat.card_coe_set_eq (s := (U : Set V))).symm
    omega
  rw [hSnc] at hdiv
  -- convert to finrank
  have hcard : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
    haveI : Module.Finite (ZMod 2) ↥U := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U)]
    norm_num
  rw [hcard] at hdiv
  exact (Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n) (k := Module.finrank (ZMod 2) U)
    (by norm_num) (by omega)).mp hdiv

end Work.Higman.Layers
