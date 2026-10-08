import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aP_ne_bot
import Submission.Work.CORE3.fittingPiIn_eq_iSup_pCoreIn
import Submission.Work.DSTR.fittingPiIn_eq_iSup_pCoreIn_prime

set_option linter.style.haveILetI false

/-!
# `p = 3` in the subcase `Ĥ = H` of Bender's §3

Bender 1981, p. 222 (subcase `Ĥ = H` of the proof of Theorem 2.10): the prime `p` is chosen
with `p ∈ π(F(U))`, `O_p(U)` is centralized by `t₁` and inverted by `t₂`.  Bender then notes
"Since `p` necessarily is 3, both `tᵢ` invert `F_p(U)`".

This file proves the first half of that sentence: if *additionally* `t₁` inverts the `3'`-part
`F_{3'}(U) = O_{3'}(F(U))` of the Fitting subgroup of `U`, then `p = 3`.

The argument is elementary.  Suppose `p ≠ 3`.  Then `O_p(U) ≤ F_{3'}(U)`, so `t₁` both inverts
`O_p(U)` (the hypothesis) and centralizes it (`D.cent`); hence every `x ∈ O_p(U)` satisfies
`x⁻¹ = x`, i.e. `x² = 1`.  But `O_p(U)` is a `p`-group with `p` odd (since `p` divides
`|F(U)|` and `U = O(H)` has odd order), so `orderOf x` is a power of the odd prime `p` and
divides `2`; therefore `x = 1`.  Thus `O_p(U) = ⊥`, contradicting `O_p(U) ≠ ⊥`
(`Work.CORE3.Case1aP_ne_bot`).

## Contents

* `pCoreIn_le_fittingPiIn_three_compl` — for a prime `q ≠ 3`, `O_q(K) ≤ F_{3'}(K)`
  (join decomposition of `F_π`, `Work.DSTR.FittingPiImg.fittingPiIn_eq_iSup_pCoreIn'`);
* `eq_one_of_mem_pCoreIn_of_inv_eq_self` — an element of an odd-order prime core that is its
  own inverse is trivial;
* `p_eq_three` — the deliverable.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- For a prime `q ≠ 3`, the `q`-core `O_q(K)` lies in the `3'`-part `F_{3'}(K)` of the Fitting
subgroup of `K`.  Immediate from the join decomposition
`F_π(K) = ⨆_{q ∈ π, q prime} O_q(K)` of `Work.DSTR.FittingPiImg.fittingPiIn_eq_iSup_pCoreIn'`
with `π = {3}ᶜ`. -/
theorem pCoreIn_le_fittingPiIn_three_compl {G : Type} [Group G] [Finite G]
    (K : Subgroup G) {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) :
    Work.GW2.pCoreIn q K ≤ Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K := by
  rw [Work.DSTR.FittingPiImg.fittingPiIn_eq_iSup_pCoreIn' (X := K) ({3}ᶜ : Set ℕ)]
  exact le_iSup_of_le q (le_iSup_of_le (by simpa using hq3) (le_iSup_of_le hq le_rfl))

/-- An element `x` of an odd prime core `O_p(K)` that equals its own inverse is trivial.

`x⁻¹ = x` gives `x² = 1`, i.e. `orderOf x ∣ 2`; and `O_p(K)` is a `p`-group, so `orderOf x` is a
power of the odd prime `p`.  Hence `orderOf x` is odd and divides `2`, so `orderOf x = 1`. -/
theorem eq_one_of_mem_pCoreIn_of_inv_eq_self {G : Type} [Group G] [Finite G]
    (K : Subgroup G) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) {x : G}
    (hx : x ∈ Work.GW2.pCoreIn p K) (hxinv : x⁻¹ = x) : x = 1 := by
  -- `x * x = 1`
  have hxx : x * x = 1 := by
    have h := mul_inv_cancel x
    rwa [hxinv] at h
  -- `orderOf x ∣ 2`
  have hdvd : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hxx
  -- `orderOf x = p ^ k`
  obtain ⟨k, hk⟩ :=
    (Work.CORE3.c1aIsPGroup_pCoreIn p K).exists_orderOf_eq_pow
      (⟨x, hx⟩ : ↥(Work.GW2.pCoreIn p K))
  have hkx : orderOf x = p ^ k :=
    (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(Work.GW2.pCoreIn p K))).trans hk
  have hodd : Odd (orderOf x) := hkx ▸ (Odd.pow hp_odd : Odd (p ^ k))
  -- an odd divisor of `2` is `1`
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega

/-- **Bender 1981, §3 (subcase `Ĥ = H`): the prime `p` is `3`.**

If an involution `t₁` inverts the `3'`-part `F_{3'}(U)` of `F(U)`, then the prime `p` with
`p ∈ π(F(U))` (equivalently `O_p(U) ≠ 1`) must be `3`: for `p ≠ 3` one has
`O_p(U) ≤ F_{3'}(U)`, so `t₁` inverts *and* centralizes `O_p(U)`
(`D.cent`), forcing `O_p(U) = ⊥`, contrary to `Work.CORE3.Case1aP_ne_bot`. -/
theorem p_eq_three {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case1aData B)
    (hinv : Work.GW2.Inverts D.t1 (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) B.U)) :
    D.p = 3 := by
  classical
  by_contra hp3
  haveI hpFact : Fact D.p.Prime := ⟨D.hp⟩
  -- `p` is odd: it divides `|F(U)|`, and `|U|` is odd
  have hp_odd : Odd D.p := by
    have h1 : D.p ∣ Nat.card ↥(Work.GW2.fittingIn B.U) :=
      (Nat.mem_primeFactors.mp D.p_mem).2.1
    have h2 : D.p ∣ Nat.card ↥B.U :=
      dvd_trans h1 (Subgroup.card_dvd_of_le (Work.CORE3.c1aFittingIn_le B.U))
    exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) h2
  -- `O_p(U) ≠ ⊥`, so it contains a nontrivial element `x`
  have hne : Work.GW2.pCoreIn D.p B.U ≠ ⊥ := Work.CORE3.Case1aP_ne_bot G B D
  obtain ⟨x, hxP, hxne⟩ : ∃ x ∈ Work.GW2.pCoreIn D.p B.U, x ≠ 1 := by
    by_contra h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  -- `x ∈ F_{3'}(U)`, so `t₁` inverts it; and `t₁` centralizes it
  have hxF : x ∈ Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) B.U :=
    pCoreIn_le_fittingPiIn_three_compl B.U D.hp hp3 hxP
  have hinvx : D.t1 * x * D.t1⁻¹ = x⁻¹ := hinv x hxF
  have hcenx : D.t1 * x * D.t1⁻¹ = x := by
    have hc := (Subgroup.mem_centralizer_iff.mp (D.cent hxP)) D.t1 (by simp)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hxne (eq_one_of_mem_pCoreIn_of_inv_eq_self B.U hp_odd hxP (hinvx.symm.trans hcenx))

end Work.CORE3
