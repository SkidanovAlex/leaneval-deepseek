import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.ThmF.Tools.appX_mem_pCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.Tools

/-!
# Fixed-point-free action of the Fitting subgroup

Peterfalvi II, Appendix X, step (8): if `ρ : G →* MulAut E` is an action of a finite group `G`
on a finite group `E` whose restriction to every `p`-core `O_p(G)` (`p ∣ |G|`) is
fixed-point-free, then the restriction to the whole Fitting subgroup `F(G) = ⨆_{p ∣ |G|} O_p(G)`
is fixed-point-free.

The argument is elementary.  Let `x ∈ F(G)`, `x ≠ 1`, and let `n = orderOf x`; then `n > 1`, so
`n = p * m` for some prime `p` and some `0 < m < n`.  The element `x ^ m` of `F(G)` has order
dividing `p`, hence lies in `O_p(G)` (`Work.ThmF.Tools.appX_mem_pCore`), and is non-trivial
because `m < n = orderOf x`.  Finally any `a` fixed by `ρ x` is fixed by every power
`(ρ x) ^ k`, in particular by `ρ (x ^ m)`, so the hypothesis on `O_p(G)` forces `a = 1`.
-/

/-- **Appendix X, step (8).**  An action of a finite group `G` on a finite group `E` that is
fixed-point-free on every `p`-core `O_p(G)` is fixed-point-free on the Fitting subgroup `F(G)`. -/
theorem appX_fpf_fitting {G E : Type} [Group G] [Finite G] [Group E] [Finite E]
    (ρ : G →* MulAut E)
    (h : ∀ p ∈ (Nat.card G).primeFactors,
      ∀ x ∈ Work.Fitting.pCore p G, x ≠ 1 → ∀ a : E, (ρ x) a = a → a = 1) :
    ∀ x ∈ Work.Fitting.fitting G, x ≠ 1 → ∀ a : E, (ρ x) a = a → a = 1 := by
  intro x hx hx1 a ha
  -- `x ≠ 1` means `orderOf x ≠ 1`, so a prime `p` divides `orderOf x`.
  have hxord : orderOf x ≠ 1 := fun ho => hx1 (orderOf_eq_one_iff.mp ho)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hxord
  haveI : Fact p.Prime := ⟨hp⟩
  have hpcard : p ∣ Nat.card G := dvd_trans hpdvd (orderOf_dvd_natCard x)
  -- Write `orderOf x = p * m`.
  obtain ⟨m, hm⟩ := hpdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, mul_zero] at hm
      exact absurd hm (orderOf_pos x).ne'
    · exact hpos
  -- `m < orderOf x`, so `x ^ m ≠ 1`.
  have hxmn : x ^ m ≠ 1 := by
    intro h1
    have hdiv : orderOf x ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hle := Nat.le_of_dvd hmpos hdiv
    rw [hm] at hle
    nlinarith [hp.two_le, hmpos]
  -- `x ^ m` has `p`-power order, hence lies in `O_p(G)`.
  have hord_dvd : orderOf (x ^ m) ∣ p ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by
      rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one])
  have hmem : x ^ m ∈ Work.Fitting.pCore p G :=
    appX_mem_pCore (pow_mem hx m) hord_dvd
  have hp_mem : p ∈ (Nat.card G).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, hpcard, Nat.card_pos.ne'⟩
  -- Any fixed point of `ρ x` is a fixed point of every power of `ρ x`.
  have hpowa : ∀ n : ℕ, ((ρ x) ^ n) a = a := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, ha, ih]
  have haff : (ρ (x ^ m)) a = a := by rw [map_pow]; exact hpowa m
  exact h p hp_mem (x ^ m) hmem hxmn a haff

end Work.ThmF.Tools
