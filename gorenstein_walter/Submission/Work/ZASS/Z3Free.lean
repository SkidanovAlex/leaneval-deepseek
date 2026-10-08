/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: step Z3, `H = G_{∞0}` acts fixed-point-freely on `U`

If `h ∈ G_{∞0}`, `h ≠ 1`, commutes with `u ∈ U ≤ G_∞`, then `h` fixes exactly `∞` and `0`,
and `u` preserves that fixed-point set; as `u` also fixes `∞`, either `u • 0 = ∞` — which
would give `u^m • 0 = ∞` for all `m ≥ 1`, contradicting `u ^ orderOf u = 1` — or `u • 0 = 0`,
so that `u ∈ U ⊓ G_{∞0} = ⊥` by coprimality of `|U| = p^k` and `|G_{∞0}| = (q-1)/2`.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.Zassenhaus.zass_coprime_pow_half

open scoped MatrixGroups

namespace Work.ZASS

open Work.GW2 (ZassHyps2)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

/-- **Z3.** `H = G_{∞0}` acts fixed-point-freely on `U ≤ B` by conjugation. -/
theorem fixedPointFreeConj_pairStab {G X : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] {p k : ℕ} [Fact p.Prime] (hp : Odd p) {q : ℕ} (h : ZassHyps2 G X q)
    (hq : q = p ^ k) {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (hUB : U ≤ borel G inf) (hcardU : Nat.card U = p ^ k)
    (hcardH : Nat.card (pairStab G inf zero) = (q - 1) / 2) :
    FixedPointFreeConj U (pairStab G inf zero) := by
  intro h' hh hh1 u hu hconj
  -- `h'` fixes `∞` and `0`
  obtain ⟨hz, hi⟩ := Work.Zassenhaus.mem_pairStab_iff.mp hh
  -- `h'` and `u` commute
  have hcomm : h' * u = u * h' := by
    have h1 : h' * u * h'⁻¹ = u := hconj
    calc h' * u = h' * u * h'⁻¹ * h' := by group
      _ = u * h' := by rw [h1]
  -- the fixed points of `h'` are exactly `∞` and `0`
  have hfix_eq : ∀ x : X, h' • x = x → x = inf ∨ x = zero := by
    intro x hx
    by_contra hc
    push_neg at hc
    exact hh1 (eq_one_of_fixes_three h hc.1 hc.2 hne hx hi hz)
  -- `u` preserves the two fixed points of `h'`
  have huz : u • zero = inf ∨ u • zero = zero :=
    hfix_eq (u • zero) (by rw [← mul_smul, hcomm, mul_smul, hz])
  have huinf : u • inf = inf := Work.Zassenhaus.mem_borel_iff.mp (hUB hu)
  rcases huz with hcase | hcase
  · -- `u • 0 = ∞`: then `u^m • 0 = ∞` for every `m ≥ 1`, contradicting `u ^ orderOf u = 1`
    exfalso
    have huinf_pow : ∀ m : ℕ, u ^ m • inf = inf := fun m =>
      Work.Zassenhaus.mem_borel_iff.mp ((borel G inf).pow_mem (hUB hu) m)
    have hpow : ∀ m : ℕ, 1 ≤ m → u ^ m • zero = inf := by
      intro m hm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [pow_succ, mul_smul, hcase, huinf_pow j]
    have h1 := hpow (orderOf u) (orderOf_pos u)
    rw [pow_orderOf_eq_one, one_smul] at h1
    exact hne h1.symm
  · -- `u • 0 = 0`: then `u ∈ U ⊓ G_{∞0} = ⊥` by coprimality
    have hmem : u ∈ U ⊓ pairStab G inf zero :=
      ⟨hu, Work.Zassenhaus.mem_pairStab_iff.mpr ⟨hcase, huinf⟩⟩
    have hdvdU : Nat.card ↥(U ⊓ pairStab G inf zero) ∣ p ^ k := by
      rw [← hcardU]
      exact Subgroup.card_dvd_of_le (H := U ⊓ pairStab G inf zero) (K := U) inf_le_left
    have hdvdH : Nat.card ↥(U ⊓ pairStab G inf zero) ∣ (q - 1) / 2 := by
      rw [← hcardH]
      exact Subgroup.card_dvd_of_le (H := U ⊓ pairStab G inf zero)
        (K := pairStab G inf zero) inf_le_right
    have hcard : Nat.card ↥(U ⊓ pairStab G inf zero) = 1 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at hdvdU
        exact Nat.dvd_one.mp hdvdU
      · have hcop : Nat.Coprime (p ^ k) ((q - 1) / 2) := by
          rw [hq]
          exact Work.Zassenhaus.zass_coprime_pow_half (Fact.out) hp hkpos
        have hcop' : (p ^ k).gcd ((q - 1) / 2) = 1 := by simpa [Nat.Coprime] using hcop
        exact Nat.dvd_one.mp (hcop' ▸ Nat.dvd_gcd hdvdU hdvdH)
    haveI : Fintype ↥(U ⊓ pairStab G inf zero) := Fintype.ofFinite ↥(U ⊓ pairStab G inf zero)
    haveI : Subsingleton ↥(U ⊓ pairStab G inf zero) :=
      Fintype.card_le_one_iff_subsingleton.mp (by rw [← Nat.card_eq_fintype_card, hcard])
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨u, hmem⟩ : ↥(U ⊓ pairStab G inf zero)) 1)

end Work.ZASS
