/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA DSTR / M110 / Aut : the order `p ^ k` subgroups of `PSL(2,p^k)` fixing `∞`

For `F = GF(p^k)` with `p` odd and `p ^ k ≥ 5`, every subgroup `H ≤ PSL(2,F)` of cardinality
`p ^ k` all of whose elements fix `∞` is the group of translations `x ↦ x + b`.

The argument is the classical one.  An element of `pslImage F` fixing `∞` is affine,
`x ↦ a²x + b` (`Work.AUTL2.element_fixing_infty`).  If its multiplier `a²` were different from
`1`, that element would have exactly two fixed points on `ℙ¹(F)`, namely `∞` and `-b/(a²-1)`.
But `⟨g⟩` is a `p`-group, and a `p`-group acting on a finite set `X` has a number of fixed points
congruent to `|X|` modulo `p` (`IsPGroup.card_modEq_card_fixedPoints`); here `|ℙ¹(F)| = p ^ k + 1`
so the number of fixed points must be `≡ 1 (mod p)`, whereas it is `2`.  Hence every `g ∈ H` has
multiplier `1`, i.e. `H ≤ translSub`, and since both have cardinality `p ^ k` they are equal.

This is the `Work.DSTR.M110` copy of the statement; the module `Submission.Work.AUTL2.Aut.geometry`
is a parallel development that cannot be imported here (both provide `Work.AUTL2.P1`).
-/
import Mathlib
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.Normalizer.le_pgammaL

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.Aut

open Work.AUTL2

/-! ## Cardinalities -/

/-- The projective line over `GF(p^k)` has `p ^ k + 1` points. -/
theorem card_P1 (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] (hq : 5 ≤ p ^ k) :
    Nat.card (P1 (GaloisField p k)) = p ^ k + 1 := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have h1 : Nat.card (P1 (GaloisField p k)) = Fintype.card (P1 (GaloisField p k)) :=
    Nat.card_eq_fintype_card
  have h2 : Fintype.card (P1 (GaloisField p k)) = Fintype.card (GaloisField p k) + 1 :=
    Fintype.card_option
  have h3 : (Fintype.card (GaloisField p k) : ℕ) = p ^ k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p k hk
  omega

/-- The translation group `{x ↦ x + b}` has `p ^ k` elements. -/
theorem card_translSub (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hq : 5 ≤ p ^ k) :
    Nat.card (Normalizer.translSub (GaloisField p k)) = p ^ k := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have hinj : Function.Injective (Normalizer.translHom (GaloisField p k)) := by
    intro a b hab
    exact Multiplicative.toAdd.injective
      (Normalizer.transl_injective (GaloisField p k) hab)
  have h1 : Nat.card (Normalizer.translSub (GaloisField p k)) =
      Nat.card (Multiplicative (GaloisField p k)) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  rw [h1, Nat.card_congr (Multiplicative.ofAdd (α := GaloisField p k)).symm,
    GaloisField.card p k hk]

/-! ## The key structural lemma -/

/-- **Key structural lemma.**  A subgroup of `pslImage F` of cardinality `p ^ k`
(`F = GF(p^k)`, `p` odd) all of whose elements fix `∞` is the translation group
`{x ↦ x + b}`. -/
theorem eqTranslSub (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k) (H : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) (hH : H ≤ Work.AUTL2.pslImage (GaloisField p k)) (hcard : Nat.card H = p ^ k) (hfix : ∀ g ∈ H, g OnePoint.infty = OnePoint.infty) : H = Work.AUTL2.Normalizer.translSub (GaloisField p k) := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have hle : H ≤ Normalizer.translSub (GaloisField p k) := by
    intro g hg
    obtain ⟨a, b, hab⟩ := element_fixing_infty (GaloisField p k) g (hH hg) (hfix g hg)
    by_cases ha : (↑a : GaloisField p k) ^ 2 = 1
    · -- the multiplier is `1`, so `g` is the translation `x ↦ x + b`
      have hg_eq : g = transl (GaloisField p k) b := by
        ext x
        rcases x with _ | x
        · change g ∞ = transl (GaloisField p k) b ∞
          rw [hfix g hg, transl_infty]
        · change g ((x : GaloisField p k) : P1 (GaloisField p k)) =
            transl (GaloisField p k) b ((x : GaloisField p k) : P1 (GaloisField p k))
          rw [hab x, transl_formula, ha, one_mul]
      rw [hg_eq]
      exact Normalizer.transl_mem_translSub (GaloisField p k) b
    · -- a multiplier `≠ 1` gives exactly two fixed points, contradicting the `p`-group
      -- congruence for the number of fixed points
      exfalso
      have hden : (↑a : GaloisField p k) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ha
      set x0 : GaloisField p k := -b / ((↑a : GaloisField p k) ^ 2 - 1) with hx0def
      have hx0fix : g ((x0 : GaloisField p k) : P1 (GaloisField p k)) =
          (x0 : GaloisField p k) := by
        rw [hab x0, hx0def]
        congr 1
        field_simp
        ring
      -- powers of `g` fix every point that `g` fixes
      have hpow : ∀ (y : P1 (GaloisField p k)), g y = y → ∀ n : ℤ, (g ^ n) y = y := by
        intro y hy n
        have hmem : g ∈ MulAction.stabilizer (Equiv.Perm (P1 (GaloisField p k))) y :=
          MulAction.mem_stabilizer_iff.mpr hy
        exact MulAction.mem_stabilizer_iff.mp
          (Subgroup.zpow_mem (MulAction.stabilizer (Equiv.Perm (P1 (GaloisField p k))) y)
            hmem n)
      -- the fixed points of the cyclic group `⟨g⟩` are exactly `∞` and `x₀`
      have hfixset : MulAction.fixedPoints ↥(Subgroup.zpowers g) (P1 (GaloisField p k)) =
          ({(∞ : P1 (GaloisField p k)), ((x0 : GaloisField p k) : P1 (GaloisField p k))} :
            Set (P1 (GaloisField p k))) := by
        ext y
        rw [MulAction.mem_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hy
          have hgy : g y = y := hy ⟨g, Subgroup.mem_zpowers g⟩
          rcases y with _ | x
          · exact Or.inl rfl
          · refine Or.inr ?_
            suffices h : x = x0 by
              show ((x : GaloisField p k) : P1 (GaloisField p k)) =
                ((x0 : GaloisField p k) : P1 (GaloisField p k))
              rw [h]
            have hx : (↑a : GaloisField p k) ^ 2 * x + b = x := by
              have h2 : g ((x : GaloisField p k) : P1 (GaloisField p k)) =
                  ((x : GaloisField p k) : P1 (GaloisField p k)) := hgy
              rw [hab x] at h2
              exact OnePoint.coe_eq_coe.mp h2
            rw [hx0def, eq_div_iff hden]
            linear_combination hx
        · rintro (rfl | rfl)
          · intro u
            obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp u.2
            calc u • (∞ : P1 (GaloisField p k)) =
                (u : Equiv.Perm (P1 (GaloisField p k))) ∞ := rfl
              _ = (g ^ m) ∞ := by rw [← hm]
              _ = ∞ := hpow ∞ (hfix g hg) m
          · intro u
            obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp u.2
            calc u • ((x0 : GaloisField p k) : P1 (GaloisField p k)) =
                (u : Equiv.Perm (P1 (GaloisField p k)))
                  ((x0 : GaloisField p k) : P1 (GaloisField p k)) := rfl
              _ = (g ^ m) ((x0 : GaloisField p k) : P1 (GaloisField p k)) := by rw [← hm]
              _ = ((x0 : GaloisField p k) : P1 (GaloisField p k)) := hpow _ hx0fix m
      have hgcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers g)
          (P1 (GaloisField p k))) = 2 := by
        rw [Nat.card_coe_set_eq, hfixset]
        exact Set.ncard_pair (OnePoint.infty_ne_coe x0)
      -- `⟨g⟩` is a `p`-group
      have horder : orderOf g ∣ p ^ k := by
        rw [← hcard]
        exact Subgroup.orderOf_dvd_natCard H hg
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp horder
      have hpgroup : IsPGroup p ↥(Subgroup.zpowers g) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
      -- the congruence counting fixed points contradicts `|ℙ¹(F)| = p ^ k + 1`
      have hcong := hpgroup.card_modEq_card_fixedPoints (P1 (GaloisField p k))
      rw [card_P1 p k hq, hgcard] at hcong
      have h1 : p ^ k ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p hk)
      have h2 : p ^ k + 1 ≡ 1 [MOD p] := by simpa using h1.add_right 1
      have h12 : (1 : ℕ) ≡ 2 [MOD p] := h2.symm.trans hcong
      have hdvd : p ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp h12
      have hle1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_translSub p k hq, hcard]

end Work.DSTR.M110.Aut
