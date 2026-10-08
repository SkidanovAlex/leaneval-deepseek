/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — pieces of Bender §4 (11): subgroup counts transported into `E(M)`

Bender 1981, §4 (11) (p. 227): *"As `E` has `q k'` subgroups of order `p`, `P × E` contains
`(p₁ − 1) q k'` conjugates `X ≠ P` of `P`."*  The first half of that sentence is the transfer of
the concrete `L₂(q)`-count `I.l2primeCount` (`L2PrimeSubgroupCountProp`) along the isomorphism
`E(M) ≃* PSL(2, GaloisField pF kF)` supplied by §4 (9).

Recall `L2PrimeSubgroupCountProp`: if `r` is an odd prime `≠ pF` with `r ∣ (q + ε)/2` (`ε = ±1`,
`q = pF ^ kF`) then `L₂(q)` has `q (q − ε)/2` subgroups of order `r`.  Bender needs the case
`r = p` (§4's prime `p`, dividing `|F|`, hence `k`): with `2k = q + ε` and `2k' = q − ε` the count
is `q k'` — exactly the `q k'` of (11).

The statement is kept in the canonical numerical shape used by the rest of the area
(compare `Work.CORE4.Case2Parity`): `q = pF ^ kF`, `Even k`, `Odd k'`,
`(2k, 2k') = (q+1, q−1)` or `(q−1, q+1)`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountAssembly

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-! ## 1. Subgroup counts are invariant under multiplicative equivalences -/

/-- Counting subgroups of a given order is invariant under a multiplicative equivalence:
`Y ↦ Y.map φ` is a bijection between the subgroups of order `r`, with inverse given by `φ.symm`. -/
theorem ncard_subgroups_eq_of_mulEquiv {M N : Type*} [Group M] [Group N] (φ : M ≃* N) (r : ℕ) :
    {Y : Subgroup M | Nat.card Y = r}.ncard = {Y : Subgroup N | Nat.card Y = r}.ncard := by
  have hidM : (φ.symm : N ≃* M).toMonoidHom.comp φ.toMonoidHom = MonoidHom.id M :=
    MonoidHom.ext (fun x => φ.symm_apply_apply x)
  have hidN : φ.toMonoidHom.comp (φ.symm : N ≃* M).toMonoidHom = MonoidHom.id N :=
    MonoidHom.ext (fun x => φ.apply_symm_apply x)
  refine Set.ncard_congr (fun (Y : Subgroup M) _ => Y.map φ.toMonoidHom) ?_ ?_ ?_
  · intro Y hY
    simp only [Set.mem_setOf_eq] at hY ⊢
    rw [Subgroup.card_map_of_injective (K := Y) φ.injective, hY]
  · intro A B hA hB hAB
    have h2 := congrArg (fun Z : Subgroup N => Z.map (φ.symm : N ≃* M).toMonoidHom) hAB
    rw [Subgroup.map_map, Subgroup.map_map, hidM, Subgroup.map_id, Subgroup.map_id] at h2
    exact h2
  · intro Y hY
    refine ⟨Y.map (φ.symm : N ≃* M).toMonoidHom, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [Subgroup.card_map_of_injective (K := Y)
        (f := (φ.symm : N ≃* M).toMonoidHom) φ.symm.injective]
      exact hY
    · rw [Subgroup.map_map, hidN, Subgroup.map_id]

/-! ## 2. §4 (11): `E` has `q k'` subgroups of the prime order `p` -/

/-- **Bender §4 (11), the count `q k'`.**

`E = E(M)` is isomorphic to `L₂(q)` with `q = pF ^ kF` an odd prime power, `k` is the even half of
`q ∓ 1` and `k'` the odd one (so `|M : M ⊓ H| = q k'`), and `r` is an odd prime dividing `k`.
Then `E` has exactly `q k'` subgroups of order `r`.

For the application `r` is §4's prime `p`: `p ∣ |F|` and `p ∣ |K|` with `k = |K| |S₀|`, so
`p ∣ k`; hence `r ∣ (q ± 1)/2` with the sign matching `k`, and `L2PrimeSubgroupCountProp` gives
the count `q (q ∓ 1)/2 = q k'`.  Note `r ≠ pF` is automatic: `r ∣ (q ± 1)/2` while `pF ∣ q`. -/
theorem L2PrimeCountTransfer (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G),
      ∀ (h : Work.GW2.Case2Ctx B) (pF kF : ℕ) (_ : Fact pF.Prime)
        (φ : (Work.GW2.layerIn h.D.M) ≃* PSL(2, GaloisField pF kF))
        (q k k' r : ℕ),
        Odd pF → 5 ≤ pF ^ kF → q = pF ^ kF → Even k → Odd k' →
        ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) →
        r.Prime → r ≠ 2 → r ∣ k →
        {Y : Subgroup (Work.GW2.layerIn h.D.M) | Nat.card Y = r}.ncard = q * k' := by
  intro G _ _ B h pF kF hpF φ q k k' r hpFodd hpF5 hq hk hk' hdisj hr hr2 hrk
  haveI : Fact pF.Prime := hpF
  have hkF : kF ≠ 0 := by rintro rfl; norm_num at hpF5
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow kF pF hpF.out.pos
  -- `r ≠ pF`: `pF ∣ q` while `r ∣ k` gives `pF ∣ q ± 1`
  have hrpF : r ≠ pF := by
    intro hEq
    have hdpFq : pF ∣ q := by rw [hq]; exact dvd_pow_self pF hkF
    have hdpFk : pF ∣ k := hEq ▸ hrk
    have hone : pF ∣ 1 := by
      rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩
      · have h2 : pF ∣ q + 1 := by
          rw [← h1]; exact dvd_mul_of_dvd_right hdpFk 2
        exact (Nat.dvd_add_iff_right hdpFq).mpr h2
      · have h2 : pF ∣ q - 1 := by
          rw [← h1]; exact dvd_mul_of_dvd_right hdpFk 2
        have h3 : pF ∣ 1 + (q - 1) := by rwa [Nat.add_comm, Nat.sub_add_cancel hq1]
        exact (Nat.dvd_add_iff_left h2).mpr h3
    exact absurd (Nat.le_of_dvd one_pos hone) (by have := hpF.out.two_le; omega)
  have htransfer := ncard_subgroups_eq_of_mulEquiv φ r
  rw [htransfer]
  set C : ℕ := {Y : Subgroup (PSL(2, GaloisField pF kF)) | Nat.card Y = r}.ncard with hC
  have hcast_q : ((pF ^ kF : ℕ) : ℤ) = (q : ℤ) := by rw [← hq]
  have hmain : (C : ℤ) = (q * k' : ℕ) := by
    rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `2k = q + 1`, `2k' = q - 1`; use `ε = 1`
      have hql : ((pF ^ kF : ℕ) : ℤ) + 1 = 2 * (k : ℤ) := by
        have h : (2 * k : ℕ) = pF ^ kF + 1 := by rw [← hq]; exact h1
        have h2n : ((2 * k : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) + 1 := by exact_mod_cast h
        push_cast at h2n
        linarith
      have hd : (r : ℤ) ∣ (((pF ^ kF : ℕ) : ℤ) + 1) / 2 := by
        rw [Int.ediv_eq_of_eq_mul_right (by norm_num) hql]
        exact_mod_cast hrk
      have hcount := I.l2primeCount pF kF hpFodd hpF5 r hr hr2 hrpF 1 (Or.inl rfl) hd
      rw [← hC] at hcount
      have hk'cast : ((pF ^ kF : ℕ) : ℤ) - 1 = 2 * (k' : ℤ) := by
        have h : (2 * k' : ℕ) = pF ^ kF - 1 := by rw [← hq]; exact h2
        have h2n : ((2 * k' : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) - 1 := by
          rw [h, Nat.cast_sub (by omega : 1 ≤ pF ^ kF)]; simp
        push_cast at h2n
        linarith
      have hk'q : (q : ℤ) - 1 = 2 * (k' : ℤ) := by rw [← hcast_q]; exact hk'cast
      have h2c : 2 * (C : ℤ) = 2 * ((q * k' : ℕ) : ℤ) := by
        rw [hcast_q, hk'q] at hcount
        rw [hcount]; push_cast; ring
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2c
    · -- `2k = q - 1`, `2k' = q + 1`; use `ε = -1`
      have hql : ((pF ^ kF : ℕ) : ℤ) + (-1) = 2 * (k : ℤ) := by
        have h : (2 * k : ℕ) = pF ^ kF - 1 := by rw [← hq]; exact h1
        have h2n : ((2 * k : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) - 1 := by
          rw [h, Nat.cast_sub (by omega : 1 ≤ pF ^ kF)]; simp
        push_cast at h2n
        linarith
      have hd : (r : ℤ) ∣ (((pF ^ kF : ℕ) : ℤ) + (-1)) / 2 := by
        rw [Int.ediv_eq_of_eq_mul_right (by norm_num) hql]
        exact_mod_cast hrk
      have hcount := I.l2primeCount pF kF hpFodd hpF5 r hr hr2 hrpF (-1) (Or.inr rfl) hd
      rw [← hC] at hcount
      have hk'cast : ((pF ^ kF : ℕ) : ℤ) + 1 = 2 * (k' : ℤ) := by
        have h : (2 * k' : ℕ) = pF ^ kF + 1 := by rw [← hq]; exact h2
        have h2n : ((2 * k' : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) + 1 := by exact_mod_cast h
        push_cast at h2n
        linarith
      have hk'q : (q : ℤ) - (-1) = 2 * (k' : ℤ) := by rw [← hcast_q]; exact hk'cast
      have h2c : 2 * (C : ℤ) = 2 * ((q * k' : ℕ) : ℤ) := by
        rw [hcast_q, hk'q] at hcount
        rw [hcount]; push_cast; ring
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2c
  exact_mod_cast hmain

end Work.CORE4
