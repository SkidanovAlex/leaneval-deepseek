import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.characteristic_fittingPiIn
import Submission.Work.DSTR.M110.PiCoreFacts

/-!
# GW design 25A: the "hard case" of the Fitting transfer, with `N` odd

The unconditional form of the hard case is **FALSE** (GAP: `SmallGroup(168,9) ≍ C₂`, order 56448,
32 failing configurations; see `NOTES_LEAD_gw_design25.md` §4 and `~/core25_out/named.out`).  At the
only call site (`Work.DSTR.d110ii`) the normal subgroup `N` has *odd* order, and then the case is
vacuous: a dihedral trick shows `y ∈ C_G(t)·N` whenever `[y,t] ∈ N` and `|N|` is odd.

This file is the port of `_design_gw/Core25a.lean` into the area (namespace `Work.DSTR`).
-/

namespace Work.DSTR

open Subgroup

/-- `F_{2'}(K) = O_{2'}(F(K))` has odd order. -/
theorem odd_card_fittingPiIn_of_subgroup' {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    Odd (Nat.card ↥(Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} K)) := by
  have h1 : Odd (Nat.card ↥(Work.GW2.piCore {k : ℕ | k ≠ 2} ↥(Work.GW2.fitting ↥K))) :=
    Work.GW2.piCore_odd _
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi]
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]
  exact h1

/-- **Dihedral trick.**  If `N ◁ G` has odd order, `t` is an involution and `[y,t] ∈ N`, then
`y ∈ C_G(t)·N`.  (For `n = [y,t] ∈ N` one has `t n t⁻¹ = n⁻¹`, and since `n` has odd order, the
element `b = (n^k)⁻¹` with `|n| = 2k + 1` lies in `N` and conjugates `t` to `y t y⁻¹`; hence
`b⁻¹ y` centralizes `t`.) -/
theorem mem_centralizer_sup_of_odd {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) (t y : G) (ht : orderOf t = 2)
    (hy : y * t * y⁻¹ * t⁻¹ ∈ N) :
    y ∈ Subgroup.centralizer ({t} : Set G) ⊔ N := by
  set n := y * t * y⁻¹ * t⁻¹ with hn
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  -- `t n t⁻¹ = n⁻¹`
  have hconj : t * n * t⁻¹ = n⁻¹ := by
    rw [hn, htinv]
    simp only [mul_inv_rev, inv_inv, htinv]
    calc t * (y * t * y⁻¹ * t) * t = t * y * t * y⁻¹ * (t * t) := by group
      _ = t * y * t * y⁻¹ := by rw [htt, mul_one]
      _ = t * (y * (t * y⁻¹)) := by group
  -- `n` has odd order `2k+1`
  have hnodd : Odd (orderOf n) := by
    have h1 : orderOf (⟨n, hy⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hN h1
  obtain ⟨k, hk⟩ := hnodd
  -- `b = (n^k)⁻¹` conjugates `t` to `y t y⁻¹ = n t`
  have hpow : t * n ^ k * t⁻¹ = (n ^ k)⁻¹ := by
    rw [← conj_pow, hconj, inv_pow]
  have htn : t * n ^ k = (n ^ k)⁻¹ * t := by
    calc t * n ^ k = t * n ^ k * t⁻¹ * t := by group
      _ = (n ^ k)⁻¹ * t := by rw [hpow]
  have hn1 : n ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one n
  have hn2k : (n ^ (2 * k))⁻¹ = n := by
    rw [pow_succ] at hn1
    exact inv_eq_of_mul_eq_one_right hn1
  set b : G := (n ^ k)⁻¹ with hb
  have hbN : b ∈ N := N.inv_mem (N.pow_mem hy k)
  have hbt : b * t * b⁻¹ = y * t * y⁻¹ := by
    have e1 : b * t * b⁻¹ = (n ^ k)⁻¹ * (t * n ^ k) := by rw [hb, inv_inv]; group
    have e2 : y * t * y⁻¹ = n * t := by rw [hn]; group
    rw [e1, htn, e2, ← mul_assoc, ← mul_inv_rev, ← pow_add, ← two_mul, hn2k]
  have hc : b⁻¹ * y ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    have : (b⁻¹ * y) * t * (b⁻¹ * y)⁻¹ = t := by
      calc (b⁻¹ * y) * t * (b⁻¹ * y)⁻¹ = b⁻¹ * (y * t * y⁻¹) * b := by group
        _ = b⁻¹ * (b * t * b⁻¹) * b := by rw [hbt]
        _ = t := by group
    calc t * (b⁻¹ * y) = ((b⁻¹ * y) * t * (b⁻¹ * y)⁻¹) * (b⁻¹ * y) := by rw [this]
      _ = (b⁻¹ * y) * t := by group
  have : y = b * (b⁻¹ * y) := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hbN hc

/-- The restated hard case: with `Odd (Nat.card N)` it is vacuous. -/
theorem fittingPiIn_conj_le_sup_of_not_mem_sup_odd {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (t y : G) (ht : orderOf t = 2)
    (hy : y * t * y⁻¹ * t⁻¹ ∈ N)
    (hynot : y ∉ Subgroup.centralizer ({t} : Set G) ⊔ N)
    (_hFnot : ¬ Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} (Subgroup.centralizer ({t} : Set G)) ≤ N) :
    (Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} (Subgroup.centralizer ({t} : Set G))).map
        (MulAut.conj y).toMonoidHom
      ≤ Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} (Subgroup.centralizer ({t} : Set G)) ⊔ N :=
  absurd (mem_centralizer_sup_of_odd N hNodd t y ht hy) hynot

/-! ## Record: the unconditional form of the hard case is FALSE

The statement below is kept as a record.  It is **FALSE** (lead ruling, design 25,
`NOTES_LEAD_gw_design25.md` §4; GAP counterexample `SmallGroup(168,9) ≍ C₂`, order 56448, 32
failing configurations).  Do not attempt to prove it; the call site in `Work.DSTR.d110ii` uses
`fittingPiIn_conj_le_sup_of_not_mem_sup_odd` above instead, where the extra hypothesis
`Odd (Nat.card N)` holds because `N = C_X(E) ∩ Y` is the centralizer of a quasisimple subgroup.

```
theorem fittingPiIn_conj_le_sup_of_not_mem_sup {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (t y : G) (ht : orderOf t = 2)
    (hy : y * t * y⁻¹ * t⁻¹ ∈ N)
    (hynot : y ∉ Subgroup.centralizer ({t} : Set G) ⊔ N)
    (hFnot : ¬ Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} (Subgroup.centralizer ({t} : Set G)) ≤ N) :
    (Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} (Subgroup.centralizer ({t} : Set G))).map
        (MulAut.conj y).toMonoidHom
      ≤ Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} (Subgroup.centralizer ({t} : Set G)) ⊔ N
```
-/

end Work.DSTR
