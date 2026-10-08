import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.nCases
import Submission.Work.BG.s02_quotCyclic
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.sq_eq_one_eq_of_isCyclic

namespace Work.BG

/-!
# `tU` is a square in `H₀/U` (for `|S| ≥ 8`)

`H₀/U` is a finite cyclic `2`-group of order `n = |S₀| = |S|/2`; when `4 ≤ D.n` its order is
`2^k` with `k ≥ 2`, so its unique non-identity element of order two — the class `tU` of the
central involution `t` — is a square.
-/

open Subgroup

/-- In a finite cyclic group of order `2 ^ k` with `2 ≤ k`, every non-identity element of
order dividing `2` is a square. -/
theorem exists_sq_root_of_cyclic_card_pow_two {A : Type} [Group A] [Finite A] [IsCyclic A]
    {k : ℕ} (hk : 2 ≤ k) (hcard : Nat.card A = 2 ^ k) {a : A}
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) : ∃ x : A, x ^ 2 = a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hord : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g ^ (2 ^ (k - 2)), ?_⟩
  have hpow : (g ^ (2 ^ (k - 2))) ^ 2 = g ^ (2 ^ (k - 1)) := by
    rw [← pow_mul]
    congr 1
    rw [← pow_succ]
    congr 1
    omega
  have hpow2 : ((g ^ (2 ^ (k - 2))) ^ 2) ^ 2 = 1 := by
    rw [hpow, ← pow_mul]
    have hk2 : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hk2, ← hcard, ← hord]
    exact pow_orderOf_eq_one g
  have hne : (g ^ (2 ^ (k - 2))) ^ 2 ≠ 1 := by
    rw [hpow]
    intro hcontra
    have hdvd : orderOf g ∣ 2 ^ (k - 1) := orderOf_dvd_iff_pow_eq_one.mpr hcontra
    rw [hord, hcard] at hdvd
    have hlt : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpos : 0 < 2 ^ (k - 1) := pow_pos (by norm_num) _
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  exact sq_eq_one_eq_of_isCyclic (C := A) (z := (g ^ (2 ^ (k - 2))) ^ 2) (a := a)
    hne ha1 hpow2 ha2

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
theorem c3TUIsSquare {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) (hn : 4 ≤ D.n) :
    ∃ x : Work.BG.quotGroup C.P, x ^ 2 = Work.BG.tU C := by
  -- `H₀/U` is cyclic and has order `|S₀| = n`.
  have hcardA : Nat.card (quotGroup C.P) = D.n := by
    rw [← Subgroup.index_eq_card (Work.GW2.C16.Uin C), rem31IndexUin D C hC]
  -- `D.n = 2 ^ k` with `k ≥ 2`: `S₀` is a `2`-group of order `D.n`, and `4 ≤ D.n`.
  have hS0pg : IsPGroup 2 ↥D.S0 := IsPGroup.to_le D.S.isPGroup' D.S0_le
  obtain ⟨k, hk0⟩ := IsPGroup.exists_card_eq (p := 2) hS0pg
  have hS0card : Nat.card ↥D.S0 = D.n := (nCases G D).2
  have hk : D.n = 2 ^ k := by rw [← hS0card, hk0]
  have hk2 : 2 ≤ k := by
    have h4 : 2 ^ 2 ≤ 2 ^ k := by rw [← hk]; exact hn
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h4
  have hcard : Nat.card (quotGroup C.P) = 2 ^ k := hcardA.trans hk
  obtain ⟨x, hx⟩ :=
    @exists_sq_root_of_cyclic_card_pow_two (quotGroup C.P) _ _ (quotGroup_isCyclic C)
      k hk2 hcard (tU C) (tU_sq C) (tU_ne_one C)
  exact ⟨x, hx⟩

end Work.BG
