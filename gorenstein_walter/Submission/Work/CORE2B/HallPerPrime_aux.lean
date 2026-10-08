import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.HallAux
import Submission.Work.BMAX.InvolutionInverts

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# AREA CORE2B — the per-prime step of Bender's Theorem 2.10 (`I_U(s)` Hall in `F(U)`)

Bender's proof of Theorem 2.10 (p. 222) has a per-prime step: for `s ∈ S − S₀` and every prime
`p`,

> `O_p(U) ≤ C_G(s)` or `O_p(U) ∩ C_G(s) = 1`,

i.e. an involution `s ∈ S − S₀` either centralizes or acts fixed-point-freely on each `p`-core of
`U = O(H)` (`H = C_G(t)`).  Via `C_{O_p(U)}(s) = 1 ⟺ s` inverts `O_p(U)`
(`Work.BMAX.InvolutionInverts`) this gives exactly the hypothesis
`hact : ∀ p prime, (∀ z ∈ O_p(U), s z s⁻¹ = z) ∨ (∀ z ∈ O_p(U), s z s⁻¹ = z⁻¹)`
of `invSet_le_centralizer_fittingIn` (`HallAux.lean`), whence `I_U(s) ≤ F(U)` and then `I_U(s)`
Hall in `F(U)` and normal in `U`.

This file holds the scaffolding (`p = 2`, the commuting facts) and the target statement.
-/

/-! ## 1. Generalities -/

/-- An involution of a group which fixes no non-trivial element of an invariant subgroup inverts
it.  (A re-export of `Work.BMAX.InvolutionInverts` in the CORE2B vocabulary.) -/
theorem involution_inverts_of_no_fixed {G : Type} [Group G] (N : Subgroup G) (t : G)
    [Finite N] (ht : t * t = 1) (htN : t ∈ Subgroup.normalizer (N : Set G))
    (hfix : ∀ x ∈ N, t * x * t⁻¹ = x → x = 1) :
    ∀ x ∈ N, t * x * t⁻¹ = x⁻¹ :=
  Work.BMAX.InvolutionInverts N t ht htN hfix

/-- `C_K(s) = ⊥` for an involution `s` normalising `K` means that `s` inverts `K`. -/
theorem inverts_of_inf_centralizer_eq_bot {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (s : G) (hs : s * s = 1) (hsN : s ∈ Subgroup.normalizer (K : Set G))
    (hbot : K ⊓ Subgroup.centralizer ({s} : Set G) = ⊥) :
    ∀ x ∈ K, s * x * s⁻¹ = x⁻¹ := by
  refine involution_inverts_of_no_fixed K s hs hsN ?_
  intro x hx hcon
  have hsx : s * x = x * s := by
    have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    rw [hs1] at hcon
    calc s * x = (s * x * s) * s := by rw [mul_assoc (s * x) s s, hs, mul_one]
      _ = x * s := by rw [hcon]
  have hmem : x ∈ K ⊓ Subgroup.centralizer ({s} : Set G) := by
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hsx
  rw [hbot] at hmem
  simpa using hmem

/-- `O_2(K) = 1` when `K` has odd order. -/
theorem pCore_two_eq_bot_of_odd {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hodd : Odd (Nat.card K)) : Work.GW2.pCoreIn 2 K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Work.GW2.pCoreIn 2 K ≤ K := by
    rw [Work.GW2.pCoreIn]
    exact Subgroup.map_subtype_le _
  have hpg : IsPGroup 2 (Work.GW2.pCoreIn 2 K) := by
    rw [Work.GW2.pCoreIn, hall_pCore_eq_opCore (G := ↥K) (p := 2)]
    exact (OddOrder.Isaacs.Ch01.opCore_isPGroup 2 ↥K).map K.subtype
  have hodd' : Odd (Nat.card (Work.GW2.pCoreIn 2 K)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn0 : n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ 2 ^ n := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h)
        exact ⟨2 ^ m, by rw [pow_succ']⟩
      exact (Nat.not_even_iff_odd.mpr (hn ▸ hodd')) (even_iff_two_dvd.mpr (hn ▸ h2))
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.mp hn

/-! ## 2. `U = O(H)` in the `BenderSetup` -/

/-- `U = O(H)` has odd order. -/
theorem odd_card_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Odd (Nat.card B.U) := by
  rw [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn,
    Subgroup.card_map_of_injective B.H.subtype_injective]
  exact oddCore_odd (G := ↥B.H)

/-- `O_2(U) = 1`. -/
theorem pCoreIn_two_eq_bot {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Work.GW2.pCoreIn 2 B.U = ⊥ :=
  pCore_two_eq_bot_of_odd B.U (odd_card_U B)

/-- `t` commutes with every element of `U = O(H)`. -/
theorem t_commutes_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    ∀ u ∈ B.U, B.t * u = u * B.t := by
  intro u hu
  have hle : B.U ≤ B.H := (in_le_self B.H 2 ∅).1
  have hmem : u ∈ B.H := hle hu
  have hH : B.H = Subgroup.centralizer ({B.t} : Set G) := rfl
  rw [hH, Subgroup.mem_centralizer_iff] at hmem
  exact hmem B.t (Set.mem_singleton B.t)

/-- `S ≤ H = C_G(t)`: `t` is the central involution of `S`. -/
theorem S_le_H {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    (B.S : Subgroup G) ≤ B.H := by
  intro x hx
  have hcomm : x * B.t = B.t * x := t_central_in_S B x hx
  rw [Work.GW2.BenderSetup.H, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hcomm.symm

/-- `S` normalises `U = O(H)` (because `U` is characteristic in `H`). -/
theorem S_normalizes_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := by
  have hH : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := le_normalizer_map_subtype_local B.H (Work.GW2.oddCore ↥B.H)
      (Work.GW2.oddCore_normal ↥B.H)
    simpa [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn] using h
  exact (S_le_H B).trans hH

end Work.CORE2B
