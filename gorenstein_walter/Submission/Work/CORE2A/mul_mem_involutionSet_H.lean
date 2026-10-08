import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.bswHyps2_of_config

namespace Work.CORE2A

open Subgroup

/-- `U = O(H)` has odd order and `S` is a Sylow `2`-subgroup, so `U ⊓ S = ⊥`. -/
theorem inf_U_S_eq_bot_of_odd {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.U ⊓ (B.S : Subgroup G) = ⊥ := by
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_card (p := 2) (G := ↥(B.S : Subgroup G))).mp B.S.isPGroup'
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact ((bSetup_U_odd B).coprime_two_right).pow_right k

/-- **Bender's Lemma 2.2, counting step.**  For `s ∈ S − S₀`, `u ∈ I_U(s)` and `c ∈ S₀`, the
element `u * (s * c)` is an involution of `H = C_G(t)`, and it is not `t`.

The element `s` is an involution of `S` (`Work.CORE2A.dihedral_index_two`) which inverts `S₀`
(the index-two cyclic subgroup of the dihedral group `S`), and `u` is inverted by `s` by
definition of `I_U(s)`.  Since `c` commutes with `u` and `s c = c⁻¹ s`, we get
`u * (s * c) = (u * c⁻¹) * s` where `s` inverts `u * c⁻¹`; hence the square is `1`.  It is
nontrivial (and different from `t`) because otherwise `u ∈ U ⊓ S = ⊥`, forcing `s ∈ S₀`. -/
theorem mul_mem_involutionSet_H {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n))
    {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G))
    {c u : G} (hc : c ∈ B.S0) (hu : u ∈ Work.GW2.invSet B.U s) :
    u * (s * c) ∈ Work.GW2.involutionSet B.H ∧ u * (s * c) ≠ B.t := by
  classical
  -- `s` is an involution of `S` and inverts `S₀`
  have hs2 : orderOf s = 2 :=
    dihedral_index_two n hn (B.S : Subgroup G) B.S0 hdih B.S0_le B.S0_cyclic B.S0_index s hsS hs0
  have hss : s * s = 1 := by
    have h : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
    simpa [pow_two] using h
  have hinvS0 : ∀ z ∈ B.S0, s * z * s⁻¹ = z⁻¹ :=
    bsw_dihedral_inverts_index_two n hn (B.S : Subgroup G) B.S0 hdih B.S0_le B.S0_cyclic
      B.S0_index s hsS hs0
  -- `u ∈ U` is inverted by `s`, and commutes with `c ∈ S₀`
  have huU : u ∈ B.U := (mem_invSet.mp hu).1
  have hu_inv : s * u * s⁻¹ = u⁻¹ := (mem_invSet.mp hu).2
  have hcu : u * c = c * u := Subgroup.mem_centralizer_iff.mp (hS0C hc) u huU
  have hcu_inv : u⁻¹ * c = c * u⁻¹ :=
    Subgroup.mem_centralizer_iff.mp (hS0C hc) u⁻¹ (B.U.inv_mem huU)
  -- `u * (s * c) ∈ H = C_G(t)`
  have hsH : s ∈ B.H := bSetup_S_le_H B hsS
  have hcH : c ∈ B.H := bSetup_S_le_H B (B.S0_le hc)
  have huH : u ∈ B.H := bSetup_U_le_H B huU
  have hxH : u * (s * c) ∈ B.H := B.H.mul_mem huH (B.H.mul_mem hsH hcH)
  -- `s * c = c⁻¹ * s`, and `s` inverts `u * c⁻¹`
  have hsc : s * c = c⁻¹ * s := by
    calc s * c = (s * c) * (s⁻¹ * s) := by rw [inv_mul_cancel, mul_one]
      _ = ((s * c) * s⁻¹) * s := by group
      _ = c⁻¹ * s := by rw [hinvS0 c hc]
  have hx_eq : u * (s * c) = (u * c⁻¹) * s := by rw [hsc, mul_assoc]
  have hcinv : s * c⁻¹ * s⁻¹ = c := by
    calc s * c⁻¹ * s⁻¹ = (s * c * s⁻¹)⁻¹ := by group
      _ = (c⁻¹)⁻¹ := by rw [hinvS0 c hc]
      _ = c := inv_inv c
  have hinva : s * (u * c⁻¹) * s⁻¹ = (u * c⁻¹)⁻¹ := by
    calc s * (u * c⁻¹) * s⁻¹ = (s * u * s⁻¹) * (s * c⁻¹ * s⁻¹) := by group
      _ = u⁻¹ * c := by rw [hu_inv, hcinv]
      _ = (u * c⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]; exact hcu_inv
  have hx2 : (u * (s * c)) * (u * (s * c)) = 1 := by
    rw [hx_eq]
    calc (u * c⁻¹) * s * ((u * c⁻¹) * s)
        = (u * c⁻¹) * (s * (u * c⁻¹) * s⁻¹) * (s * s) := by group
      _ = (u * c⁻¹) * (u * c⁻¹)⁻¹ * 1 := by rw [hinva, hss]
      _ = 1 := by group
  -- `u * (s * c) ≠ 1`
  have hx_ne_one : u * (s * c) ≠ 1 := by
    intro h1
    have hu_eq : u = (s * c)⁻¹ := by
      have h := congrArg (fun z => z * (s * c)⁻¹) h1
      rw [mul_assoc, mul_inv_cancel, mul_one, one_mul] at h
      exact h
    have huS : u ∈ (B.S : Subgroup G) := by
      rw [hu_eq]
      exact (B.S : Subgroup G).inv_mem ((B.S : Subgroup G).mul_mem hsS (B.S0_le hc))
    have hmem : u ∈ (⊥ : Subgroup G) := by
      have h : u ∈ B.U ⊓ (B.S : Subgroup G) := ⟨huU, huS⟩
      rwa [inf_U_S_eq_bot_of_odd B] at h
    have hu1 : u = 1 := Subgroup.mem_bot.mp hmem
    rw [hu1, one_mul] at h1
    have hseq : s = c⁻¹ := by
      have h := congrArg (fun z => z * c⁻¹) h1
      rw [mul_assoc, mul_inv_cancel, mul_one, one_mul] at h
      exact h
    exact hs0 (by rw [hseq]; exact B.S0.inv_mem hc)
  -- `u * (s * c) ≠ t`
  have hx_ne_t : u * (s * c) ≠ B.t := by
    intro h1
    have hu_eq : u = B.t * (s * c)⁻¹ := by
      have h := congrArg (fun z => z * (s * c)⁻¹) h1
      rw [mul_assoc, mul_inv_cancel, mul_one] at h
      exact h
    have huS : u ∈ (B.S : Subgroup G) := by
      rw [hu_eq]
      exact (B.S : Subgroup G).mul_mem (B.S0_le B.t_mem)
        ((B.S : Subgroup G).inv_mem ((B.S : Subgroup G).mul_mem hsS (B.S0_le hc)))
    have hmem : u ∈ (⊥ : Subgroup G) := by
      have h : u ∈ B.U ⊓ (B.S : Subgroup G) := ⟨huU, huS⟩
      rwa [inf_U_S_eq_bot_of_odd B] at h
    have hu1 : u = 1 := Subgroup.mem_bot.mp hmem
    rw [hu1, one_mul] at h1
    have hseq : s = B.t * c⁻¹ := by
      have h := congrArg (fun z => z * c⁻¹) h1
      rw [mul_assoc, mul_inv_cancel, mul_one] at h
      exact h
    exact hs0 (by rw [hseq]; exact B.S0.mul_mem B.t_mem (B.S0.inv_mem hc))
  exact ⟨⟨hxH, orderOf_eq_prime (by rw [pow_two]; exact hx2) hx_ne_one⟩, hx_ne_t⟩

end Work.CORE2A
