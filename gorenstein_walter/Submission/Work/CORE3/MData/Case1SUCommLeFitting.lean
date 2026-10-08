import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE2A.Basic

/-!
# `⁅S, U⁆ ≤ F(U)` under Case (1) of Bender's Theorem 2.10

Bender 1981 §3 (the case (1) analysis): with `S` the fixed Sylow 2-subgroup, `H = C_G(t)` and
`U = O(H)`, one wants `⁅S, U⁆ ≤ F(U)` (Bender's `[S,U] ≤ F(U)`).

In case (1) each `s ∈ S − S₀` carries a Hall subgroup `I = I_U(s) ⊆ F(U)` with normalizer
controlled through `Ĥ` (Bender, hypotheses (8)).  The subgroup `U = O(H)` is odd of order prime
to `2`, `S ≤ H ≤ N_G(U)` and `F(U) ◁ U`; consequently, for `φ ∈ S − S₀` and `u ∈ U` the element
`u⁻¹(φuφ⁻¹)` lies in `I ⊆ F(U)` and `⁅φ, u⁆ = u·(u⁻¹(φuφ⁻¹))·u⁻¹` is its `U`-conjugate, hence
lies in `F(U)`.  Every `g ∈ S₀` is a product `g = s₀·(s₀g)` of two elements of `S − S₀`, and the
identity `⁅ab,u⁆ = a⁅b,u⁆a⁻¹·⁅a,u⁆` finishes.
-/

open scoped MatrixGroups commutatorElement

namespace Work.CORE3.MData

open Subgroup

theorem Case1SUCommLeFitting {G : Type} [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hCase1 : Work.GW2.Case1 B) : ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U := by
  classical
  -- `S` is dihedral, so every element of `S − S₀` is an involution.
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hCtx B
  have hord : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → orderOf s = 2 :=
    Work.CORE3.OutsideS0OrderTwo G hCtx B n hn2 hdih
  -- `S ≤ H ≤ N_G(U)`.
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE3.le_normalizer_map_subtype_of_normal' (K := B.H) (N := Work.GW2.oddCore ↥B.H)
      inferInstance
  have hSN : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    (Work.CORE2A.bSetup_S_le_H B).trans hHN
  -- `U ≤ N_G(F(U))`, since `F(U)` is characteristic (hence normal) in `U`.
  have hUN : B.U ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    Work.CORE3.le_normalizer_map_subtype_of_normal' (K := B.U) (N := Work.GW2.fitting B.U)
      (Subgroup.normalCore_normal _)
  have hnorm : ∀ u ∈ B.U, ∀ w ∈ Work.GW2.fittingIn B.U,
      u * w * u⁻¹ ∈ Work.GW2.fittingIn B.U := by
    rw [Subgroup.le_normalizer_iff] at hUN
    exact fun u hu w hw => hUN u hu w hw
  -- **Key step.** For `φ ∈ S − S₀` and `u ∈ U`, the commutator `⁅φ,u⁆` lies in `F(U)`.
  have key : ∀ φ ∈ (B.S : Subgroup G), φ ∉ B.S0 →
      ∀ u ∈ B.U, ⁅φ, u⁆ ∈ Work.GW2.fittingIn B.U := by
    intro φ hφS hφ0 u hu
    obtain ⟨I, hIeq, hIH⟩ := hCase1.1 φ hφS hφ0
    have hIle : I ≤ Work.GW2.fittingIn B.U := hIH.1
    have hφ2 : φ * φ = 1 := by
      have h := hord φ hφS hφ0
      rw [orderOf_eq_iff (by norm_num : 0 < 2)] at h
      simpa [pow_two] using h.1
    -- `u⁻¹(φuφ⁻¹) ∈ I = I_U(φ)`.
    have hmem : u⁻¹ * (φ * u * φ⁻¹) ∈ I := by
      have hs : u⁻¹ * (φ * u * φ⁻¹) ∈ (I : Set G) := by
        rw [hIeq, Work.GW2.invSet]
        refine ⟨?_, ?_⟩
        · exact B.U.mul_mem (B.U.inv_mem hu)
            ((Subgroup.mem_normalizer_iff.mp (hSN hφS) u).mp hu)
        · show φ * (u⁻¹ * (φ * u * φ⁻¹)) * φ⁻¹ = (u⁻¹ * (φ * u * φ⁻¹))⁻¹
          have hφinv : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφ2
          have e1 : (u⁻¹ * (φ * u * φ⁻¹))⁻¹ = φ * u⁻¹ * φ * u := by
            rw [show (u⁻¹ * (φ * u * φ⁻¹))⁻¹ = φ * u⁻¹ * φ⁻¹ * u from by group, hφinv]
          rw [e1, hφinv]
          have e2 : φ * (u⁻¹ * (φ * u * φ)) * φ = φ * u⁻¹ * φ * u * (φ * φ) := by group
          rw [e2, hφ2, mul_one]
      exact hs
    -- `⁅φ,u⁆` is the `u`-conjugate of that element, hence lies in the normal `F(U)`.
    have hconj : u * (u⁻¹ * (φ * u * φ⁻¹)) * u⁻¹ ∈ Work.GW2.fittingIn B.U :=
      hnorm u hu _ (hIle hmem)
    convert hconj using 1
    rw [commutatorElement_def]
    group
  -- Decompose an arbitrary `g ∈ S` into two elements outside `S₀`.
  obtain ⟨s0, hs0S, hs00⟩ := Work.CORE2A.bSetup_exists_mem_S_not_mem_S0 B
  have hs02 : s0 * s0 = 1 := by
    have h := hord s0 hs0S hs00
    rw [orderOf_eq_iff (by norm_num : 0 < 2)] at h
    simpa [pow_two] using h.1
  rw [Subgroup.commutator_le]
  intro g hg u hu
  by_cases hg0 : g ∈ B.S0
  · have h1 : ⁅s0, u⁆ ∈ Work.GW2.fittingIn B.U := key s0 hs0S hs00 u hu
    have hgs0S : g * s0 ∈ (B.S : Subgroup G) := (B.S).mul_mem hg hs0S
    have hgs00 : g * s0 ∉ B.S0 := by
      intro h
      apply hs00
      have h' : s0 = g⁻¹ * (g * s0) := by group
      rw [h']
      exact B.S0.mul_mem (B.S0.inv_mem hg0) h
    have h2 : s0 * ⁅s0 * g, u⁆ * s0⁻¹ ∈ Work.GW2.fittingIn B.U := by
      have hbase : ⁅g * s0, s0 * u * s0⁻¹⁆ ∈ Work.GW2.fittingIn B.U :=
        key (g * s0) hgs0S hgs00 (s0 * u * s0⁻¹)
          ((Subgroup.mem_normalizer_iff.mp (hSN hs0S) u).mp hu)
      have heq : s0 * (s0 * g) * s0⁻¹ = g * s0 := by
        rw [← mul_assoc s0 s0 g, hs02, one_mul, inv_eq_of_mul_eq_one_right hs02]
      rw [conjugate_commutatorElement (s0 * g) u s0, heq]
      exact hbase
    have hdecomp : ⁅g, u⁆ = s0 * ⁅s0 * g, u⁆ * s0⁻¹ * ⁅s0, u⁆ := by
      have hg' : g = s0 * (s0 * g) := by rw [← mul_assoc, hs02, one_mul]
      conv_lhs => rw [hg']
      exact commutatorElement_mul_left_eq_conj_mul s0 (s0 * g) u
    rw [hdecomp]
    exact (Work.GW2.fittingIn B.U).mul_mem h2 h1
  · exact key g hg hg0 u hu

end Work.CORE3.MData
