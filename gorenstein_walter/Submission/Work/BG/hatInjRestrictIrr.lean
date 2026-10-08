import Mathlib
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.CharBridge

namespace Work.BG

set_option linter.style.haveILetI false in
open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
/-- For `ν ∈ 𝒮₄(C)` (irreducible, `s`-invariant, `t ∈ ker ν`), the restriction `ν|_U` is an
irreducible character of `U = C.P.U`.

Route: `t ∈ ker ν` forces `ν(u·t) = ν(u)` for all `u ∈ U`
(`OddOrder.RepresentationTheory.apply_mul_eq_of_mem_characterKernel`), and `H₀ = U ∪ t·U` because
`[H₀ : U] = 2` (`Work.BG.rem31IndexUin` plus `hn`), hence
`(ν|_U, ν|_U)_U = (ν, ν)_{H₀} = 1`; irreducibility then follows from the norm-one criterion
`OddOrder.RepresentationTheory.isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`
(`ν|_U` is a genuine character because `IsIrreducibleCharacter` is representation-based).

The proof below takes the equivalent inflation route, which avoids the normalization of the
inner product: `t ∈ ker ν` puts `⟨t⟩` inside the character kernel of `ν`, so
`OddOrder.RepresentationTheory.exists_inflate_eq_of_subset_characterKernel` writes
`ν = mk'⟨t⟩ * χ̄` for an irreducible `χ̄` of `H₀/⟨t⟩`; and `U → H₀/⟨t⟩`,
`u ↦ u⟨t⟩`, is *onto* because `H₀ = U ∪ t·U` (from `[H₀ : U] = 2`, `t ∉ U`). Hence `ν|_U` is
the pullback of the irreducible `χ̄` along a surjection, hence irreducible
(`IsIrreducibleCharacter.compHom_of_surjective`). -/
theorem hatInjRestrictIrr {G : Type} [Group G] [Finite G] {D : Work.GW2.BGData G}
    (C : Work.BG.Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.S4Index C) :
    IsIrreducibleCharacter (Work.BG.restrictU C ν) := by
  classical
  -- `U = C.P.U` has index two in `H₀`, and `t ∉ U`.
  have hidx : (Work.GW2.C16.Uin C).index = 2 := by rw [Work.BG.rem31IndexUin D C hc, hn]
  have htU : C.t ∉ Work.GW2.C16.Uin C := by
    intro h; exact C.t_not_mem_U ((Subgroup.mem_subgroupOf.mp h))
  -- Coset decomposition: every `x ∉ U` in `H₀` is `t * u` with `u ∈ U`.
  have hcoset : ∀ x : ↥C.P.H0, x ∉ Work.GW2.C16.Uin C →
      ∃ u : ↥C.P.U, x = C.t * Subgroup.inclusion C.P.U_le_H0 u := by
    intro x hx
    have htinv : (C.t)⁻¹ ∉ Work.GW2.C16.Uin C :=
      fun h => htU (by simpa using (Work.GW2.C16.Uin C).inv_mem h)
    have hmem : (C.t)⁻¹ * x ∈ Work.GW2.C16.Uin C := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false htinv hx
    refine ⟨⟨(((C.t)⁻¹ * x : ↥C.P.H0) : G), Subgroup.mem_subgroupOf.mp hmem⟩, ?_⟩
    apply Subtype.ext
    show (x : G) = (C.t : G) * (((C.t)⁻¹ * x : ↥C.P.H0) : G)
    rw [show (((C.t)⁻¹ * x : ↥C.P.H0) : G) = (C.t : G)⁻¹ * (x : G) from rfl]
    group
  -- `⟨t⟩ ⊴ H₀`: `t` is central in `H = C_G(t)`.
  haveI hNnormal : (Subgroup.zpowers C.t).Normal := ⟨fun n hn g => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hcomm : g * C.t = C.t * g := by
        apply Subtype.ext
        exact C.t_comm_H (g : G) (C.P.H0_le_H g.2)
      have hconj : g * C.t * g⁻¹ = C.t := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [← hk, ← conj_zpow, hconj]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩
  -- `t` lies in the character kernel of `ν` (this is `ν ∈ 𝒮₄(C)`).
  have ht_ker : C.t ∈ OddOrder.Peterfalvi.S03.characterKernel ν := by
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    exact hν.2.2
  have hker : ((Subgroup.zpowers C.t : Subgroup ↥C.P.H0) : Set ↥C.P.H0)
      ⊆ OddOrder.Peterfalvi.S03.characterKernel ν := by
    have hK : C.t ∈ OddOrder.Peterfalvi.S03.characterKernelSubgroup hν.1.isCharacter := by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernelSubgroup]
      exact ht_ker
    have hle := Subgroup.zpowers_le_of_mem hK
    intro x hx
    have hx' : x ∈ OddOrder.Peterfalvi.S03.characterKernelSubgroup hν.1.isCharacter := hle hx
    rwa [OddOrder.Peterfalvi.S03.mem_characterKernelSubgroup] at hx'
  -- `ν` is the inflation of an irreducible character `χbar` of `H₀/⟨t⟩`.
  obtain ⟨χbar, hχbar⟩ := OddOrder.RepresentationTheory.exists_inflate_eq_of_subset_characterKernel
      (Subgroup.zpowers C.t) (⟨ν, hν.1⟩ : IrreducibleCharacter ↥C.P.H0) hker
  have hνeq : ν = ClassFunction.compHom (QuotientGroup.mk' (Subgroup.zpowers C.t))
      (χbar : ClassFunction (↥C.P.H0 ⧸ Subgroup.zpowers C.t) ℂ) := by
    have h1 := congrArg
      (fun χ : IrreducibleCharacter ↥C.P.H0 => (χ : ClassFunction ↥C.P.H0 ℂ)) hχbar
    rw [OddOrder.RepresentationTheory.inflate_coe] at h1
    exact h1.symm
  -- `U → H₀/⟨t⟩` (the composite `mk' ⟨t⟩ ∘ incl`) is surjective: `H₀ = U ∪ t·U` and `t ∈ ⟨t⟩`.
  have hsurj : Function.Surjective ((QuotientGroup.mk' (Subgroup.zpowers C.t)).comp
      (Subgroup.inclusion C.P.U_le_H0)) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers C.t) q
    by_cases hy : y ∈ Work.GW2.C16.Uin C
    · refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
      show QuotientGroup.mk' (Subgroup.zpowers C.t)
          (Subgroup.inclusion C.P.U_le_H0
            (⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ : ↥C.P.U))
        = QuotientGroup.mk' (Subgroup.zpowers C.t) y
      have h2 : Subgroup.inclusion C.P.U_le_H0
          (⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ : ↥C.P.U) = y := by
        apply Subtype.ext
        rfl
      rw [h2]
    · obtain ⟨u, hu⟩ := hcoset y hy
      refine ⟨u, ?_⟩
      show QuotientGroup.mk' (Subgroup.zpowers C.t) (Subgroup.inclusion C.P.U_le_H0 u)
        = QuotientGroup.mk' (Subgroup.zpowers C.t) y
      have htN : C.t ∈ Subgroup.zpowers C.t := Subgroup.mem_zpowers C.t
      have h1 : QuotientGroup.mk' (Subgroup.zpowers C.t)
          (C.t * Subgroup.inclusion C.P.U_le_H0 u)
          = QuotientGroup.mk' (Subgroup.zpowers C.t) (Subgroup.inclusion C.P.U_le_H0 u) := by
        rw [map_mul, show QuotientGroup.mk' (Subgroup.zpowers C.t) C.t = 1 from ?_, one_mul]
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff C.t).mpr htN
      rw [hu]
      exact h1.symm
  -- `ν|_U` is the pullback of `χbar` along this surjection, hence irreducible.
  have hkey : Work.BG.restrictU C ν = ClassFunction.compHom
      ((QuotientGroup.mk' (Subgroup.zpowers C.t)).comp (Subgroup.inclusion C.P.U_le_H0))
      (χbar : ClassFunction (↥C.P.H0 ⧸ Subgroup.zpowers C.t) ℂ) := by
    unfold Work.BG.restrictU
    rw [hνeq]
    rfl
  rw [hkey]
  exact IsIrreducibleCharacter.compHom_of_surjective hsurj χbar.isIrreducible

end Work.BG
