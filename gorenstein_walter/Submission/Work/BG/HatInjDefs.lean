import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.invJCard

/-!
# Area BG: `HatInjProp` — shared vocabulary

Conjugation by `C.s` (an involution of `C.P.H ∖ C.P.H0`) preserves `C.P.U`: for `u ∈ U`,
`C.s * u * C.s⁻¹ = (C.s * u * C.s⁻¹ * u) * u⁻¹` with both factors in `U` (the first by
`Sec2Ctx.s_inverts`, the second because `U` is a subgroup).  Hence conjugation by `C.s`
restricts to an automorphism `sigmaU C` of `↥C.P.U`, an involution, whose fixed points
`fixedSubgroup (sigmaU C)` are the elements of `U` centralized by `C.s`.

The abstract lemma `Work.BG.glauberman_injective` (in `hatInjCore.lean`) is stated for an
arbitrary finite group of odd order with an involutive automorphism; `sigmaU` is the
instantiation used for `HatInjProp`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

section defs

variable (C : Sec2Ctx G)

/-- Conjugation by `s` preserves `U`. -/
theorem conj_mem_U {u : G} (hu : u ∈ C.P.U) : (C.s : G) * u * (C.s : G)⁻¹ ∈ C.P.U := by
  have h1 : (C.s : G) * u * (C.s : G)⁻¹ * u ∈ C.P.U := C.s_inverts u (C.P.U_le_H0 hu)
  have h2 : u⁻¹ ∈ C.P.U := C.P.U.inv_mem hu
  have heq : (C.s : G) * u * (C.s : G)⁻¹
      = ((C.s : G) * u * (C.s : G)⁻¹ * u) * u⁻¹ := by group
  rw [heq]
  exact C.P.U.mul_mem h1 h2

theorem s_mul_self_coe : (C.s : G) * (C.s : G) = 1 := by
  have h := congrArg (fun x : ↥C.P.H => (x : G)) C.s_sq
  simpa [pow_two] using h

/-- Conjugation by `s` as an automorphism of `↥C.P.U`. -/
noncomputable def sigmaU : ↥C.P.U ≃* ↥C.P.U where
  toFun u := ⟨(C.s : G) * (u : G) * (C.s : G)⁻¹, conj_mem_U C u.2⟩
  invFun u := ⟨(C.s : G) * (u : G) * (C.s : G)⁻¹, conj_mem_U C u.2⟩
  left_inv u := by
    apply Subtype.ext
    have hs := s_mul_self_coe C
    show (C.s : G) * ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹ = (u : G)
    calc (C.s : G) * ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹
        = ((C.s : G) * (C.s : G)) * (u : G) * ((C.s : G)⁻¹ * (C.s : G)⁻¹) := by group
      _ = (u : G) := by
          rw [hs, one_mul, ← mul_inv_rev, hs, inv_one, mul_one]
  right_inv u := by
    apply Subtype.ext
    have hs := s_mul_self_coe C
    show (C.s : G) * ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹ = (u : G)
    calc (C.s : G) * ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹
        = ((C.s : G) * (C.s : G)) * (u : G) * ((C.s : G)⁻¹ * (C.s : G)⁻¹) := by group
      _ = (u : G) := by
          rw [hs, one_mul, ← mul_inv_rev, hs, inv_one, mul_one]
  map_mul' u v := by
    apply Subtype.ext
    show (C.s : G) * ((u : G) * (v : G)) * (C.s : G)⁻¹
        = ((C.s : G) * (u : G) * (C.s : G)⁻¹) * ((C.s : G) * (v : G) * (C.s : G)⁻¹)
    group

@[simp] theorem sigmaU_apply_coe (u : ↥C.P.U) :
    ((sigmaU C u : ↥C.P.U) : G) = (C.s : G) * (u : G) * (C.s : G)⁻¹ := rfl

/-- `sigmaU` is an involution. -/
theorem sigmaU_mul_self : sigmaU C * sigmaU C = 1 := by
  refine MulEquiv.ext fun u => ?_
  show sigmaU C (sigmaU C u) = u
  apply Subtype.ext
  have hs := s_mul_self_coe C
  rw [sigmaU_apply_coe, sigmaU_apply_coe]
  calc (C.s : G) * ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹
      = ((C.s : G) * (C.s : G)) * (u : G) * ((C.s : G)⁻¹ * (C.s : G)⁻¹) := by group
    _ = (u : G) := by
        rw [hs, one_mul, ← mul_inv_rev, hs, inv_one, mul_one]

end defs

section compat

variable {D : BGData G} {C : Sec2Ctx G}

/-- `U = C.P.U` has odd order. -/
theorem odd_card_U_of_compat (hc : Compat D C) : Odd (Nat.card ↥C.P.U) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [hc.U_eq]
  exact odd_card_U D

end compat

section abstract

variable {U : Type*} [Group U]

/-- The `σ`-invariant irreducible characters of `U`. -/
abbrev SigmaInvIrr (U : Type*) [Group U] (σ : MulAut U) : Type _ :=
  {α : IrreducibleCharacter U // ∀ u : U, (α : ClassFunction U ℂ) (σ u) = (α : ClassFunction U ℂ) u}

end abstract

section restrict

variable {G : Type} [Group G] [Finite G]

/-- Restriction of a class function of `H₀` to `U` (along `U ≤ H₀`). -/
noncomputable def restrictU (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction ↥C.P.U ℂ :=
  ClassFunction.compHom (Subgroup.inclusion C.P.U_le_H0) ν

theorem restrictU_apply (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) (u : ↥C.P.U) :
    restrictU C ν u = ν ⟨(u : G), C.P.U_le_H0 u.2⟩ := rfl

end restrict

end Work.BG
