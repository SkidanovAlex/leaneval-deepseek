import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.s02_assemblyCore

/-!
# Area BG: input I-4a — the `Λ`-orbit sum vanishes off `U`

This file proves `Work.BG.s02_orbitSumVanish`, i.e. `Work.BG.OrbitSumVanishProp C`
(Bender–Glauberman 1981, Lemma 1.7(i) in orbit form, in the shape used by the
coherence theorem 2.3): for `ν ∈ Irr(H₀)` and `g ∈ H₀ ∖ U`,

  `∑_{ξ ∈ Irr(H₀)} [ξ ∈ Λν] · ξ(g) = 0`,

where `[ξ ∈ Λν]` is the indicator of the `Λ`-orbit of `ν` (`Λ` = the group of linear
characters of `H₀/U`, `Work.BG.Lambda`).

The argument does not need the paper's normalised orbit sum: since multiplication by a
linear character is a bijection of `Irr(H₀)` that preserves the orbit `Λν` (`lambda_mul_irreducible`,
`s02c_LamEquiv_trans`), the value `(λ_β · χ)(g) = λ_β(g)·χ(g)` gives, for every `β`,

  `reflection(β) : ∑_{χ ∈ Λν} (λ_β χ)(g) = λ_β(g) · ∑_{χ ∈ Λν} χ(g)`,

so summing over all `β ∈ (H₀/U)^*` and using the regular-character vanishing
`∑_β λ_β(g) = 0` (`Work.BG.lambdaSum_apply_eq_zero_of_not_mem_U`, which needs `H₀/U`
abelian — here `H₀/U` is cyclic by `Sec2Ctx.quot_cyclic`) yields
`|(H₀/U)^*| · ∑_{χ ∈ Λν} χ(g) = 0`, whence the claim.

The only group-theoretic input is that `H₀/U` is commutative, which is extracted from the
cyclicity recorded in `Sec2Ctx.quot_cyclic` (`commutator_mem_of_quot_cyclic`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory
open scoped commutatorElement
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- `H₀/U` is commutative: the commutator of any two elements of `H₀` lies in `U`.

The hypothesis `Sec2Ctx.quot_cyclic` exhibits an element `c` whose image generates
`H₀/U`, so all elements of `H₀/U` are powers of one element and the quotient is
commutative; `U ◁ H₀` is the kernel of the projection. -/
theorem commutator_mem_of_quot_cyclic (C : Sec2Ctx G) :
    ∀ x y : ↥C.P.H0, ⁅x, y⁆ ∈ C.P.U.subgroupOf C.P.H0 := by
  classical
  intro x y
  set N := C.P.U.subgroupOf C.P.H0 with hN
  haveI : N.Normal := C.U_normal
  obtain ⟨c, hc, hcyc⟩ := C.quot_cyclic
  set c0 : ↥C.P.H0 := ⟨c, hc⟩ with hc0
  -- every element of `H₀/U` is a power of the image of `c`
  have hqx : ∀ z : ↥C.P.H0,
      QuotientGroup.mk' N z ∈ Subgroup.zpowers (QuotientGroup.mk' N c0) := by
    intro z
    obtain ⟨k, hk⟩ := hcyc (z : G) z.2
    have hmem : (⟨(z : G) * (c ^ k)⁻¹,
        C.P.H0.mul_mem z.2 (C.P.H0.inv_mem (Subgroup.zpow_mem C.P.H0 hc k))⟩ : ↥C.P.H0) ∈ N :=
      Subgroup.mem_subgroupOf.mpr hk
    have h1 : QuotientGroup.mk' N (⟨(z : G) * (c ^ k)⁻¹,
        C.P.H0.mul_mem z.2 (C.P.H0.inv_mem (Subgroup.zpow_mem C.P.H0 hc k))⟩ : ↥C.P.H0) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have he : (⟨(z : G) * (c ^ k)⁻¹,
        C.P.H0.mul_mem z.2 (C.P.H0.inv_mem (Subgroup.zpow_mem C.P.H0 hc k))⟩ : ↥C.P.H0)
        = z * (c0 ^ k)⁻¹ := by
      apply Subtype.ext
      simp [c0]
    rw [he, map_mul, map_inv, map_zpow] at h1
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, (mul_inv_eq_one.mp h1).symm⟩
  have hgen : ∀ a : quotGroup C.P, a ∈ Subgroup.zpowers (QuotientGroup.mk' N c0) := by
    intro a
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective N a
    rw [← hz]
    exact hqx z
  have hcomm : ∀ a b : quotGroup C.P, a * b = b * a := by
    intro a b
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
    rw [← hm, ← hn]
    exact ((Commute.refl _).zpow_zpow m n).eq
  have hmain : QuotientGroup.mk' N ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  exact (QuotientGroup.eq_one_iff _).mp hmain

set_option maxHeartbeats 2000000 in
/-- **I-4a.** The `Λ`-orbit sum of `ν ∈ Irr(H₀)` vanishes on `H₀ ∖ U`
(Bender–Glauberman 1981, Lemma 1.7(i), in the `Irr(H₀)`-indexed form used by 2.3). -/
theorem s02_orbitSumVanish {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)] :
    Work.BG.OrbitSumVanishProp C := by
  classical
  intro ν hν g hg
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(C.P.U.subgroupOf C.P.H0) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (quotGroup C.P →* ℂˣ) := Fintype.ofFinite _
  -- `∑_{β} λ_β` (the regular character of `H₀/U`) vanishes at `g ∉ U`
  have hgU : g ∉ C.P.U.subgroupOf C.P.H0 := fun h => hg (Subgroup.mem_subgroupOf.mp h)
  have hsum0 : Work.BG.lambdaSum C.P g = 0 :=
    Work.BG.lambdaSum_apply_eq_zero_of_not_mem_U C.P (commutator_mem_of_quot_cyclic C) hgU
  -- the orbit of `ν` inside `Irr(H₀)`, and its sum of values at `g`
  let O := {χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 //
    LamEquiv C ν (χ : ClassFunction ↥C.P.H0 ℂ)}
  let S : ℂ := ∑ χ : O, ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g)
  have hIrred : ∀ (β : quotGroup C.P →* ℂˣ) (δ : ClassFunction ↥C.P.H0 ℂ),
      IsIrreducibleCharacter δ → IsIrreducibleCharacter (lamCF C β * δ) :=
    fun β δ hδ => lambda_mul_irreducible C.P (show lamCF C β ∈ Lambda C.P from ⟨β, rfl⟩) hδ
  have horb : ∀ (β : quotGroup C.P →* ℂˣ)
      (χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0),
      LamEquiv C ν (χ : ClassFunction ↥C.P.H0 ℂ) →
      LamEquiv C ν (lamCF C β * (χ : ClassFunction ↥C.P.H0 ℂ)) :=
    fun β χ hχ => s02c_LamEquiv_trans C hχ ⟨β, rfl⟩
  -- multiplication of the orbit `Λν` by `λ_β` is a permutation of `Λν`
  let tau : (quotGroup C.P →* ℂˣ) → (O ≃ O) := fun β =>
    { toFun := fun χ => ⟨⟨lamCF C β * (χ.1 : ClassFunction ↥C.P.H0 ℂ),
        hIrred β (χ.1 : ClassFunction ↥C.P.H0 ℂ) χ.1.2⟩,
        horb β χ.1 χ.2⟩
      invFun := fun χ => ⟨⟨lamCF C β⁻¹ * (χ.1 : ClassFunction ↥C.P.H0 ℂ),
        hIrred β⁻¹ (χ.1 : ClassFunction ↥C.P.H0 ℂ) χ.1.2⟩,
        horb β⁻¹ χ.1 χ.2⟩
      left_inv := fun χ => by
        apply Subtype.ext
        apply Subtype.ext
        show lamCF C β⁻¹ * (lamCF C β * (χ.1 : ClassFunction ↥C.P.H0 ℂ))
          = (χ.1 : ClassFunction ↥C.P.H0 ℂ)
        rw [← s02c_cf_mul_assoc, ← s02c_lamCF_mul,
          show (β⁻¹ * β) = (1 : quotGroup C.P →* ℂˣ) from inv_mul_cancel β,
          s02c_lamCF_one_mul]
      right_inv := fun χ => by
        apply Subtype.ext
        apply Subtype.ext
        show lamCF C β * (lamCF C β⁻¹ * (χ.1 : ClassFunction ↥C.P.H0 ℂ))
          = (χ.1 : ClassFunction ↥C.P.H0 ℂ)
        rw [← s02c_cf_mul_assoc, ← s02c_lamCF_mul,
          show (β * β⁻¹) = (1 : quotGroup C.P →* ℂˣ) from mul_inv_cancel β,
          s02c_lamCF_one_mul] }
  have hstep1 : ∀ β : quotGroup C.P →* ℂˣ,
      (∑ χ : O, (lamCF C β * (χ.1 : ClassFunction ↥C.P.H0 ℂ)) g) = S := fun β =>
    Equiv.sum_comp (tau β) (fun χ : O => ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g))
  -- the target sum is the sum over the orbit
  have htarget : (∑ ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
      orbitTerm C ν (ξ : ClassFunction ↥C.P.H0 ℂ) g) = S := by
    have hfilt : (∑ ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        orbitTerm C ν (ξ : ClassFunction ↥C.P.H0 ℂ) g)
        = ∑ ξ ∈ Finset.univ.filter
            (fun ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 =>
              LamEquiv C ν (ξ : ClassFunction ↥C.P.H0 ℂ)),
            ((ξ : ClassFunction ↥C.P.H0 ℂ) g) := by
      simp only [orbitTerm]
      exact (Finset.sum_filter (s := Finset.univ)
        (fun ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 =>
          LamEquiv C ν (ξ : ClassFunction ↥C.P.H0 ℂ))
        (fun ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 =>
          ((ξ : ClassFunction ↥C.P.H0 ℂ) g))).symm
    rw [hfilt]
    exact Finset.sum_subtype _ (by intro x; simp) _
  -- summing the identity `S = λ_β(g)·S` over all `β`
  have hchain : (Fintype.card (quotGroup C.P →* ℂˣ) : ℂ) * S = 0 := by
    have h2 : (∑ β : quotGroup C.P →* ℂˣ, (1:ℂ))
        = (Fintype.card (quotGroup C.P →* ℂˣ) : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have h1 : (∑ β : quotGroup C.P →* ℂˣ, (1:ℂ)) * S = ∑ β : quotGroup C.P →* ℂˣ, S := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun β _ => one_mul S)
    have hsumr : (∑ β : quotGroup C.P →* ℂˣ, (lamCF C β) g) = Work.BG.lambdaSum C.P g := by
      simp only [Work.BG.lambdaSum, Work.BG.lamCF, ClassFunction.sum_apply]
    rw [← h2, h1]
    calc ∑ β : quotGroup C.P →* ℂˣ, S
        = ∑ β : quotGroup C.P →* ℂˣ, ∑ χ : O,
            (lamCF C β * (χ.1 : ClassFunction ↥C.P.H0 ℂ)) g :=
          Finset.sum_congr rfl (fun β _ => (hstep1 β).symm)
      _ = ∑ χ : O, ∑ β : quotGroup C.P →* ℂˣ,
            (lamCF C β * (χ.1 : ClassFunction ↥C.P.H0 ℂ)) g := Finset.sum_comm
      _ = ∑ χ : O, ∑ β : quotGroup C.P →* ℂˣ,
            (lamCF C β) g * ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g) :=
          Finset.sum_congr rfl (fun χ _ => Finset.sum_congr rfl (fun β _ => by
            rw [ClassFunction.mul_apply]))
      _ = ∑ χ : O, (∑ β : quotGroup C.P →* ℂˣ, (lamCF C β) g) *
            ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g) :=
          Finset.sum_congr rfl (fun χ _ =>
            (Finset.sum_mul Finset.univ (fun β : quotGroup C.P →* ℂˣ => (lamCF C β) g)
              ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g)).symm)
      _ = ∑ χ : O, (Work.BG.lambdaSum C.P g) * ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [hsumr]
      _ = ∑ χ : O, (0 : ℂ) * ((χ.1 : ClassFunction ↥C.P.H0 ℂ) g) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [hsum0]
      _ = 0 := by simp
  have hcard : (Fintype.card (quotGroup C.P →* ℂˣ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨1⟩).ne'
  have hS0 : S = 0 := by
    rcases mul_eq_zero.mp hchain with h | h
    · exact absurd h hcard
    · exact h
  rw [htarget, hS0]

end Work.BG
