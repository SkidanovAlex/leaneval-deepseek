import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.centralValue
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_quotCyclic
import Submission.Work.BG.s02_lamSign
import Submission.Work.BG.s02_lamDualCyclic
import Submission.Work.BG.s02_indexSq

/-!
# Area BG: BG Lemma 2.1's extension clause (`Lemma21ExtProp`)

Bender–Glauberman 1981, p. 204 (Lemma 2.1 and its use on p. 206): for `ν ∈ Irr(H₀)` with
`ν^s ≠ ν` and not (`|Λν| = 4` and `(Λν)^s = Λν`), the orbit `Λν` contains a character `μ`
with `μ^s ≠ μ` and `μ(t) = -ν(t)`.

The proof runs through the dual group `Λ = H₀/U →* ℂˣ` (`Work.BG.lamDual`):

* if `ν(t) = 0`, then `μ := ν` works;
* otherwise every `λ ∈ Λ ∖ Λ¹` (where `Λ¹ = ker(t-eval)`) twists `ν` into an element of the orbit
  whose value at `t` is `-ν(t)`; if such a twist were always `s`-fixed, then all squares of
  `Λ¹` would stabilise `ν`, whence `[Λ : Λ₁] = [Λ : Λ¹]·[Λ¹ : Λ₁] ≤ 2·2 = 4`, and since
  `[Λ : Λ₁] ≠ 1` (the excluded configuration), it is exactly `4` — i.e. the excluded
  configuration occurs and the hypothesis of the lemma is violated.

This file also holds the small auxiliary facts about `Λ` and the `Λ`-action used in the argument.
-/

namespace Work.BG

set_option linter.style.haveILetI false

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary algebra of `lamCF` -/

/-- Cancellation: `lamCF C β⁻¹ * (lamCF C β * ν) = ν`. -/
theorem lamCF_cancel (C : Sec2Ctx G) (β : lamDual C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β⁻¹ * (lamCF C β * ν) = ν := by
  rw [← mul_assoc_cf, ← lamCF_mul, show β⁻¹ * β = 1 from inv_mul_cancel β, lamCF_one, one_mul_cf]

/-- Reassociation: `lamCF C β * (lamCF C γ * ν) = lamCF C (β * γ) * ν`. -/
theorem lamCF_mul_assoc_h (C : Sec2Ctx G) (β γ : lamDual C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β * (lamCF C γ * ν) = lamCF C (β * γ) * ν := by
  rw [← mul_assoc_cf, ← lamCF_mul]

/-- Cancellation, in the other order: `lamCF C β * (lamCF C β⁻¹ * f) = f`. -/
theorem lamCF_cancel_left (C : Sec2Ctx G) (β : lamDual C) (f : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β * (lamCF C β⁻¹ * f) = f := by
  rw [← mul_assoc_cf, ← lamCF_mul, show β * β⁻¹ = 1 from mul_inv_cancel β, lamCF_one, one_mul_cf]

/-- If two `Λ`-twists of `ν` agree, the quotient of the twisting characters stabilises `ν`. -/
theorem mem_lamStab_of_mul_eq (C : Sec2Ctx G) {ν : ClassFunction ↥C.P.H0 ℂ} {β γ : lamDual C}
    (h : lamCF C β * ν = lamCF C γ * ν) : β⁻¹ * γ ∈ lamStab C ν := by
  rw [mem_lamStab]
  have h2 := congrArg (fun f => lamCF C β⁻¹ * f) h
  rw [lamCF_cancel C β ν, lamCF_mul_assoc_h C β⁻¹ γ ν] at h2
  exact h2.symm

/-! ## `Λ¹ = ker (t-eval)` and the `Λ`-orbits -/

/-- **`Λ¹` has index `2` in `Λ`**: evaluation at `tU` is onto `{±1}` (by `s02_lamSign`) and its
values are `±1` (as `tU² = 1`). -/
theorem lamKernel_index (C : Sec2Ctx G) : (lamKernel C).index = 2 := by
  obtain ⟨b0, hb0⟩ := s02_lamSign C
  rw [lamKernel, Subgroup.index_ker]
  have hle : (lamEvt C).range ≤ Subgroup.zpowers (-1 : ℂˣ) := by
    rintro x ⟨β, rfl⟩
    have h2 : (β (tU C)) ^ 2 = 1 := by rw [← map_pow, tU_sq, map_one]
    have h2C : (((β (tU C) : ℂˣ)) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    rcases mul_eq_zero.mp (show ((((β (tU C) : ℂˣ)) : ℂ) - 1) *
        ((((β (tU C) : ℂˣ)) : ℂ) + 1) = 0 by linear_combination h2C) with h | h
    · have h1 : (lamEvt C) β = 1 := by
        rw [lamEvt_apply]
        exact Units.ext (sub_eq_zero.mp h)
      rw [h1]
      exact Subgroup.one_mem _
    · have h1 : (lamEvt C) β = -1 := by
        rw [lamEvt_apply]
        refine Units.ext ?_
        simp only [Units.val_neg, Units.val_one]
        linear_combination h
      rw [h1]
      exact Subgroup.mem_zpowers _
  have hge : Subgroup.zpowers (-1 : ℂˣ) ≤ (lamEvt C).range :=
    Subgroup.zpowers_le.mpr ⟨b0, hb0⟩
  rw [le_antisymm hle hge, Nat.card_zpowers]
  exact orderOf_eq_prime (by norm_num) (by norm_num)

/-- **Orbit–stabiliser for the `Λ`-action**: `|Λν| = [Λ : Λ_ν]`. -/
theorem ncard_lamOrbit_eq_index (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    (lamOrbit C ν).ncard = (lamStab C ν).index := by
  rw [lamStab, ← orbit_eq_lamOrbit C ν]
  exact (MulAction.index_stabilizer (lamDual C) ν).symm

/-- When `ν(t) ≠ 0`, the stabiliser `Λ_ν` lies in `Λ¹` (a character fixing `ν` is trivial at
`t`). -/
theorem lamStab_le_lamKernel (C : Sec2Ctx G) {ν : ClassFunction ↥C.P.H0 ℂ} (h0 : ν C.t ≠ 0) :
    lamStab C ν ≤ lamKernel C := by
  intro β hβ
  rw [mem_lamKernel]
  rw [mem_lamStab] at hβ
  have h2 : (lamCF C β * ν) C.t = ν C.t := by rw [hβ]
  rw [mul_apply_t] at h2
  have h2' : ((β (tU C) : ℂˣ) : ℂ) * ν C.t = 1 * ν C.t := by rw [h2, one_mul]
  have h3 : ((β (tU C) : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ h0 h2'
  exact Units.ext h3

/-! ## The main lemma -/

theorem s02_lemma21Ext {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) : Work.BG.Lemma21ExtProp C := by
  intro ν hν hne hnot
  by_cases h0 : ν C.t = 0
  · refine ⟨ν, ⟨1, ?_⟩, hne, ?_⟩
    · rw [lamCF_one, one_mul_cf]
    · rw [h0, neg_zero]
  · obtain ⟨b0, hb0⟩ := s02_lamSign C
    by_contra hcon
    -- `hbad`: every orbit element with value `-ν(t)` at `t` is `s`-fixed
    have hbad : ∀ μ, μ ∈ lamOrbit C ν → μ C.t = -ν C.t → sconj C μ = μ := by
      intro μ hμ hval
      by_contra hfix
      exact hcon ⟨μ, hμ, hfix, hval⟩
    -- the twist of `ν` by `b0` has value `-ν(t)` at `t`, hence is `s`-fixed
    have hμ₀ : lamCF C b0 * ν ∈ lamOrbit C ν := ⟨b0, rfl⟩
    have hval₀ : (lamCF C b0 * ν) C.t = -ν C.t := by
      rw [mul_apply_t, hb0]
      simp
    have hfix₀ : sconj C (lamCF C b0 * ν) = lamCF C b0 * ν := hbad _ hμ₀ hval₀
    -- hence `ν^s = (b0)² • ν`
    have hz : sconj C ν = lamCF C (b0 * b0) * ν := by
      have h1 : lamCF C b0⁻¹ * sconj C ν = lamCF C b0 * ν := by
        rw [← sconjLam C b0 ν]
        exact hfix₀
      have h2 := congrArg (fun f => lamCF C b0 * f) h1
      rw [lamCF_cancel_left C b0 (sconj C ν), lamCF_mul_assoc_h C b0 b0 ν] at h2
      exact h2
    -- squares of `Λ¹` stabilise `ν`
    have hsq : ∀ δ ∈ lamKernel C, δ ^ 2 ∈ lamStab C ν := by
      intro δ hδ
      have hδ' : δ (tU C) = 1 := hδ
      have hμ : lamCF C (b0 * δ) * ν ∈ lamOrbit C ν := ⟨b0 * δ, rfl⟩
      have hval : (lamCF C (b0 * δ) * ν) C.t = -ν C.t := by
        rw [mul_apply_t, MonoidHom.mul_apply, hb0, hδ']
        simp
      have hfix := hbad _ hμ hval
      have h1 : lamCF C ((b0 * δ)⁻¹ * (b0 * b0)) * ν = lamCF C (b0 * δ) * ν := by
        rw [← lamCF_mul_assoc_h, ← hz, ← sconjLam C (b0 * δ) ν]
        exact hfix
      have h2 : ((b0 * δ)⁻¹ * (b0 * b0))⁻¹ * (b0 * δ) ∈ lamStab C ν :=
        mem_lamStab_of_mul_eq C h1
      have h3 : ((b0 * δ)⁻¹ * (b0 * b0))⁻¹ * (b0 * δ) = δ * δ := by
        ext x
        simp
        field_simp
      rw [h3] at h2
      simpa [pow_two] using h2
    -- the index arithmetic
    haveI hcyc : IsCyclic (lamDual C) := (s02_lamDualCyclic C).2
    haveI hfin : Finite (lamDual C) := (s02_lamDualCyclic C).1
    have hKleL : lamStab C ν ≤ lamKernel C := lamStab_le_lamKernel C h0
    have hz0L : b0 * b0 ∈ lamKernel C := by
      have h := Subgroup.sq_mem_of_index_two (lamKernel_index C) b0
      simpa [pow_two] using h
    have hz0K : b0 * b0 ∉ lamStab C ν := by
      intro h
      rw [mem_lamStab] at h
      exact hne (by rw [hz, h])
    have hKL : lamStab C ν ≠ lamKernel C := fun heq => hz0K (heq ▸ hz0L)
    have hK'top : (lamStab C ν).subgroupOf (lamKernel C) ≠ ⊤ := by
      intro h
      exact hKL (le_antisymm hKleL (Subgroup.subgroupOf_eq_top.mp h))
    have hK'le : ((lamStab C ν).subgroupOf (lamKernel C)).index ≤ 2 :=
      s02_indexSq (lamStab C ν) (lamKernel C) hKleL hsq
    have hK'ne0 : ((lamStab C ν).subgroupOf (lamKernel C)).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hK'ne1 : ((lamStab C ν).subgroupOf (lamKernel C)).index ≠ 1 :=
      fun h1 => hK'top (Subgroup.index_eq_one.mp h1)
    have hrel2 : (lamStab C ν).relIndex (lamKernel C) = 2 := by
      show ((lamStab C ν).subgroupOf (lamKernel C)).index = 2
      omega
    have hindex : (lamStab C ν).index = 4 := by
      have h := Subgroup.relIndex_mul_index (H := lamStab C ν) (K := lamKernel C) hKleL
      rw [hrel2, lamKernel_index C] at h
      omega
    have hcard : (lamOrbit C ν).ncard = 4 := by
      rw [ncard_lamOrbit_eq_index, hindex]
    -- `s`-invariance of the orbit
    have hsub : sconj C '' lamOrbit C ν ⊆ lamOrbit C ν := by
      rintro _ ⟨χ, ⟨β, rfl⟩, rfl⟩
      exact ⟨β⁻¹ * (b0 * b0), by
        rw [sconjLam, hz, lamCF_mul_assoc_h C β⁻¹ (b0 * b0) ν]⟩
    have himage : sconj C '' lamOrbit C ν = lamOrbit C ν := by
      refine Set.Subset.antisymm hsub ?_
      intro χ hχ
      exact ⟨sconj C χ, hsub ⟨χ, hχ, rfl⟩, sconj_sconj C χ⟩
    exact hnot ⟨hcard, himage⟩

end Work.BG
