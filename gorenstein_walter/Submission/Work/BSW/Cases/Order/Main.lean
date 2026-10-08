/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW, Bender §2: the two computations of `⟨θ*, i⟩`

This file proves, for `θ* = α*` or `β*` (`Work.BSW.alphaFun`, `Work.BSW.betaFun`),
Bender's two evaluations of the pairing with the involution-pair class function `i`
(`Work.BSW.Order.invPairCF`, `REFS/bender1974_bsw.txt` p. 231):

* **directly** (Frobenius reciprocity + the values of `i` on `K`): `⟨α*, i⟩ = k`,
  `⟨β*, i⟩ = 0`;
* **via the character formula** (Gorenstein 9.4.21): `⟨α*, i⟩ = |G|/|C_G(t)|²` times
  `Σ_χ (χ(t)²/χ(1))·⟨α*, χ⟩`.

Together with the decompositions of `α*` and `β*` (`Work.BSW.Cases.Order.existsDecompThree`,
`existsDecompTwo`) these are Bender's relations (i) and (ii) of §2, Step 6.
-/
import Mathlib
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.Char.inner_alpha_beta
import Submission.Work.BSW.Cases.Order.induceApplyCoeMemK
import Submission.Work.BSW.Char.sum_chi_t_sq
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterProduct
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

namespace Work.BSW.Order

open Subgroup Work.GW2 OddOrder.RepresentationTheory

noncomputable section

variable {G : Type} [Group G] [Finite G] [Fintype G]

section ZIrr

/-- A linear character, as a class function, is a virtual character. -/
theorem linearClassFunction_mem_ZIrr {L : Type} [Group L] (χ : L →* ℂˣ) :
    linearClassFunction χ ∈ ZIrr L := by
  rw [← linearIrreducibleCharacter_coe χ]
  exact IrreducibleCharacter.mem_ZIrr (linearIrreducibleCharacter χ)

/-- `α* = ind_K^G (1_K − ρ)` is a virtual character of `G`. -/
theorem alphaFun_mem_ZIrr {K : Subgroup G} [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card G : ℂ)] (ρ : ↥K →* ℂˣ) :
    Work.BSW.alphaFun K ρ ∈ ZIrr G := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  refine ClassFunction.induce_mem_ZIrr K ?_
  exact Submodule.sub_mem _ (linearClassFunction_mem_ZIrr _) (linearClassFunction_mem_ZIrr _)

/-- `β* = ind_K^G (ρ₁ − ρ₂)` is a virtual character of `G`. -/
theorem betaFun_mem_ZIrr {K : Subgroup G} [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card G : ℂ)] (ρ₁ ρ₂ : ↥K →* ℂˣ) :
    Work.BSW.betaFun K ρ₁ ρ₂ ∈ ZIrr G := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  refine ClassFunction.induce_mem_ZIrr K ?_
  exact Submodule.sub_mem _ (linearClassFunction_mem_ZIrr _) (linearClassFunction_mem_ZIrr _)

end ZIrr

section Sums

/-- The sum of a nontrivial linear character over a finite group vanishes. -/
theorem sum_linearClassFunction_eq_zero {L : Type} [Group L] [Finite L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (χ : L →* ℂˣ) (hχ : χ ≠ 1) :
    (∑ x : L, (χ x : ℂ)) = 0 := by
  have key : ClassFunction.inner (linearClassFunction χ) (trivialClassFunction L) = 0 := by
    rw [← linearIrreducibleCharacter_coe χ, ← IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      irreducibleCharacter_inner_eq_ite]
    rw [if_neg (fun h => hχ (linearIrreducibleCharacter_eq_trivial_iff.mp h))]
  have h2 : ClassFunction.innerSum (linearClassFunction χ) (trivialClassFunction L) = 0 := by
    rw [← ClassFunction.card_mul_inner]; rw [key]; ring
  rw [ClassFunction.innerSum] at h2
  simpa [linearClassFunction_apply, trivialClassFunction_apply] using h2

/-- The trivial linear character is the trivial class function. -/
@[simp] theorem linearClassFunction_one_eq_trivial {L : Type} [Group L] :
    linearClassFunction (1 : L →* ℂˣ) = trivialClassFunction L := by
  refine ClassFunction.ext fun x => ?_
  simp [linearClassFunction_apply, trivialClassFunction_apply]

end Sums

section InnerTrivial

/-- `⟨α*, 1_G⟩ = 1` (Frobenius reciprocity). -/
theorem inner_alphaFun_trivial {K : Subgroup G} [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card G : ℂ)] (ρ : ↥K →* ℂˣ) (hρ : ρ ≠ 1) :
    ClassFunction.inner (Work.BSW.alphaFun K ρ) (trivialClassFunction G) = 1 := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  show ClassFunction.inner (ClassFunction.induce K
    (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ)) (trivialClassFunction G) = 1
  have hθ : ClassFunction.inner
      (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ)
      (trivialClassFunction ↥K) = 1 := by
    rw [ClassFunction.inner_sub_left, ← linearClassFunction_one_eq_trivial (L := ↥K),
      Work.BSW.Char.inner_linearClassFunction (1 : ↥K →* ℂˣ) (1 : ↥K →* ℂˣ),
      Work.BSW.Char.inner_linearClassFunction ρ (1 : ↥K →* ℂˣ), if_pos rfl, if_neg hρ]
    ring
  have := ClassFunction.induce_inner_trivial (G := G) K
    (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ)
  rw [this]
  exact hθ

/-- `⟨β*, 1_G⟩ = 0` (Frobenius reciprocity). -/
theorem inner_betaFun_trivial {K : Subgroup G} [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card G : ℂ)] (ρ₁ ρ₂ : ↥K →* ℂˣ) (h₁ : ρ₁ ≠ 1) (h₂ : ρ₂ ≠ 1) :
    ClassFunction.inner (Work.BSW.betaFun K ρ₁ ρ₂) (trivialClassFunction G) = 0 := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  show ClassFunction.inner (ClassFunction.induce K
    (linearClassFunction ρ₁ - linearClassFunction ρ₂)) (trivialClassFunction G) = 0
  have hθ : ClassFunction.inner (linearClassFunction ρ₁ - linearClassFunction ρ₂)
      (trivialClassFunction ↥K) = 0 := by
    rw [ClassFunction.inner_sub_left, ← linearClassFunction_one_eq_trivial (L := ↥K),
      Work.BSW.Char.inner_linearClassFunction ρ₁ (1 : ↥K →* ℂˣ),
      Work.BSW.Char.inner_linearClassFunction ρ₂ (1 : ↥K →* ℂˣ), if_neg h₁, if_neg h₂]
    ring
  have := ClassFunction.induce_inner_trivial (G := G) K
    (linearClassFunction ρ₁ - linearClassFunction ρ₂)
  rw [this]
  exact hθ

end InnerTrivial

section ValuesOne

/-- `α*(1) = 0`. -/
theorem alphaFun_apply_one {K : Subgroup G} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (ρ : ↥K →* ℂˣ) : Work.BSW.alphaFun K ρ (1 : G) = 0 := by
  show ClassFunction.induce K
    (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ) (1 : G) = 0
  rw [ClassFunction.induce_apply_one, ClassFunction.sub_apply,
    linearClassFunction_apply, linearClassFunction_apply]
  simp

/-- `β*(1) = 0`. -/
theorem betaFun_apply_one {K : Subgroup G} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (ρ₁ ρ₂ : ↥K →* ℂˣ) : Work.BSW.betaFun K ρ₁ ρ₂ (1 : G) = 0 := by
  show ClassFunction.induce K (linearClassFunction ρ₁ - linearClassFunction ρ₂) (1 : G) = 0
  rw [ClassFunction.induce_apply_one, ClassFunction.sub_apply,
    linearClassFunction_apply, linearClassFunction_apply]
  simp

/-- `(⟨t, ·⟩ : ↥K) ≠ 1`. -/
theorem tInK_ne_one {t s : G} {K : Subgroup G} (h : BSWHyps2 G t s K) :
    (⟨t, Work.BSW.t_mem_K h⟩ : ↥K) ≠ 1 := by
  intro hc
  exact Work.BSW.t_ne_one h (by simpa using congrArg (fun z : ↥K => (z : G)) hc)

/-- `(⟨t, ·⟩ : ↥K)⁻¹ = ⟨t, ·⟩`. -/
theorem tInK_inv {t s : G} {K : Subgroup G} (h : BSWHyps2 G t s K) :
    (⟨t, Work.BSW.t_mem_K h⟩ : ↥K)⁻¹ = ⟨t, Work.BSW.t_mem_K h⟩ :=
  Subtype.ext (Work.BSW.t_inv h)

/-- `α*(t) = 0`. -/
theorem alphaFun_apply_t {t s : G} {K : Subgroup G} [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] (h : BSWHyps2 G t s K) (ρ : ↥K →* ℂˣ)
    (hρ : ρ ⟨t, Work.BSW.t_mem_K h⟩ = 1) : Work.BSW.alphaFun K ρ t = 0 := by
  show ClassFunction.induce K
    (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ) t = 0
  rw [Work.BSW.Cases.Order.induceApplyCoeMemK (a := ⟨t, Work.BSW.t_mem_K h⟩) h _
    (Work.BSW.t_ne_one h)]
  norm_num [ClassFunction.sub_apply, linearClassFunction_apply, tInK_inv h, hρ]

/-- `β*(t) = 4`. -/
theorem betaFun_apply_t {t s : G} {K : Subgroup G} [Fintype ↥K]
    [Invertible (Nat.card ↥K : ℂ)] (h : BSWHyps2 G t s K) (ρ₁ ρ₂ : ↥K →* ℂˣ)
    (h₁ : ρ₁ ⟨t, Work.BSW.t_mem_K h⟩ = 1) (h₂ : ρ₂ ⟨t, Work.BSW.t_mem_K h⟩ = -1) :
    Work.BSW.betaFun K ρ₁ ρ₂ t = 4 := by
  show ClassFunction.induce K (linearClassFunction ρ₁ - linearClassFunction ρ₂) t = 4
  rw [Work.BSW.Cases.Order.induceApplyCoeMemK (a := ⟨t, Work.BSW.t_mem_K h⟩) h _
    (Work.BSW.t_ne_one h)]
  norm_num [ClassFunction.sub_apply, linearClassFunction_apply, tInK_inv h, h₁, h₂]

end ValuesOne

section DirectCalc

variable {t s : G} {K : Subgroup G} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
  [Invertible (Nat.card G : ℂ)]

/-- `i(a) = k` for every `a ∈ K`, `a ≠ 1` (Bender's `i(t) = k` and `i(x) = k` combined). -/
theorem invPairCount_mem_K' (h : BSWHyps2 G t s K) {a : ↥K} (ha : a ≠ 1) :
    (Work.BSW.invPairCount G (a : G) : ℂ) = (Nat.card ↥K : ℂ) := by
  rcases eq_or_ne (a : G) t with ht | ht
  · rw [ht]; exact_mod_cast Work.BSW.Order.invPairCount_t h
  · exact_mod_cast Work.BSW.Order.invPairCount_mem_K h a.2
      (fun hc => ha (Subtype.ext (by simpa using hc))) ht

/-- The direct computation of `⟨θ*, i⟩` for a class function `θ` supported on `K`: the sum over
`K` of `θ(a)·i(a)` equals `|K|·Σ_{a∈K}θ(a)`. -/
theorem sum_mul_invPairCount (h : BSWHyps2 G t s K) (θ : ClassFunction ↥K ℂ)
    (hθ : θ 1 = 0) :
    (∑ a : ↥K, θ a * star (ClassFunction.restrict K (invPairCF G t) a)) =
      (Nat.card ↥K : ℂ) * (∑ a : ↥K, θ a) := by
  classical
  have hterm : ∀ a : ↥K, θ a * star (ClassFunction.restrict K (invPairCF G t) a) =
      θ a * (Nat.card ↥K : ℂ) := by
    intro a
    rw [ClassFunction.restrict_apply,
      Work.BSW.Order.invPairCF_apply (Work.BSW.orderOf_t h) (Work.BSW.involutions_conj h) (a : G),
      star_natCast]
    by_cases ha : a = 1
    · subst ha
      rw [hθ]; ring
    · rw [invPairCount_mem_K' h ha]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.sum_mul]
  ring

/-- `θ₁(1) = 0`. -/
theorem theta1_apply_one (ρ : ↥K →* ℂˣ) :
    (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ) (1 : ↥K) = 0 := by
  rw [ClassFunction.sub_apply, linearClassFunction_apply, linearClassFunction_apply]
  simp

/-- `⟨α*, i⟩ = k` (Bender, §2, p. 231): the direct computation, by Frobenius reciprocity and the
values `i(x) = k` on `K ∖ {1}`, `i(1) = |G : C_G(t)|`, and `α(1) = α(t) = 0`. -/
theorem inner_alphaFun_invPairCF (h : BSWHyps2 G t s K) (ρ : ↥K →* ℂˣ) (hρ : ρ ≠ 1) :
    ClassFunction.inner (Work.BSW.alphaFun K ρ) (invPairCF G t) = (Nat.card ↥K : ℂ) := by
  classical
  show ClassFunction.inner
    (ClassFunction.induce K (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ))
    (invPairCF G t) = (Nat.card ↥K : ℂ)
  rw [ClassFunction.inner_induce_eq_inner_restrict, ClassFunction.inner, ClassFunction.innerSum,
    sum_mul_invPairCount h _ (theta1_apply_one ρ)]
  have hsumθ : (∑ a : ↥K,
      (linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ) a) =
      (Nat.card ↥K : ℂ) := by
    simp only [ClassFunction.sub_apply]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ a : ↥K, (linearClassFunction (1 : ↥K →* ℂˣ)) a) = (Nat.card ↥K : ℂ) := by
      simp [linearClassFunction_apply, Finset.sum_const, Nat.card_eq_fintype_card]
    have h2 : (∑ a : ↥K, (linearClassFunction ρ) a) = 0 := by
      have hh := sum_linearClassFunction_eq_zero (L := ↥K) ρ hρ
      simpa [linearClassFunction_apply] using hh
    rw [h1, h2, sub_zero]
  rw [hsumθ, ← mul_assoc, invOf_mul_self, one_mul]

/-- `θ₂(1) = 0`. -/
theorem theta2_apply_one (ρ₁ ρ₂ : ↥K →* ℂˣ) :
    (linearClassFunction ρ₁ - linearClassFunction ρ₂) (1 : ↥K) = 0 := by
  rw [ClassFunction.sub_apply, linearClassFunction_apply, linearClassFunction_apply]
  simp

/-- `⟨β*, i⟩ = 0` (Bender, §2, p. 231). -/
theorem inner_betaFun_invPairCF (h : BSWHyps2 G t s K) (ρ₁ ρ₂ : ↥K →* ℂˣ)
    (h₁ : ρ₁ ≠ 1) (h₂ : ρ₂ ≠ 1) :
    ClassFunction.inner (Work.BSW.betaFun K ρ₁ ρ₂) (invPairCF G t) = 0 := by
  classical
  show ClassFunction.inner (ClassFunction.induce K (linearClassFunction ρ₁ - linearClassFunction ρ₂))
    (invPairCF G t) = 0
  rw [ClassFunction.inner_induce_eq_inner_restrict, ClassFunction.inner, ClassFunction.innerSum,
    sum_mul_invPairCount h _ (theta2_apply_one ρ₁ ρ₂)]
  have hsumθ : (∑ a : ↥K, (linearClassFunction ρ₁ - linearClassFunction ρ₂) a) = 0 := by
    simp only [ClassFunction.sub_apply]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ a : ↥K, (linearClassFunction ρ₁) a) = 0 := by
      have hh := sum_linearClassFunction_eq_zero (L := ↥K) ρ₁ h₁
      simpa [linearClassFunction_apply] using hh
    have h2 : (∑ a : ↥K, (linearClassFunction ρ₂) a) = 0 := by
      have hh := sum_linearClassFunction_eq_zero (L := ↥K) ρ₂ h₂
      simpa [linearClassFunction_apply] using hh
    rw [h1, h2, sub_zero]
  rw [hsumθ, mul_zero, mul_zero]

end DirectCalc

section FormulaCalc

variable {t s : G} {K : Subgroup G} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
  [Invertible (Nat.card G : ℂ)]

/-- `Σ_χ e χ · ⟨a, χ⟩ = e ⟨a, ·⟩` for an irreducible class function `a`. -/
theorem sum_mul_inner_irreducible {a : ClassFunction G ℂ} (ha : IsIrreducibleCharacter a)
    (e : IrreducibleCharacter G → ℂ) :
    (∑ χ : IrreducibleCharacter G, e χ * ClassFunction.inner a (χ : ClassFunction G ℂ)) =
      e ⟨a, ha⟩ := by
  classical
  rw [Finset.sum_eq_single (⟨a, ha⟩ : IrreducibleCharacter G)]
  · rw [irr_cf_inner ha ha, ite_eq_left rfl, mul_one]
  · intro b _ hb
    rw [irr_cf_inner ha (mem_irreducibleCharacters.mpr b.2),
      ite_eq_right (fun hcon => hb (Subtype.ext hcon.symm)), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **The character-formula computation of `⟨φ, i⟩`** (Bender §2, p. 231): if `φ = 1_G + ψ₁ − ψ₂`
with `ψ₁, ψ₂` irreducible, then
`⟨φ, i⟩ = |G|/|C_G(t)|² · (1 + ψ₁(t)²/ψ₁(1) − ψ₂(t)²/ψ₂(1))`. -/
theorem inner_invPairCF_eq (h : BSWHyps2 G t s K) {φ ψ₁ ψ₂ : ClassFunction G ℂ}
    (hψ₁ : IsIrreducibleCharacter ψ₁) (hψ₂ : IsIrreducibleCharacter ψ₂)
    (hdec : φ = trivialClassFunction G + ψ₁ - ψ₂) :
    ClassFunction.inner φ (invPairCF G t) =
      ((Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) *
        (1 + ψ₁ t ^ 2 / ψ₁ 1 - ψ₂ t ^ 2 / ψ₂ 1) := by
  classical
  set c : ℂ := (Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 with hc
  set d : IrreducibleCharacter G → ℂ :=
    fun χ => ((χ : ClassFunction G ℂ) t) ^ 2 / ((χ : ClassFunction G ℂ) 1) with hd
  have hstar_c : star c = c := by
    rw [hc]; simp [star_div₀, star_pow, star_natCast]
  have hstar_one : ∀ χ : IrreducibleCharacter G, star ((χ : ClassFunction G ℂ) 1) =
      (χ : ClassFunction G ℂ) 1 := by
    intro χ
    obtain ⟨m, _, hm⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    rw [show (χ : ClassFunction G ℂ) 1
      = ((χ : ClassFunction G ℂ) : G → ℂ) 1 from rfl, hm, star_natCast]
  have hstar_d : ∀ χ : IrreducibleCharacter G, star (d χ) = d χ := by
    intro χ
    rw [hd, star_div₀, star_pow,
      (Work.BSW.Char.chi_apply_eq_star_of_orderOf_eq_two (Work.BSW.orderOf_t h) χ).symm,
      hstar_one χ]
  have hrepr : invPairCF G t =
      c • (∑ χ : IrreducibleCharacter G, d χ • (χ : ClassFunction G ℂ)) := rfl
  have hstep1 : ClassFunction.inner φ (invPairCF G t) =
      c * (∑ χ : IrreducibleCharacter G, d χ * ClassFunction.inner φ (χ : ClassFunction G ℂ)) := by
    rw [hrepr, ClassFunction.inner_smul_right, hstar_c, inner_sum_right]
    refine congrArg (c * ·) (Finset.sum_congr rfl (fun χ _ => ?_))
    rw [ClassFunction.inner_smul_right, hstar_d]
  rw [hstep1]
  congr 1
  have hexp : ∀ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner φ (χ : ClassFunction G ℂ) =
        d χ * ClassFunction.inner (trivialClassFunction G) (χ : ClassFunction G ℂ) +
          d χ * ClassFunction.inner ψ₁ (χ : ClassFunction G ℂ) -
            d χ * ClassFunction.inner ψ₂ (χ : ClassFunction G ℂ) := by
    intro χ
    rw [hdec, ClassFunction.inner_sub_left, ClassFunction.inner_add_left]
    ring
  rw [Finset.sum_congr rfl (fun χ _ => hexp χ),
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have htriv : (∑ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner (trivialClassFunction G) (χ : ClassFunction G ℂ)) = 1 := by
    rw [sum_mul_inner_irreducible trivialClassFunction_isIrreducible d, hd]
    simp [trivialClassFunction_apply]
  have hp1 : (∑ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner ψ₁ (χ : ClassFunction G ℂ)) = ψ₁ t ^ 2 / ψ₁ 1 := by
    rw [sum_mul_inner_irreducible hψ₁ d, hd]
  have hp2 : (∑ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner ψ₂ (χ : ClassFunction G ℂ)) = ψ₂ t ^ 2 / ψ₂ 1 := by
    rw [sum_mul_inner_irreducible hψ₂ d, hd]
  rw [htriv, hp1, hp2]

/-- **The character-formula computation of `⟨φ, i⟩`, difference form**: if `φ = ν₁ − ν₂` with
`ν₁, ν₂` irreducible, then `⟨φ, i⟩ = |G|/|C_G(t)|² · (ν₁(t)²/ν₁(1) − ν₂(t)²/ν₂(1))`. -/
theorem inner_invPairCF_eq_sub (h : BSWHyps2 G t s K) {φ ν₁ ν₂ : ClassFunction G ℂ}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hdec : φ = ν₁ - ν₂) :
    ClassFunction.inner φ (invPairCF G t) =
      ((Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) *
        (ν₁ t ^ 2 / ν₁ 1 - ν₂ t ^ 2 / ν₂ 1) := by
  classical
  set c : ℂ := (Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 with hc
  set d : IrreducibleCharacter G → ℂ :=
    fun χ => ((χ : ClassFunction G ℂ) t) ^ 2 / ((χ : ClassFunction G ℂ) 1) with hd
  have hstar_c : star c = c := by
    rw [hc]; simp [star_div₀, star_pow, star_natCast]
  have hstar_one : ∀ χ : IrreducibleCharacter G, star ((χ : ClassFunction G ℂ) 1) =
      (χ : ClassFunction G ℂ) 1 := by
    intro χ
    obtain ⟨m, _, hm⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    rw [show (χ : ClassFunction G ℂ) 1
      = ((χ : ClassFunction G ℂ) : G → ℂ) 1 from rfl, hm, star_natCast]
  have hstar_d : ∀ χ : IrreducibleCharacter G, star (d χ) = d χ := by
    intro χ
    rw [hd, star_div₀, star_pow,
      (Work.BSW.Char.chi_apply_eq_star_of_orderOf_eq_two (Work.BSW.orderOf_t h) χ).symm,
      hstar_one χ]
  have hrepr : invPairCF G t =
      c • (∑ χ : IrreducibleCharacter G, d χ • (χ : ClassFunction G ℂ)) := rfl
  have hstep1 : ClassFunction.inner φ (invPairCF G t) =
      c * (∑ χ : IrreducibleCharacter G, d χ * ClassFunction.inner φ (χ : ClassFunction G ℂ)) := by
    rw [hrepr, ClassFunction.inner_smul_right, hstar_c, inner_sum_right]
    refine congrArg (c * ·) (Finset.sum_congr rfl (fun χ _ => ?_))
    rw [ClassFunction.inner_smul_right, hstar_d]
  rw [hstep1]
  congr 1
  have hexp : ∀ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner φ (χ : ClassFunction G ℂ) =
        d χ * ClassFunction.inner ν₁ (χ : ClassFunction G ℂ) -
          d χ * ClassFunction.inner ν₂ (χ : ClassFunction G ℂ) := by
    intro χ
    rw [hdec, ClassFunction.inner_sub_left]
    ring
  rw [Finset.sum_congr rfl (fun χ _ => hexp χ), Finset.sum_sub_distrib]
  have hp1 : (∑ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner ν₁ (χ : ClassFunction G ℂ)) = ν₁ t ^ 2 / ν₁ 1 := by
    rw [sum_mul_inner_irreducible hν₁ d, hd]
  have hp2 : (∑ χ : IrreducibleCharacter G,
      d χ * ClassFunction.inner ν₂ (χ : ClassFunction G ℂ)) = ν₂ t ^ 2 / ν₂ 1 := by
    rw [sum_mul_inner_irreducible hν₂ d, hd]
  rw [hp1, hp2]

end FormulaCalc

end

end Work.BSW.Order
