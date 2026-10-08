import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma24
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.Lambda
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lemma17_iii_aux
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.s4dNorm4b
import Submission.Work.BG.lemma41
import Submission.Work.BG.caseA
import Submission.Work.BG.caseB
import Submission.Work.BG.comb413
import Submission.Work.BG.lemma42
import Submission.Work.BG.congContra

/-!
# Area BG: `Work.BG.s4Decomp` (Bender–Glauberman 1981, §4, the case `|S| = 4`)

The target `Work.GW2.C16.S4DecompProp D C` is BG's S4-DEC (p. 214): in the case `D.n = 2`
(`|S| = 4`, so `H₀/U` has order `2`), for the non-trivial `β₂ : H₀/U →* ℂˣ`,

  `(1 - λ₂)* = 1_G + φ₁ + φ₂ + φ₃`,  with `φᵢ ∈ ±Irr(G)`, `φᵢ(t) = 1`, `φᵢ(1)` odd,

where `λ₂ = lamCF C β₂` and `δ_ν := (ν - λ₂ν)*` (`Work.GW2.C16.delta`).

The file first builds the `|S| = 4` structure (`H₀/U ≅ C₂`) and computes the three character
sums `⟨δ_ν, δ_ν⟩ = 4`, `δ_ν(t) = 4ν(t)`, `⟨1_G, δ_ν⟩ = [ν = lamCF C 1]` from the proved
Brauer–Suzuki Gram matrix (`s02_gram`) and Frobenius reciprocity.
-/

namespace Work.BG

set_option linter.unusedSectionVars false

open OddOrder.RepresentationTheory Work.GW2 Work.BG

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 0. Elementary facts about `lamCF` (kept local to avoid a heavy import) -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
/-- `lamCF C 1` is the trivial character of `H₀`. -/
theorem s4d_lamCF_one_eq_trivial {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) :
    Work.BG.lamCF C (1 : Work.BG.quotGroup C.P →* ℂˣ) =
      trivialClassFunction ↥C.P.H0 := by
  rw [lamCF_one]
  ext h
  simp [linearClassFunction_apply, trivialClassFunction_apply]

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
/-- `lamCF C 1` is `s`-invariant. -/
theorem s4d_sconj_lamCF_one {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) :
    Work.BG.sconj C (Work.BG.lamCF C 1) = Work.BG.lamCF C 1 := by
  rw [s4d_lamCF_one_eq_trivial]
  ext h
  simp [Work.BG.sconj, conjByH_apply]

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
/-- `lamCF C β` is irreducible (a linear character). -/
theorem s4d_lamCF_irreducible {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    (β : Work.BG.quotGroup C.P →* ℂˣ) :
    IsIrreducibleCharacter (Work.BG.lamCF C β) := by
  have h1irr : IsIrreducibleCharacter (Work.BG.lamCF C (1 : Work.BG.quotGroup C.P →* ℂˣ)) := by
    rw [s4d_lamCF_one_eq_trivial]
    exact trivialClassFunction_isIrreducible
  have hmem : Work.BG.lamCF C β ∈ Work.BG.Lambda C.P := ⟨β, rfl⟩
  have h := Work.BG.lambda_mul_irreducible C.P hmem h1irr
  have hmul : Work.BG.lamCF C β * Work.BG.lamCF C 1 = Work.BG.lamCF C β := by
    rw [lamCF_one, ClassFunction.mul_linearClassFunction_one]
  simpa [hmul] using h

/-! ## 1. The `|S| = 4` structure -/

section Sec4

variable (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

open Work.GW2.C16 in
/-- **`|H₀/U| = 2`.**  `[H₀ : U] = |S₀| = D.n` (`rem31IndexUin`), so `D.n = 2`. -/
theorem s4d_quot_card (hc : Compat D C) (hn : D.n = 2) : Nat.card (quotGroup C.P) = 2 := by
  rw [← Subgroup.index_eq_card (Uin C), rem31IndexUin D C hc, hn]

open Work.GW2.C16 in
/-- The dual of a two-element group: `β = 1` or `β = β₂`, and `β₂ = -1` off the identity. -/
theorem s4d_dual {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1) :
    (∀ β : quotGroup C.P →* ℂˣ, β = 1 ∨ β = β₂) ∧
      (∀ x : quotGroup C.P, x ≠ 1 → ((β₂ x : ℂˣ) : ℂ) = -1) :=
  lemma17_iii_dualC2 C.P (s4d_quot_card D C hc hn) hβ

open Work.GW2.C16 in
/-- In the `D.n = 2` case every `β : H₀/U →* ℂˣ` is an involution. -/
theorem s4d_beta_inv {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) : β₂⁻¹ = β₂ := by
  rcases (s4d_dual D C hc hn hβ).1 β₂⁻¹ with h | h
  · exfalso
    have h2 : β₂ = 1 := by
      have h3 := mul_inv_cancel β₂
      rw [h] at h3
      simpa using h3
    exact hβ h2
  · exact h

open Work.GW2.C16 in
/-- `λ₂ = lamCF C β₂` is `s`-invariant (`s` inverts `H₀/U` and `β₂` is an involution). -/
theorem s4d_sconj_two {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) : sconj C (lamCF C β₂) = lamCF C β₂ := by
  rw [LamCFFixed.sconj_lamCF C β₂, s4d_beta_inv D C hc hn hβ]

open Work.GW2.C16 in
/-- `λ₂` is not the trivial character. -/
theorem s4d_lamCF_two_ne_triv {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1) :
    lamCF C β₂ ≠ lamCF C 1 := fun h => hβ (LamCFFixed.lamCF_injective C h)

open Work.GW2.C16 in
/-- `λ₂(t) = -1`. -/
theorem s4d_lamCF_two_apply_t {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) : lamCF C β₂ C.t = -1 := by
  rw [lamCF_apply_t]
  exact (s4d_dual D C hc hn hβ).2 (tU C) (tU_ne_one C)

open Work.GW2.C16 in
/-- `lamCF C β * lamCF C 1 = lamCF C β`. -/
theorem s4d_lamCF_mul_one (β : quotGroup C.P →* ℂˣ) :
    lamCF C β * lamCF C 1 = lamCF C β := by
  rw [s4d_lamCF_one_eq_trivial]
  ext h
  simp [ClassFunction.mul_apply, trivialClassFunction_apply]

open Work.GW2.C16 in
/-- `δ_{λ₁} = (λ₁ - λ₂)*`, written with `lamCF C 1` (the trivial character). -/
theorem s4d_delta_eq (β₂ : quotGroup C.P →* ℂˣ) :
    delta C β₂ (lamCF C 1) = ind C (lamCF C 1 - lamCF C β₂) := by
  simp only [delta]
  rw [s4d_lamCF_mul_one C β₂]

open Work.GW2.C16 in
/-- `λ₂ · ν ≠ ν` when `ν(t) ≠ 0` (evaluate at `t`, where `λ₂ = -1`). -/
theorem s4d_lamCF_mul_ne {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν C.t ≠ 0) :
    lamCF C β₂ * ν ≠ ν := by
  intro h
  have hlamt : lamCF C β₂ C.t = -1 := s4d_lamCF_two_apply_t D C hc hn hβ
  have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
  rw [ClassFunction.mul_apply, hlamt] at h1
  exact hν (by linear_combination (-1/2 : ℂ) * h1)

open Work.GW2.C16 in
/-- `lamCF C 1 ∈ 𝒮'`: the trivial character of `H₀` is `s`-invariant with `ν(t) = ν(1)`. -/
theorem s4d_mem_S4Index_one : lamCF C 1 ∈ S4Index C := by
  refine ⟨?_, s4d_sconj_lamCF_one C, ?_⟩
  · rw [s4d_lamCF_one_eq_trivial]; exact trivialClassFunction_isIrreducible
  · rw [s4d_lamCF_one_eq_trivial, trivialClassFunction_apply, trivialClassFunction_apply]

open Work.GW2.C16 in
/-- **`δ_ν ∈ ℤ[Irr G]` and `δ_ν(1) = 0`** for `ν ∈ 𝒮'` (`IndDiffProp`). -/
theorem s4d_delta_ziir_deg {β₂ : quotGroup C.P →* ℂˣ}
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) :
    delta C β₂ ν ∈ ZIrr G ∧ delta C β₂ ν 1 = 0 :=
  s02_indDiff C ν (lamCF C β₂ * ν) hν.1
    (lambda_mul_irreducible C.P ⟨β₂, rfl⟩ hν.1) ⟨β₂, rfl⟩

open Work.GW2.C16 in
/-- **Gram computation**: `‖δ_ν‖² = 4` for `ν ∈ 𝒮'`. -/
theorem s4d_delta_norm {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) :
    ClassFunction.inner (delta C β₂ ν) (delta C β₂ ν) = 4 := by
  have hνirr : IsIrreducibleCharacter ν := hν.1
  have hνs : sconj C ν = ν := hν.2.1
  have hβirr : IsIrreducibleCharacter (lamCF C β₂ * ν) :=
    lambda_mul_irreducible C.P ⟨β₂, rfl⟩ hνirr
  have hνt : ν C.t ≠ 0 := by
    rw [hν.2.2]
    exact IsPmIrr.apply_one_ne_zero (Or.inl hνirr)
  have hsν : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν := by
    rw [sconjLam C β₂ ν, hνs, s4d_beta_inv D C hc hn hβ]
  have hneq : lamCF C β₂ * ν ≠ ν := s4d_lamCF_mul_ne D C hc hn hβ hνt
  have h11 : cH C ν ν = 2 := by simp [cH, hνs]; norm_num
  have h12 : cH C ν (lamCF C β₂ * ν) = 0 := by simp [cH, hneq, hνs]
  have h21 : cH C (lamCF C β₂ * ν) ν = 0 := by simp [cH, hneq.symm, hsν]
  have h22 : cH C (lamCF C β₂ * ν) (lamCF C β₂ * ν) = 2 := by simp [cH, hsν]; norm_num
  simp only [delta]
  rw [s02_gram C ν (lamCF C β₂ * ν) ν (lamCF C β₂ * ν) hνirr hβirr hνirr hβirr
    ⟨β₂, rfl⟩ ⟨β₂, rfl⟩, h11, h12, h21, h22]
  norm_num

open Work.GW2.C16 in
/-- **The value at `t`**: `δ_ν(t) = 4ν(t)` (BG Lemma 1.3 value form, `λ₂(t) = -1`). -/
theorem s4d_delta_t {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) :
    delta C β₂ ν (C.t : G) = 4 * ν C.t := by
  have hbs := s02_bsValueAtT C ν (lamCF C β₂ * ν) hν.1
    (lambda_mul_irreducible C.P ⟨β₂, rfl⟩ hν.1) ⟨β₂, rfl⟩
  have hlamt : lamCF C β₂ C.t = -1 := s4d_lamCF_two_apply_t D C hc hn hβ
  simp only [delta]
  rw [hbs, ClassFunction.mul_apply, hlamt]
  ring

open Work.GW2.C16 in
/-- **Frobenius**: `⟨1_G, δ_ν⟩ = [ν = lamCF C 1]` for `ν ∈ 𝒮'`; in particular it is `0` for
`ν ≠ lamCF C 1`. -/
theorem s4d_inner_triv_delta {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C)
    (hne : ν ≠ lamCF C 1) :
    ClassFunction.inner (trivialClassFunction G) (delta C β₂ ν) = 0 := by
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- `ν(1) = ν(t)` is a positive integer, so `ν(t) ≠ -1`
  have hν1 : ν (1 : ↥C.P.H0) ≠ -1 := by
    obtain ⟨d, hd, hgd⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨ν, hν.1⟩ : IrreducibleCharacter ↥C.P.H0)
    rw [IrreducibleCharacter.coe_mk] at hgd
    rw [hgd]
    intro hh
    have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have h2 : ((d : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_natCast, hh]
      simp
    have h3 : (d : ℝ) = -1 := Complex.ofReal_injective h2
    linarith
  have hne₂ : lamCF C β₂ * ν ≠ trivialClassFunction ↥C.P.H0 := by
    intro h
    have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
    rw [ClassFunction.mul_apply, s4d_lamCF_two_apply_t D C hc hn hβ,
      trivialClassFunction_apply] at h1
    have ht : ν C.t = -1 := by linear_combination (-1 : ℂ) * h1
    rw [hν.2.2] at ht
    exact hν1 ht
  have hνne : ν ≠ trivialClassFunction ↥C.P.H0 := by
    intro h
    exact hne (by rw [h, s4d_lamCF_one_eq_trivial])
  have hfrob : ClassFunction.inner (delta C β₂ ν) (trivialClassFunction G)
      = ClassFunction.inner (ν - lamCF C β₂ * ν)
          (ClassFunction.restrict C.P.H0 (trivialClassFunction G)) := by
    rw [delta]
    exact ClassFunction.inner_induce_eq_inner_restrict C.P.H0 (ν - lamCF C β₂ * ν)
      (trivialClassFunction G)
  have hres : ClassFunction.restrict C.P.H0 (trivialClassFunction G)
      = trivialClassFunction ↥C.P.H0 := by
    ext h
    simp
  have h1 : ClassFunction.inner ν (trivialClassFunction ↥C.P.H0) = 0 := by
    rw [irr_cf_inner hν.1 trivialClassFunction_isIrreducible]
    exact ite_eq_right hνne
  have h2 : ClassFunction.inner (lamCF C β₂ * ν) (trivialClassFunction ↥C.P.H0) = 0 := by
    have hirr : IsIrreducibleCharacter (lamCF C β₂ * ν) :=
      lambda_mul_irreducible C.P ⟨β₂, rfl⟩ hν.1
    rw [irr_cf_inner (a := lamCF C β₂ * ν) (b := trivialClassFunction ↥C.P.H0) hirr
      trivialClassFunction_isIrreducible]
    exact ite_eq_right hne₂
  rw [ClassFunction.inner_star_comm, hfrob, hres, ClassFunction.inner_sub_left, h1, h2]
  simp

open Work.GW2.C16 in
/-- **Frobenius, `ν = lamCF C 1`**: `⟨1_G, δ_1⟩ = 1`. -/
theorem s4d_inner_triv_delta_one {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) :
    ClassFunction.inner (trivialClassFunction G) (delta C β₂ (lamCF C 1)) = 1 := by
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  have hlamne : lamCF C β₂ ≠ lamCF C 1 := s4d_lamCF_two_ne_triv C hβ
  have hfrob : ClassFunction.inner (ind C (lamCF C 1 - lamCF C β₂)) (trivialClassFunction G)
      = ClassFunction.inner (lamCF C 1 - lamCF C β₂)
          (ClassFunction.restrict C.P.H0 (trivialClassFunction G)) :=
    ClassFunction.inner_induce_eq_inner_restrict C.P.H0 (lamCF C 1 - lamCF C β₂)
      (trivialClassFunction G)
  have hres : ClassFunction.restrict C.P.H0 (trivialClassFunction G)
      = trivialClassFunction ↥C.P.H0 := by
    ext h
    simp
  have h1 : ClassFunction.inner (lamCF C 1) (trivialClassFunction ↥C.P.H0) = 1 := by
    rw [irr_cf_inner (by rw [s4d_lamCF_one_eq_trivial]; exact trivialClassFunction_isIrreducible)
      trivialClassFunction_isIrreducible]
    exact ite_eq_left rfl
  have h2 : ClassFunction.inner (lamCF C β₂) (trivialClassFunction ↥C.P.H0) = 0 := by
    rw [irr_cf_inner (s4d_lamCF_irreducible C β₂) trivialClassFunction_isIrreducible]
    exact ite_eq_right hlamne
  rw [s4d_delta_eq C β₂, ClassFunction.inner_star_comm, hfrob, hres,
    ClassFunction.inner_sub_left, h1, h2]
  simp

end Sec4

/-! ## 2. Two signed irreducibles with inner product `1` are equal -/

/-- For `φ ψ ∈ ±Irr(K)`, `⟨φ, ψ⟩ = 1` forces `φ = ψ`. -/
theorem s4d_inner_one_eq {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ ψ : ClassFunction K ℂ} (hφ : IsPmIrr φ) (hψ : IsPmIrr ψ)
    (h : ClassFunction.inner φ ψ = 1) : φ = ψ := by
  rcases hφ with hφ | hφ <;> rcases hψ with hψ | hψ
  · rw [irr_cf_inner hφ hψ] at h
    by_contra hne
    rw [ite_eq_right hne] at h
    exact one_ne_zero h.symm
  · exfalso
    have h' := irr_cf_inner hφ hψ
    rw [ClassFunction.inner_neg_right, h] at h'
    by_cases hcase : φ = -ψ
    · rw [ite_eq_left hcase] at h'; norm_num at h'
    · rw [ite_eq_right hcase] at h'; norm_num at h'
  · exfalso
    have h' := irr_cf_inner hφ hψ
    rw [ClassFunction.inner_neg_left, h] at h'
    by_cases hcase : -φ = ψ
    · rw [ite_eq_left hcase] at h'; norm_num at h'
    · rw [ite_eq_right hcase] at h'; norm_num at h'
  · have h' := irr_cf_inner hφ hψ
    simp only [ClassFunction.inner_neg_right, ClassFunction.inner_neg_left, h, neg_neg] at h'
    by_contra hne
    have hcase : ¬ (-φ = -ψ) := fun hh => hne (neg_inj.mp hh)
    rw [ite_eq_right hcase] at h'
    norm_num at h'

/-! ## 3. `ν₀ = lamCF C 1` is isolated in the graph `Δ` of Theorem 4.3 -/

section Isolated

variable (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

open Work.GW2.C16 in
/-- **The `TripleAt` alternative of Theorem 4.3 at `ν₀ = lamCF C 1` is impossible.**

Its sign pattern makes `1_G` a constituent of both `δ_{ν₀} = χ₁+χ₂+χ₃+χ₄` and
`δ_{μ₂} = χ₁-χ₂+χ₃-χ₄`; pairing the two expansions shows `⟨1_G, δ_{μ₂}⟩` is odd, while
`⟨1_G, δ_μ⟩ = [μ = ν₀]` (Frobenius).  So `μ₂ = ν₀`, the two expansions coincide, and then
`χ₂ + χ₄ = 0`, `δ_{ν₀} = χ₁ + χ₃` with `⟨χ₁, χ₃⟩ = 1` (from `‖δ_{ν₀}‖² = 4`), hence
`χ₁ = χ₃` and `δ_{ν₀} = 2χ₁` has nonzero value at `1` — contradicting `δ_{ν₀}(1) = 0`. -/
theorem s4d_not_triple {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) : ¬ Work.GW2.C23.TripleAt D C β₂ (lamCF C 1) := by
  rintro ⟨μ₂, hμ₂, μ₃, hμ₃, χ₁, χ₂, χ₃, χ₄, hχ₁, hχ₂, hχ₃, hχ₄, heq1, heq2, heq3, hhat⟩
  have hone : ClassFunction.inner (trivialClassFunction G) (delta C β₂ (lamCF C 1)) = 1 :=
    s4d_inner_triv_delta_one D C hc hn hβ
  have hdeg : delta C β₂ (lamCF C 1) 1 = 0 := (s4d_delta_ziir_deg C
    (s4d_mem_S4Index_one C)).2
  have hnorm : ClassFunction.inner (delta C β₂ (lamCF C 1)) (delta C β₂ (lamCF C 1)) = 4 :=
    s4d_delta_norm D C hc hn hβ (s4d_mem_S4Index_one C)
  -- expand both `⟨1_G, ·⟩`
  have hsum0 : ClassFunction.inner (trivialClassFunction G) (delta C β₂ (lamCF C 1))
      = ClassFunction.inner (trivialClassFunction G) χ₁
        + ClassFunction.inner (trivialClassFunction G) χ₂
        + ClassFunction.inner (trivialClassFunction G) χ₃
        + ClassFunction.inner (trivialClassFunction G) χ₄ := by
    rw [heq1]
    simp only [ClassFunction.inner_add_right]
  have hsum1 : ClassFunction.inner (trivialClassFunction G) (delta C β₂ μ₂)
      = ClassFunction.inner (trivialClassFunction G) χ₁
        - ClassFunction.inner (trivialClassFunction G) χ₂
        + ClassFunction.inner (trivialClassFunction G) χ₃
        - ClassFunction.inner (trivialClassFunction G) χ₄ := by
    rw [heq2]
    simp only [ClassFunction.inner_add_right, ClassFunction.inner_sub_right]
  -- integrality of two of the four coefficients
  have htrivZIrr : trivialClassFunction G ∈ ZIrr G :=
    IsPmIrr.mem_ZIrr (Or.inl trivialClassFunction_isIrreducible)
  have htriv1 : ClassFunction.inner (trivialClassFunction G) (trivialClassFunction G) = 1 :=
    IsPmIrr.inner_self (Or.inl trivialClassFunction_isIrreducible)
  obtain ⟨m₁, hm₁, -⟩ := inner_eq_int_and_sq_le htrivZIrr 1
    (by rw [Nat.cast_one]; exact htriv1) hχ₁
  obtain ⟨m₃, hm₃, -⟩ := inner_eq_int_and_sq_le htrivZIrr 1
    (by rw [Nat.cast_one]; exact htriv1) hχ₃
  have hsum0' : (1 : ℂ) = ClassFunction.inner (trivialClassFunction G) χ₁
        + ClassFunction.inner (trivialClassFunction G) χ₂
        + ClassFunction.inner (trivialClassFunction G) χ₃
        + ClassFunction.inner (trivialClassFunction G) χ₄ := by
    rw [← hone]; exact hsum0
  rw [hm₁, hm₃] at hsum0'
  have hbd : ClassFunction.inner (trivialClassFunction G) χ₂
      + ClassFunction.inner (trivialClassFunction G) χ₄
      = 1 - (m₁ : ℂ) - (m₃ : ℂ) := by
    linear_combination (-1 : ℂ) * hsum0'
  have hz : ClassFunction.inner (trivialClassFunction G) (delta C β₂ μ₂)
      = 2 * ((m₁ : ℂ) + (m₃ : ℂ)) - 1 := by
    rw [hsum1, hm₁, hm₃]
    linear_combination (-1 : ℂ) * hbd
  have hz_ne : ClassFunction.inner (trivialClassFunction G) (delta C β₂ μ₂) ≠ 0 := by
    rw [hz]
    intro hh
    have hcast : ((2 * (m₁ + m₃) - 1 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
      push_cast
      linear_combination hh
    have hint : 2 * (m₁ + m₃) - 1 = 0 := Int.cast_injective hcast
    omega
  have hmu2eq : μ₂ = lamCF C 1 := by
    by_contra hne
    exact hz_ne (s4d_inner_triv_delta D C hc hn hβ hμ₂ hne)
  have heq2' : delta C β₂ (lamCF C 1) = χ₁ - χ₂ + χ₃ - χ₄ := by
    rw [← hmu2eq]; exact heq2
  have hchi24 : χ₂ + χ₄ = 0 := by
    have h1' : χ₁ + χ₂ + χ₃ + χ₄ = χ₁ - χ₂ + χ₃ - χ₄ := heq1.symm.trans heq2'
    have h2' : (χ₂ + χ₄) + (χ₂ + χ₄) = 0 := by
      rw [show (χ₂ + χ₄) + (χ₂ + χ₄)
          = (χ₁ + χ₂ + χ₃ + χ₄) - (χ₁ - χ₂ + χ₃ - χ₄) from by abel, ← h1', sub_self]
    have h3 : (2 : ℂ) • (χ₂ + χ₄) = 0 := by
      rw [show (2 : ℂ) • (χ₂ + χ₄) = (χ₂ + χ₄) + (χ₂ + χ₄) from by module]
      exact h2'
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hdec : delta C β₂ (lamCF C 1) = χ₁ + χ₃ := by
    rw [heq1, show χ₁ + χ₂ + χ₃ + χ₄ = (χ₁ + χ₃) + (χ₂ + χ₄) from by abel, hchi24,
      add_zero]
  have hn2 : ClassFunction.inner (χ₁ + χ₃) (χ₁ + χ₃) = 4 := by
    rw [← hdec]; exact hnorm
  have hz13 : ClassFunction.inner χ₁ χ₃ = 1 := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hχ₁, IsPmIrr.inner_self hχ₃] at hn2
    obtain ⟨m, hm, -⟩ := inner_eq_int_and_sq_le (IsPmIrr.mem_ZIrr hχ₁) 1
      (by rw [Nat.cast_one]; exact IsPmIrr.inner_self hχ₁) hχ₃
    have hstar : ClassFunction.inner χ₃ χ₁ = (m : ℂ) := by
      have hs := ClassFunction.inner_star_comm χ₃ χ₁
      rw [hm, star_intCast] at hs
      exact hs
    rw [hstar, hm] at hn2
    have hmm : ((2 * m - 2 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
      push_cast
      linear_combination hn2
    have h2m : 2 * m - 2 = 0 := Int.cast_injective hmm
    have hm1 : m = 1 := by omega
    rw [hm1] at hm
    simpa only [Int.cast_one] using hm
  have hchi13 : χ₁ = χ₃ := s4d_inner_one_eq hχ₁ hχ₃ hz13
  have hzero : χ₁ 1 = 0 := by
    have h24 : delta C β₂ (lamCF C 1) = χ₁ + χ₁ := by rw [hdec, hchi13]
    have hval : delta C β₂ (lamCF C 1) 1 = χ₁ 1 + χ₁ 1 := by rw [h24]; rfl
    rw [hdeg] at hval
    linear_combination (-1 / 2 : ℂ) * hval
  exact IsPmIrr.apply_one_ne_zero hχ₁ hzero

open Work.GW2.C16 in
/-- **`ν₀ = lamCF C 1` is isolated**: `δ_{ν₀}` is disjoint from every other `δ_μ`, `μ ∈ 𝒮'`.

By Theorem 4.3 applied at `ν₀` it suffices to exclude the `TripleAt` alternative, which is
`s4d_not_triple`. -/
theorem s4d_disjoint_one {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) (h43 : Work.GW2.C23.Thm43HatProp D C) :
    ∀ μ ∈ S4Index C, delta C β₂ μ ≠ delta C β₂ (lamCF C 1) →
      DisjointCF (delta C β₂ (lamCF C 1)) (delta C β₂ μ) := by
  intro μ hμ hne
  rcases h43 hc hn β₂ hβ (lamCF C 1) (s4d_mem_S4Index_one C) with hdisj | htri
  · exact hdisj μ hμ hne
  · exact absurd htri (s4d_not_triple D C hc hn hβ)

end Isolated

/-! ## 4. Assembly: `S4DecompProp` from the leaves -/

section Assembly

variable (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

open Work.GW2.C16 in
/-- `δ_•` is injective on `𝒮'`: `δ_μ = δ_{ν₀}` forces `μ = ν₀` because `⟨1_G, δ_μ⟩ = [μ = ν₀]`. -/
theorem s4d_delta_inj {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ S4Index C)
    (heq : delta C β₂ μ = delta C β₂ (lamCF C 1)) : μ = lamCF C 1 := by
  by_contra hne
  have h0 := s4d_inner_triv_delta D C hc hn hβ hμ hne
  rw [heq, s4d_inner_triv_delta_one D C hc hn hβ] at h0
  exact one_ne_zero h0

open Work.GW2.C16 in
/-- **Lemma 4.1 (ii) + (iv) at `ν₀`**: an irreducible `ψ` whose `δ`-coefficient is `±1` has
`ψ(t)` equal to that coefficient and odd degree — because `𝒮'(ψ) = {ν₀}` (isolation). -/
theorem s4d_constituent_irr {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) (h41 : Lemma41Prop D C)
    (hdisj : ∀ μ ∈ S4Index C, delta C β₂ μ ≠ delta C β₂ (lamCF C 1) →
      DisjointCF (delta C β₂ (lamCF C 1)) (delta C β₂ μ))
    {ψ : ClassFunction G ℂ} (hψ : IsIrreducibleCharacter ψ)
    (hval : ClassFunction.inner ψ (delta C β₂ (lamCF C 1)) = 1 ∨
      ClassFunction.inner ψ (delta C β₂ (lamCF C 1)) = -1) :
    ψ (C.t : G) = ClassFunction.inner ψ (delta C β₂ (lamCF C 1)) ∧
      ∃ d : ℤ, Odd d ∧ ψ 1 = d := by
  have hne : ClassFunction.inner ψ (delta C β₂ (lamCF C 1)) ≠ 0 := by
    rcases hval with h | h <;> rw [h] <;> norm_num
  have hmem : (bset' C β₂ ψ).Nonempty := ⟨lamCF C 1, s4d_mem_S4Index_one C, hne⟩
  obtain ⟨-, hsum, d, hdodd, hdval⟩ := h41 hc hn β₂ hβ ψ (Or.inl hψ) hmem
  have hset : bset' C β₂ ψ = {lamCF C 1} := by
    ext ν
    refine ⟨fun hν => ?_, fun hν => ?_⟩
    · rw [Set.mem_singleton_iff]
      by_contra hne'
      have hδne : delta C β₂ ν ≠ delta C β₂ (lamCF C 1) :=
        fun hh => hne' (s4d_delta_inj D C hc hn hβ hν.1 hh)
      rcases hdisj ν hν.1 hδne ⟨ψ, hψ⟩ with hz | hz
      · have hz' : ClassFunction.inner (delta C β₂ (lamCF C 1)) ψ ≠ 0 := by
          rw [ClassFunction.inner_star_comm]
          rcases hval with h | h <;> rw [h] <;> norm_num
        exact hz' hz
      · have hz2 : ClassFunction.inner ψ (delta C β₂ ν) = 0 := by
          have h := ClassFunction.inner_star_comm ψ (delta C β₂ ν)
          rw [hz, star_zero] at h
          exact h
        exact hν.2 hz2
    · rw [Set.mem_singleton_iff] at hν
      rw [hν]
      exact ⟨s4d_mem_S4Index_one C, hne⟩
  rw [hset] at hsum
  have hsingle : (∑ᶠ ν ∈ ({lamCF C 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ClassFunction.inner ψ (delta C β₂ ν) * ν 1)
      = ClassFunction.inner ψ (delta C β₂ (lamCF C 1)) * 1 := by
    rw [finsum_mem_def, finsum_eq_single _ (lamCF C 1)]
    · rw [Set.indicator_of_mem (Set.mem_singleton _), s4d_lamCF_one_eq_trivial,
        trivialClassFunction_apply]
    · intro b hb
      have hbmem : b ∉ ({lamCF C 1} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
        simp only [Set.mem_singleton_iff]
        exact hb
      rw [Set.indicator_of_notMem hbmem]
  rw [hsingle, mul_one] at hsum
  exact ⟨hsum, d, hdodd, hdval⟩

open Work.GW2.C16 in
/-- A signed irreducible `φ` of `δ`-coefficient `1` has `φ(t) = 1` and odd degree. -/
theorem s4d_constituent {β₂ : quotGroup C.P →* ℂˣ} (hc : Compat D C) (hn : D.n = 2)
    (hβ : β₂ ≠ 1) (h41 : Lemma41Prop D C)
    (hdisj : ∀ μ ∈ S4Index C, delta C β₂ μ ≠ delta C β₂ (lamCF C 1) →
      DisjointCF (delta C β₂ (lamCF C 1)) (delta C β₂ μ))
    {φ : ClassFunction G ℂ} (hφ : IsPmIrr φ)
    (h1 : ClassFunction.inner (delta C β₂ (lamCF C 1)) φ = 1) :
    φ (C.t : G) = 1 ∧ ∃ a : ℤ, Odd a ∧ φ 1 = a := by
  have hφδ : ClassFunction.inner φ (delta C β₂ (lamCF C 1)) = 1 := by
    rw [ClassFunction.inner_star_comm, h1]
    simp
  rcases hφ with hirr | hnegr
  · have h := s4d_constituent_irr D C hc hn hβ h41 hdisj hirr (Or.inl hφδ)
    exact ⟨by rw [h.1, hφδ], h.2⟩
  · have hval : ClassFunction.inner (-φ) (delta C β₂ (lamCF C 1)) = -1 := by
      rw [ClassFunction.inner_neg_left, hφδ]
    obtain ⟨ht, d, hdodd, hdval⟩ := s4d_constituent_irr D C hc hn hβ h41 hdisj hnegr (Or.inr hval)
    have ht' : φ (C.t : G) = 1 := by
      have h := ht
      rw [ClassFunction.neg_apply, hval] at h
      linear_combination (-1 : ℂ) * h
    refine ⟨ht', -d, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hdodd
      exact ⟨-k - 1, by omega⟩
    · have h := hdval
      rw [ClassFunction.neg_apply] at h
      push_cast
      linear_combination (-1 : ℂ) * h

open Work.GW2.C16 in
/-- **Assembly of `S4DecompProp`** from BG Lemma 4.1 (`hL41`), BG Theorem 4.3 (`hT43`) and the
Fourier-algebra splitting of a norm-`4` virtual character (`hnorm4`). -/
theorem s4Decomp_of_leaves
    (hL41 : ∀ {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Work.GW2.C16.Lemma41Prop D C)
    (hT43 : ∀ {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Work.GW2.C23.Thm43HatProp D C)
    (hnorm4 : ∀ {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
      {δ : ClassFunction K ℂ}, δ ∈ ZIrr K → ClassFunction.inner δ δ = 4 →
      ClassFunction.inner (trivialClassFunction K) δ = 1 →
      ∃ φ₁ φ₂ φ₃ : ClassFunction K ℂ, IsPmIrr φ₁ ∧ IsPmIrr φ₂ ∧ IsPmIrr φ₃ ∧
        ClassFunction.inner δ φ₁ = 1 ∧ ClassFunction.inner δ φ₂ = 1 ∧
        ClassFunction.inner δ φ₃ = 1 ∧
        δ = trivialClassFunction K + φ₁ + φ₂ + φ₃) :
    S4DecompProp D C := by
  intro hc hn β₂ hβ
  have hZ : delta C β₂ (lamCF C 1) ∈ ZIrr G :=
    (s4d_delta_ziir_deg C (s4d_mem_S4Index_one C)).1
  have hnorm : ClassFunction.inner (delta C β₂ (lamCF C 1)) (delta C β₂ (lamCF C 1)) = 4 :=
    s4d_delta_norm D C hc hn hβ (s4d_mem_S4Index_one C)
  have hone : ClassFunction.inner (trivialClassFunction G) (delta C β₂ (lamCF C 1)) = 1 :=
    s4d_inner_triv_delta_one D C hc hn hβ
  obtain ⟨φ₁, φ₂, φ₃, hpm1, hpm2, hpm3, hd1, hd2, hd3, hdec⟩ := hnorm4 hZ hnorm hone
  have hdisj : ∀ μ ∈ S4Index C, delta C β₂ μ ≠ delta C β₂ (lamCF C 1) →
      DisjointCF (delta C β₂ (lamCF C 1)) (delta C β₂ μ) :=
    s4d_disjoint_one D C hc hn hβ (hT43 D C)
  have hc1 := s4d_constituent D C hc hn hβ (hL41 D C) hdisj hpm1 hd1
  have hc2 := s4d_constituent D C hc hn hβ (hL41 D C) hdisj hpm2 hd2
  have hc3 := s4d_constituent D C hc hn hβ (hL41 D C) hdisj hpm3 hd3
  obtain ⟨a, haodd, haval⟩ := hc1.2
  obtain ⟨b, hbodd, hbval⟩ := hc2.2
  obtain ⟨c, hcodd, hcval⟩ := hc3.2
  exact ⟨φ₁, φ₂, φ₃, hpm1, hpm2, hpm3, hdec, hc1.1, hc2.1, hc3.1,
    ⟨a, b, c, haodd, hbodd, hcodd, haval, hbval, hcval⟩⟩

end Assembly

/-- **BG Theorem 4.3** assembled from its two cases (pp. 212-214): case (a) is
`Work.BG.caseA`; case (b) is `Work.BG.caseB_of_leaves`, fed with its leaves `Comb413Prop`
(`Work.BG.comb413`), `Lemma41Prop` (`Work.BG.lemma41`), `Lemma42Prop` (`Work.BG.lemma42`) and
`CongContraProp` (`Work.BG.congContra`). -/
theorem s4T43_assembled {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Work.GW2.C23.Thm43HatProp D C :=
  Work.GW2.C23.thm43_of_cases D C (caseA D C)
    (caseB_of_leaves D C comb413 (lemma41 D C) (lemma42 D C) (congContra D C))

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem s4Decomp {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Work.GW2.C16.S4DecompProp D C :=
  s4Decomp_of_leaves D C (fun D C => lemma41 D C) (fun D C => s4T43_assembled D C)
    (fun hZ hnorm h1 => s4dNorm4b hZ hnorm h1)

end Work.BG
