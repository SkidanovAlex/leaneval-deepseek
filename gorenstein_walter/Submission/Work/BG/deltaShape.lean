/-
Area BG: `Work.GW2.C23.DeltaShapeProp` — Bender–Glauberman 1981 §4, p. 212, "DELTA-SHAPE".

For `ν ∈ 𝒮₄(C)` (i.e. `ν ∈ Irr(H₀)`, `s`-fixed, `ν(t) = ν(1)`) and the non-trivial
`β₂ : H₀/U →* ℂˣ`, the virtual character `δ_ν = (ν - λ₂ν)^G` is a sum of four distinct
`±Irr` characters of `G`.

The proof has three ingredients, all formalised here:

* `δ_ν ∈ ℤ[Irr G]` and `δ_ν(1) = 0`: `s02_indDiff` (`IndDiffProp`) applied to the pair
  `(ν, λ₂ν)`, which is `Λ`-equivalent;
* `(δ_ν, δ_ν) = 4`: the Brauer–Suzuki Gram matrix `s02_gram` (`GramProp`) together with the
  `|S| = 4` structure facts (`H₀/U` of order two);
* the pure Fourier lemma `dsShapeOfZIrr`: a virtual character of norm `4` and degree `0` is a
  signed sum of four *distinct* irreducible characters.
-/
import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.H0Conj
import Submission.Work.BG.Lambda
import Submission.Work.BG.lemma17_ii_aux
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.centralValue
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.sumSqFourSplit

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## 1. The pure Fourier lemma -/

/-- A virtual character `δ ∈ ℤ[Irr K]` with `‖δ‖² = 4` and `δ(1) = 0` is a signed sum of
four *distinct* irreducible characters: there is a four-element set `T ⊆ Irr(K)` with all
Fourier coefficients `⟨δ, χ⟩` equal to `±1` on `T` and `0` off `T`. -/
theorem dsShapeOfZIrr {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)]
    (δ : ClassFunction K ℂ) (hZ : δ ∈ ZIrr K)
    (hnorm : ClassFunction.inner δ δ = 4) (h0 : δ 1 = 0) :
    ∃ T : Finset (IrreducibleCharacter K), T.card = 4 ∧
      (∀ χ ∈ T, ClassFunction.inner δ (χ : ClassFunction K ℂ) = 1 ∨
        ClassFunction.inner δ (χ : ClassFunction K ℂ) = -1) ∧
      ∀ χ ∉ T, ClassFunction.inner δ (χ : ClassFunction K ℂ) = 0 := by
  classical
  obtain ⟨c, hsupp, hrepr, hnorm_sum⟩ := mem_ZIrr_inner_self_eq_sum_sq hZ
  have hsum_int : ∑ a ∈ c.support, c a ^ 2 = 4 := by
    have hc : ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) = 4 := by
      push_cast
      rw [← hnorm_sum, hnorm]
    exact_mod_cast hc
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  have hsupp' : ∀ a ∈ c.support, IsIrreducibleCharacter a :=
    fun a ha => mem_irreducibleCharacters.mp (hsupp ha)
  rcases sumSqFourSplit hne hsum_int with
      ⟨α, hs, hsq⟩ | ⟨S, T, hS, hT, hdisj, hcover, hS2, hT2⟩
  · -- Single constituent `δ = (±2)·α` is impossible because `δ(1) = 0`.
    exfalso
    have hαirr : IsIrreducibleCharacter α := hsupp' α (by rw [hs]; simp)
    have hδeq : δ = (c α : ℂ) • α := by rw [hrepr, hs, Finset.sum_singleton]
    obtain ⟨d, hd, hα1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨α, hαirr⟩ : IrreducibleCharacter K)
    simp only [IrreducibleCharacter.coe_mk] at hα1
    have hα1ne : α 1 ≠ 0 := by rw [hα1]; exact Nat.cast_ne_zero.mpr hd.ne'
    have hcval : c α = 2 ∨ c α = -2 := by
      have hfac : (c α - 2) * (c α + 2) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hfac with h | h
      · left; omega
      · right; omega
    have hcnz : (c α : ℂ) ≠ 0 := by
      rcases hcval with h | h <;> rw [h] <;> norm_num
    rw [hδeq, ClassFunction.smul_apply] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hcnz h
    · exact hα1ne h
  · -- Two norm-`2` parts: each is a pair of distinct irreducibles with coefficients `±1`.
    obtain ⟨α₁, α₂, hα₁₂, hS_eq, hcα₁, hcα₂⟩ :=
      exists_pair_of_sum_sq_eq_two (s := S) (fun a ha => hne a (hS ha)) hS2
    obtain ⟨α₃, α₄, hα₃₄, hT_eq, hcα₃, hcα₄⟩ :=
      exists_pair_of_sum_sq_eq_two (s := T) (fun a ha => hne a (hT ha)) hT2
    have hScard : S.card = 2 := by rw [hS_eq, Finset.card_pair hα₁₂]
    have hTcard : T.card = 2 := by rw [hT_eq, Finset.card_pair hα₃₄]
    have hcard : c.support.card = 4 := by
      rw [← hcover, Finset.card_union_of_disjoint hdisj, hScard, hTcard]
    have hcoeff : ∀ a ∈ c.support, c a = 1 ∨ c a = -1 := by
      intro a ha
      have ha' : a ∈ S ∪ T := by rw [hcover]; exact ha
      rcases Finset.mem_union.mp ha' with haS | haT
      · have haS' : a ∈ ({α₁, α₂} : Finset (ClassFunction K ℂ)) := by rw [← hS_eq]; exact haS
        rcases Finset.mem_insert.mp haS' with h | h
        · rw [h]; exact hcα₁
        · rw [Finset.mem_singleton.mp h]; exact hcα₂
      · have haT' : a ∈ ({α₃, α₄} : Finset (ClassFunction K ℂ)) := by rw [← hT_eq]; exact haT
        rcases Finset.mem_insert.mp haT' with h | h
        · rw [h]; exact hcα₃
        · rw [Finset.mem_singleton.mp h]; exact hcα₄
    let g : {x // x ∈ c.support} → IrreducibleCharacter K :=
      fun a => ⟨(a : ClassFunction K ℂ), mem_irreducibleCharacters.mp (hsupp a.2)⟩
    have hg_inj : Function.Injective g := by
      intro a b hab
      have h1 : (g a : ClassFunction K ℂ) = (g b : ClassFunction K ℂ) := by rw [hab]
      have h2 : (a : ClassFunction K ℂ) = (b : ClassFunction K ℂ) := h1
      exact Subtype.ext h2
    refine ⟨c.support.attach.map ⟨g, hg_inj⟩, ?_, ?_, ?_⟩
    · rw [Finset.card_map, Finset.card_attach, hcard]
    · intro χ hχ
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hχ
      change ClassFunction.inner δ (a : ClassFunction K ℂ) = 1 ∨
        ClassFunction.inner δ (a : ClassFunction K ℂ) = -1
      have hinner : ClassFunction.inner δ (a : ClassFunction K ℂ)
          = (c (a : ClassFunction K ℂ) : ℂ) := by
        rw [hrepr]
        exact inner_eq_coeff_of_repr
          ⟨(a : ClassFunction K ℂ), mem_irreducibleCharacters.mp (hsupp a.2)⟩ hsupp
      rw [hinner]
      rcases hcoeff (a : ClassFunction K ℂ) a.2 with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
    · intro χ hχ
      have hnotmem : (χ : ClassFunction K ℂ) ∉ c.support := by
        intro hmem
        apply hχ
        refine Finset.mem_map.mpr
          ⟨⟨(χ : ClassFunction K ℂ), hmem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
      have hinner : ClassFunction.inner δ (χ : ClassFunction K ℂ)
          = (c (χ : ClassFunction K ℂ) : ℂ) := by
        rw [hrepr]
        exact inner_eq_coeff_of_repr χ hsupp
      have hcz : c (χ : ClassFunction K ℂ) = 0 := by
        by_contra hc0
        exact hnotmem (Finsupp.mem_support_iff.mpr hc0)
      rw [hinner, hcz]; norm_num

/-! ## 2. The `|S| = 4` structure facts (`H₀/U` of order two) -/

/-- `|H₀/U| = 2` in the case `|S| = 4` (`D.n = 2`). -/
theorem dsQuotCardTwo {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (C : Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) :
    Nat.card (quotGroup C.P) = 2 := by
  rw [show Nat.card (quotGroup C.P) = (Work.GW2.C16.Uin C).index from rfl,
    rem31IndexUin D C hc, hn]

/-- `λ₂(t) = -1` when `|H₀/U| = 2` and `β₂ ≠ 1`. -/
theorem dsLamTwoApplyT {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    lamCF C β₂ C.t = -1 := by
  have hx : quotMk C.P C.t ≠ 1 := by
    intro h
    exact C.t_not_mem_U ((QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) C.t).mp h)
  exact (lemma17_iii_dualC2 C.P h2 hβ).2 _ hx

/-- `λ₂` is its own inverse in the `|S| = 4` case. -/
theorem dsLamTwoInvEq {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    lamCF C β₂⁻¹ = lamCF C β₂ := by
  rcases (lemma17_iii_dualC2 C.P h2 hβ).1 β₂⁻¹ with h | h
  · exfalso
    have h1 : β₂ = 1 := by
      calc β₂ = (β₂⁻¹)⁻¹ := (inv_inv β₂).symm
        _ = (1 : quotGroup C.P →* ℂˣ)⁻¹ := by rw [h]
        _ = 1 := by ext x; simp
    exact hβ h1
  · rw [h]

/-- `s`-conjugation commutes with multiplication by `λ₂`. -/
theorem dsSconjLamTwoMul {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (lamCF C β₂ * ν) = lamCF C β₂ * sconj C ν := by
  rw [sconjLam C β₂ ν, dsLamTwoInvEq C h2 hβ]

/-- `(λ₂ν)(t) = -ν(t)`. -/
theorem dsLamTwoMulApplyT {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) : (lamCF C β₂ * ν) C.t = -ν C.t := by
  rw [ClassFunction.mul_apply, dsLamTwoApplyT C h2 hβ]
  ring

/-- The degree of an irreducible character of `H₀` is non-zero. -/
theorem dsIrrApplyOneNeZero {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) : ν 1 ≠ 0 := by
  obtain ⟨n, hn, hval, -⟩ := hν.exists_natDegree_charValue_one_dvd_card
  rw [hval]
  exact_mod_cast hn.ne'

/-- Schur for the central involution `t`: `ν(t) ≠ 0`. -/
theorem dsTValNeZero {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) : ν C.t ≠ 0 := by
  rcases (centralValue C ν hν).1 with h | h
  · rw [h]; exact dsIrrApplyOneNeZero C hν
  · rw [h]; exact neg_ne_zero.mpr (dsIrrApplyOneNeZero C hν)

/-- `λ₂ν ≠ ν` for `ν ∈ Irr(H₀)`. -/
theorem dsLamTwoMulNeSelf {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    lamCF C β₂ * ν ≠ ν := by
  intro h
  have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
  rw [dsLamTwoMulApplyT C h2 hβ ν] at h1
  have h2' : (2 : ℂ) * ν C.t = 0 := by linear_combination (-1) * h1
  exact dsTValNeZero C hν ((mul_eq_zero.mp h2').resolve_left (by norm_num))

/-- `λ₂ν` is irreducible when `ν` is. -/
theorem dsLamTwoMulIrr {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ} {ν : ClassFunction ↥C.P.H0 ℂ}
    (hν : IsIrreducibleCharacter ν) : IsIrreducibleCharacter (lamCF C β₂ * ν) :=
  lambda_mul_irreducible C.P (lambdaInf_mem C.P β₂) hν

/-! ## 3. `δ_ν ∈ ℤ[Irr G]`, `δ_ν(1) = 0`, `‖δ_ν‖² = 4` -/

theorem dsDeltaS4Facts {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hn : D.n = 2) (β₂ : Work.BG.quotGroup C.P →* ℂˣ)
    (hβ₂ : β₂ ≠ 1) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : ν ∈ Work.GW2.C16.S4Index C) :
    Work.GW2.C16.delta C β₂ ν ∈ ZIrr G ∧ Work.GW2.C16.delta C β₂ ν 1 = 0 ∧
      ClassFunction.inner (Work.GW2.C16.delta C β₂ ν) (Work.GW2.C16.delta C β₂ ν) = 4 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨hνirr, hνs, _hνt⟩ := hν
  have h2 : Nat.card (quotGroup C.P) = 2 := dsQuotCardTwo D C hC hn
  set ν' := lamCF C β₂ * ν with hν'def
  have hν'irr : IsIrreducibleCharacter ν' := dsLamTwoMulIrr C hνirr
  have hlam : LamEquiv C ν ν' := ⟨β₂, by rw [hν'def]⟩
  have hID := s02_indDiff C ν ν' hνirr hν'irr hlam
  have hne : ν' ≠ ν := by rw [hν'def]; exact dsLamTwoMulNeSelf C h2 hβ₂ hνirr
  have hsconj : sconj C ν' = ν' := by
    rw [hν'def, dsSconjLamTwoMul C h2 hβ₂ ν, hνs]
  have hii : ClassFunction.inner ν ν = 1 := by
    rw [irr_cf_inner (mem_irreducibleCharacters.mpr hνirr)
      (mem_irreducibleCharacters.mpr hνirr)]
    simp
  have hij : ClassFunction.inner ν ν' = 0 := by
    rw [irr_cf_inner (mem_irreducibleCharacters.mpr hνirr)
      (mem_irreducibleCharacters.mpr hν'irr)]
    simp [Ne.symm hne]
  have hji : ClassFunction.inner ν' ν = 0 := by
    rw [irr_cf_inner (mem_irreducibleCharacters.mpr hν'irr)
      (mem_irreducibleCharacters.mpr hνirr)]
    simp [hne]
  have hjj : ClassFunction.inner ν' ν' = 1 := by
    rw [irr_cf_inner (mem_irreducibleCharacters.mpr hν'irr)
      (mem_irreducibleCharacters.mpr hν'irr)]
    simp
  have hg := s02_gram C ν ν' ν ν' hνirr hν'irr hνirr hν'irr hlam hlam
  have e1 : cH C ν ν = 2 := by
    rw [cH_eq_inner_add C hνirr hνirr, hνs, hii]; norm_num
  have e2 : cH C ν ν' = 0 := by
    rw [cH_eq_inner_add C hνirr hν'irr, hsconj, hij]; ring
  have e3 : cH C ν' ν = 0 := by
    rw [cH_eq_inner_add C hν'irr hνirr, hνs, hji]; ring
  have e4 : cH C ν' ν' = 2 := by
    rw [cH_eq_inner_add C hν'irr hν'irr, hsconj, hjj]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [Work.GW2.C16.delta, ← hν'def]; exact hID.1
  · rw [Work.GW2.C16.delta, ← hν'def]; exact hID.2
  · rw [Work.GW2.C16.delta, ← hν'def, hg, e1, e2, e3, e4]; norm_num

/-! ## 4. The target -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem deltaShape {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.DeltaShapeProp D C := by
  intro hC hn β₂ hβ₂ ν hν
  obtain ⟨hZ, h0, hnorm⟩ := dsDeltaS4Facts D C hC hn β₂ hβ₂ ν hν
  exact dsShapeOfZIrr (Work.GW2.C16.delta C β₂ ν) hZ hnorm h0

end Work.BG
