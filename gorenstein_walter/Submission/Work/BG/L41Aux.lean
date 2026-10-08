/-
# Area BG: the §4 (`|S| = 4`, i.e. `D.n = 2`) structure lemmas (Bender–Glauberman 1981)

This module collects the structural facts about the `|S| = 4` case of Bender–Glauberman,
J. Algebra **70** (1981), §4 (pp. 211–215), which are used

* to build a coherent map (Theorem 2.3) in that case, and
* to prove Lemma 4.1 (`Work.GW2.C16.Lemma41Prop`).

In the `D.n = 2` situation the quotient `H₀/U` has order two, so `Λ = {λ₁, λ₂}`, and the
`Λ`-orbit of any `ν ∈ Irr(H₀)` is `{ν, λ₂ν}`.  Everything below is stated with a fixed
non-trivial `β₂ : H₀/U →* ℂˣ` and the corresponding `λ₂ = lamCF C β₂`:
`dualC2_generic` (in `Submission.Work.BG.lemma17_iii_dualC2`) says that every `β` is `1`
or `β₂` and that `β₂` is `-1` off the identity of `H₀/U`.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.nCases
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.centralValue
import Submission.Work.BG.sconjLam
import Submission.Work.BG.H0Conj
import Submission.Work.BG.Lambda
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.lemma17_iii_lam2Conj
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.hatInjRestrictIrr
import Submission.Work.BG.s02_twoCase
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_assemblyFull
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.s02_lamDual

set_option linter.unusedSectionVars false

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

section Sec4

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-! ## 1. The quotient `H₀/U` and the dual group `{1, β₂}` -/

/-- **`|H₀/U| = 2` in the `|S| = 4` case.**  `[H₀ : U] = |S₀| = D.n` (`rem31IndexUin`), so
`D.n = 2` makes `H₀/U` a group of order two. -/
theorem quotGroup_card_two (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) :
    Nat.card (quotGroup C.P) = 2 := by
  rw [← Subgroup.index_eq_card (Work.GW2.C16.Uin C)]
  rw [rem31IndexUin D C hc, hn]

/-- In a group of order two every element is an involution. -/
theorem quotGroup_sq_eq_one {x : quotGroup C.P} (h2 : Nat.card (quotGroup C.P) = 2) :
    x ^ 2 = 1 := by
  by_cases hx1 : x = 1
  · rw [hx1, one_pow]
  · have hdvd : orderOf x ∣ 2 := by rw [← h2]; exact orderOf_dvd_natCard x
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf x) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · rw [← h]; exact pow_orderOf_eq_one x

/-- **The dual of `H₀/U` is `{1, β₂}`.** -/
theorem hom_eq_one_or_two {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) (β : quotGroup C.P →* ℂˣ) : β = 1 ∨ β = β₂ :=
  (lemma17_iii_dualC2 C.P h2 hβ).1 β

/-- `β₂` is `-1` on every non-identity element of `H₀/U`. -/
theorem quot_ne_one_apply_ne_one {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) {x : quotGroup C.P} (hx : x ≠ 1) :
    ((β₂ x : ℂˣ) : ℂ) = -1 :=
  (lemma17_iii_dualC2 C.P h2 hβ).2 x hx

/-- `lamCF` and `lambdaInf` are the same inflation. -/
theorem lamCF_eq_lambdaInf (β : quotGroup C.P →* ℂˣ) : lamCF C β = lambdaInf C.P β := rfl

/-- The trivial element of `Λ`. -/
theorem lamCF_one_eq : lamCF C (1 : quotGroup C.P →* ℂˣ) =
    linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) := by
  rw [lamCF_eq_lambdaInf, lambdaInf_one]

/-- Every element of `Λ` is `1` or `λ₂ = lamCF C β₂`. -/
theorem lamCF_eq_one_or_two {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) (β : quotGroup C.P →* ℂˣ) :
    lamCF C β = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) ∨ lamCF C β = lamCF C β₂ := by
  rcases hom_eq_one_or_two C h2 hβ β with h | h
  · exact Or.inl (by rw [h, lamCF_one_eq])
  · exact Or.inr (by rw [h])

/-- `λ₂ ≠ 1` when `β₂ ≠ 1`. -/
theorem lamCF_two_ne_trivial {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1) :
    lamCF C β₂ ≠ linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) := by
  intro h
  apply hβ
  refine MonoidHom.ext fun x => ?_
  obtain ⟨h0, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) x
  have hval : (β₂ (quotMk C.P h0) : ℂ) = 1 := by
    have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ h0) h
    simpa [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply] using h1
  exact Units.ext hval

/-- The value of `λ₂` at `t`: `λ₂(t) = -1`. -/
theorem lamCF_two_apply_t {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    lamCF C β₂ C.t = -1 := by
  rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  have hx : quotMk C.P C.t ≠ 1 := by
    intro h
    exact C.t_not_mem_U ((QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) C.t).mp h)
  exact quot_ne_one_apply_ne_one C h2 hβ hx

/-- `λ₂` is an involution. -/
theorem lamCF_two_mul_self {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) :
    lamCF C β₂ * lamCF C β₂ = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) := by
  have hsq : β₂ * β₂ = 1 := by
    refine MonoidHom.ext fun x => ?_
    show β₂ x * β₂ x = (1 : quotGroup C.P →* ℂˣ) x
    rw [MonoidHom.one_apply, ← sq, ← map_pow, quotGroup_sq_eq_one C h2, map_one]
  rw [lamCF_eq_lambdaInf, lambdaInf_mul, hsq, lambdaInf_one]

/-- `λ₂` is its own inverse: `lamCF C β₂⁻¹ = lamCF C β₂`. -/
theorem lamCF_two_inv_eq {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) : lamCF C β₂⁻¹ = lamCF C β₂ := by
  rcases hom_eq_one_or_two C h2 hβ β₂⁻¹ with h | h
  · refine absurd ?_ hβ
    rw [← inv_inv β₂, h]
    refine MonoidHom.ext fun x => ?_
    simp
  · rw [h]

/-! ## 2. `s`-conjugation -/

/-- `s`-conjugation commutes with multiplication by `λ₂`. -/
theorem sconj_lam_two_mul {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (lamCF C β₂ * ν) = lamCF C β₂ * sconj C ν := by
  rw [sconjLam C β₂ ν, lamCF_two_inv_eq C h2 hβ]

/-- `(λ₂ν)` is `s`-fixed iff `ν` is. -/
theorem sconj_lam_two_mul_eq_iff {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    (sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν) ↔ sconj C ν = ν := by
  rw [sconj_lam_two_mul C h2 hβ]
  constructor
  · intro h
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => lamCF C β₂ * φ) h
    rw [← mul_assoc_cf, ← mul_assoc_cf, lamCF_two_mul_self C h2] at h'
    simpa [one_mul_cf] using h'
  · intro h
    rw [h]

/-! ## 3. Values at `t` -/

/-- The degree of an irreducible character of `H₀` is non-zero. -/
theorem irr_apply_one_ne_zero {ν : ClassFunction ↥C.P.H0 ℂ}
    (hν : IsIrreducibleCharacter ν) : ν 1 ≠ 0 := by
  obtain ⟨n, hn, hval, -⟩ := hν.exists_natDegree_charValue_one_dvd_card
  rw [hval]
  exact_mod_cast hn.ne'

/-- Schur for the central involution `t`: `ν(t) = ±ν(1)`. -/
theorem t_val_or {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    ν C.t = ν 1 ∨ ν C.t = -ν 1 := (centralValue C ν hν).1

/-- `ν(t) ≠ 0` for `ν ∈ Irr(H₀)`. -/
theorem t_val_ne_zero {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    ν C.t ≠ 0 := by
  rcases t_val_or C hν with h | h
  · rw [h]; exact irr_apply_one_ne_zero C hν
  · rw [h]; exact neg_ne_zero.mpr (irr_apply_one_ne_zero C hν)

/-- The value of `λ₂ν` at `t`: `(λ₂ν)(t) = -ν(t)`. -/
theorem lam_two_mul_apply_t {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) : (lamCF C β₂ * ν) C.t = -ν C.t := by
  rw [ClassFunction.mul_apply, lamCF_two_apply_t C h2 hβ]
  ring

/-- `λ₂ν ≠ ν` for `ν ∈ Irr(H₀)`. -/
theorem lam_two_mul_ne_self {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    lamCF C β₂ * ν ≠ ν := by
  intro h
  have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
  rw [lam_two_mul_apply_t C h2 hβ ν] at h1
  have h2' : (2 : ℂ) * ν C.t = 0 := by linear_combination (-1) * h1
  exact t_val_ne_zero C hν ((mul_eq_zero.mp h2').resolve_left (by norm_num))

/-- `ν^s ≠ λ₂ν` for `ν ∈ Irr(H₀)`. -/
theorem sconj_ne_lam_two_mul {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    sconj C ν ≠ lamCF C β₂ * ν := by
  intro h
  have h1 := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
  rw [sconj_apply_t C ν, lam_two_mul_apply_t C h2 hβ ν] at h1
  have h2' : (2 : ℂ) * ν C.t = 0 := by linear_combination h1
  exact t_val_ne_zero C hν ((mul_eq_zero.mp h2').resolve_left (by norm_num))

/-- `λ₂ν` is irreducible when `ν` is. -/
theorem lam_two_mul_irr {β₂ : quotGroup C.P →* ℂˣ} {ν : ClassFunction ↥C.P.H0 ℂ}
    (hν : IsIrreducibleCharacter ν) : IsIrreducibleCharacter (lamCF C β₂ * ν) :=
  lambda_mul_irreducible C.P (lambdaInf_mem C.P β₂) hν

/-! ## 4. The `Λ`-orbits and the key of `ν` -/

/-- **`Λμ = {μ, λ₂μ}`**: `μ` and `ν` are `Λ`-equivalent iff `ν = μ` or `ν = λ₂μ`. -/
theorem LamEquiv_iff {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) (μ ν : ClassFunction ↥C.P.H0 ℂ) :
    LamEquiv C μ ν ↔ ν = μ ∨ ν = lamCF C β₂ * μ := by
  constructor
  · rintro ⟨β, rfl⟩
    rcases lamCF_eq_one_or_two C h2 hβ β with h | h
    · left
      rw [h, one_mul_cf]
    · right
      rw [h]
  · rintro (h | h)
    · rw [h]
      exact ⟨1, by rw [lamCF_one_eq, one_mul_cf]⟩
    · rw [h]
      exact ⟨β₂, rfl⟩

/-- The `Λ`-orbit of `μ`, in the `|S| = 4` case. -/
theorem lamOrbit_eq {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) (μ : ClassFunction ↥C.P.H0 ℂ) :
    lamOrbit C μ = {ν | ν = μ ∨ ν = lamCF C β₂ * μ} := by
  ext ν
  show LamEquiv C μ ν ↔ _
  rw [LamEquiv_iff C h2 hβ, Set.mem_ofPred_eq]

/-- The `Λ`-orbit of an irreducible has exactly two elements. -/
theorem lamOrbit_ncard_eq_two {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) :
    (lamOrbit C μ).ncard = 2 := by
  have hset : {ν : ClassFunction ↥C.P.H0 ℂ | ν = μ ∨ ν = lamCF C β₂ * μ} =
      {μ, lamCF C β₂ * μ} := by
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [lamOrbit_eq C h2 hβ μ, hset,
    Set.ncard_pair (Ne.symm (lam_two_mul_ne_self C h2 hβ hμ))]

/-- The `s`-image of a `Λ`-orbit in the `|S| = 4` case. -/
theorem sconj_image_lamOrbit {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) (μ : ClassFunction ↥C.P.H0 ℂ) :
    sconj C '' lamOrbit C μ = {ν | ν = sconj C μ ∨ ν = lamCF C β₂ * sconj C μ} := by
  rw [lamOrbit_eq C h2 hβ μ]
  ext ν
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx | hx, hνx⟩
    · exact Or.inl (by rw [← hνx, hx])
    · exact Or.inr (by rw [← hνx, hx, sconj_lam_two_mul C h2 hβ])
  · rintro (h | h)
    · exact ⟨μ, Or.inl rfl, by rw [h]⟩
    · refine ⟨lamCF C β₂ * μ, Or.inr rfl, ?_⟩
      rw [h, sconj_lam_two_mul C h2 hβ]

/-- The key `Λν ∪ (Λν)^s` in the `|S| = 4` case. -/
theorem orbitKey_eq {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ : β₂ ≠ 1) (μ : ClassFunction ↥C.P.H0 ℂ) :
    orbitKey C μ = ({ν | ν = μ ∨ ν = lamCF C β₂ * μ} ∪
      {ν | ν = sconj C μ ∨ ν = lamCF C β₂ * sconj C μ}) := by
  rw [orbitKey, sconj_image_lamOrbit C h2 hβ μ, lamOrbit_eq C h2 hβ μ]

/-! ## 5. `δ_ν = (ν - λ₂ν)^*` -/

/-- Linearity of induction in the difference of class functions. -/
theorem l41_induce_sub {H : Subgroup G} [Invertible (Nat.card ↥H : ℂ)]
    (θ ψ : ClassFunction ↥H ℂ) :
    ClassFunction.induce H (θ - ψ) =
      ClassFunction.induce H θ - ClassFunction.induce H ψ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ClassFunction.induce_add]
  congr 1
  have h1 : (-ψ : ClassFunction ↥H ℂ) = (-1 : ℂ) • ψ := by
    ext h; simp
  rw [h1, ClassFunction.induce_smul]
  simp

/-- Induction to `G` does not see `s`-conjugation. -/
theorem l41_ind_sconj (μ : ClassFunction ↥C.P.H0 ℂ) : ind C (sconj C μ) = ind C μ :=
  induce_conjByH C.P C.s μ

/-- Induction to `G` is invariant under `s`-conjugation of both arguments. -/
theorem l41_ind_sconj_sub (μ ν : ClassFunction ↥C.P.H0 ℂ) :
    ind C (sconj C μ - sconj C ν) = ind C (μ - ν) := by
  show ClassFunction.induce C.P.H0 (sconj C μ - sconj C ν) =
    ClassFunction.induce C.P.H0 (μ - ν)
  rw [l41_induce_sub, l41_induce_sub,
    show ClassFunction.induce C.P.H0 (sconj C μ) = ClassFunction.induce C.P.H0 μ from
      l41_ind_sconj C μ,
    show ClassFunction.induce C.P.H0 (sconj C ν) = ClassFunction.induce C.P.H0 ν from
      l41_ind_sconj C ν]

/-- `δ_ν ∈ ℤ[Irr G]`. -/
theorem l41_delta_mem_ZIrr {β₂ : quotGroup C.P →* ℂˣ}
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    Work.GW2.C16.delta C β₂ ν ∈ ZIrr G :=
  (s02_indDiff C ν (lamCF C β₂ * ν) hν (lam_two_mul_irr C hν) ⟨β₂, rfl⟩).1

/-- `δ_ν` has degree zero. -/
theorem l41_delta_apply_one {β₂ : quotGroup C.P →* ℂˣ}
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    Work.GW2.C16.delta C β₂ ν 1 = 0 :=
  (s02_indDiff C ν (lamCF C β₂ * ν) hν (lam_two_mul_irr C hν) ⟨β₂, rfl⟩).2

/-- The diagonal `cH` value at an `s`-fixed character. -/
theorem l41_cH_self_eq {ν : ClassFunction ↥C.P.H0 ℂ} (h : sconj C ν = ν) :
    cH C ν ν = 2 := by
  classical
  have hc : cH C ν ν
      = (if ν = ν then 1 else 0) + (if ν = sconj C ν then 1 else 0) := rfl
  rw [hc, if_pos rfl, if_pos h.symm]
  norm_num

/-- The diagonal `cH` value at a non-`s`-fixed character. -/
theorem l41_cH_self_ne {ν : ClassFunction ↥C.P.H0 ℂ} (h : sconj C ν ≠ ν) :
    cH C ν ν = 1 := by
  classical
  have hc : cH C ν ν
      = (if ν = ν then 1 else 0) + (if ν = sconj C ν then 1 else 0) := rfl
  rw [hc, if_pos rfl, if_neg (fun hh => h hh.symm)]
  norm_num

/-- The mixed `cH` value `cH C ν (λ₂ν)`. -/
theorem l41_cH_cross_nu {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    cH C ν (lamCF C β₂ * ν) = 0 := by
  classical
  have hc : cH C ν (lamCF C β₂ * ν)
      = (if (lamCF C β₂ * ν) = ν then 1 else 0)
        + (if (lamCF C β₂ * ν) = sconj C ν then 1 else 0) := rfl
  rw [hc, if_neg (lam_two_mul_ne_self C h2 hβ hν),
    if_neg (Ne.symm (sconj_ne_lam_two_mul C h2 hβ hν))]
  norm_num

/-- The mixed `cH` value `cH C (λ₂ν) ν`. -/
theorem l41_cH_cross_lam {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    cH C (lamCF C β₂ * ν) ν = 0 := by
  classical
  have h1 : ν ≠ lamCF C β₂ * ν := fun h => lam_two_mul_ne_self C h2 hβ hν h.symm
  have h2' : ν ≠ sconj C (lamCF C β₂ * ν) := by
    intro hconj
    -- `hconj : ν = (λ₂ν)^s = λ₂·ν^s`, hence `ν^s = λ₂ν`
    have hνeq : ν = lamCF C β₂ * sconj C ν := by
      conv_lhs => rw [hconj]
      rw [sconj_lam_two_mul C h2 hβ]
    refine sconj_ne_lam_two_mul C h2 hβ hν ?_
    have key : lamCF C β₂ * ν = sconj C ν := by
      conv_lhs => rw [hνeq]
      rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
    exact key.symm
  have hc : cH C (lamCF C β₂ * ν) ν
      = (if ν = lamCF C β₂ * ν then 1 else 0)
        + (if ν = sconj C (lamCF C β₂ * ν) then 1 else 0) := rfl
  rw [hc, if_neg h1, if_neg h2']
  norm_num

/-- The diagonal `cH` value at `λ₂ν` when `ν` is `s`-fixed. -/
theorem l41_cH_lam_self_eq {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (h : sconj C ν = ν) :
    cH C (lamCF C β₂ * ν) (lamCF C β₂ * ν) = 2 := by
  classical
  have h' : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν :=
    (sconj_lam_two_mul_eq_iff C h2 hβ ν).mpr h
  have hc : cH C (lamCF C β₂ * ν) (lamCF C β₂ * ν)
      = (if (lamCF C β₂ * ν) = (lamCF C β₂ * ν) then 1 else 0)
        + (if (lamCF C β₂ * ν) = sconj C (lamCF C β₂ * ν) then 1 else 0) := rfl
  rw [hc, if_pos rfl, if_pos h'.symm]
  norm_num

/-- The diagonal `cH` value at `λ₂ν` when `ν` is not `s`-fixed. -/
theorem l41_cH_lam_self_ne {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (h : sconj C ν ≠ ν) :
    cH C (lamCF C β₂ * ν) (lamCF C β₂ * ν) = 1 := by
  classical
  have h' : sconj C (lamCF C β₂ * ν) ≠ lamCF C β₂ * ν :=
    fun hh => h ((sconj_lam_two_mul_eq_iff C h2 hβ ν).mp hh)
  have hc : cH C (lamCF C β₂ * ν) (lamCF C β₂ * ν)
      = (if (lamCF C β₂ * ν) = (lamCF C β₂ * ν) then 1 else 0)
        + (if (lamCF C β₂ * ν) = sconj C (lamCF C β₂ * ν) then 1 else 0) := rfl
  rw [hc, if_pos rfl, if_neg (fun hh => h' hh.symm)]
  norm_num

/-- **The norm of `δ_ν`** (BG §4, p. 212): `(δ_ν, δ_ν) = 4` if `ν` is `s`-fixed and `2`
otherwise.  The Brauer–Suzuki Gram matrix `GramProp` gives
`(δ_ν, δ_ν) = cH C ν ν - cH C ν (λ₂ν) - cH C (λ₂ν) ν + cH C (λ₂ν) (λ₂ν)`; the two mixed
terms vanish because `ν` and `λ₂ν` can never be `Λ`-equivalent *and* `s`-conjugate. -/
theorem l41_delta_inner_self {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    ClassFunction.inner (Work.GW2.C16.delta C β₂ ν) (Work.GW2.C16.delta C β₂ ν) =
      (by classical exact if sconj C ν = ν then 4 else 2) := by
  classical
  have hlam : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hν
  have hLam : LamEquiv C ν (lamCF C β₂ * ν) := ⟨β₂, rfl⟩
  have hgram := (s02_gram C) ν (lamCF C β₂ * ν) ν (lamCF C β₂ * ν) hν hlam hν hlam hLam hLam
  show ClassFunction.inner (ind C (ν - lamCF C β₂ * ν)) (ind C (ν - lamCF C β₂ * ν)) = _
  rw [hgram, l41_cH_cross_nu C h2 hβ hν, l41_cH_cross_lam C h2 hβ hν]
  by_cases h : sconj C ν = ν
  · rw [l41_cH_self_eq C h, l41_cH_lam_self_eq C h2 hβ h, if_pos h]
    norm_num
  · rw [l41_cH_self_ne C h, l41_cH_lam_self_ne C h2 hβ h, if_neg h]
    norm_num

/-- **The degree of a member of `𝒮₄(C)` is odd.**  `ν ∈ S4Index` restricts to an
irreducible character of the odd-order group `U` (with the same degree), and an
irreducible degree divides the group order. -/
theorem l41_s4Index_one_odd (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.S4Index C) :
    ∃ d : ℤ, Odd d ∧ ν 1 = d := by
  have hirr : IsIrreducibleCharacter (restrictU C ν) := hatInjRestrictIrr C hc hn hν
  obtain ⟨n, hnpos, hnval, hndvd⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  have hdeg : ν 1 = (n : ℂ) := by
    have h1 : (restrictU C ν) (1 : ↥C.P.U) = ν 1 := by
      rw [restrictU_apply]
      rfl
    rw [← h1, hnval]
  have hUodd : Odd (Nat.card ↥C.P.U) := by
    have hUpi : C.P.U.IsPiSubgroup ({q : ℕ | q ≠ 2}) := by
      rw [show C.P.U = D.U from hc.U_eq, show D.U = Work.GW2.oddCoreIn D.H from rfl,
        Work.GW2.oddCoreIn_eq_opiCoreInG]
      exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
    rcases Nat.even_or_odd (Nat.card ↥C.P.U) with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      have h2dvd : 2 ∣ Nat.card ↥C.P.U := ⟨k, by rw [hk]; ring⟩
      exact hUpi 2 (Nat.prime_two.mem_primeFactors h2dvd (Nat.card_pos.ne')) rfl
    · exact ho
  have hnodd : Odd n := by
    obtain ⟨j, hj⟩ := hndvd
    rw [hj] at hUodd
    exact (Nat.odd_mul.mp hUodd).1
  exact ⟨(n : ℤ), by exact_mod_cast hnodd, by rw [hdeg]; norm_num⟩

/-! ## 6. The §3 hypothesis holds automatically when `D.n = 2` -/

/-- **`Sec3Hyp` in the `|S| = 4` case.**  `D.n = 2` gives `|S₀| = 2` (`Work.BG.nCases`), so
every `x ∈ S₀` is an involution and `x ^ 2` is central. -/
theorem l41_sec3Hyp (D : Work.GW2.BGData G) (hn : D.n = 2) :
    Work.GW2.C16.Sec3Hyp D := by
  intro x hx u hu
  have hS0 : Nat.card ↥D.S0 = 2 := by rw [(Work.BG.nCases G D).2, hn]
  have hx2 : x ^ 2 = 1 := by
    have h : (⟨x, hx⟩ : ↥D.S0) ^ 2 = 1 := by
      have hdvd : orderOf (⟨x, hx⟩ : ↥D.S0) ∣ 2 := by
        rw [← hS0]
        exact orderOf_dvd_natCard _
      have hpow : (⟨x, hx⟩ : ↥D.S0) ^ orderOf (⟨x, hx⟩ : ↥D.S0) = 1 :=
        pow_orderOf_eq_one _
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hdvd with h1 | h1
      · rw [h1, pow_one] at hpow
        rw [hpow, one_pow]
      · rw [h1] at hpow
        exact hpow
    have h2 := congrArg (fun y : ↥D.S0 => (y : G)) h
    simpa using h2
  rw [hx2, one_mul, mul_one]

end Sec4

end Work.BG
