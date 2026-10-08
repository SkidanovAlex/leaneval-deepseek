/-
# Area BG: `DecompBigProp` — Bender–Glauberman 1981, Lemma 2.5 (first lines)

`Work.GW2.C16.DecompBigProp D C` states (BG p. 207, for `|S| ≥ 8`, i.e. `n ≥ 4`): for a
coherent map `f` there is `β` with `λ_β(t) = -1`, `λ_β` not `s`-fixed, `f (λ_β) = ±Irr` with
value `-2` at `t`, and

  `f (λ_1) = 1_G + φ`,  `φ = ±Irr`,  `φ ⊥ 1_G`,  `φ ⊥ f (λ_β)`,  `φ(t) = 1`.

The paper's route (BG pp. 206–207):

* `f (λ_β)(t) = 2 λ_β(t) = -2`: for `n ≥ 8` this is clause (vi) of the coherence theorem
  (the exception `|Λν| = 4 ∧ (Λν)^s = Λν` needs `|Λ| = n = 4`); for `n = 4` it is
  Lemma 3.4, which applies because `S' = ⟨t⟩` is central in `H` (`sec3Hyp_of_n_eq_four`).
* `f (λ_1) ∈ ℤ[Irr G]` has norm `2` and inner product `1` with `1_G` (Frobenius
  reciprocity for `f λ_1 - f λ_β = (λ_1 - λ_β)*`), so `f (λ_1) = 1_G + φ` with `φ = ±Irr`,
  `φ ⊥ 1_G`, `φ(t) = f(λ_1)(t) - 1 = (f λ_β(t) + 4) - 1 = 1`
  (coherence clause (v) at `t`: `f(λ_1)(t) - f(λ_β)(t) = 2(λ_1(t) - λ_β(t)) = 4`).
-/
import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_lemma21Ext
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.lemma24
import Submission.Work.BG.exists_lamCF_t_neg_one_sconj_ne
import Submission.Work.BG.sec3Hyp_of_n_eq_four
import Submission.Work.BG.noThirdExceptional

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

section Helpers

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `lamCF C 1` is the trivial class function of `H₀`. -/
theorem lamCF_one_eq_trivial (C : Sec2Ctx G) :
    lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 := by
  rw [lamCF_one]
  ext h
  simp [linearClassFunction_apply, trivialClassFunction_apply]

/-- `lamCF C 1` is `s`-invariant. -/
theorem sconj_lamCF_one (C : Sec2Ctx G) : sconj C (lamCF C 1) = lamCF C 1 := by
  rw [lamCF_one_eq_trivial]
  ext h
  simp [sconj, conjByH_apply]

/-- `lamCF C β` is irreducible (it is a linear character). -/
theorem isIrreducibleCharacter_lamCF (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    IsIrreducibleCharacter (lamCF C β) := by
  have h1triv : lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 :=
    lamCF_one_eq_trivial C
  have h1irr : IsIrreducibleCharacter (lamCF C 1) := by
    rw [h1triv]; exact trivialClassFunction_isIrreducible
  have hmem : lamCF C β ∈ Lambda C.P := ⟨β, rfl⟩
  have h := lambda_mul_irreducible C.P hmem h1irr
  have hmul : lamCF C β * lamCF C 1 = lamCF C β := by
    rw [lamCF_one, ClassFunction.mul_linearClassFunction_one]
  simpa [hmul] using h

/-- The `Λ`-stabiliser of a *linear* character `λ_β` is trivial: `λ_γ λ_β = λ_β` forces
`λ_γ = 1`, so `γ = 1`. -/
theorem lamStab_lamCF_eq_bot (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    lamStab C (lamCF C β) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  rw [mem_lamStab] at hγ
  refine LamCFFixed.lamCF_injective C ?_
  have hγeq : lamCF C γ = lamCF C 1 := by
    have hpt : ∀ x : ↥C.P.H0, lamCF C γ x * lamCF C β x = lamCF C β x := by
      intro x
      have h := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ x) hγ
      simpa using h
    ext x
    have hne : lamCF C β x ≠ 0 := by
      rw [lamCF_apply]
      exact_mod_cast Units.ne_zero (β (quotMk C.P x))
    have h1 : lamCF C γ x = 1 :=
      mul_right_cancel₀ hne (by rw [hpt x, one_mul])
    rw [h1, lamCF_one_eq_trivial, trivialClassFunction_apply]
  rw [hγeq, lamCF_one_eq_trivial]

/-- The `Λ`-orbit of a linear character `λ_β` has `|H₀ : U|` elements. -/
theorem lamOrbit_lamCF_ncard (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    (lamOrbit C (lamCF C β)).ncard = (Uin C).index := by
  have h := rem31StabCard C (lamCF C β)
  rw [lamStab_lamCF_eq_bot C β] at h
  simpa using h

/-- The value of `sconj C (lamCF C β) = λ_{β⁻¹}` at `t`, when `λ_β(t) = -1`. -/
theorem sconj_lamCF_apply_t (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (hβt : lamCF C β C.t = -1) : sconj C (lamCF C β) C.t = -1 := by
  have hβunit : β (tU C) = -1 := by
    apply Units.ext
    rw [Units.val_neg, Units.val_one, ← lamCF_apply_t, hβt]
  rw [LamCFFixed.sconj_lamCF, lamCF_apply_t, MonoidHom.inv_apply, hβunit]
  simp

end Helpers

section Main

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **The exceptional (`n = 4`) value `f (λ_β)(t) = -2`.**  Given that `𝒮(f λ_β)` has no
element other than `λ_β` and `λ_β^s` (BG Lemma 3.4's exceptional case), Lemma 2.4 at `t`
gives `f(λ_β)(t) = 2λ_β(t) = -2`: the two members of `𝒮` contribute `(fλ_β, fλ_β)·λ_β(t)`
and `(fλ_β, f(sconj λ_β))·(sconj λ_β)(t)`, and `f(sconj λ_β) = f(λ_β)` with norm `1`. -/
theorem valC_of_noThird (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (β : quotGroup C.P →* ℂˣ) (hβt : lamCF C β C.t = -1)
    (hβs : sconj C (lamCF C β) ≠ lamCF C β)
    (hnoThird : ∀ ξ ∈ bset C f (f (lamCF C β)), ξ ≠ lamCF C β →
      ξ ≠ sconj C (lamCF C β) → False) :
    f (lamCF C β) (C.t : G) = -2 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  have hνirr : IsIrreducibleCharacter (lamCF C β) := isIrreducibleCharacter_lamCF C β
  have hGν := hf.1 (lamCF C β) hνirr
  have hEν : lamCF C β ∈ orbitKey C (lamCF C β) := Or.inl (s02c_LamEquiv_refl C _)
  obtain ⟨hCZI, hCsconj, hCnorm, -, -, -⟩ :=
    hGν (lamCF C β) hEν (lamCF C β) hEν hνirr hνirr
  have hCnorm1 : ClassFunction.inner (f (lamCF C β)) (f (lamCF C β)) = 1 := by
    rw [hCnorm, if_neg hβs]
  have hCpm : IsPmIrr (f (lamCF C β)) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one hCZI hCnorm1
  have hmem1 : lamCF C β ∈ bset C f (f (lamCF C β)) :=
    ⟨hνirr, by rw [hCnorm1]; norm_num⟩
  have hmem2 : sconj C (lamCF C β) ∈ bset C f (f (lamCF C β)) := by
    refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hνirr, ?_⟩
    rw [hCsconj, hCnorm1]
    norm_num
  have hbset : bset C f (f (lamCF C β)) = {lamCF C β, sconj C (lamCF C β)} := by
    apply Set.Subset.antisymm
    · intro ξ hξ
      by_cases h1 : ξ = lamCF C β
      · rw [h1]; exact Set.mem_insert _ _
      · by_cases h2 : ξ = sconj C (lamCF C β)
        · rw [h2]; exact Set.mem_insert_of_mem _ rfl
        · exact (hnoThird ξ hξ h1 h2).elim
    · intro ξ hξ
      rcases Set.mem_insert_iff.mp hξ with h | h
      · rw [h]; exact hmem1
      · rw [Set.mem_singleton_iff.mp h]; exact hmem2
  -- BG Lemma 2.4 at `t`
  have h24 := (lemma24 C f hf (f (lamCF C β)) hCpm).2.1 C.t C.t_not_mem_U
  rw [hbset] at h24
  have hnotmem : lamCF C β ∉ ({sconj C (lamCF C β)} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    rw [Set.mem_singleton_iff]
    exact fun h => hβs h.symm
  rw [finsum_mem_insert (f := fun η => ClassFunction.inner (f (lamCF C β)) (f η) * η C.t)
      (a := lamCF C β) (s := ({sconj C (lamCF C β)} : Set (ClassFunction ↥C.P.H0 ℂ)))
      hnotmem (Set.toFinite _), finsum_mem_singleton] at h24
  rw [hCsconj, hCnorm1, hβt, sconj_lamCF_apply_t C β hβt] at h24
  rw [h24]
  norm_num

/-- **DEC-BIG**, in the form used by the caller: the conclusions of `DecompBigProp` from the
two inputs needed to select `β` and to reach the `n = 4` case of BG Lemma 3.4. -/
theorem decompBig_aux (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hcompat : Compat D C) (hn : 4 ≤ D.n)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (hβ : ∃ β : quotGroup C.P →* ℂˣ, lamCF C β C.t = -1 ∧ sconj C (lamCF C β) ≠ lamCF C β)
    (hNoThird : ∀ (β : quotGroup C.P →* ℂˣ), lamCF C β C.t = -1 →
      sconj C (lamCF C β) ≠ lamCF C β → D.n = 4 →
      ∀ ξ ∈ bset C f (f (lamCF C β)), ξ ≠ lamCF C β →
        ξ ≠ sconj C (lamCF C β) → False) :
    ∃ β : quotGroup C.P →* ℂˣ,
      lamCF C β C.t = -1 ∧ sconj C (lamCF C β) ≠ lamCF C β ∧
      IsPmIrr (f (lamCF C β)) ∧ f (lamCF C β) (C.t : G) = -2 ∧
      ∃ φ : ClassFunction G ℂ, IsPmIrr φ ∧
        ClassFunction.inner φ (trivialClassFunction G) = 0 ∧
        ClassFunction.inner φ (f (lamCF C β)) = 0 ∧
        f (lamCF C 1) = trivialClassFunction G + φ ∧ φ (C.t : G) = 1 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  obtain ⟨β, hβt, hβs⟩ := hβ
  -- ## Basic facts about `λ_1` and `λ_β`
  have hν1triv : lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 :=
    lamCF_one_eq_trivial C
  have hν1irr : IsIrreducibleCharacter (lamCF C 1) := by
    rw [hν1triv]; exact trivialClassFunction_isIrreducible
  have hν1sconj : sconj C (lamCF C 1) = lamCF C 1 := sconj_lamCF_one C
  have hνirr : IsIrreducibleCharacter (lamCF C β) := isIrreducibleCharacter_lamCF C β
  have hβmul : lamCF C β * lamCF C 1 = lamCF C β := by
    have h1 : β * (1 : quotGroup C.P →* ℂˣ) = β := mul_one β
    rw [← lamCF_mul, h1]
  have hν_ne_one : lamCF C β ≠ lamCF C 1 := by
    intro h
    have h1 : lamCF C β C.t = lamCF C 1 C.t := by rw [h]
    rw [hβt, hν1triv, trivialClassFunction_apply] at h1
    norm_num at h1
  have hβunit : β (tU C) = -1 := by
    apply Units.ext
    rw [Units.val_neg, Units.val_one, ← lamCF_apply_t, hβt]
  have hβinv : β⁻¹ (tU C) = -1 := by
    rw [MonoidHom.inv_apply, hβunit]
    simp
  have hsconj_ne_one : sconj C (lamCF C β) ≠ lamCF C 1 := by
    intro h
    have h2 : lamCF C β⁻¹ = lamCF C 1 := by rw [← LamCFFixed.sconj_lamCF C β, h]
    have h3 : lamCF C β⁻¹ C.t = lamCF C 1 C.t := by rw [h2]
    rw [lamCF_apply_t] at h3
    rw [hν1triv, trivialClassFunction_apply] at h3
    rw [hβinv] at h3
    simp only [Units.val_neg, Units.val_one] at h3
    norm_num at h3
  -- ## The coherence data at `λ_β`
  have hGν := hf.1 (lamCF C β) hνirr
  have hEν : lamCF C β ∈ orbitKey C (lamCF C β) := Or.inl (s02c_LamEquiv_refl C _)
  obtain ⟨hCZI, hCsconj, hCnorm, hCind, hCdisj, hCvi⟩ :=
    hGν (lamCF C β) hEν (lamCF C β) hEν hνirr hνirr
  have hCnorm1 : ClassFunction.inner (f (lamCF C β)) (f (lamCF C β)) = 1 := by
    rw [hCnorm, if_neg hβs]
  have hCpm : IsPmIrr (f (lamCF C β)) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one hCZI hCnorm1
  -- ## The value `f (λ_β)(t) = -2`
  have hncard : (lamOrbit C (lamCF C β)).ncard = D.n := by
    rw [lamOrbit_lamCF_ncard C β, rem31IndexUin D C hcompat]
  have hvalC : f (lamCF C β) (C.t : G) = -2 := by
    by_cases h4 : D.n = 4
    · -- exceptional case: BG Lemma 3.4 via Lemma 2.4 at `t`
      exact valC_of_noThird D C f hf β hβt hβs (hNoThird β hβt hβs h4)
    · -- generic case: coherence clause (vi)
      have hnotex : ¬ ((lamOrbit C (lamCF C β)).ncard = 4 ∧
          sconj C '' lamOrbit C (lamCF C β) = lamOrbit C (lamCF C β)) := by
        rintro ⟨h1, -⟩
        rw [hncard] at h1
        exact h4 h1
      have hval := hCvi hβs hnotex
      rw [hval, hβt]
      norm_num
  -- ## `f (λ_1)`: coherence (ii), (iii), the norms and the Brauer–Suzuki Gram matrix
  have hGν1 := hf.1 (lamCF C 1) hν1irr
  have hlamEq1 : LamEquiv C (lamCF C 1) (lamCF C β) := ⟨β, hβmul.symm⟩
  have hμE : lamCF C 1 ∈ orbitKey C (lamCF C 1) := Or.inl (s02c_LamEquiv_refl C _)
  have hνE1 : lamCF C β ∈ orbitKey C (lamCF C 1) := Or.inl hlamEq1
  have hind_eq : ind C (lamCF C 1 - lamCF C β) = f (lamCF C 1) - f (lamCF C β) :=
    (hGν1 (lamCF C 1) hμE (lamCF C β) hνE1 hν1irr hνirr).2.2.2.1 hlamEq1
  have hlamEq' : LamEquiv C (lamCF C β) (lamCF C 1) :=
    ⟨β⁻¹, by rw [← lamCF_mul]; exact (congrArg (lamCF C) (inv_mul_cancel β)).symm⟩
  have hEν1 : lamCF C 1 ∈ orbitKey C (lamCF C β) := Or.inl hlamEq'
  have hAnorm : ClassFunction.inner (f (lamCF C 1)) (f (lamCF C 1)) = 2 := by
    have h := (hGν (lamCF C β) hEν (lamCF C 1) hEν1 hνirr hν1irr).2.2.1
    rw [h, if_pos hν1sconj]
  have hAZI : f (lamCF C 1) ∈ ZIrr G :=
    (hGν (lamCF C β) hEν (lamCF C 1) hEν1 hνirr hν1irr).1
  have hAdisj : DisjointCF (f (lamCF C β)) (f (lamCF C 1)) :=
    (hGν (lamCF C β) hEν (lamCF C 1) hEν1 hνirr hν1irr).2.2.2.2.1 hlamEq' hν_ne_one
      (fun h => hν_ne_one (h.trans hν1sconj))
  -- ## `(f λ_1, f λ_β) = 0`: disjointness (coherence (iii)) plus `f λ_β = ±Irr`
  have hAC : ClassFunction.inner (f (lamCF C 1)) (f (lamCF C β)) = 0 := by
    rcases hCpm with hpm | hpm
    · have hχ := hAdisj ⟨f (lamCF C β), hpm⟩
      rcases hχ with h0 | h0
      · rw [IsIrreducibleCharacter.inner_self_eq_one hpm] at h0
        exact absurd h0 (by norm_num)
      · exact h0
    · have hχ := hAdisj ⟨-(f (lamCF C β)), hpm⟩
      rcases hχ with h0 | h0
      · rw [ClassFunction.inner_neg_right, hCnorm1] at h0
        exact absurd h0 (by norm_num)
      · rw [ClassFunction.inner_neg_right] at h0
        exact neg_eq_zero.mp h0
  -- ## `(1_G, f λ_β) = 0`
  have h1C : ClassFunction.inner (trivialClassFunction G) (f (lamCF C β)) = 0 := by
    rcases hCpm with hpm | hpm
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩ : IrreducibleCharacter G)
        ⟨f (lamCF C β), hpm⟩
      rw [if_neg] at h
      · simpa using h
      · intro heq
        have hval := congrArg (fun χ : IrreducibleCharacter G =>
          (χ : ClassFunction G ℂ) (C.t : G)) heq
        simp only [Subtype.coe_mk] at hval
        rw [trivialClassFunction_apply, hvalC] at hval
        norm_num at hval
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩ : IrreducibleCharacter G)
        ⟨-(f (lamCF C β)), hpm⟩
      rw [if_neg] at h
      · rw [ClassFunction.inner_neg_right] at h
        simpa using h
      · intro heq
        have hval := congrArg (fun χ : IrreducibleCharacter G =>
          (χ : ClassFunction G ℂ) (C.t : G)) heq
        simp only [Subtype.coe_mk] at hval
        rw [trivialClassFunction_apply, ClassFunction.neg_apply, hvalC] at hval
        norm_num at hval
  -- ## Frobenius reciprocity: `(1_G, f λ_1 − f λ_β) = 1`
  have h11 : ClassFunction.inner (trivialClassFunction ↥C.P.H0)
      (trivialClassFunction ↥C.P.H0) = 1 := by
    have := irreducibleCharacter_inner_eq_ite
      (⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩ :
        IrreducibleCharacter ↥C.P.H0)
      ⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩
    simpa using this
  have hν1 : ClassFunction.inner (lamCF C β)
      (trivialClassFunction ↥C.P.H0) = 0 := by
    have := irreducibleCharacter_inner_eq_ite ⟨lamCF C β, hνirr⟩
      ⟨trivialClassFunction ↥C.P.H0, trivialClassFunction_isIrreducible⟩
    rw [if_neg] at this
    · simpa using this
    · intro heq
      have h' := congrArg (fun χ : IrreducibleCharacter ↥C.P.H0 =>
        (χ : ClassFunction ↥C.P.H0 ℂ)) heq
      exact hν_ne_one (h'.trans hν1triv.symm)
  have hind1 : ClassFunction.inner (ind C (lamCF C 1 - lamCF C β))
      (trivialClassFunction G) = 1 := by
    simp only [ind]
    rw [ClassFunction.induce_inner_trivial, ClassFunction.inner_sub_left, hν1triv,
      h11, hν1]
    norm_num
  have h1AC : ClassFunction.inner (trivialClassFunction G)
      (f (lamCF C 1) - f (lamCF C β)) = 1 := by
    rw [← hind_eq, ClassFunction.inner_star_comm, hind1]
    norm_num
  have h1A : ClassFunction.inner (trivialClassFunction G) (f (lamCF C 1)) = 1 := by
    rw [ClassFunction.inner_sub_right] at h1AC
    rw [h1C] at h1AC
    simpa using h1AC
  -- ## The auxiliary character `φ = f λ_1 − 1_G`
  have h1self : ClassFunction.inner (trivialClassFunction G) (trivialClassFunction G) = 1 := by
    have := irreducibleCharacter_inner_eq_ite
      (⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩ : IrreducibleCharacter G)
      ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩
    simpa using this
  have hA1 : ClassFunction.inner (f (lamCF C 1)) (trivialClassFunction G) = 1 := by
    rw [ClassFunction.inner_star_comm, h1A]
    norm_num
  have hφself : ClassFunction.inner (f (lamCF C 1) - trivialClassFunction G)
      (f (lamCF C 1) - trivialClassFunction G) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hAnorm, hA1, h1A, h1self]
    norm_num
  have hφZI : (f (lamCF C 1) - trivialClassFunction G) ∈ ZIrr G :=
    Submodule.sub_mem _ hAZI (trivialClassFunction_isIrreducible.mem_ZIrr)
  have hφpm : IsPmIrr (f (lamCF C 1) - trivialClassFunction G) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one hφZI hφself
  have hφorth1 : ClassFunction.inner (f (lamCF C 1) - trivialClassFunction G)
      (trivialClassFunction G) = 0 := by
    rw [ClassFunction.inner_sub_left, hA1, h1self]
    norm_num
  have hφorthC : ClassFunction.inner (f (lamCF C 1) - trivialClassFunction G)
      (f (lamCF C β)) = 0 := by
    rw [ClassFunction.inner_sub_left, hAC, h1C]
    norm_num
  have hAC_t : (f (lamCF C 1) - f (lamCF C β)) (C.t : G) = 4 := by
    have h := hf.2.2 (lamCF C 1) (lamCF C β) hν1irr hνirr hlamEq1 C.t C.t_not_mem_U
    rw [h, conjMulEquiv_s_t C]
    have h1 : lamCF C 1 C.t = 1 := by rw [hν1triv]; rfl
    rw [ClassFunction.sub_apply, h1, hβt]
    norm_num
  have hφt : (f (lamCF C 1) - trivialClassFunction G) (C.t : G) = 1 := by
    rw [ClassFunction.sub_apply, trivialClassFunction_apply]
    have h : f (lamCF C 1) (C.t : G) - f (lamCF C β) (C.t : G) = 4 := by
      simpa only [ClassFunction.sub_apply] using hAC_t
    rw [hvalC] at h
    linear_combination h
  -- ## Conclusion
  refine ⟨β, hβt, hβs, hCpm, hvalC, f (lamCF C 1) - trivialClassFunction G, hφpm,
    hφorth1, hφorthC, ?_, hφt⟩
  rw [add_comm, sub_add_cancel]

end Main

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem decompBig {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.DecompBigProp D C := by
  intro hcompat hn f hf
  refine decompBig_aux D C hcompat hn f hf
    (exists_lamCF_t_neg_one_sconj_ne D C hcompat hn) ?_
  intro β hβt hβs h4
  exact noThirdExceptional D C hcompat (sec3Hyp_of_n_eq_four D h4) f hf β hβt hβs
    (by rw [lamOrbit_lamCF_ncard C β, rem31IndexUin D C hcompat]) h4

end Work.BG
