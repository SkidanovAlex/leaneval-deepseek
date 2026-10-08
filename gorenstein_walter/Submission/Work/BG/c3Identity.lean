import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.lemma22Gen
import Submission.Work.BG.lemma22Kappa
import Submission.Work.BG.constituentSum
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.normTwoSignedPair
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_lamSign
import Submission.Work.BG.Lambda
import Submission.Work.BG.sconjLam
import Submission.Work.BG.nCases
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.s02_quotCyclic
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.H0Conj
import Submission.Work.BG.thm32
import Submission.Work.BG.c3NormTwoPair
import Submission.Work.BG.c3TUIsSquare
import Submission.Work.BG.c3LamOrbitKappa

/-!
# Area BG: Bender–Glauberman 1981, the identity (6) of Theorem C, `|S| ≥ 8`

`Work.GW2.C16.C3IdentityProp` is BG pp. 210–211, facts (1) and (6) of the proof of
Theorem C in the case `|S| ≥ 8`, for the coherent map `f` of Theorem 2.3 (BG 1981,
J. Algebra **70**, 200–215).

Given `κ` admissible (`κ` linear `≠ 1` of `H₀`, trivial on `S₀`, `s`-invariant) and
`β : H₀/U →* ℂˣ` with `λ_β(t) = -1`, the statement is: writing `ν := λ_β κ`, the images
`f κ = χ₁ + χ₂` (two orthogonal signed irreducibles) and `χ₃ := f ν` satisfy
`χ₃(t)² = 4`, `χ₁(t) + χ₂(t) = 2`, and

  `|G : H| (χ₁(t)²/χ₁(1) + χ₂(t)²/χ₂(1) − 4/χ₃(1)) = 2k²`     (6).

## Route

* `Λ_κ = 1` because `κ` is trivial on `S₀ = (H₀/U)`-generators (`H₀ = U·S₀`), so
  `|Λκ| = |Λ| = n = D.n`; in particular `Λ(λ_β κ) = Λκ` has `n` elements.
* `λ_β(t) = -1` plus `4 ≤ n` forces `β² ≠ 1`: if `β² = 1` then `β` would be trivial on the
  square `tU = x²` of `tU ∈ H₀/U` (a square because `H₀/U` is a cyclic 2-group of order
  `n ≥ 4`), contradicting `β(tU) = -1`. Hence `λ_β κ` is *not* `s`-fixed and `f (λ_β κ)` is
  a signed irreducible (norm `1`).
* Its value at `t` is `2(λ_β κ)(t) = -2`: CG clause (vi) when `n ≠ 4`, and BG Lemma 3.4
  (`Work.BG.lemma34Leaf`) when `n = 4`, where `|Λν| = n` supplies the hypothesis.
* Clause (v) at `t` for the pair `(λ_β κ, κ)` gives `f κ(t) = f (λ_β κ)(t) + 4 = 2`, i.e.
  `χ₁(t) + χ₂(t) = 2`.
* Lemma 2.2 in the `κ`-form (`Work.BG.lemma22Kappa`) together with the constituent sum
  identity X1 (`Work.GW2.C16.ConstituentSumProp`, `Work.BG.constituentSum`) applied to
  `θ = f κ − f (λ_β κ) = χ₁ + χ₂ − χ₃` gives (6).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas -/

/-- `IsPmIrr` is invariant under negation. -/
private theorem isPmIrr_neg {K : Type} [Group K] {φ : ClassFunction K ℂ}
    (h : IsPmIrr φ) : IsPmIrr (-φ) := by
  rcases h with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Cancellation of the `Λ`-action on `κ`.**  If `κ` is trivial on `S₀ = D.S0` then
`λ_γ κ = λ_{γ'} κ` forces `γ = γ'`: evaluating on the elements of `S₀` (where `κ = 1`) shows
`λ_γ = λ_{γ'}` on `S₀`, and since `H₀/U` is the image of `S₀` (as `H₀ = U · S₀`) while all
`λ` are trivial on `U`, this gives `γ = γ'`. -/
private theorem lamCF_mul_cancel {G : Type} [Group G] [Finite G] (D : BGData G)
    (C : Sec2Ctx G) (hcompat : Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    {γ γ' : quotGroup C.P →* ℂˣ} (h : lamCF C γ * κ = lamCF C γ' * κ) : γ = γ' := by
  -- the values of `λ_γ` and `λ_{γ'}` agree on `S₀`
  have hval' : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → γ (quotMk C.P s) = γ' (quotMk C.P s) := by
    intro s hs
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ s) h
    simp only [ClassFunction.mul_apply] at h'
    rw [hκS0 s hs] at h'
    rw [lamCF_apply, lamCF_apply] at h'
    exact Units.ext (by simpa using h')
  -- conclude on all of `H₀/U`, using `H₀ = U · S₀`
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
  obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hcompat x
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
  calc γ (quotMk C.P x) = γ (quotMk C.P s) := by rw [hπ]
    _ = γ' (quotMk C.P s) := hval' s hs
    _ = γ' (quotMk C.P x) := by rw [hπ]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **`λ_β κ` is not `s`-fixed** when `λ_β(t) = -1`, `κ = 1` on `S₀` and `4 ≤ D.n`: if
`β² = 1` then `β` is trivial on the square `tU = x²` of `tU` (`H₀/U` has order `n ≥ 4`),
contradicting `β(tU) = -1`. -/
private theorem sconj_lamCF_mul_ne {G : Type} [Group G] [Finite G] (D : BGData G)
    (C : Sec2Ctx G) (hcompat : Compat D C) (hn : 4 ≤ D.n)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    (hκsconj : sconj C κ = κ)
    (β : quotGroup C.P →* ℂˣ) (hβt : lamCF C β C.t = -1) :
    sconj C (lamCF C β * κ) ≠ lamCF C β * κ := by
  intro hfix
  have hA : sconj C (lamCF C β * κ) = lamCF C β⁻¹ * κ := by
    rw [sconjLam C β κ, hκsconj]
  have h1 : lamCF C β⁻¹ * κ = lamCF C β * κ := by rw [← hA]; exact hfix
  have h2 : β⁻¹ = β := lamCF_mul_cancel D C hcompat κ hκS0 h1
  have h3 : β * β = 1 := by
    calc β * β = β⁻¹ * β := by rw [h2]
      _ = 1 := inv_mul_cancel β
  obtain ⟨x, hx⟩ := c3TUIsSquare D C hcompat hn
  have h4 : β (tU C) = 1 := by
    have h' : β x * β x = 1 := by
      have hh := congrArg (fun f : quotGroup C.P →* ℂˣ => f x) h3
      simpa [MonoidHom.mul_apply] using hh
    have h5 : tU C = x * x := by rw [← hx, pow_two]
    rw [h5, map_mul]
    exact h'
  have h6 : ((β (tU C) : ℂˣ) : ℂ) = 1 := by rw [h4]; rfl
  rw [lamCF_apply_t] at hβt
  rw [h6] at hβt
  norm_num at hβt

/-- **X1 (`ConstituentSumProp`) in three-term form.** -/
private theorem constituentSum3 {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] [Fintype (IrreducibleCharacter K)]
    (ε₁ ε₂ ε₃ : ClassFunction K ℂ) (h1 : IsPmIrr ε₁) (h2 : IsPmIrr ε₂)
    (h3 : IsPmIrr ε₃) (g : K) :
    ∑ χ : IrreducibleCharacter K, (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
        ClassFunction.inner (ε₁ + ε₂ + ε₃) (χ : ClassFunction K ℂ) =
      ε₁ g ^ 2 / ε₁ 1 + ε₂ g ^ 2 / ε₂ 1 + ε₃ g ^ 2 / ε₃ 1 := by
  have hε : ∀ i : Fin 3, IsPmIrr ((![ε₁, ε₂, ε₃] : Fin 3 → ClassFunction K ℂ) i) := by
    intro i
    fin_cases i <;> simp [h1, h2, h3]
  have h := constituentSum (K := K) (ι := Fin 3)
    (![ε₁, ε₂, ε₃] : Fin 3 → ClassFunction K ℂ) hε g
  simpa [Fin.sum_univ_three] using h

/-! ## The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3Identity {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype (IrreducibleCharacter G)] :
    Work.GW2.C16.C3IdentityProp D C := by
  intro hcompat hn hS3 f hf κ hκ β hβt
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, -⟩ := hκ
  -- ## Basic facts about `ν = λ_β κ`
  have hνirr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hκt : κ C.t = 1 := hκS0 C.t (by rw [hcompat.t_eq]; exact D.t_mem)
  have hνt : (lamCF C β * κ) C.t = -1 := by
    rw [ClassFunction.mul_apply, hκt, hβt, mul_one]
  have hLam : LamEquiv C κ (lamCF C β * κ) := ⟨β, rfl⟩
  have hsconj : sconj C (lamCF C β * κ) ≠ lamCF C β * κ :=
    sconj_lamCF_mul_ne D C hcompat hn κ hκS0 hκsconj β hβt
  -- ## The orbit `Λκ = Λ(λ_β κ)` has `n` elements
  have horbκ : (lamOrbit C κ).ncard = D.n := c3LamOrbitKappa D C hcompat κ hκS0
  have horb : (lamOrbit C (lamCF C β * κ)).ncard = D.n := by
    rw [← lamOrbit_eq_of_lamEquiv hLam]; exact horbκ
  -- ## Coherence data
  have hκkey : κ ∈ orbitKey C κ := Or.inl (s02c_LamEquiv_refl C κ)
  have hνkey : (lamCF C β * κ) ∈ orbitKey C κ := Or.inl hLam
  have hGκν := (hf.1 κ hκirr) κ hκkey (lamCF C β * κ) hνkey hκirr hνirr
  have hZN : f (lamCF C β * κ) ∈ ZIrr G := hGκν.1
  have hnormν : ClassFunction.inner (f (lamCF C β * κ)) (f (lamCF C β * κ)) = 1 := by
    have h := hGκν.2.2.1
    rwa [if_neg hsconj] at h
  have hpmν : IsPmIrr (f (lamCF C β * κ)) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one hZN hnormν
  have hind : ind C (κ - lamCF C β * κ) = f κ - f (lamCF C β * κ) :=
    hGκν.2.2.2.1 hLam
  -- ## The value of `f (λ_β κ)` at `t`
  have hvalν : f (lamCF C β * κ) (C.t : G) = -2 := by
    by_cases hn4 : D.n = 4
    · -- exceptional configuration: BG Lemma 3.4
      have hνmem : (lamCF C β * κ) ∈ bset C f (f (lamCF C β * κ)) :=
        ⟨hνirr, by rw [hnormν]; norm_num⟩
      have hdisj : sconj C (lamCF C β * κ) ∉ lamOrbit C (lamCF C β * κ) ∨
          (lamOrbit C (lamCF C β * κ)).ncard = D.n := Or.inr horb
      have hL := (lemma34Leaf D C hcompat hS3 f hf (f (lamCF C β * κ)) hpmν
        (lamCF C β * κ) hνmem hsconj hdisj).2
      rw [hL, hνt]
      norm_num
    · -- generic case: coherence clause (vi)
      have hnotex : ¬ ((lamOrbit C (lamCF C β * κ)).ncard = 4 ∧
          sconj C '' lamOrbit C (lamCF C β * κ) = lamOrbit C (lamCF C β * κ)) := by
        rintro ⟨h1, -⟩
        rw [horb] at h1
        exact hn4 h1
      have hL := hGκν.2.2.2.2.2 hsconj hnotex
      rw [hL, hνt]
      norm_num
  -- ## The decomposition `f κ = χ₁ + χ₂`
  have hGκκ := (hf.1 κ hκirr) κ hκkey κ hκkey hκirr hκirr
  have hnormκ : ClassFunction.inner (f κ) (f κ) = 2 := by
    have h := hGκκ.2.2.1
    rwa [if_pos hκsconj] at h
  obtain ⟨χ₁, χ₂, hpm1, hpm2, horth, hsum⟩ := c3NormTwoPair hGκκ.1 hnormκ
  -- ## Clause (v) at `t` for the pair `(λ_β κ, κ)`
  have hfκt : f κ (C.t : G) = 2 := by
    have h := hf.2.2 (lamCF C β * κ) κ hνirr hκirr (s02c_LamEquiv_symm C hLam)
      C.t C.t_not_mem_U
    rw [conjMulEquiv_s_t C] at h
    simp only [ClassFunction.sub_apply] at h
    have h1 : f (lamCF C β * κ) (C.t : G) - f κ (C.t : G) =
        2 * ((lamCF C β * κ) C.t - κ C.t) := by
      rw [h]
      ring
    rw [hνt, hκt] at h1
    linear_combination -h1 + hvalν
  -- ## Lemma 2.2 and the constituent sum
  have h22 := lemma22Kappa D C hcompat κ β hκirr hκ1 hκsconj hκS0 (Or.inl hsconj)
  have hX1 := constituentSum3 (K := G) χ₁ χ₂ (-(f (lamCF C β * κ))) hpm1 hpm2
    (isPmIrr_neg hpmν) (C.t : G)
  have hnum : (-(f (lamCF C β * κ) (C.t : G))) ^ 2 = 4 := by
    rw [hvalν]
    norm_num
  have h3 : (-(f (lamCF C β * κ))) (C.t : G) ^ 2 / (-(f (lamCF C β * κ))) 1
      = -(4 / f (lamCF C β * κ) 1) := by
    rw [ClassFunction.neg_apply, ClassFunction.neg_apply, hnum, div_neg]
  have hsumε : χ₁ + χ₂ + -(f (lamCF C β * κ)) = ind C (κ - lamCF C β * κ) := by
    rw [hind, hsum]
    abel
  rw [h3] at hX1
  rw [hsumε] at hX1
  have hbr : χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 - 4 / f (lamCF C β * κ) 1
      = χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 +
        (-(4 / f (lamCF C β * κ) 1)) := by
    rw [sub_eq_add_neg]
  have hmain : (D.H.index : ℂ) * (χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 -
      4 / f (lamCF C β * κ) 1) = 2 * (D.k : ℂ) ^ 2 := by
    rw [hbr, ← hX1]
    exact h22
  -- ## Conclusion
  refine ⟨χ₁, χ₂, hpm1, hpm2, horth, hsum, hpmν, ?_, ?_, ?_⟩
  · rw [hvalν]
    norm_num
  · have : (χ₁ + χ₂) (C.t : G) = 2 := by rw [← hsum]; exact hfκt
    simpa using this
  · exact hmain

end Work.BG
