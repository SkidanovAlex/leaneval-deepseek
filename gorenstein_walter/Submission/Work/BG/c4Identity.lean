import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.lemma17_iii_lam2Conj
import Submission.Work.BG.lemma22Kappa
import Submission.Work.BG.constituentSum
import Submission.Work.BG.normFourPmIrr
import Submission.Work.BG.deltaNormFour
import Submission.Work.BG.kEqSmallAlt

namespace Work.BG

/-!
# Area BG: **C4-ID** (Bender–Glauberman 1981, §4, p. 214, identity (2))

For `|S| = 4` (`D.n = 2`), a nontrivial `β₂ : H₀/U →* ℂˣ` and an admissible linear
character `κ` of `H₀` (`Work.GW2.C16.IsKappa`), the degree-zero virtual character
`δ_κ = (κ - λ₂κ)^G` (`Work.GW2.C16.delta`) is a sum of four `±Irr` characters `χ₁,…,χ₄` with

`|G : H| · (χ₁(t)²/χ₁(1) + χ₂(t)²/χ₂(1) + χ₃(t)²/χ₃(1) + χ₄(t)²/χ₄(1)) = 2 k²`.

Route (BG p. 214): `δ_κ ∈ ℤ[Irr G]` and `δ_κ(1) = 0` (Lemma 1.3, `s02_indDiff`), and
`‖δ_κ‖² = 4` (the Brauer–Suzuki Gram matrix `s02_gram` + `lemma17_iii_lam2Conj` +
`rem31IndexUin`, packaged as `deltaNormFour`); by `normFourPmIrr` a norm-`4`, degree-`0`
virtual character is a sum of four `±Irr` functions.  Lemma 2.2 in the `κ`-form
(`lemma22Kappa`, with `λ₂ = λ_{β₂}` `s`-invariant — `D.n = 2` forces `H₀/U ≅ C₂` — and
`k₁ = k₂` by G5, `kEqSmallAlt`) computes

`|G : H| · Σ_{χ ∈ Irr G} χ(t)²/χ(1) · (δ_κ, χ) = 2 k²`,

and `constituentSum` (X1) rewrites the constituent sum
`Σ_χ χ(t)²/χ(1)·(δ_κ,χ)` as `Σ_i χ_i(t)²/χ_i(1)` because `δ_κ = χ₁+χ₂+χ₃+χ₄`.
-/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c4Identity {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype (IrreducibleCharacter G)] :
    Work.GW2.C16.C4IdentityProp D C := by
  intro hC hn β₂ hβ₂ κ hκ
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : DecidableEq (ClassFunction G ℂ) := Classical.decEq _
  -- (1) `|H₀ : U| = |S₀| = n = 2`.
  have h2q : Nat.card (Work.BG.quotGroup C.P) = 2 := by
    have h1 : (Work.GW2.C16.Uin C).index = D.n := Work.BG.rem31IndexUin D C hC
    have h2 : (Work.GW2.C16.Uin C).index = Nat.card (↥C.P.H0 ⧸ Work.GW2.C16.Uin C) :=
      Subgroup.index_eq_card (Work.GW2.C16.Uin C)
    change Nat.card (↥C.P.H0 ⧸ C.P.U.subgroupOf C.P.H0) = 2
    rw [← h2, h1, hn]
  -- (2) `λ₂ = λ_{β₂}` is `s`-invariant (`H₀/U ≅ C₂`).
  have hsconj : sconj C (lamCF C β₂) = lamCF C β₂ := by
    have h := Work.BG.lemma17_iii_lam2Conj C.P h2q hβ₂ C.s
    simpa [Work.BG.sconj, Work.BG.lamCF, Work.BG.lambdaInf] using h
  -- (3) `δ_κ = (κ - λ₂κ)^G` is a virtual character of degree `0` (Lemma 1.3).
  have hδ : delta C β₂ κ ∈ ZIrr G ∧ delta C β₂ κ 1 = 0 := by
    have hνirr : IsIrreducibleCharacter (lamCF C β₂ * κ) :=
      Work.BG.lambda_mul_irreducible C.P ⟨β₂, rfl⟩ hκ.1
    have hlam : Work.BG.LamEquiv C κ (lamCF C β₂ * κ) := ⟨β₂, rfl⟩
    exact Work.BG.s02_indDiff C κ (lamCF C β₂ * κ) hκ.1 hνirr hlam
  -- (4) `‖δ_κ‖² = 4` (Brauer–Suzuki Gram matrix).
  have hnorm : ClassFunction.inner (delta C β₂ κ) (delta C β₂ κ) = 4 :=
    Work.BG.deltaNormFour D C hC hn β₂ hβ₂ κ hκ
  -- (5) `δ_κ` is a sum of four `±Irr` characters.
  obtain ⟨χ₁, χ₂, χ₃, χ₄, hχ1, hχ2, hχ3, hχ4, hsum⟩ :=
    Work.BG.normFourPmIrr (delta C β₂ κ) hδ.1 hnorm hδ.2
  refine ⟨χ₁, χ₂, χ₃, χ₄, hχ1, hχ2, hχ3, hχ4, hsum, ?_⟩
  -- (6) Lemma 2.2 (`κ`-form): `|G : H| · Σ_χ χ(t)²/χ(1)·(δ_κ,χ) = 2k²`.
  have hrel : (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H
      = (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H :=
    Work.BG.kEqSmallAlt G D hn
  have hdisj : sconj C (lamCF C β₂ * κ) ≠ lamCF C β₂ * κ ∨
      (β₂ ≠ 1 ∧ sconj C (lamCF C β₂) = lamCF C β₂ ∧
        (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H =
          (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H) :=
    Or.inr ⟨hβ₂, hsconj, hrel⟩
  have hK := Work.BG.lemma22Kappa D C hC κ β₂ hκ.1 hκ.2.1 hκ.2.2.1 hκ.2.2.2.1 hdisj
  -- (7) The constituent sum `Σ_χ χ(t)²/χ(1)·(δ_κ,χ) = Σ_i χᵢ(t)²/χᵢ(1)` (X1).
  have hcx : (∑ χ : IrreducibleCharacter G, (χ : ClassFunction G ℂ) (C.t : G) ^ 2 /
        (χ : ClassFunction G ℂ) 1 *
          ClassFunction.inner (ind C (κ - lamCF C β₂ * κ)) (χ : ClassFunction G ℂ))
      = χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 +
        χ₃ (C.t : G) ^ 2 / χ₃ 1 + χ₄ (C.t : G) ^ 2 / χ₄ 1 := by
    have hε : ∀ i : Fin 4, IsPmIrr (![χ₁, χ₂, χ₃, χ₄] i) := by
      intro i; fin_cases i <;> assumption
    have hsum' : (∑ i : Fin 4, ![χ₁, χ₂, χ₃, χ₄] i) = ind C (κ - lamCF C β₂ * κ) := by
      rw [Fin.sum_univ_four]
      norm_num
      exact hsum.symm
    have hX := Work.BG.constituentSum (K := G) (ι := Fin 4) ![χ₁, χ₂, χ₃, χ₄] hε (C.t : G)
    rw [hsum'] at hX
    rw [Fin.sum_univ_four] at hX
    simpa using hX
  rw [hcx] at hK
  exact hK

end Work.BG
