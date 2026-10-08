import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma17_ii
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lambda_mul_mem

/-!
# Area BG: auxiliary vocabulary for Lemma 1.7 on `T` (`s02_lemma17T`)

Bender–Glauberman 1981, Lemma 1.7 evaluated on `T = H₀ ∖ U` (`Lemma17TProp`) states that
for every class function `χ` of `G`, every transversal-style choice `rep` of `Λ`-orbit
representatives of `Irr(H₀)` and every `g ∈ H₀ ∖ U`,

`χ(g) = Σ_{ν ∈ Irr(H₀)} (χ, (ν − rep ν)^G)_G · ν(g)`.

The proof has two ingredients:

* **Fourier inversion**, via `(χ, θ^G)_G = (χ|_{H₀}, θ)_{H₀}`: the first summand
  `(χ, ν^G)_G` reassembles `χ(g)`;
* **the orbit-constant part vanishes on `T`**: with `a_ν = (χ|_{H₀}, ν)`, the sum
  `Σ_ν a_{rep ν}·ν(g)` vanishes because `rep` is constant on `Λ`-orbits, so it is
  invariant under the twist `ν ↦ λ_β·ν` for every `β`, while some `β` has
  `λ_β(g) ≠ 1` (here `r(Λ) = Σ_β λ_β` is the regular character of `H₀/U`, which is `0`
  off `U` since `H₀/U` is cyclic, hence abelian).

This module holds only the *vocabulary* of the second ingredient: the twist
`lamTwist C β : Irr(H₀) → Irr(H₀)`, `ν ↦ λ_β·ν`, and the fact that it is a bijection
(with inverse the twist by `β⁻¹`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- The `Λ`-twist of an irreducible character of `H₀`: `ν ↦ λ_β · ν`, where
`λ_β = lamCF C β` is the inflation of `β : H₀/U →* ℂˣ`.  It is irreducible by
`Work.BG.lambda_mul_irreducible`. -/
noncomputable def lamTwist (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : IrreducibleCharacter ↥C.P.H0) : IrreducibleCharacter ↥C.P.H0 :=
  ⟨lamCF C β * (ν : ClassFunction ↥C.P.H0 ℂ),
    lambda_mul_irreducible C.P ⟨β, rfl⟩ ν.isIrreducible⟩

@[simp] theorem lamTwist_coe (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : IrreducibleCharacter ↥C.P.H0) :
    (lamTwist C β ν : ClassFunction ↥C.P.H0 ℂ) =
      lamCF C β * (ν : ClassFunction ↥C.P.H0 ℂ) :=
  rfl

/-- `λ_β · ν` is `Λ`-equivalent to `ν`. -/
theorem lamEquiv_lamTwist (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : IrreducibleCharacter ↥C.P.H0) :
    LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (lamTwist C β ν) :=
  ⟨β, rfl⟩

theorem lamTwist_inv_cancel (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : IrreducibleCharacter ↥C.P.H0) :
    lamTwist C β⁻¹ (lamTwist C β ν) = ν := by
  apply IrreducibleCharacter.ext
  show (lamTwist C β⁻¹ (lamTwist C β ν) : ClassFunction ↥C.P.H0 ℂ) =
    (ν : ClassFunction ↥C.P.H0 ℂ)
  rw [lamTwist_coe, lamTwist_coe]
  calc lamCF C β⁻¹ * (lamCF C β * (ν : ClassFunction ↥C.P.H0 ℂ))
      = (lamCF C β⁻¹ * lamCF C β) * (ν : ClassFunction ↥C.P.H0 ℂ) :=
        (mul_assoc_cf _ _ _).symm
    _ = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) * (ν : ClassFunction ↥C.P.H0 ℂ) := by
        rw [show lamCF C β⁻¹ * lamCF C β = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) from
          lambdaInf_inv_mul C.P β]
    _ = (ν : ClassFunction ↥C.P.H0 ℂ) := one_mul_cf _

/-- The twist `ν ↦ λ_β·ν` is a bijection of `Irr(H₀)`, with inverse the twist by `β⁻¹`. -/
theorem lamTwist_bijective (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    Function.Bijective (lamTwist C β) := by
  refine ⟨fun a b hab => ?_, fun b => ⟨lamTwist C β⁻¹ b, ?_⟩⟩
  · have h := congrArg (lamTwist C β⁻¹) hab
    rwa [lamTwist_inv_cancel, lamTwist_inv_cancel] at h
  · apply IrreducibleCharacter.ext
    show (lamTwist C β (lamTwist C β⁻¹ b) : ClassFunction ↥C.P.H0 ℂ) =
      (b : ClassFunction ↥C.P.H0 ℂ)
    rw [lamTwist_coe, lamTwist_coe]
    calc lamCF C β * (lamCF C β⁻¹ * (b : ClassFunction ↥C.P.H0 ℂ))
        = (lamCF C β * lamCF C β⁻¹) * (b : ClassFunction ↥C.P.H0 ℂ) :=
          (mul_assoc_cf _ _ _).symm
      _ = (lamCF C β⁻¹ * lamCF C β) * (b : ClassFunction ↥C.P.H0 ℂ) := by
          rw [mul_comm_cf (lamCF C β) (lamCF C β⁻¹)]
      _ = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) * (b : ClassFunction ↥C.P.H0 ℂ) := by
          rw [show lamCF C β⁻¹ * lamCF C β = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) from
            lambdaInf_inv_mul C.P β]
      _ = (b : ClassFunction ↥C.P.H0 ℂ) := one_mul_cf _

end Work.BG
