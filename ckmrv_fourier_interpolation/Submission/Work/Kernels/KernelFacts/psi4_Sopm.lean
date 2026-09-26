/-
# `psi_4` is invariant under the `S`-slash at weight `4`

CKMRV Proposition 4.3 exhibits the basis `(ψ_0, ψ_2, ψ_4)` of `Ann_{2-d/2}(𝓘₊, 𝒫)` with

  `ψ_4 = ξ₄ 𝓛 + (ξ₄|₄S) 𝓛_S`.

Each `ψ_k` is annihilated by the operator `S - I` at weight `k` (the ideal `𝓘₊` contains
`S + I`, and combined with the other generator one gets `S - I` on this particular space);
here we prove the `k = 4` case, `Sopm 4 (psi4 ℓ) = 0`, i.e. `ψ_4 |[4] S = ψ_4`.

The point is purely the structure of the two terms: the two `S`-transforms of `ξ₄ 𝓛` and of
`(ξ₄|₄S) 𝓛_S` exchange the two summands, because `𝓛 |[0] S = 𝓛_S` and `𝓛_S |[0] S = 𝓛`
(the defining laws of `Work.Kernels.LogLambdaData`), while `ξ₄` itself is `S`-invariant at
weight `4` because `S² = -1` acts trivially at even weight.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

/-! ## Elementary facts about the `S`-slash -/

/-- `S * S = -1` in `SL(2,ℤ)`. -/
lemma S_mul_S_eq_neg_one : (ModularGroup.S * ModularGroup.S : SL(2,ℤ)) = -1 := by decide

/-- At even weight the slash action of `-1 ∈ SL(2,ℤ)` is the identity: `-1` acts on `ℍ`
trivially and its factor of automorphy is `-1`, whose `(-k)`-th power is `1` for even `k`. -/
lemma slash_neg_one_of_even {k : ℤ} (hk : Even k) (F : ℍ → ℂ) :
    F ∣[k] (-1 : SL(2,ℤ)) = F := by
  ext τ
  rw [ModularForm.SL_slash_apply]
  have hsmul : ((-1 : SL(2,ℤ)) • τ) = τ := by
    rw [show (-1 : SL(2,ℤ)) = -(1 : SL(2,ℤ)) by simp]
    rw [ModularGroup.SL_neg_smul, one_smul]
  have hden : UpperHalfPlane.denom
      (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) (-1 : SL(2,ℤ))))
      (τ : ℂ) = -1 := by
    rw [show SpecialLinearGroup.toGL
        ((SpecialLinearGroup.map (Int.castRingHom ℝ)) (-1 : SL(2,ℤ))) = (-1 : GL (Fin 2) ℝ) by
      ext i j; fin_cases i <;> fin_cases j <;> simp]
    rw [UpperHalfPlane.denom_neg, UpperHalfPlane.denom_one]
  rw [hsmul, hden]
  have hpow : ((-1 : ℂ)) ^ (-k) = 1 := by
    have h : Even (-k) := hk.neg
    simpa using h.neg_one_zpow (α := ℂ)
  rw [hpow, mul_one]

/-- At even weight, `S`-slash is an involution: `(F |[k] S) |[k] S = F`. -/
lemma slash_S_slash_S_of_even {k : ℤ} (hk : Even k) (F : ℍ → ℂ) :
    (F ∣[k] ModularGroup.S) ∣[k] ModularGroup.S = F := by
  rw [← SlashAction.slash_mul, S_mul_S_eq_neg_one]
  exact slash_neg_one_of_even hk F

/-- The product rule `(F·G) |[k] S = (F |[k] S)·(G |[0] S)` for a second factor of weight `0`. -/
lemma mul_slash_S_weight_zero (F G : ℍ → ℂ) (k : ℤ) :
    (F * G) ∣[k] ModularGroup.S = F ∣[k] ModularGroup.S * G ∣[(0 : ℤ)] ModularGroup.S := by
  have := ModularForm.mul_slash_SL2 k 0 ModularGroup.S F G
  simpa using this

/-! ## The main result -/

theorem psi4_Sopm (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.Sopm 4 (Work.Kernels.psi4 ℓ) = 0 := by
  have hSS : (((xi4Fun : ℍ → ℂ) ∣[(4 : ℤ)] ModularGroup.S) ∣[(4 : ℤ)] ModularGroup.S) =
      xi4Fun :=
    slash_S_slash_S_of_even (by norm_num) xi4Fun
  have hL : (ℓ.L ∣[(0 : ℤ)] ModularGroup.S) = ℓ.L_S := ℓ.slash_S
  have hLS : (ℓ.L_S ∣[(0 : ℤ)] ModularGroup.S) = ℓ.L := ℓ.slash_S_S
  ext τ
  simp only [Sopm, Pi.zero_apply]
  rw [show psi4 ℓ = (xi4Fun * ℓ.L) + ((xi4Fun ∣[(4 : ℤ)] ModularGroup.S) * ℓ.L_S) from rfl]
  rw [SlashAction.add_slash]
  rw [mul_slash_S_weight_zero xi4Fun ℓ.L 4, hL]
  rw [mul_slash_S_weight_zero (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) ℓ.L_S 4, hLS]
  rw [hSS]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

end Work.Kernels.KernelFacts
