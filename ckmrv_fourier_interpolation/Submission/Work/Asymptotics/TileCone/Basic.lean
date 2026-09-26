/-
# The cleared identity of the CKMRV kernel on the cusp-`±1` tile cone

`Work.Asymptotics.two_KfunClear_S_eq_eight` / `..._twentyfour`:
at the tile point `τ = n + w` and `z` in the cone `{1 ≤ Im z}`, the cleared kernel
`2 KfunClear(τ, S z)` equals `z^{10}Δ(τ)(Ξ₈/c₈ + Ncusp)` (resp. `z^{14}Δ(τ)Δ(z)(Ξ₂₄/c₂₄ + Ncusp)`).
This is the identity through which the *divisor* `Δ(z)(jτ - jz)` cancels the exponential
factors of the numerators `Ξ_d` (`Xi8`, `Xi24`) and `Ncusp`, in the route to the tile
principal-part window (`Submission/Work/Asymptotics/tilePPWindow_lowHalf.lean`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane ModularGroup

/-- `c₈ = 36 π^{-2} i`, the normalisation constant of `Xi8_eq`. -/
def cEight : ℂ := (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I

/-- `c₂₄ = 36·1728 π^{-2} i`, the normalisation constant of `Xi24_eq`. -/
def cTwentyFour : ℂ := (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I

lemma cEight_ne_zero : cEight ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
  exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)

lemma cTwentyFour_ne_zero : cTwentyFour ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
  · simp [Work.Kernels.c1728]
  · exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)

/-- `Δ(S • z) = z¹² Δ(z)`. -/
lemma DeltaFun_S_smul_eq (z : ℍ) :
    Work.Kernels.DeltaFun (ModularGroup.S • z) = (z : ℂ) ^ 12 * Work.Kernels.DeltaFun z := by
  have hh := Work.Asymptotics.DeltaFun_S_smul' (ModularGroup.S • z)
  rw [Work.Asymptotics.S_smul_S_smul] at hh
  exact hh

/-- `j(S • z) = j(z)`. -/
lemma jInvariantFun_S_smul_eq (z : ℍ) :
    Work.Kernels.jInvariantFun (ModularGroup.S • z) = Work.Kernels.jInvariantFun z :=
  Work.Kernels.KernelFacts.jInvariantFun_S_smul z

/-- `E₄(S • z) = z⁴ E₄(z)`. -/
lemma E4Fun_S_smul_eq (z : ℍ) :
    Work.Kernels.E4Fun (ModularGroup.S • z) = (z : ℂ) ^ 4 * Work.Kernels.E4Fun z := by
  have hh := Work.Asymptotics.E4Fun_S_smul' (ModularGroup.S • z)
  rw [Work.Asymptotics.S_smul_S_smul] at hh
  exact hh

/-- `E₆(S • z) = z⁶ E₆(z)`. -/
lemma E6Fun_S_smul_eq (z : ℍ) :
    Work.Kernels.E6Fun (ModularGroup.S • z) = (z : ℂ) ^ 6 * Work.Kernels.E6Fun z := by
  have hh := Work.Asymptotics.E6Fun_S_smul' (ModularGroup.S • z)
  rw [Work.Asymptotics.S_smul_S_smul] at hh
  exact hh

/-- The elementary algebraic core of the cleared identity. -/
lemma cleared_alg (c : ℂ) (z Dτ Dz J X N KP KM : ℂ) (hc : c ≠ 0)
    (hX : c * (Dz * J) * (z ^ 2 * KP) = X) (hN : N = Dz * J * (z ^ 2 * KM)) :
    Dτ * (z ^ 12 * Dz) * J * KP + Dτ * (z ^ 12 * Dz) * J * KM
      = z ^ 10 * Dτ * (X / c + N) := by
  rw [← hX, hN]
  field_simp

/-- The same core in the exponent `14 / 10` shape of dimension `24`. -/
lemma cleared_alg24 (c : ℂ) (z Dτ Dz J X N KP KM : ℂ) (hc : c ≠ 0)
    (hX : c * (Dz * J) * (z ^ 10 * KP) = X) (hN : N = Dz * J * (z ^ 10 * KM)) :
    Dτ * (z ^ 12 * Dz) ^ 2 * J * KP + Dτ * (z ^ 12 * Dz) ^ 2 * J * KM
      = z ^ 14 * Dτ * Dz * (X / c + N) := by
  rw [← hX, hN]
  field_simp

/-- **The cleared identity in dimension `8`.** -/
theorem two_KfunClear_S_eq_eight (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    2 * Work.Kernels.KfunClear ℓ 8 τ (ModularGroup.S • z)
      = (z : ℂ) ^ 10 * Work.Kernels.DeltaFun τ *
          (Work.Asymptotics.Xi8 τ z / cEight + Work.Asymptotics.Ncusp ℓ 8 τ z) := by
  have hSj := jInvariantFun_S_smul_eq z
  have h' : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ModularGroup.S • z) := by
    rw [hSj]; exact h
  have hΔ := DeltaFun_S_smul_eq z
  have hp := Work.Kernels.ClearLink.KPlusClear_eq_smul 8 (Or.inl rfl) τ (ModularGroup.S • z) h'
  have hm := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ 8 (Or.inl rfl) τ (ModularGroup.S • z) h'
  have hgp : Work.Kernels.growthPrefactor 8 τ (ModularGroup.S • z)
      = Work.Kernels.DeltaFun τ * ((z : ℂ) ^ 12 * Work.Kernels.DeltaFun z)
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
    rw [Work.Kernels.growthPrefactor, if_pos rfl]
    simp only [pow_one, hΔ, hSj]
  have hxi := Xi8_eq τ z h
  have hnc := Ncusp_ident ℓ 8 (Or.inl rfl) τ z h
  have hze : (-(2 - ((8 : ℕ) : ℤ) / 2)) = (2 : ℤ) := by norm_num
  rw [hze] at hnc
  rw [Work.Kernels.KfunClear, hp, hm, hgp]
  have h2 : ∀ A B : ℂ, (2 : ℂ) * ((A + B) / 2) = A + B := by
    intro A B; ring
  rw [h2]
  exact cleared_alg cEight z (Work.Kernels.DeltaFun τ) (Work.Kernels.DeltaFun z)
    (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
    (Work.Asymptotics.Xi8 τ z) (Work.Asymptotics.Ncusp ℓ 8 τ z)
    (Work.Kernels.KPlus 8 τ (ModularGroup.S • z))
    (Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)) cEight_ne_zero hxi hnc

/-- **The cleared identity in dimension `24`.** -/
theorem two_KfunClear_S_eq_twentyfour (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    2 * Work.Kernels.KfunClear ℓ 24 τ (ModularGroup.S • z)
      = (z : ℂ) ^ 14 * Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Asymptotics.Xi24 τ z / cTwentyFour + Work.Asymptotics.Ncusp ℓ 24 τ z) := by
  have hSj := jInvariantFun_S_smul_eq z
  have h' : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ModularGroup.S • z) := by
    rw [hSj]; exact h
  have hΔ := DeltaFun_S_smul_eq z
  have hp := Work.Kernels.ClearLink.KPlusClear_eq_smul 24 (Or.inr rfl) τ (ModularGroup.S • z) h'
  have hm := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ 24 (Or.inr rfl) τ (ModularGroup.S • z) h'
  have hgp : Work.Kernels.growthPrefactor 24 τ (ModularGroup.S • z)
      = Work.Kernels.DeltaFun τ * ((z : ℂ) ^ 12 * Work.Kernels.DeltaFun z) ^ 2
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
    rw [Work.Kernels.growthPrefactor, if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
    simp only [hΔ, hSj]
  have hxi := Xi24_eq τ z h
  have hnc := Ncusp_ident ℓ 24 (Or.inr rfl) τ z h
  have hze : (-(2 - ((24 : ℕ) : ℤ) / 2)) = (10 : ℤ) := by norm_num
  rw [hze] at hnc
  rw [Work.Kernels.KfunClear, hp, hm, hgp]
  have h2 : ∀ A B : ℂ, (2 : ℂ) * ((A + B) / 2) = A + B := by
    intro A B; ring
  rw [h2]
  exact cleared_alg24 cTwentyFour z (Work.Kernels.DeltaFun τ) (Work.Kernels.DeltaFun z)
    (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
    (Work.Asymptotics.Xi24 τ z) (Work.Asymptotics.Ncusp ℓ 24 τ z)
    (Work.Kernels.KPlus 24 τ (ModularGroup.S • z))
    (Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)) cTwentyFour_ne_zero hxi hnc

end

end Work.Asymptotics
