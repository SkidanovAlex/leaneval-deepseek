import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Asymptotics.KhatE1Core.jq_second_order

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# Multiplication by the `j`-invariant in the `Big` calculus

`j(τ) = jInvariantFun τ` is `O(1/‖q(τ)‖)`, so multiplying a `Big k` statement by `j` costs
exactly one power of `‖q(τ)‖`: `Big (k+1) F → Big k (j·F)`.  This is the only place where the
non-`Big` behaviour of `j` is used; everything else in the funnel `τ`-atom algebra is
multiplicative in the `Big` sense.
-/

/-- The nome `q(τ) = e^{2πiτ}`. -/
def qAt (τ : ℍ) : ℂ := Work.Kernels.qParamFun τ

/-- The `j`-invariant. -/
def jAt (τ : ℍ) : ℂ := Work.Kernels.jInvariantFun τ

/-- `j·q` is bounded on the funnel. -/
theorem jq_uniform_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖jAt τ * qAt τ‖ ≤ K := by
  obtain ⟨Cj, hCj, hj⟩ := jq_second_order
  refine ⟨1 + 744 + Cj, by positivity, fun τ hτ => ?_⟩
  have hq1 : ‖qAt τ‖ ≤ 1 := by
    have h := Big.qnorm_le_one τ hτ
    simpa only [qAt] using h
  have hq0 : (0 : ℝ) ≤ ‖qAt τ‖ := norm_nonneg _
  have h := hj τ (by have := hτ.2; linarith)
  have hL : Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
      - 744 * Work.Kernels.qParamFun τ = jAt τ * qAt τ - (1 + 744 * qAt τ) := by
    simp only [qAt, jAt]; ring
  rw [hL] at h
  have h3 : ‖jAt τ * qAt τ - (1 + 744 * qAt τ)‖ ≤ Cj * ‖qAt τ‖ ^ 2 := by
    simpa [qAt] using h
  have h4 : ‖(1 : ℂ) + 744 * qAt τ‖ ≤ 1 + 744 * ‖qAt τ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one, norm_mul, Complex.norm_ofNat]
  have hsplit : jAt τ * qAt τ
      = (jAt τ * qAt τ - (1 + 744 * qAt τ)) + ((1 : ℂ) + 744 * qAt τ) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h5 : ‖qAt τ‖ ^ 2 ≤ ‖qAt τ‖ := by nlinarith [hq0, hq1]
  nlinarith [h3, h4, h5, hq0, hCj.le]

/-- The general form: `Big (k+1) F → Big k (j·F)`. -/
theorem jmul_big {k : ℕ} {F : ℍ → ℂ} (hF : Big (k + 1) F) :
    Big k (fun τ => jAt τ * F τ) := by
  obtain ⟨K, hK0, hKb⟩ := jq_uniform_bound
  obtain ⟨Cf, Nf, hCf, hNf, hFb⟩ := hF
  refine ⟨K * Cf, Nf, by positivity, hNf, fun τ hτ => ?_⟩
  have hqpos : 0 < ‖qAt τ‖ := by
    rw [norm_pos_iff]
    simp only [qAt, Work.Kernels.qParamFun]
    exact Complex.exp_ne_zero _
  have h1 : ‖jAt τ‖ * ‖qAt τ‖ ≤ K := by
    rw [← norm_mul]
    exact hKb τ hτ
  have h2 : ‖jAt τ‖ ≤ K / ‖qAt τ‖ := (le_div_iff₀ hqpos).mpr h1
  have h3 : ‖F τ‖ ≤ Cf * (Work.Kernels.scale τ) ^ Nf * ‖qAt τ‖ ^ (k + 1) := hFb τ hτ
  have hp : ‖qAt τ‖ ^ (k + 1) = ‖qAt τ‖ ^ k * ‖qAt τ‖ := pow_succ _ _
  calc ‖jAt τ * F τ‖ = ‖jAt τ‖ * ‖F τ‖ := norm_mul _ _
    _ ≤ (K / ‖qAt τ‖) * (Cf * (Work.Kernels.scale τ) ^ Nf * ‖qAt τ‖ ^ (k + 1)) :=
        mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    _ = K * Cf * (Work.Kernels.scale τ) ^ Nf * ‖qAt τ‖ ^ k := by
        rw [hp, div_mul_eq_mul_div]
        field_simp

/-- `Big 2 F → Big 1 (j·F)`. -/
theorem jmul2 {F : ℍ → ℂ} (hF : Big 2 F) : Big 1 (fun τ => jAt τ * F τ) :=
  jmul_big (k := 1) hF

/-- `Big 3 F → Big 2 (j·F)`. -/
theorem jmul3 {F : ℍ → ℂ} (hF : Big 3 F) : Big 2 (fun τ => jAt τ * F τ) :=
  jmul_big (k := 2) hF

end

end Work.Asymptotics.KhatE1Core
