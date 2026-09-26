/-
# The funnel tail expansion of the CKMRV kernel: `funnelKernelTail`

This file proves `Work.Asymptotics.funnelKernelTail`, the estimate

  `‖Kaxis (Kfun ℓ d) τ t - Aexp G τ t‖ ≤ C (scale τ)^N (1+t)^M e^{-π(t - Im τ)}`

on the *funnel* `{τ ∈ 𝒟 : 2 ≤ Im τ}`, `t ≥ Im τ + 1`, with the model `G = Compact.Gcoef d ℓ`
(whose coefficient functions agree with `Work.Asymptotics.Gcusp ℓ d` for `d ∈ {8, 24}`).

## Ingredients

* the four half-estimates `KPlus_funnel_tail_eight`, `KMinus_funnel_tail_eight`,
  `KPlus_funnel_tail_twentyfour`, `KMinus_funnel_tail_twentyfour`, bounding
  `K_±^{(d)}(τ,z) - 𝒢_±^{(d)}(τ,z)` by `O((scale τ)^N (1+t)^M e^{-π(t - Im τ)})` for
  `z = i t`, `t ≥ Im τ + 1` (here `𝒢_±^{(d)} = Compact.Gplus/Gminus`);
* `Compact.gfun_eq`, identifying `(𝒢_+ + 𝒢_-)/2` with `Compact.Gfun`;
* `Compact.Aexp_Gcoef`, identifying `Aexp (Gcoef d ℓ) τ t` with
  `Compact.Gfun d ℓ τ (i t)`;
* `Gcoef_moderate_univ` below, giving the moderate growth of the coefficient functions on
  all of `ℍ` (the existing `Compact.gcoef_moderate` proves the same statement internally
  but exposes only its restriction to `𝒟`).

The rest is the triangle inequality together with `1 ≤ scale τ`, `1 ≤ 1 + t`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Kernels.KernelGrowth.PhiVec_InP
import Submission.Work.Asymptotics.KMinus_funnel_tail_eight
import Submission.Work.Asymptotics.KMinus_funnel_tail_twentyfour
import Submission.Work.Asymptotics.KPlus_funnel_tail_eight
import Submission.Work.Asymptotics.KPlus_funnel_tail_twentyfour

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

/-! ## Moderate growth of the cusp coefficients `Gcoef` on all of `ℍ`

The `InP` assembly below mirrors the one inside
`Submission/Work/Asymptotics/Compact/gcoef_moderate.lean` (whose helper lemmas are
`private`): every atom occurring in `Compact.Gcoef` lies in `𝒫 = Work.Kernels.InP`, the class
of holomorphic functions of moderate growth on all of `ℍ`. -/

private lemma InP_mul_const {F : ℍ → ℂ} (c : ℂ) (h : Work.Kernels.InP F) :
    Work.Kernels.InP (fun τ => F τ * c) := by
  have h' := h.const_mul c
  have heq : (fun τ : ℍ => c * F τ) = (fun τ : ℍ => F τ * c) := by
    funext τ; ring
  rwa [heq] at h'

private lemma InP_div_const {F : ℍ → ℂ} (c : ℂ) (h : Work.Kernels.InP F) :
    Work.Kernels.InP (fun τ => F τ / c) := by
  have h' : Work.Kernels.InP (fun τ => F τ * c⁻¹) := InP_mul_const c⁻¹ h
  simpa [div_eq_mul_inv] using h'

private lemma InP_phi1 : Work.Kernels.InP Compact.phi1 := by
  change Work.Kernels.InP (fun τ : ℍ =>
    (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))
  exact Work.Kernels.KernelGrowth.phi0_InP

private lemma InP_phi2t : Work.Kernels.InP Compact.phi2t := by
  change Work.Kernels.InP (fun τ : ℍ =>
    (τ : ℂ) * Work.Kernels.E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ)
  exact Work.Kernels.KernelGrowth.phi2_InP

/-- `Compact.Gcoef d ℓ i j ∈ 𝒫` for `d ≠ 8` (the `d = 24` branch of `Gcoef`): every branch is
a sum of products of the atoms `τ, E₄, E₆, Δ, φ_1, φ_2, ψ₂, ψ₄` and the constant `cuspC ℓ`. -/
private lemma InP_Gcoef_of_ne_eight (ℓ : Work.Kernels.LogLambdaData) {d : ℕ} (hd : ¬ d = 8)
    (i j : Fin 2) : Work.Kernels.InP (fun τ : ℍ => Compact.Gcoef d ℓ i j τ) := by
  have hE4 : Work.Kernels.InP Work.Kernels.E4Fun :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP
  have hE6 : Work.Kernels.InP Work.Kernels.E6Fun :=
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP
  have hD : Work.Kernels.InP Work.Kernels.DeltaFun :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
  have hτ : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ)) := Work.Kernels.KernelGrowth.InP_coe
  have hpsi := Work.Asymptotics.psi_InP ℓ
  have hE14 : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) :=
    (hE4.pow 2).mul hE6
  have hE10 : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) :=
    hE4.mul hE6
  have hE4c : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3) := hE4.pow 3
  have hE4sq : Work.Kernels.InP (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2) := hE4.pow 2
  have key := Work.Kernels.ClassicalFacts.E4Fun_mem_InP
  by_cases h00 : i = 0 ∧ j = 0
  · -- branch `(0,0)`
    simp only [Compact.Gcoef, if_neg hd, if_pos h00]
    have h0 : Work.Kernels.InP (fun τ : ℍ =>
        -(13 * Complex.I / 12) * ((τ : ℂ) * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) :=
      Work.Kernels.InP.const_mul (-(13 * Complex.I / 12)) (hτ.mul hE14)
    have h1 : Work.Kernels.InP (fun τ : ℍ =>
        Complex.I / 6 * (Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3)) :=
      Work.Kernels.InP.const_mul (Complex.I / 6) (InP_phi1.mul hE4c)
    have h2 : Work.Kernels.InP (fun τ : ℍ =>
        168 * Complex.I * (Compact.phi1 τ * Work.Kernels.DeltaFun τ)) :=
      Work.Kernels.InP.const_mul (168 * Complex.I) (InP_phi1.mul hD)
    have h3 : Work.Kernels.InP (fun τ : ℍ =>
        Complex.I / 12 * (Compact.phi2t τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) :=
      Work.Kernels.InP.const_mul (Complex.I / 12) (InP_phi2t.mul hE10)
    have h4 : Work.Kernels.InP (fun τ : ℍ =>
        720 * Work.Kernels.DeltaFun τ * Compact.cuspC ℓ / (Real.pi : ℂ)) :=
      InP_div_const (Real.pi : ℂ)
        (InP_mul_const (Compact.cuspC ℓ) (Work.Kernels.InP.const_mul 720 hD))
    have h5 : Work.Kernels.InP (fun τ : ℍ =>
        36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)) :=
      InP_div_const (Real.pi : ℂ) (Work.Kernels.InP.const_mul 36 hD)
    have h6 : Work.Kernels.InP (fun τ : ℍ =>
        Work.Kernels.E4Fun τ ^ 3 * Compact.cuspC ℓ / (Real.pi : ℂ)) :=
      InP_div_const (Real.pi : ℂ) (InP_mul_const (Compact.cuspC ℓ) hE4c)
    have h7 : Work.Kernels.InP (fun τ : ℍ =>
        7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) /
          (24 * (Real.pi : ℂ))) :=
      InP_div_const (24 * (Real.pi : ℂ))
        (Work.Kernels.InP.const_mul 7 (hpsi.1.mul hE10))
    have h8 : Work.Kernels.InP (fun τ : ℍ =>
        5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))) :=
      InP_div_const (24 * (Real.pi : ℂ))
        (Work.Kernels.InP.const_mul 5 (hpsi.2.mul hE4sq))
    refine InP_div_const 2 ?_
    refine Work.Kernels.InP.sub ?_ h8
    refine Work.Kernels.InP.sub ?_ h7
    refine Work.Kernels.InP.add ?_ h6
    refine Work.Kernels.InP.sub ?_ h5
    refine Work.Kernels.InP.sub ?_ h4
    refine Work.Kernels.InP.sub ?_ h3
    refine Work.Kernels.InP.sub ?_ h2
    exact Work.Kernels.InP.add h0 h1
  · by_cases h01 : i = 0 ∧ j = 1
    · -- branch `(0,1)`
      simp only [Compact.Gcoef, if_neg hd, if_neg h00, if_pos h01]
      have hA : Work.Kernels.InP (fun τ : ℍ =>
          (τ : ℂ) * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)) := hτ.mul hE14
      have hB : Work.Kernels.InP (fun τ : ℍ =>
          720 * (Compact.phi1 τ * Work.Kernels.DeltaFun τ)) :=
        Work.Kernels.InP.const_mul 720 (InP_phi1.mul hD)
      have hC : Work.Kernels.InP (fun τ : ℍ =>
          Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3) := InP_phi1.mul hE4c
      have hX : Work.Kernels.InP (fun τ : ℍ =>
          (Real.pi : ℂ) / 3 *
            ((τ : ℂ) * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) +
              720 * (Compact.phi1 τ * Work.Kernels.DeltaFun τ) -
              Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3)) :=
        Work.Kernels.InP.const_mul ((Real.pi : ℂ) / 3) ((hA.add hB).sub hC)
      have hY : Work.Kernels.InP (fun τ : ℍ =>
          Complex.I * (720 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)) :=
        Work.Kernels.InP.const_mul Complex.I
          ((Work.Kernels.InP.const_mul 720 hD).sub hE4c)
      exact InP_div_const 2 (hX.sub hY)
    · by_cases h10 : i = 1 ∧ j = 0
      · -- branch `(1,0)`
        simp only [Compact.Gcoef, if_neg hd, if_neg h00, if_neg h01, if_pos h10]
        have hA : Work.Kernels.InP (fun τ : ℍ =>
            -(Complex.I / 288) * ((τ : ℂ) * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) +
              Compact.phi2t τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) :=
          Work.Kernels.InP.const_mul (-(Complex.I / 288))
            ((hτ.mul hE14).add (InP_phi2t.mul hE10))
        have hB : Work.Kernels.InP (fun τ : ℍ =>
            Complex.I / 144 * (Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3)) :=
          Work.Kernels.InP.const_mul (Complex.I / 144) (InP_phi1.mul hE4c)
        have hC : Work.Kernels.InP (fun τ : ℍ =>
            7 * Complex.I * (Compact.phi1 τ * Work.Kernels.DeltaFun τ)) :=
          Work.Kernels.InP.const_mul (7 * Complex.I) (InP_phi1.mul hD)
        have hDd : Work.Kernels.InP (fun τ : ℍ =>
            Work.Kernels.DeltaFun τ * (Compact.cuspC ℓ - 1) / (Real.pi : ℂ)) :=
          InP_div_const (Real.pi : ℂ)
            (InP_mul_const (Compact.cuspC ℓ - 1) hD)
        have hE : Work.Kernels.InP (fun τ : ℍ =>
            (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) -
              Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) /
              (1152 * (Real.pi : ℂ))) :=
          InP_div_const (1152 * (Real.pi : ℂ))
            ((hpsi.1.mul hE10).sub (hpsi.2.mul hE4sq))
        refine InP_div_const 2 ?_
        refine Work.Kernels.InP.add ?_ hE
        refine Work.Kernels.InP.add ?_ hDd
        refine Work.Kernels.InP.sub ?_ hC
        exact hA.add hB
      · -- branch `(1,1)`
        simp only [Compact.Gcoef, if_neg hd, if_neg h00, if_neg h01, if_neg h10]
        have hA : Work.Kernels.InP (fun τ : ℍ =>
            (Real.pi : ℂ) / 864 *
              ((τ : ℂ) * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) +
                Compact.phi2t τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) +
                1728 * (Compact.phi1 τ * Work.Kernels.DeltaFun τ) -
                2 * (Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3))) :=
          Work.Kernels.InP.const_mul ((Real.pi : ℂ) / 864)
            ((((hτ.mul hE14).add (InP_phi2t.mul hE10)).add
              (Work.Kernels.InP.const_mul 1728 (InP_phi1.mul hD))).sub
              (Work.Kernels.InP.const_mul 2 (InP_phi1.mul hE4c)))
        have hB : Work.Kernels.InP (fun τ : ℍ =>
            Complex.I * Work.Kernels.DeltaFun τ) :=
          Work.Kernels.InP.const_mul Complex.I hD
        exact InP_div_const 2 (hA.add hB)

/-- `Compact.Gcoef 8 ℓ i j ∈ 𝒫`. -/
private lemma InP_Gcoef_eight (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Work.Kernels.InP (fun τ : ℍ => Compact.Gcoef 8 ℓ i j τ) := by
  have hE4 : Work.Kernels.InP Work.Kernels.E4Fun :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP
  have hE6 : Work.Kernels.InP Work.Kernels.E6Fun :=
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP
  have hτ : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ)) := Work.Kernels.KernelGrowth.InP_coe
  have hpsi := Work.Asymptotics.psi_InP ℓ
  by_cases hi : i = 1
  · simp only [Compact.Gcoef, if_pos trivial, if_pos hi]
    exact Work.Kernels.InP.zero
  · by_cases hj : j = 0
    · simp only [Compact.Gcoef, if_pos trivial, if_neg hi, if_pos hj]
      have hA : Work.Kernels.InP (fun τ : ℍ =>
          -Complex.I * (τ : ℂ) * Work.Kernels.E6Fun τ) :=
        (Work.Kernels.InP.const_mul (-Complex.I) hτ).mul hE6
      have hB : Work.Kernels.InP (fun τ : ℍ =>
          (Work.Kernels.E4Fun τ * Compact.cuspC ℓ - Work.Kernels.psi4 ℓ τ / 2) /
            (Real.pi : ℂ)) :=
        InP_div_const (Real.pi : ℂ)
          ((InP_mul_const (Compact.cuspC ℓ) hE4).sub (InP_div_const 2 hpsi.2))
      exact InP_div_const 2 (hA.add hB)
    · simp only [Compact.Gcoef, if_pos trivial, if_neg hi, if_neg hj]
      have hA : Work.Kernels.InP (fun τ : ℍ =>
          (Real.pi : ℂ) / 3 * ((τ : ℂ) * Work.Kernels.E6Fun τ -
            Compact.phi1 τ * Work.Kernels.E4Fun τ)) :=
        Work.Kernels.InP.const_mul ((Real.pi : ℂ) / 3)
          ((hτ.mul hE6).sub (InP_phi1.mul hE4))
      have hB : Work.Kernels.InP (fun τ : ℍ => Complex.I * Work.Kernels.E4Fun τ) :=
        Work.Kernels.InP.const_mul Complex.I hE4
      exact InP_div_const 2 (hA.add hB)

/-- **Moderate growth on all of `ℍ` of the cusp coefficient functions.**
For `d ∈ {8, 24}` each `Work.Asymptotics.Compact.Gcoef d ℓ i j` is a sum of products of the
atoms `τ, E₄, E₆, Δ, φ_0, φ_2, ψ₂, ψ₄` and the constant `cuspC ℓ`, all of which lie in the
class `𝒫 = Work.Kernels.InP` of holomorphic functions of moderate growth on `ℍ`; hence it is
of moderate growth on all of `ℍ`.  (This is the `Set.univ` companion of
`Work.Asymptotics.Compact.gcoef_moderate`, which exposes only the restriction to `𝒟`.) -/
theorem Gcoef_moderate_univ (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (i j : Fin 2) :
    Work.Kernels.ModerateGrowthOn Set.univ (Compact.Gcoef d ℓ i j) := by
  have key : Work.Kernels.InP (Compact.Gcoef d ℓ i j) := by
    rcases hd with hd8 | hd24
    · subst hd8
      exact InP_Gcoef_eight ℓ i j
    · subst hd24
      exact InP_Gcoef_of_ne_eight ℓ (by decide) i j
  exact key.2

/-! ## The elementary combination of two `O`-bounds -/

/-- If `x₁ ≤ C₁ S^{N₁} T^{M₁} e` and `x₂ ≤ C₂ S^{N₂} T^{M₂} e` with `S, T ≥ 1`, `e ≥ 0` and
`C₁, C₂ ≥ 0`, then `x₁ + x₂ ≤ (C₁ + C₂) S^{max N₁ N₂} T^{max M₁ M₂} e`. -/
private theorem add_le_add_bounds {S T e x1 x2 C1 C2 N1 N2 M1 M2 : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (he : 0 ≤ e) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : x1 ≤ C1 * S ^ N1 * T ^ M1 * e) (h2 : x2 ≤ C2 * S ^ N2 * T ^ M2 * e) :
    x1 + x2 ≤ (C1 + C2) * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hA : C1 * S ^ N1 * T ^ M1 * e ≤ C1 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have hs : S ^ N1 ≤ S ^ (max N1 N2) :=
      Real.rpow_le_rpow_of_exponent_le hS (le_max_left _ _)
    have ht : T ^ M1 ≤ T ^ (max M1 M2) :=
      Real.rpow_le_rpow_of_exponent_le hT (le_max_left _ _)
    calc C1 * S ^ N1 * T ^ M1 = (C1 * S ^ N1) * T ^ M1 := by ring
      _ ≤ (C1 * S ^ (max N1 N2)) * T ^ (max M1 M2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs hC1) ht
            (Real.rpow_nonneg hT0 _) (mul_nonneg hC1 (Real.rpow_nonneg hS0 _))
      _ = C1 * S ^ (max N1 N2) * T ^ (max M1 M2) := by ring
  have hB : C2 * S ^ N2 * T ^ M2 * e ≤ C2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have hs : S ^ N2 ≤ S ^ (max N1 N2) :=
      Real.rpow_le_rpow_of_exponent_le hS (le_max_right _ _)
    have ht : T ^ M2 ≤ T ^ (max M1 M2) :=
      Real.rpow_le_rpow_of_exponent_le hT (le_max_right _ _)
    calc C2 * S ^ N2 * T ^ M2 = (C2 * S ^ N2) * T ^ M2 := by ring
      _ ≤ (C2 * S ^ (max N1 N2)) * T ^ (max M1 M2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs hC2) ht
            (Real.rpow_nonneg hT0 _) (mul_nonneg hC2 (Real.rpow_nonneg hS0 _))
      _ = C2 * S ^ (max N1 N2) * T ^ (max M1 M2) := by ring
  calc x1 + x2 ≤ C1 * S ^ N1 * T ^ M1 * e + C2 * S ^ N2 * T ^ M2 * e := add_le_add h1 h2
    _ ≤ C1 * S ^ (max N1 N2) * T ^ (max M1 M2) * e
          + C2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := add_le_add hA hB
    _ = (C1 + C2) * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by ring

/-- The two terms of the split of `K^{(d)} - Aexp G` are bounded by `z`-independent
`O((scale τ)^N (1+t)^M e^{-π(t - Im τ)})` expressions; combine them. -/
private theorem funnel_combine {S T e C1 C2 N1 N2 M1 M2 x1 x2 : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (he : 0 ≤ e) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : x1 ≤ C1 * S ^ N1 * T ^ M1 * e) (h2 : x2 ≤ C2 * S ^ N2 * T ^ M2 * e) :
    (x1 + x2) / 2 ≤ (C1 + C2) / 2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
  have h := add_le_add_bounds hS hT he hC1 hC2 h1 h2
  have h2 := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
  have hEq : ((C1 + C2) * S ^ (max N1 N2) * T ^ (max M1 M2) * e) / 2
      = (C1 + C2) / 2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by ring
  rwa [hEq] at h2


/-! ## `Aexp (Gcoef d ℓ)` on the imaginary axis -/

/-- `Aexp (Gcoef d ℓ) τ t` is `Compact.Gfun d ℓ τ` evaluated at the point `i t` of the
imaginary axis.  (This is `Work.Asymptotics.Compact.Aexp_Gcoef`, reproved here so as not to
depend on `Compact.tail_on_compact`.) -/
private lemma Aexp_Gcoef (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (t : ℝ)
    (ht : 0 < t) :
    Aexp (Compact.Gcoef d ℓ) τ t = Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht) := by
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  have hE : (Work.Residues.Ept (Work.Kernels.imagAxis t ht)) ^ (-2 : ℤ) =
      Complex.exp (2 * Real.pi * t) := by
    rw [Work.Residues.Ept, hcoe]
    have h1 : Real.pi * Complex.I * ((t : ℂ) * Complex.I)
        = (Real.pi * (t : ℂ)) * (Complex.I * Complex.I) := by ring
    rw [h1, Complex.I_mul_I, zpow_neg, zpow_ofNat, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    ring
  rw [Aexp, Compact.Gfun, hcoe, hE]

/-! ## The final assembly -/

theorem funnelKernelTail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (C N M : ℝ),
      (∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Set.univ (G i j)) ∧
      (d = 8 → ∀ j : Fin 2, G 1 j = 0) ∧ 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → τ.im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - τ.im))) := by
  rcases hd with h8 | h24
  · subst h8
    obtain ⟨C1, N1, M1, hC1, hN1, hM1, hP⟩ := KPlus_funnel_tail_eight
    obtain ⟨C2, N2, M2, hC2, hN2, hM2, hM⟩ := KMinus_funnel_tail_eight ℓ
    refine ⟨Compact.Gcoef 8 ℓ, (C1 + C2) / 2, max N1 N2, max M1 M2,
      fun i j => Gcoef_moderate_univ ℓ 8 (Or.inl rfl) i j, ?_, ?_, le_max_of_le_left hN1,
      le_max_of_le_left hM1, ?_⟩
    · intro _ j
      funext τ
      fin_cases j <;> simp [Compact.Gcoef]
    · linarith
    · intro τ t hτD hτ2 ht
      have ht0 : 0 < t := by linarith
      set z : UpperHalfPlane := Work.Kernels.imagAxis t ht0 with hzdef
      have hz : (z : ℂ) = (t : ℂ) * Complex.I := by rw [hzdef]; rfl
      have hF : Funnel τ := ⟨hτD, hτ2⟩
      have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t
          = Work.Kernels.Kfun ℓ 8 τ z := by
        rw [Work.Kernels.Kaxis, dif_pos ht0, hzdef]
      have hA : Aexp (Compact.Gcoef 8 ℓ) τ t = Compact.Gfun 8 ℓ τ z := by
        rw [Aexp_Gcoef ℓ 8 τ t ht0, hzdef]
      have hG : Compact.Gfun 8 ℓ τ z
          = (Compact.Gplus 8 τ z + Compact.Gminus 8 ℓ τ z) / 2 := by
        rw [Compact.gfun_eq ℓ 8 (Or.inl rfl) τ z]
        ring
      have hsplit : Work.Kernels.Kfun ℓ 8 τ z - Compact.Gfun 8 ℓ τ z
          = ((Work.Kernels.KPlus 8 τ z - Compact.Gplus 8 τ z)
              + (Work.Kernels.KMinus ℓ 8 τ z - Compact.Gminus 8 ℓ τ z)) / 2 := by
        rw [Work.Kernels.Kfun_eq, hG]
        ring
      have h1 := hP τ z t hF ht hz
      have h2 := hM τ z t hF ht hz
      rw [hKaxis, hA, hsplit, norm_div, Complex.norm_ofNat]
      refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
      exact funnel_combine (Work.Kernels.one_le_scale τ) (by linarith) (Real.exp_nonneg _)
        hC1.le hC2.le h1 h2
  · subst h24
    obtain ⟨C1, N1, M1, hC1, hN1, hM1, hP⟩ := KPlus_funnel_tail_twentyfour
    obtain ⟨C2, N2, M2, hC2, hN2, hM2, hM⟩ := KMinus_funnel_tail_twentyfour ℓ
    refine ⟨Compact.Gcoef 24 ℓ, (C1 + C2) / 2, max N1 N2, max M1 M2,
      fun i j => Gcoef_moderate_univ ℓ 24 (Or.inr rfl) i j, ?_, ?_, le_max_of_le_left hN1,
      le_max_of_le_left hM1, ?_⟩
    · intro h
      exact absurd h (by decide)
    · linarith
    · intro τ t hτD hτ2 ht
      have ht0 : 0 < t := by linarith
      set z : UpperHalfPlane := Work.Kernels.imagAxis t ht0 with hzdef
      have hz : (z : ℂ) = (t : ℂ) * Complex.I := by rw [hzdef]; rfl
      have hF : Funnel τ := ⟨hτD, hτ2⟩
      have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t
          = Work.Kernels.Kfun ℓ 24 τ z := by
        rw [Work.Kernels.Kaxis, dif_pos ht0, hzdef]
      have hA : Aexp (Compact.Gcoef 24 ℓ) τ t = Compact.Gfun 24 ℓ τ z := by
        rw [Aexp_Gcoef ℓ 24 τ t ht0, hzdef]
      have hG : Compact.Gfun 24 ℓ τ z
          = (Compact.Gplus 24 τ z + Compact.Gminus 24 ℓ τ z) / 2 := by
        rw [Compact.gfun_eq ℓ 24 (Or.inr rfl) τ z]
        ring
      have hsplit : Work.Kernels.Kfun ℓ 24 τ z - Compact.Gfun 24 ℓ τ z
          = ((Work.Kernels.KPlus 24 τ z - Compact.Gplus 24 τ z)
              + (Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z)) / 2 := by
        rw [Work.Kernels.Kfun_eq, hG]
        ring
      have h1 := hP τ z t hF ht hz
      have h2 := hM τ z t hF ht hz
      rw [hKaxis, hA, hsplit, norm_div, Complex.norm_ofNat]
      refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
      exact funnel_combine (Work.Kernels.one_le_scale τ) (by linarith) (Real.exp_nonneg _)
        hC1.le hC2.le h1 h2

end

end Work.Asymptotics
