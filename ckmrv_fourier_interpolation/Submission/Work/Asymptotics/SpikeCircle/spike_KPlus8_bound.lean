import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SphereBoundAux

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels

/-!
# The spike-circle bound for `K_+^{(8)}`

On the spike circle `‖ζ - τ‖ = 29/20` around a point `τ` of the funnel, `K_+^{(8)}(τ,ζ)` is
bounded by a power of the scale `S τ = 1 + (Im τ)⁻¹ + |τ|`:

  `‖K_+^{(8)}(τ,ζ)‖ ≤ C (S τ)^N`   (`τ ∈ 𝔽`, `Im τ ≥ 3`).

The `τ`-atoms of the decomposition `Work.Asymptotics.KPlus_eight_decomposition` are already
controlled by the `SB` calculus of `SphereBoundAux` (`SB_E4_tau`, `SB_phi0_tau`, …).  Since the
spike circle lies in `{Im ζ ≥ 1}` (`one_le_zeta_im`), the `ζ`-atoms `ζ²`, `E₄(ζ)`, `E₆(ζ)`,
`Δ(ζ)`, `E₂|₂S(ζ)` are bounded by constants (`E4Fun_bound`, `DeltaFunBoundsHalf`,
`exists_norm_E2S_le'`, …), hence are `SB`-atoms too.  The two "dangerous" factors
`1/(Δ(τ)(jτ-jζ))` and `1/(Δ(ζ)(jτ-jζ))` are exactly the proven `SB_inv_DeltaTauJ` and
`SB_inv_DeltaZetaJ`; the point of splitting the decomposition as

  `(φ₂ E₁₄ Δζ φ̃₀ + Δτ·Q)/(Δτ Δζ (jτ-jζ)) = (φ₂ E₁₄ φ̃₀)/(Δτ(jτ-jζ)) + Q/(Δζ(jτ-jζ))`

is that each quotient pairs the `Δ` of the corresponding variable with `jτ-jζ`, so that the
exponential factors of `Δ` and of `jτ-jζ` cancel and only the constant factor on the sphere
remains.  The final transfer is `SB.of_pointwise` along the (algebraic) decomposition.
-/

/-! ## The `ζ`-atoms -/

private lemma SB_E4_zeta : SB (fun _ (ζ : ℍ) => E4Fun ζ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E4Fun_bound
  refine SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  exact h ζ (one_le_zeta_im hζ hH)

private lemma SB_E6_zeta : SB (fun _ (ζ : ℍ) => E6Fun ζ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_bound
  refine SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  exact h ζ (one_le_zeta_im hζ hH)

private lemma SB_Delta_zeta : SB (fun _ (ζ : ℍ) => DeltaFun ζ) := by
  obtain ⟨c, C, hc, hC, h⟩ := DeltaFunBoundsHalf
  refine SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 := (h ζ (by have := one_le_zeta_im hζ hH; linarith)).2
  have he : Real.exp (-(2 * Real.pi * ζ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, ζ.im_pos]
  have hep := Real.exp_pos (-(2 * Real.pi * ζ.im))
  nlinarith [h1, he, hC.le]

private lemma SB_E2S_zeta : SB (fun _ (ζ : ℍ) => E2S ζ) := by
  obtain ⟨C, hC, h⟩ := exists_norm_E2S_le'
  refine SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  exact h ζ (one_le_zeta_im hζ hH)

private lemma SB_E8_zeta : SB (fun _ (ζ : ℍ) => E8Fun ζ) := by
  refine SB.congr (SB.mul SB_E4_zeta SB_E4_zeta) (fun τ ζ => ?_)
  ring

private lemma SB_E10_zeta : SB (fun _ (ζ : ℍ) => E10Fun ζ) := by
  refine SB.congr (SB.mul SB_E4_zeta SB_E6_zeta) (fun τ ζ => ?_)
  ring

private lemma SB_phit0 : SB (fun _ (ζ : ℍ) => phitVec ζ 0) := by
  refine SB.congr SB_zeta_sq (fun τ ζ => ?_)
  rfl

private lemma SB_phit1 : SB (fun _ (ζ : ℍ) => phitVec ζ 1) := by
  refine SB.congr (SB.mul SB_zeta_sq SB_E2S_zeta) (fun τ ζ => ?_)
  rfl

private lemma SB_phit2 : SB (fun _ (ζ : ℍ) => phitVec ζ 2) := by
  refine SB.congr (SB.mul SB_zeta_sq (SB.mul SB_E2S_zeta SB_E2S_zeta)) (fun τ ζ => ?_)
  show (ζ : ℂ) ^ 2 * (E2S ζ * E2S ζ) = (ζ : ℂ) ^ 2 * (E2S ζ) ^ 2
  ring

/-! ## The split form of the decomposition -/

private lemma KPlus8_split_sb :
    SB (fun τ ζ => ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
      (phitVec ζ 0 * ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ)
        + (phi2 τ * E14Fun τ * phitVec ζ 0)
            * (DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ))⁻¹
        + ((τ : ℂ) * E6Fun τ * E8Fun ζ * phitVec ζ 2
            - 2 * phi0 τ * E4Fun τ * E10Fun ζ * phitVec ζ 1)
          * (DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ))⁻¹)) := by
  have hT1 : SB (fun τ ζ =>
      phitVec ζ 0 * ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ)) :=
    SB.mul SB_phit0
      (SB.sub (SB.mul SB_tau SB_E6_tau)
        (SB.mul (SB.mul (SB.const 2) SB_phi0_tau) SB_E4_tau))
  have hA1 : SB (fun τ ζ => (phi2 τ * E14Fun τ * phitVec ζ 0)
      * (DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ))⁻¹) :=
    SB.mul (SB.mul (SB.mul SB_phi2_tau SB_E14_tau) SB_phit0) SB_inv_DeltaTauJ
  have hP1 : SB (fun τ ζ => (τ : ℂ) * E6Fun τ * E8Fun ζ * phitVec ζ 2) :=
    SB.mul (SB.mul (SB.mul SB_tau SB_E6_tau) SB_E8_zeta) SB_phit2
  have hP2 : SB (fun τ ζ => 2 * phi0 τ * E4Fun τ * E10Fun ζ * phitVec ζ 1) :=
    SB.mul (SB.mul (SB.mul (SB.mul (SB.const 2) SB_phi0_tau) SB_E4_tau) SB_E10_zeta)
      SB_phit1
  have hQ : SB (fun τ ζ => (τ : ℂ) * E6Fun τ * E8Fun ζ * phitVec ζ 2
      - 2 * phi0 τ * E4Fun τ * E10Fun ζ * phitVec ζ 1) := SB.sub hP1 hP2
  have hA2 : SB (fun τ ζ => ((τ : ℂ) * E6Fun τ * E8Fun ζ * phitVec ζ 2
      - 2 * phi0 τ * E4Fun τ * E10Fun ζ * phitVec ζ 1)
        * (DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ))⁻¹) :=
    SB.mul hQ SB_inv_DeltaZetaJ
  exact SB.const_mul _ (SB.add (SB.add hT1 hA1) hA2)

/-! ## The theorem -/

theorem spike_KPlus8_bound : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
    ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → 3 ≤ τ.im →
    ‖Work.Kernels.KPlus 8 τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  refine SB.of_pointwise KPlus8_split_sb (fun τ ζ hτ hζ hH => ?_)
  rw [KPlus_eight_decomposition τ ζ (jne_of_spike hτ hζ)]
  have hDτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun ζ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero ζ
  have hJ : jInvariantFun τ - jInvariantFun ζ ≠ 0 := sub_ne_zero.mpr (jne_of_spike hτ hζ)
  congr 1
  field_simp
  ring

end Work.Asymptotics.SpikeCircle
