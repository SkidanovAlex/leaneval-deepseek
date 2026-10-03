import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs
import Submission.Work.KMTAreas.A4.schwartzSamplingSummable

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The character `fourier` on the frequency circle is multiplicative in the index against the
(integer) action on the circle: `e(n m · ξ) = e(n · (m ξ))`. -/
private lemma fourier_mul_smul {T : ℝ} (n m : ℤ) (x : AddCircle T) :
    fourier (n * m) x = fourier n (m • x) := by
  rw [fourier_apply, fourier_apply, ← mul_smul]

/-- Variant of `fourier_mul_smul` with the negation in the convenient place. -/
private lemma fourier_neg_mul_smul {T : ℝ} (n m : ℤ) (x : AddCircle T) :
    fourier (-(n * m)) x = fourier (-m) (n • x) := by
  rw [show (-(n * m) : ℤ) = (-m) * n by ring, fourier_mul_smul]

/-- The `fourier` character has unit modulus. -/
private lemma norm_fourier_eq_one {T : ℝ} (n : ℤ) (x : AddCircle T) :
    ‖fourier n x‖ = 1 := by
  simp [fourier_apply, Circle.norm_coe]

/-- The single-fibre computation: summing the smoothing weight of a *fixed* window point `m'`
against the character `e(-Q m · ξ)` produces the phase `e(-Q m' · ξ)` times the multiplier
`∑_u ψ(ε u) e(-u · (Q ξ))`. -/
private lemma lipWeight_fibre_tsum (ψ : SchwartzR) (ε : ℝ) (Q : ℤ) (ξ : FreqCircle) (m' : ℕ) :
    (∑' m : ℤ, (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ))
      = (fourier (-(Q * (m' : ℤ))) ξ : ℂ)
          * (∑' u : ℤ, (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) (Q • ξ) : ℂ)) := by
  have hre : (∑' m : ℤ, (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ))
      = ∑' c : ℤ, (ψ (ε * ((((c + (m' : ℤ) : ℤ)) : ℝ) - ((m' : ℕ) : ℝ))) : ℂ)
                  * (fourier (-(Q * (c + (m' : ℤ)))) ξ : ℂ) := by
    conv_lhs => rw [← Equiv.tsum_eq (Equiv.addRight (m' : ℤ))]
    simp only [Equiv.coe_addRight]
  rw [hre]
  calc (∑' c : ℤ, (ψ (ε * ((((c + (m' : ℤ) : ℤ)) : ℝ) - ((m' : ℕ) : ℝ))) : ℂ)
                  * (fourier (-(Q * (c + (m' : ℤ)))) ξ : ℂ))
      = ∑' c : ℤ, (ψ (ε * (c : ℝ)) : ℂ) * (fourier (-(Q * (c + (m' : ℤ)))) ξ : ℂ) := by
          refine tsum_congr (fun c => ?_)
          rw [show ε * ((((c + (m' : ℤ) : ℤ)) : ℝ) - ((m' : ℕ) : ℝ)) = ε * (c : ℝ) by
            push_cast; ring]
    _ = ∑' c : ℤ, (ψ (ε * (c : ℝ)) : ℂ)
            * ((fourier (-(Q * c)) ξ : ℂ) * (fourier (-(Q * (m' : ℤ))) ξ : ℂ)) := by
          refine tsum_congr (fun c => ?_)
          rw [show -(Q * (c + (m' : ℤ))) = -(Q * c) + -(Q * (m' : ℤ)) by ring, fourier_add]
    _ = (∑' c : ℤ, (ψ (ε * (c : ℝ)) : ℂ) * (fourier (-(Q * c)) ξ : ℂ))
            * (fourier (-(Q * (m' : ℤ))) ξ : ℂ) := by
          rw [show (∑' c : ℤ, (ψ (ε * (c : ℝ)) : ℂ)
                    * ((fourier (-(Q * c)) ξ : ℂ) * (fourier (-(Q * (m' : ℤ))) ξ : ℂ)))
              = ∑' c : ℤ, ((ψ (ε * (c : ℝ)) : ℂ) * (fourier (-(Q * c)) ξ : ℂ))
                    * (fourier (-(Q * (m' : ℤ))) ξ : ℂ) from
                  tsum_congr (fun c => (mul_assoc _ _ _).symm)]
          rw [tsum_mul_right]
    _ = (∑' c : ℤ, (ψ (ε * (c : ℝ)) : ℂ) * (fourier (-c) (Q • ξ) : ℂ))
            * (fourier (-(Q * (m' : ℤ))) ξ : ℂ) := by
          refine congrArg (· * _) ?_
          refine tsum_congr (fun c => ?_)
          rw [fourier_neg_mul_smul Q c ξ]
    _ = (fourier (-(Q * (m' : ℤ))) ξ : ℂ)
          * (∑' u : ℤ, (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) (Q • ξ) : ℂ)) := by
          rw [mul_comm]

theorem lipWeightMultiplierFactor (ψ : Work.Analysis.InverseTheory.SchwartzR) {ε : ℝ} (hε : 0 < ε)
    {N' : ℕ} (hN' : 1 ≤ N') (Q : ℤ) (ξ : Work.Analysis.InverseTheory.FreqCircle) :
    ∑' m : ℤ, Work.KMTAreas.A4.lipWeight ψ ε N' m * (fourier (-(Q * m)) ξ : ℂ)
      = (N' : ℝ)⁻¹ * (∑ m' ∈ Finset.Icc 1 N', (fourier (-(Q * (m' : ℤ))) ξ : ℂ))
          * ((ε : ℂ) * ∑' u : ℤ, (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) (Q • ξ) : ℂ)) := by
  have hpt : ∀ m : ℤ, lipWeight ψ ε N' m * (fourier (-(Q * m)) ξ : ℂ)
      = (ε : ℂ) * (N' : ℝ)⁻¹
          * (∑ m' ∈ Finset.Icc 1 N',
              (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ)) := by
    intro m
    rw [lipWeight, ← Finset.sum_mul]
    ring
  have hfiber : ∀ m' ∈ Finset.Icc 1 N', Summable (fun m : ℤ =>
      (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ)) := by
    intro m' _
    have h1 : Summable (fun m : ℤ => ‖ψ (-(ε * (m' : ℝ)) + ε * (m : ℝ))‖) :=
      schwartzSamplingSummable ψ (c := ε) (a := -(ε * (m' : ℝ))) hε.ne'
    have h2 : Summable (fun m : ℤ => ‖ψ (ε * ((m : ℝ) - (m' : ℝ)))‖) :=
      h1.congr (fun m => by
        rw [show -(ε * (m' : ℝ)) + ε * (m : ℝ) = ε * ((m : ℝ) - (m' : ℝ)) by ring])
    have h3 : Summable (fun m : ℤ =>
        ‖(ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ)‖) :=
      h2.congr (fun m => by rw [norm_mul, norm_fourier_eq_one, mul_one])
    exact h3.of_norm
  calc
    ∑' m : ℤ, lipWeight ψ ε N' m * (fourier (-(Q * m)) ξ : ℂ)
        = ∑' m : ℤ, (ε : ℂ) * (N' : ℝ)⁻¹
            * (∑ m' ∈ Finset.Icc 1 N',
                (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ)) := by
          exact tsum_congr hpt
      _ = (ε : ℂ) * (N' : ℝ)⁻¹
            * (∑' m : ℤ, ∑ m' ∈ Finset.Icc 1 N',
                (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ)) := by
          rw [tsum_mul_left]
      _ = (ε : ℂ) * (N' : ℝ)⁻¹
            * (∑ m' ∈ Finset.Icc 1 N', ∑' m : ℤ,
                (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ) * (fourier (-(Q * m)) ξ : ℂ)) := by
          rw [Summable.tsum_finsetSum hfiber]
      _ = (ε : ℂ) * (N' : ℝ)⁻¹
            * (∑ m' ∈ Finset.Icc 1 N', (fourier (-(Q * (m' : ℤ))) ξ : ℂ)
                * (∑' u : ℤ, (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) (Q • ξ) : ℂ))) := by
          congr 1
          exact Finset.sum_congr rfl (fun m' _ => lipWeight_fibre_tsum ψ ε Q ξ m')
      _ = (ε : ℂ) * (N' : ℝ)⁻¹
            * ((∑ m' ∈ Finset.Icc 1 N', (fourier (-(Q * (m' : ℤ))) ξ : ℂ))
                * (∑' u : ℤ, (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) (Q • ξ) : ℂ))) := by
          rw [Finset.sum_mul]
      _ = (N' : ℝ)⁻¹ * (∑ m' ∈ Finset.Icc 1 N', (fourier (-(Q * (m' : ℤ))) ξ : ℂ))
            * ((ε : ℂ) * ∑' u : ℤ, (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) (Q • ξ) : ℂ)) := by
          ring

end Work.KMTAreas.A4
