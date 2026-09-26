/-
# The spike-circle bound for `K_-^{(8)}`

`K_-^{(8)} = (kpre ζ τ)⁻¹ · bracket8 ℓ ζ τ`, with `(kpre ζ τ)⁻¹` and `bracket8` both controlled
by the plain calculus `SB` of `SphereBoundAux`; the transfer to `KMinus ℓ 8` uses the
decomposition `Work.Asymptotics.Compact.KMinus8_eq` and the regrouping `bracket8_eq`.

(This file is the self-contained companion of `spike_KPlus8_bound.lean`; it reproduces the
corresponding lemmas of `Kfun_sphere_bound.lean`.)
-/
import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SphereBoundAux
import Submission.Work.Asymptotics.Compact.kminus_bracket

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels


private lemma SB_bracket8 (ℓ : LogLambdaData) : SB (fun τ ζ => Work.Residues.bracket8 ℓ ζ τ) := by
  have h := SB.add (SB.add
      (SB.const_mul (-3456 : ℂ) (SB.mul (SB.mul SB_E4_tau SBz_E10) (SB_L_zeta ℓ)))
      (SB.mul (SB.mul SBz_E8 SBz_W) (SB_Gamm_tau ℓ)))
      (SB.mul (SB.mul SBz_E6 (SB.sub (SB.mul SBz_U SBz_U) (SB.mul SBz_V SBz_V)))
        (SB_Lamb_tau ℓ))
  refine SB.congr h (fun τ ζ => ?_)
  rw [Work.Residues.bracket8]
  simp only [WFun, UFun, VFun, E8Fun, E10Fun, c1728]
  ring

private lemma SB_kpre_inv : SB (fun τ ζ => (Work.Residues.kpre ζ τ)⁻¹) := by
  have hc : (2 * (1728 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) ?_
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine SB.congr (SB.const_mul ((2 * (1728 : ℂ) * (Real.pi : ℂ))⁻¹) SB_inv_DeltaZetaJ)
    (fun τ ζ => ?_)
  rw [Work.Residues.kpre]
  have hk : ((2 : ℂ) * c1728 * (Real.pi : ℂ) * DeltaFun ζ
      * (jInvariantFun τ - jInvariantFun ζ))⁻¹
      = ((2 : ℂ) * 1728 * (Real.pi : ℂ))⁻¹
        * (DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ))⁻¹ := by
    rw [c1728]
    simp only [mul_inv]
    ring
  rw [hk]

theorem spike_KMinus8_bound (ℓ : Work.Kernels.LogLambdaData) : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
    ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
      3 ≤ τ.im → ‖Work.Kernels.KMinus ℓ 8 τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  have h := SB.mul SB_kpre_inv (SB_bracket8 ℓ)
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => ?_⟩
  refine le_trans (le_of_eq ?_) (hb τ ζ hτ hζ hH)
  rw [Work.Asymptotics.Compact.KMinus8_eq]
  show ‖(Work.Residues.kpre ζ τ)⁻¹ * Work.Residues.bracket8e ℓ ζ τ‖
      = ‖(Work.Residues.kpre ζ τ)⁻¹ * Work.Residues.bracket8 ℓ ζ τ‖
  rw [Work.Residues.bracket8_eq]

/-! ## Threshold-maximality helpers for the weighted calculus

`SBs H k f` bounds `f` above by `C (S τ)^N (tpar τ)^k` for `Im τ ≥ H`.  When combining atoms
whose individual thresholds `Hᵢ` are only known existentially, it is convenient to combine them
at the threshold `max Hᵢ`, using monotonicity in `H`. -/

end Work.Asymptotics.SpikeCircle
