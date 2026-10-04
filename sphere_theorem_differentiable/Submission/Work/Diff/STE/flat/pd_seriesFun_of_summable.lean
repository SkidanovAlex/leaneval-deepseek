import Mathlib
import Submission.Work.Diff.STE.pd_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pd_seriesFun_of_summable`

The term-by-term differentiation of the Fourier series `seriesFun γ` under the *single*
weighted-`ℓ¹` hypothesis `Summable (fun k => ⟨k⟩ * ‖γ k‖)` (the version of
`Work.Diff.STE.pd_seriesFun` that does not assume the full tower
`∀ N, Summable (fun k => ⟨k⟩ ^ N * ‖γ k‖)`).

The point is that the uniform bound on the derivative of the `k`-th summand,
`‖(γ k · e_k)'‖ ≤ (2π · card ι · ⟨k⟩) ‖γ k‖`, involves only the *first* power of the weight,
so the first-order summability hypothesis is enough on its own: it simultaneously gives the
absolute convergence of the series (because `1 ≤ ⟨k⟩`) and the summable majorant of the
derivatives.  The proof is the Weierstrass-type theorem `hasFDerivAt_tsum` of Mathlib, exactly as
in `pd_seriesFun`.
-/

noncomputable section

namespace Work.Diff.STE.flat

open BigOperators

theorem pd_seriesFun_of_summable {n : ℕ} (i : Fin n) (γ : (Fin n → ℤ) → ℂ)
    (hγ : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) * ‖γ k‖)) :
    ∀ x : Fin n → ℝ, Work.Diff.STE.pd i (Work.Diff.STE.seriesFun γ) x
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i γ) x := by
  intro x
  -- The weights dominate `1`, so the first-order hypothesis also gives absolute convergence.
  have h0 : Summable (fun k : Fin n → ℤ => ‖γ k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hγ
    have h1 : (1 : ℝ) ≤ Work.Diff.STE.wt k := Work.Diff.STE.wt_one_le k
    nlinarith [norm_nonneg (γ k)]
  -- The summable majorant of the derivatives of the summands.
  have hu : Summable
      (fun k : Fin n → ℤ => (2 * Real.pi * (Fintype.card (Fin n) : ℝ) * Work.Diff.STE.wt k)
        * ‖γ k‖) := by
    have h2 : Summable
        (fun k : Fin n → ℤ =>
          (2 * Real.pi * (Fintype.card (Fin n) : ℝ)) * ((Work.Diff.STE.wt k) * ‖γ k‖)) :=
      hγ.mul_left _
    refine h2.congr (fun k => ?_)
    ring
  have hf0 : Summable (fun k : Fin n → ℤ => γ k * Work.Diff.STE.fourierExp k x) := by
    refine Summable.of_norm_bounded h0 (fun k => ?_)
    rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
  have hderiv : fderiv ℝ (Work.Diff.STE.seriesFun γ) x
      = (∑' k : Fin n → ℤ,
          (γ k * Complex.exp (Work.Diff.STE.fourierLin k x)) • (Work.Diff.STE.fourierLin k)) :=
    (hasFDerivAt_tsum hu (fun k y => Work.Diff.STE.hasFDerivAt_smul_fourierExp (γ k) k y)
      (fun k y => Work.Diff.STE.norm_smul_fourierLin_le (γ k) k y) hf0 x).fderiv
  have hS : Summable
      (fun k : Fin n → ℤ =>
        (γ k * Complex.exp (Work.Diff.STE.fourierLin k x)) • (Work.Diff.STE.fourierLin k)) :=
    Summable.of_norm_bounded hu (fun k => Work.Diff.STE.norm_smul_fourierLin_le (γ k) k x)
  have key : (∑' k : Fin n → ℤ,
          (γ k * Complex.exp (Work.Diff.STE.fourierLin k x)) • (Work.Diff.STE.fourierLin k))
        (Pi.single i (1 : ℝ))
      = ∑' k : Fin n → ℤ,
          ((γ k * Complex.exp (Work.Diff.STE.fourierLin k x)) • (Work.Diff.STE.fourierLin k))
            (Pi.single i (1 : ℝ)) := by
    have hmap := ContinuousLinearMap.map_tsum
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1 : ℝ))) hS
    simpa only [ContinuousLinearMap.apply_apply] using hmap
  simp only [Work.Diff.STE.pd]
  rw [hderiv, key]
  refine (tsum_congr (fun k => ?_)).trans rfl
  rw [smul_apply, smul_eq_mul, Work.Diff.STE.fourierLin_single,
    Work.Diff.STE.fourierExp_eq_exp_lin]
  simp only [Work.Diff.STE.dmul]
  ring

end Work.Diff.STE.flat
