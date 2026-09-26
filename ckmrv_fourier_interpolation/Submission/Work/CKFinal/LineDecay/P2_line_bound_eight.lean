import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.denom_growth_segment
import Submission.Work.CKFinal.LineDecay.KMinus_slash_bound_half_clean
import Submission.Work.CKFinal.LineDecay.P2_kernel_segment_of
import Submission.Work.CKFinal.LineDecay.P2_norm_segment

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-!
# CKMRV (5.12) on the lines `Re τ = ±1/2`: the horizontal pieces `P₂`

The pieces `P₂` of the shifted representation (`Defs.P2`) are the two integrals over the
horizontal segments `[iH, 1+iH]` and `[-1+iH, iH]`, `H = 1`, of the kernel evaluated at the
points `x ± 1 + i` (`x ∈ [0,1]` resp. `[-1,0]`) against the exponential
`e^{iπr²(x+i)} = e^{-πr²}e^{iπr²x}` of modulus `≤ 1`.

Since each of the two intervals has length `1`, the bound follows from the pointwise bound
`‖K(τ, x ± 1 + i)‖ ≤ C (Im τ)^N e^{-π Im τ}` for the two kernels `K = K^{(8)}` and `K = K̂^{(8)}`
on the whole segment `{Im z = 1, |Re z| ≤ 1}`, which in turn is obtained from

* the CKMRV quotient bound `(quotientbounds1new)` for `K_+^{(8)}`
  (`Work.Asymptotics.KPlus_slash_bound_half`) and for `K_-^{(8)}`
  (`KMinus_slash_bound_half_clean`, the clash-free copy of
  `Work.Asymptotics.KMinus_slash_bound_half`), applied with the *second* variable slashed by `S`
  (`z := S • w`, so `Im z = 1/‖w‖² ∈ [1/2,1]` and `S • z = w`);
* the lower bound `c e^{2π Im τ} ≤ ‖Δ(S • w)(j τ - j(S • w))‖` (`denom_growth_segment`), which
  converts the denominator `‖Δ z (j τ - j z)‖` of the quotient bound into the decay
  `e^{-2π Im τ}`.

The two pieces are `KMinus_slash_bound_half_clean` + `denom_growth_segment` ⟹
`P2_kernel_segment_of` (the pointwise segment bound for both kernels) ⟹
`P2_norm_segment` + the algebra `K = (K_+ ± K_-)/2` (this file).
-/

/-- `Kax` is additive in the kernel. -/
private lemma Kax_add {K₁ K₂ : ℍ → ℍ → ℂ} (τ : ℍ) (x t : ℝ) :
    Kax (fun a b => K₁ a b + K₂ a b) τ x t = Kax K₁ τ x t + Kax K₂ τ x t := by
  unfold Kax
  by_cases h : 0 < t <;> simp [h]

/-- `Kax` is additive in the kernel. -/
private lemma Kax_sub {K₁ K₂ : ℍ → ℍ → ℂ} (τ : ℍ) (x t : ℝ) :
    Kax (fun a b => K₁ a b - K₂ a b) τ x t = Kax K₁ τ x t - Kax K₂ τ x t := by
  unfold Kax
  by_cases h : 0 < t <;> simp [h]

/-- `Kax (K / 2) = (Kax K) / 2`. -/
private lemma Kax_div_two (K : ℍ → ℍ → ℂ) (τ : ℍ) (x t : ℝ) :
    Kax (fun a b => K a b / 2) τ x t = Kax K τ x t / 2 := by
  unfold Kax
  by_cases h : 0 < t <;> simp [h]

theorem P2_line_bound_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P2 (Work.Kernels.Kfun ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P2 (Work.Kernels.Khat ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))) := by
  obtain ⟨c, Yd, hc, hYd, hD⟩ := denom_growth_segment
  obtain ⟨Cm, Am, hCm, hAm, hminus⟩ := KMinus_slash_bound_half_clean ℓ
  obtain ⟨Ck, Nk, Yk, hCk, hNk, hYk, hkb⟩ :=
    P2_kernel_segment_of ℓ Cm Am hCm hAm hminus c Yd hc hD
  refine ⟨2 * Ck, Nk, max Yk 1, by positivity, hNk, le_max_right Yk 1, ?_⟩
  intro τ r hline hY
  have hyk : Yk ≤ τ.im := le_trans (le_max_left Yk 1) hY
  have hb : ∀ x : ℝ, |x| ≤ 1 → max ‖Kax (Work.Kernels.KPlus 8) τ x 1‖
      ‖Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖
        ≤ Ck * τ.im ^ Nk * Real.exp (-(Real.pi * τ.im)) := fun x hx => hkb τ x hline hyk hx
  set M : ℝ := Ck * τ.im ^ Nk * Real.exp (-(Real.pi * τ.im)) with hM
  have hfun : ∀ x : ℝ, |x| ≤ 1 → ‖Kax (Work.Kernels.Kfun ℓ 8) τ x 1‖ ≤ M := by
    intro x hx
    have hp : ‖Kax (Work.Kernels.KPlus 8) τ x 1‖ ≤ M :=
      le_trans (le_max_left _ _) (hb x hx)
    have hm : ‖Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖ ≤ M :=
      le_trans (le_max_right _ _) (hb x hx)
    rw [show Kax (Work.Kernels.Kfun ℓ 8) τ x 1
        = (Kax (Work.Kernels.KPlus 8) τ x 1
            + Kax (Work.Kernels.KMinus ℓ 8) τ x 1) / 2 from by
      rw [show Work.Kernels.Kfun ℓ 8
          = (fun a b => (Work.Kernels.KPlus 8 a b + Work.Kernels.KMinus ℓ 8 a b) / 2)
            from rfl]
      rw [Kax_div_two, Kax_add]]
    have h1 : ‖Kax (Work.Kernels.KPlus 8) τ x 1
        + Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖ ≤ M + M := by
      calc _ ≤ ‖Kax (Work.Kernels.KPlus 8) τ x 1‖
              + ‖Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖ := norm_add_le _ _
        _ ≤ M + M := add_le_add hp hm
    rw [norm_div]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hhat : ∀ x : ℝ, |x| ≤ 1 → ‖Kax (Work.Kernels.Khat ℓ 8) τ x 1‖ ≤ M := by
    intro x hx
    have hp : ‖Kax (Work.Kernels.KPlus 8) τ x 1‖ ≤ M :=
      le_trans (le_max_left _ _) (hb x hx)
    have hm : ‖Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖ ≤ M :=
      le_trans (le_max_right _ _) (hb x hx)
    rw [show Kax (Work.Kernels.Khat ℓ 8) τ x 1
        = (Kax (Work.Kernels.KPlus 8) τ x 1
            - Kax (Work.Kernels.KMinus ℓ 8) τ x 1) / 2 from by
      rw [show Work.Kernels.Khat ℓ 8
          = (fun a b => (Work.Kernels.KPlus 8 a b - Work.Kernels.KMinus ℓ 8 a b) / 2)
            from rfl]
      rw [Kax_div_two, Kax_sub]]
    have h1 : ‖Kax (Work.Kernels.KPlus 8) τ x 1
        - Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖ ≤ M + M := by
      calc _ ≤ ‖Kax (Work.Kernels.KPlus 8) τ x 1‖
              + ‖Kax (Work.Kernels.KMinus ℓ 8) τ x 1‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add hp hm
    rw [norm_div]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  refine ⟨?_, ?_⟩
  · refine le_trans (P2_norm_segment (Work.Kernels.Kfun ℓ 8) τ r M hfun) ?_
    rw [hM]
    exact le_of_eq (by ring)
  · refine le_trans (P2_norm_segment (Work.Kernels.Khat ℓ 8) τ r M hhat) ?_
    rw [hM]
    exact le_of_eq (by ring)

end Work.CKFinal.LineDecay
