import Mathlib
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.theta_E6_identity

/-!
# The deviation bound `‖E₈W - E₆(U² - V²)‖ ≤ C‖E‖` on `Im τ ≥ 1`

Writing `U = θ₀₀⁴`, `W = θ₀₁⁴`, `V = θ₁₀⁴` and `E = E(τ) = e^{πiτ}` (so `‖E‖ = e^{-π Im τ}`),
the deviation

  `D = E₈ · W - E₆ · (U² - V²)`,   `E₈ = E₄²`,

is *algebraically* of the shape `(3/2) · U · V · W · (2U² - 2UW - W²)`:

* `E₄ = (U² + V² + W²)/2` (the dimension-eight magic `Θ_{E₈} = E₄` together with the
  decomposition of `Θ_{E₈}` into eighth powers of the Jacobi theta functions),
* `E₆ = -U³ + (3/2)U²W + (3/2)UW² - W³` (`theta_E6_identity`),
* `U = V + W` (Jacobi's quartic identity `θ₃⁴ = θ₄⁴ + θ₂⁴`, `theta_quartic`).

Since `U → 1`, `W → 1` and `V = O(‖E‖)` on `Im τ ≥ 1` (`UFun_decay`, `WFun_decay`,
`VFun_decay`), the deviation is `O(‖E‖)`, which is the content of `azBound`.
-/

namespace Work.Asymptotics.TileDevBall

open UpperHalfPlane
open scoped UpperHalfPlane

noncomputable section

/-- Four-fold product monotonicity: if `0 ≤ a ≤ a'`, … , `0 ≤ d ≤ d'` then
`a * b * c * d ≤ a' * b' * c' * d'`. -/
private lemma mul_four_le_mul {a b c d a' b' c' d' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (hc'0 : 0 ≤ c') (hd'0 : 0 ≤ d') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha'0
  have h2 : c * d ≤ c' * d' := mul_le_mul hc hd hd0 hc'0
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ ≤ (a' * b') * (c' * d') := mul_le_mul h1 h2 (mul_nonneg hc0 hd0) (mul_nonneg ha'0 hb'0)
    _ = a' * b' * c' * d' := by ring

/-- **`E₄` in terms of the Jacobi theta quartics**: `E₄ = (U² + V² + W²)/2`.

This is `Θ_{E₈} = E₄` (`thetaSeries_E8_eq_E4`) combined with the decomposition
`Θ_{E₈} = (θ₃⁸ + θ₄⁸ + θ₂⁸)/2` (`thetaSeries_E8_decomposition`), i.e.
`U = θ₃⁴`, `W = θ₄⁴`, `V = θ₂⁴`. -/
lemma E4Fun_eq_thetaQuartics (τ : ℍ) :
    Work.Kernels.E4Fun τ = (1 / 2) * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
      + Work.Kernels.WFun τ ^ 2) := by
  have hdec : Work.Modular.thetaSeries Work.Modular.E8 τ
      = (1 / 2) * (Work.Modular.theta3 τ ^ 8 + Work.Modular.theta4 τ ^ 8
        + Work.Modular.theta2 τ ^ 8) := Work.Modular.thetaSeries_E8_decomposition τ
  have heq : Work.Modular.thetaSeries Work.Modular.E8 τ = Work.Kernels.E4Fun τ :=
    congrFun Work.Modular.thetaSeries_E8_eq_E4 τ
  have hkey : (1 / 2) * (Work.Modular.theta3 τ ^ 8 + Work.Modular.theta4 τ ^ 8
        + Work.Modular.theta2 τ ^ 8)
      = (1 / 2) * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
        + Work.Kernels.WFun τ ^ 2) := by
    simp only [Work.Kernels.UFun, Work.Kernels.VFun, Work.Kernels.WFun,
      Work.Kernels.theta00Fun, Work.Kernels.theta01Fun, Work.Kernels.theta10Fun,
      Work.Modular.theta3, Work.Modular.theta4, Work.Modular.theta2]
    ring
  exact (heq.symm.trans hdec).trans hkey

/-- **The algebraic shape of the deviation.**  For all `τ`,

  `E₈ W - E₆ (U² - V²) = (3/2) U V W (2U² - 2UW - W²)`. -/
lemma dev_eq (τ : ℍ) :
    Work.Kernels.E8Fun τ * Work.Kernels.WFun τ
      - Work.Kernels.E6Fun τ * (Work.Kernels.UFun τ ^ 2 - Work.Kernels.VFun τ ^ 2)
      = (3 / 2) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ * Work.Kernels.WFun τ)
        * (2 * Work.Kernels.UFun τ ^ 2 - 2 * Work.Kernels.UFun τ * Work.Kernels.WFun τ
          - Work.Kernels.WFun τ ^ 2) := by
  have hE4 := E4Fun_eq_thetaQuartics τ
  have hE6 := Work.Residues.theta_E6_identity τ
  have hV : Work.Kernels.VFun τ = Work.Kernels.UFun τ - Work.Kernels.WFun τ := by
    have h := Work.Kernels.TildeFacts.theta_quartic τ
    rw [h]
    ring
  have hE8 : Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 := rfl
  rw [hE8, hE4, hE6, hV]
  ring

theorem azBound :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : UpperHalfPlane, 1 ≤ ζ.im →
      ‖Work.Kernels.E8Fun ζ * Work.Kernels.WFun ζ
        - Work.Kernels.E6Fun ζ * (Work.Kernels.UFun ζ ^ 2 - Work.Kernels.VFun ζ ^ 2)‖
        ≤ C * ‖Work.Residues.Ept ζ‖ := by
  obtain ⟨CU, hCU, hU⟩ := Work.Residues.UFun_decay
  obtain ⟨CW, hCW, hW⟩ := Work.Residues.WFun_decay
  obtain ⟨CV, hCV, hV⟩ := Work.Residues.VFun_decay
  set P : ℝ := 2 * (1 + CU) ^ 2 + 2 * (1 + CU) * (1 + CW) + (1 + CW) ^ 2 with hPdef
  have hPpos : 0 < P := by
    rw [hPdef]
    have h1 : (0 : ℝ) < 1 + CW := by linarith
    have h2 : 0 < (1 + CW) ^ 2 := pow_pos h1 2
    have h3 : 0 ≤ 2 * (1 + CU) ^ 2 := by positivity
    have h4 : 0 ≤ 2 * (1 + CU) * (1 + CW) := by positivity
    linarith
  refine ⟨(3 / 2) * (1 + CU) * (1 + CW) * CV * P, by positivity, ?_⟩
  intro ζ hζ
  set r : ℝ := ‖Work.Residues.Ept ζ‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one ζ)
  have hEr : Real.exp (-(Real.pi * ζ.im)) = r := by rw [hrdef, Work.Residues.norm_Ept]
  -- bounds for the three theta quartics
  have hUdecay : ‖Work.Kernels.UFun ζ - 1‖ ≤ CU * r := by
    have h := hU ζ hζ
    rw [hEr] at h
    exact h
  have hWdecay : ‖Work.Kernels.WFun ζ - 1‖ ≤ CW * r := by
    have h := hW ζ hζ
    rw [hEr] at h
    exact h
  have hVdecay : ‖Work.Kernels.VFun ζ‖ ≤ CV * r := by
    have h := hV ζ hζ
    rw [hEr] at h
    exact h
  have hUabs : ‖Work.Kernels.UFun ζ‖ ≤ 1 + CU * r := by
    have h2 : ‖Work.Kernels.UFun ζ‖ ≤ ‖Work.Kernels.UFun ζ - 1‖ + ‖(1 : ℂ)‖ := by
      have h := norm_add_le (Work.Kernels.UFun ζ - 1) (1 : ℂ)
      rwa [sub_add_cancel] at h
    rw [norm_one] at h2
    linarith
  have hWabs : ‖Work.Kernels.WFun ζ‖ ≤ 1 + CW * r := by
    have h2 : ‖Work.Kernels.WFun ζ‖ ≤ ‖Work.Kernels.WFun ζ - 1‖ + ‖(1 : ℂ)‖ := by
      have h := norm_add_le (Work.Kernels.WFun ζ - 1) (1 : ℂ)
      rwa [sub_add_cancel] at h
    rw [norm_one] at h2
    linarith
  have hUc : ‖Work.Kernels.UFun ζ‖ ≤ 1 + CU := by
    have h := mul_le_mul_of_nonneg_left hr1 hCU.le
    linarith
  have hWc : ‖Work.Kernels.WFun ζ‖ ≤ 1 + CW := by
    have h := mul_le_mul_of_nonneg_left hr1 hCW.le
    linarith
  -- the quadratic factor
  have hpoly : ‖(2 : ℂ) * Work.Kernels.UFun ζ ^ 2
      - 2 * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ - Work.Kernels.WFun ζ ^ 2‖ ≤ P := by
    have h2 : ‖(2 : ℂ) * Work.Kernels.UFun ζ ^ 2‖ ≤ 2 * (1 + CU) ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hUc 2) (by norm_num)
    have h3 : ‖Work.Kernels.WFun ζ ^ 2‖ ≤ (1 + CW) ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hWc 2
    have h4 : ‖(2 : ℂ) * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ‖
        ≤ 2 * ((1 + CU) * (1 + CW)) := by
      have hUW : ‖Work.Kernels.UFun ζ‖ * ‖Work.Kernels.WFun ζ‖ ≤ (1 + CU) * (1 + CW) :=
        mul_le_mul hUc hWc (norm_nonneg _) (by linarith)
      have hnorm4 : ‖(2 : ℂ) * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ‖
          = 2 * (‖Work.Kernels.UFun ζ‖ * ‖Work.Kernels.WFun ζ‖) := by
        simp only [norm_mul, Complex.norm_ofNat]
        ring
      rw [hnorm4]
      exact mul_le_mul_of_nonneg_left hUW (by norm_num)
    have t1 : ‖(2 : ℂ) * Work.Kernels.UFun ζ ^ 2
        - (2 : ℂ) * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ‖
        ≤ 2 * (1 + CU) ^ 2 + 2 * ((1 + CU) * (1 + CW)) := by
      have h := norm_sub_le ((2 : ℂ) * Work.Kernels.UFun ζ ^ 2)
        ((2 : ℂ) * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ)
      linarith
    have t2 := norm_sub_le ((2 : ℂ) * Work.Kernels.UFun ζ ^ 2
      - (2 : ℂ) * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ) (Work.Kernels.WFun ζ ^ 2)
    rw [hPdef]
    linarith
  -- assemble
  rw [dev_eq ζ]
  have hnorm : ‖(3 / 2 : ℂ) * (Work.Kernels.UFun ζ * Work.Kernels.VFun ζ * Work.Kernels.WFun ζ)
      * (2 * Work.Kernels.UFun ζ ^ 2 - 2 * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ
        - Work.Kernels.WFun ζ ^ 2)‖
      = (3 / 2) * ‖Work.Kernels.UFun ζ‖ * ‖Work.Kernels.VFun ζ‖ * ‖Work.Kernels.WFun ζ‖
        * ‖(2 : ℂ) * Work.Kernels.UFun ζ ^ 2 - 2 * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ
          - Work.Kernels.WFun ζ ^ 2‖ := by
    have h32 : ‖((3 : ℂ) / 2)‖ = 3 / 2 := by
      rw [norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
    simp only [norm_mul]
    rw [h32]
    ring
  rw [hnorm]
  have hstep : (3 / 2) * ‖Work.Kernels.UFun ζ‖ * ‖Work.Kernels.VFun ζ‖
      * ‖Work.Kernels.WFun ζ‖
      * ‖(2 : ℂ) * Work.Kernels.UFun ζ ^ 2 - 2 * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ
        - Work.Kernels.WFun ζ ^ 2‖
      ≤ (3 / 2) * (1 + CU) * (CV * r) * (1 + CW) * P := by
    refine mul_four_le_mul (a := (3 / 2) * ‖Work.Kernels.UFun ζ‖) (a' := (3 / 2) * (1 + CU))
      (b := ‖Work.Kernels.VFun ζ‖) (b' := CV * r) (c := ‖Work.Kernels.WFun ζ‖) (c' := 1 + CW)
      (d := ‖(2 : ℂ) * Work.Kernels.UFun ζ ^ 2 - 2 * Work.Kernels.UFun ζ * Work.Kernels.WFun ζ
        - Work.Kernels.WFun ζ ^ 2‖) (d' := P) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact mul_le_mul_of_nonneg_left hUc (by norm_num)
    · exact hVdecay
    · exact hWc
    · exact hpoly
    · positivity
    · exact norm_nonneg _
    · exact norm_nonneg _
    · exact norm_nonneg _
    · positivity
    · exact mul_nonneg hCV.le hr0
    · linarith
    · exact hPpos.le
  refine le_trans hstep ?_
  rw [show (3 / 2) * (1 + CU) * (CV * r) * (1 + CW) * P
      = ((3 / 2) * (1 + CU) * (1 + CW) * CV * P) * r by ring]

end

end Work.Asymptotics.TileDevBall
