/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# The rotated per-step error of the approximate perturbed Fatou coordinate

This file proves `Work.PARIMPL.approxEcal_step_rot`: on the rotated transit regime
`Work.PARIMPL.GoodTransitRot`, one iterate of the local model dynamics moves the rotated
approximate perturbed Fatou coordinate

  `Ũ(u) = u + (τ − h₁/τ)·log(sinh(a·u)/a)`

by `−τ`, up to an error `O(‖ζ(u)‖² + λ²)` (with `ζ(u) = Work.Implosion.ecalPt a u`,
`a = iλ`).  The constant `κ = τ − h₁/τ` of the coordinate is exactly the one for which the
linear term of the step error cancels: the algebraic remainder `τ − hz + ζhz² − κζhz − κaζhz²`
(with `hz = τ + h₁ζ + O(ζ²)`) is second order, because `κτ = τ² − h₁`.

The proof reuses the team's public `Work.PARIMPL.norm_S_le_rot` for that algebraic
second-order estimate, and the analytic machinery of the `Submission.Work.Implosion`
chapter for everything else: the exact displacement identity `sinh_modelDisp_identity`,
the branch of the logarithm (`eq_of_exp_eq_of_im_lt`), the second-order displacement bound
`modelDisp_second_order` and the logarithm bound `norm_log_one_add_sub_self_le_of_le_half`.
-/
import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.norm_S_le_rot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Work.PARIMPL

open Complex
open Work.Implosion
open Work.Implosion.Approx

/-! ## The per-step error of the rotated approximate Fatou coordinate -/

/-- **The per-step error in the rotated normalisation.**  On the rotated transit regime, one
iterate of the model dynamics moves the rotated approximate perturbed Fatou coordinate
`Ũ(u) = u + (τ − h₁/τ)·log(sinh(a·u)/a)` by `−τ` up to `O(‖ζ(u)‖² + λ²)`. -/
theorem approxEcal_step_rot (h : ℂ → ℂ) (τ h1 : ℂ) (A r : ℝ) (hA : 0 ≤ A)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam R : ℝ) (a : ℂ), 0 < lam → a = (lam : ℂ) * Complex.I →
      ∀ u : ℂ, Work.PARIMPL.GoodTransitRot a h τ lam R u →
      ‖Work.Implosion.ecalPt a u‖ < r →
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Complex.sinh (a * (u + (t : ℂ) * Work.Implosion.modelDisp a h u)) / a ∈ Complex.slitPlane) →
      ‖Work.Implosion.approxEcal a (τ - h1 / τ) (u + Work.Implosion.modelDisp a h u)
        - Work.Implosion.approxEcal a (τ - h1 / τ) u + τ‖
        ≤ C * (‖Work.Implosion.ecalPt a u‖ ^ 2 + lam ^ 2) := by
  set κ : ℂ := τ - h1 / τ with hκdef
  have hτnorm : ‖τ‖ = 1 := hb.2.1
  obtain ⟨K, hK0, hKbound⟩ := norm_S_le_rot h1 τ A hA hτnorm
  let C : ℝ := K + 32*(1 + ‖κ‖/4) + 9*‖κ‖/2
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    nlinarith [hK0, norm_nonneg κ]
  refine ⟨C, hC0, ?_⟩
  intro lam R a hlam ha u hgt hzr hslit
  subst ha
  obtain ⟨hstrip, hR4, hsmall, hhτ, hh1, hh2, hZslit⟩ := hgt
  rw [mem_transitStrip_iff] at hstrip
  obtain ⟨hstr1, hstr2⟩ := hstrip
  have hane : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hlam) Complex.I_ne_zero
  have hna : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hlam.le]
  set ζ : ℂ := ecalPt ((lam : ℂ) * I) u with hζdef
  set Φ : ℂ := modelDisp ((lam : ℂ) * I) h u with hΦdef
  simp only [approxEcal]
  set W : ℂ := Complex.sinh (((lam : ℂ) * I) * (u + Φ)) / ((lam : ℂ) * I) with hWdef
  set Z : ℂ := Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I) with hZdef
  have hsum : ‖ζ‖ + lam ≤ 1/4 := by linarith [hsmall]
  have hζle : ‖ζ‖ ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hlamle : lam ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hζ3 : ‖h ζ‖ ≤ 3/2 := by
    calc ‖h ζ‖ = ‖(h ζ - τ) + τ‖ := by ring_nf
      _ ≤ ‖h ζ - τ‖ + ‖τ‖ := norm_add_le _ _
      _ ≤ 1/2 + 1 := by rw [hτnorm]; linarith
      _ = 3/2 := by norm_num
  have hζr : ‖ζ‖ < r := by simpa [← hζdef] using hzr
  have he : ‖h ζ - τ - h1*ζ‖ ≤ A*‖ζ‖^2 := hb.2.2.1 ζ hζr
  have hRΦ : ‖Φ + h ζ - ζ*h ζ^2‖ ≤ 32*(‖ζ‖^2 + lam^2) := by
    have h4 : 4 * (‖ecalPt ((lam:ℂ)*I) u‖ + ‖((lam:ℂ)*I)‖) ≤ 1 := by
      have hζ' : ‖ecalPt ((lam:ℂ)*I) u‖ = ‖ζ‖ := by rw [← hζdef]
      rw [hζ', hna]; exact hsmall
    have hres := modelDisp_second_order ((lam:ℂ)*I) h u hane h4 hh2
    simpa [← hΦdef, ← hζdef, hna] using hres
  have hΦn : ‖Φ‖ ≤ 65/16 := by
    have h1 : Φ = (Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2 := by ring
    have htri : ‖(Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2‖
        ≤ ‖Φ + h ζ - ζ*h ζ^2‖ + ‖h ζ‖ + ‖ζ*h ζ^2‖ := by
      have hadd := norm_add_le ((Φ + h ζ - ζ*h ζ^2) - h ζ) (ζ*h ζ^2)
      have hsub2 := norm_sub_le (Φ + h ζ - ζ*h ζ^2) (h ζ)
      linarith [hadd, hsub2]
    have h32 : 32*(‖ζ‖^2 + lam^2) ≤ 2 := by nlinarith [hsum, norm_nonneg ζ]
    have hz1 : ‖ζ*h ζ^2‖ ≤ (1/4)*(3/2)^2 := by
      rw [norm_mul, norm_pow]
      have h2 : ‖h ζ‖^2 ≤ (3/2)^2 := pow_le_pow_left₀ (norm_nonneg _) hζ3 2
      nlinarith [hζle, h2, norm_nonneg ζ]
    rw [h1]
    linarith [htri, hRΦ, h32, hz1, hζ3]
  have hA2decomp : dispNum2 ((lam:ℂ)*I) h u = (ζ + (lam:ℂ)*I) * h ζ := by
    rw [show dispNum2 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u + (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA1decomp : dispNum1 ((lam:ℂ)*I) h u = (ζ - (lam:ℂ)*I) * h ζ := by
    rw [show dispNum1 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u - (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA2le : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA2decomp, norm_mul]
    have h1' : ‖ζ + ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_add_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA2n : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA2le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA1le : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA1decomp, norm_mul]
    have h1' : ‖ζ - ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_sub_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA1n : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA1le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA2small : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 1/2 := by linarith
  have hA1ne : 1 + dispNum1 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum1 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA1n
    linarith
  have hA2ne : 1 + dispNum2 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum2 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA2n
    linarith
  have hEne : ecalE ((lam:ℂ)*I) u ≠ 1 := by
    intro hE
    have hmem : u ∈ periodLattice ((lam:ℂ)*I) := hE
    rw [mem_periodLattice_iff _ _ hane] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hratio : Real.pi * I / ((lam:ℂ)*I) = ((Real.pi/lam : ℝ) : ℂ) := by
      rw [mul_div_mul_right _ _ Complex.I_ne_zero]
      exact (Complex.ofReal_div _ _).symm
    rw [hratio] at hn
    have hure : u.re = (n:ℝ) * (Real.pi/lam) := by
      rw [hn]; simp [Complex.mul_re]
    have hπ : 0 < Real.pi/lam := div_pos Real.pi_pos hlam
    have h1' : (n:ℝ) * (Real.pi/lam) ≥ R := by rw [← hure]; exact hstr1
    have hpos : 0 < (n:ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [h1', hπ, hR4]
    have hposZ : (0:ℤ) < n := by exact_mod_cast hpos
    have hn1 : (1:ℤ) ≤ n := Int.lt_iff_add_one_le.mp hposZ
    have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h2' : u.re ≥ Real.pi/lam := by
      rw [hure]; nlinarith [hn1R, hπ]
    linarith [hstr2, h2']
  have hWslit : W ∈ Complex.slitPlane := by
    have hh := hslit 1 (by norm_num)
    simpa [hWdef, hΦdef] using hh
  have hZre : 0 < Z.re := by
    rw [hZdef]
    exact sinh_mul_I_div_re_pos lam R hlam hR4 u hstr1 hstr2
  have hWne : W ≠ 0 := Complex.slitPlane_ne_zero hWslit
  have hZne : Z ≠ 0 := Complex.slitPlane_ne_zero hZslit
  have hiden : W * (1 + dispNum2 ((lam:ℂ)*I) h u)
      = Z * Complex.exp (-(((lam:ℂ)*I) * Φ)) := by
    rw [hWdef, hZdef, hΦdef]
    exact sinh_modelDisp_identity ((lam:ℂ)*I) h u hane hA1ne hA2ne hEne
  have hΔ : Complex.log W - Complex.log Z
      = -(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by
    refine eq_of_exp_eq_of_im_lt (Complex.log W - Complex.log Z)
      (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) ?_ ?_
    · rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hWne, Complex.exp_log hZne,
        Complex.exp_log hA2ne]
      rw [div_eq_div_iff hZne hA2ne]
      rw [hiden]; ring
    · have hWpi : W.arg < Real.pi := by
        have hWslit' : 0 < W.re ∨ W.im ≠ 0 := hWslit
        rw [Complex.arg_lt_pi_iff]
        rcases hWslit' with hh | hh
        · exact Or.inl (le_of_lt hh)
        · exact Or.inr hh
      have hargW : |W.arg| < Real.pi := (abs_lt).mpr ⟨Complex.neg_pi_lt_arg W, hWpi⟩
      have hargZ : |Z.arg| < Real.pi/2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hZre)
      have hImval : ((Complex.log W - Complex.log Z)
          - (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))).im
          = W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
            + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im := by
        simp only [Complex.sub_im, Complex.neg_im, Complex.log_im]
        ring
      rw [hImval]
      have haΦ : |((((lam:ℂ)*I) * Φ)).im| ≤ lam*(65/16) := by
        calc |((((lam:ℂ)*I) * Φ)).im| ≤ ‖((lam:ℂ)*I) * Φ‖ := Complex.abs_im_le_norm _
          _ = ‖((lam:ℂ)*I)‖ * ‖Φ‖ := norm_mul _ _
          _ = lam * ‖Φ‖ := by rw [hna]
          _ ≤ lam*(65/16) := by gcongr
      have hLa2 : |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| ≤ 33/64 := by
        have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
          norm_log_one_add_sub_self_le_of_le_half hA2small
        have h1' : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖
            ≤ ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u‖ + ‖dispNum2 ((lam:ℂ)*I) h u‖ := by
          have h := norm_add_le (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u) (dispNum2 ((lam:ℂ)*I) h u)
          rwa [sub_add_cancel] at h
        have hnorm : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖ ≤ 33/64 := by
          nlinarith [h1', hlog, hA2n, sq_nonneg ‖dispNum2 ((lam:ℂ)*I) h u‖,
            norm_nonneg (dispNum2 ((lam:ℂ)*I) h u)]
        have h2 := Complex.abs_im_le_norm (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))
        linarith [h2, hnorm]
      have htri : |W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
          + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im|
          ≤ |W.arg - Z.arg| + |((((lam:ℂ)*I) * Φ)).im|
            + |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| := by
        have h1 := abs_add_le (W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im)
          ((Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im)
        have h2 := abs_add_le (W.arg - Z.arg) ((((lam:ℂ)*I) * Φ).im)
        linarith [h1, h2]
      have hsub : |W.arg - Z.arg| ≤ |W.arg| + |Z.arg| := by
        calc |W.arg - Z.arg| = |W.arg + (-Z.arg)| := by rw [sub_eq_add_neg]
          _ ≤ |W.arg| + |-Z.arg| := abs_add_le _ _
          _ = |W.arg| + |Z.arg| := by rw [abs_neg]
      have hpi : (49:ℝ)/16 < Real.pi := lt_trans (by norm_num) Real.pi_gt_d20
      linarith [htri, hsub, hargW, hargZ, haΦ, hLa2, hpi]
  have happrox : (u + Φ) + κ*Complex.log W - (u + κ*Complex.log Z) + τ
      = Φ + κ*(Complex.log W - Complex.log Z) + τ := by ring
  rw [happrox, hΔ]
  have hsimpl : Φ + κ*(-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) + τ
      = (1 - κ*((lam:ℂ)*I))*Φ + τ - κ*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by ring
  rw [hsimpl]
  set S : ℂ := τ - (1 - κ*((lam:ℂ)*I))*(h ζ) + (1 - κ*((lam:ℂ)*I))*ζ*(h ζ)^2
      - κ*(ζ + ((lam:ℂ)*I))*(h ζ) with hSdef
  have hdecomp : (1 - κ*((lam:ℂ)*I))*Φ + τ - κ*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
      = S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) - dispNum2 ((lam:ℂ)*I) h u) := by
    rw [hSdef, hA2decomp]; ring
  rw [hdecomp]
  have hSbound : ‖S‖ ≤ K * (‖ζ‖^2 + lam^2) := by
    have hconv : S = τ - h ζ + ζ*(h ζ)^2 - κ*ζ*(h ζ) - κ*((lam:ℂ)*I)*ζ*(h ζ)^2 := by
      rw [hSdef]; ring
    rw [hconv]
    have hres := hKbound ζ (h ζ) ((lam:ℂ)*I) κ hκdef he hζ3 hζle
      (by rw [hna]; exact hlamle)
    simpa [hna] using hres
  have hRΦb : ‖(1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
      ≤ 32*(1+‖κ‖/4)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hconst : ‖1 - κ*((lam:ℂ)*I)‖ ≤ 1 + ‖κ‖/4 := by
      calc ‖1 - κ*((lam:ℂ)*I)‖ ≤ ‖(1:ℂ)‖ + ‖κ*((lam:ℂ)*I)‖ := norm_sub_le _ _
        _ = 1 + ‖κ‖*lam := by rw [norm_one, norm_mul, hna]
        _ ≤ 1 + ‖κ‖/4 := by nlinarith [hlamle, norm_nonneg κ]
    calc ‖1 - κ*((lam:ℂ)*I)‖ * ‖Φ + h ζ - ζ*(h ζ)^2‖
        ≤ (1 + ‖κ‖/4) * (32*(‖ζ‖^2+lam^2)) := by gcongr
      _ = 32*(1+‖κ‖/4)*(‖ζ‖^2+lam^2) := by ring
  have hA22 : ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ (9/2)*(‖ζ‖^2 + lam^2) := by
    have h2 : ((‖ζ‖+lam)*(3/2))^2 ≤ (9/2)*(‖ζ‖^2+lam^2) := by
      nlinarith [sq_nonneg (‖ζ‖ - lam), norm_nonneg ζ]
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ ((‖ζ‖+lam)*(3/2))^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hA2le 2
      _ ≤ (9/2)*(‖ζ‖^2+lam^2) := h2
  have hE2b : ‖κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ (9*‖κ‖/2)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
      norm_log_one_add_sub_self_le_of_le_half hA2small
    calc ‖κ‖ * ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u‖
        ≤ ‖κ‖ * ‖dispNum2 ((lam:ℂ)*I) h u‖^2 := by gcongr
      _ ≤ ‖κ‖ * ((9/2)*(‖ζ‖^2+lam^2)) := by gcongr
      _ = (9*‖κ‖/2)*(‖ζ‖^2+lam^2) := by ring
  have hfin : ‖S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ C * (‖ζ‖^2 + lam^2) := by
    have htri2 : ‖S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖
        ≤ ‖S‖ + ‖(1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
          + ‖κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u)‖ := by
      have hsub3 := norm_sub_le (S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
        (κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u))
      have hadd2 := norm_add_le S ((1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
      linarith [hsub3, hadd2]
    refine htri2.trans ?_
    have hCexp : C = K + 32*(1 + ‖κ‖/4) + 9*‖κ‖/2 := by dsimp only [C]
    rw [hCexp]
    nlinarith [hSbound, hRΦb, hE2b, sq_nonneg ‖ζ‖, sq_nonneg lam]
  exact hfin

end Work.PARIMPL
