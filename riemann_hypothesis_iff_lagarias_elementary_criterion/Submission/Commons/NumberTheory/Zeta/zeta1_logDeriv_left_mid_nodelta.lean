import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_goodHeight
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_fe_expanded
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_strip_bound_rh
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_left_strip_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal

open Complex Filter Metric Set
open scoped Real Topology BigOperators ComplexConjugate

noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-!
# The log-derivative of `ζ₁` on the left middle strip `1/8 ≤ σ ≤ 1/2` at good heights

Under the Riemann hypothesis, at a height `T` such that no zero `ρ` of `ζ₁` has
`|ρ.im − T| ≤ δ` (with `(log(T+3)+1)·δ ≥ 1`), the logarithmic derivative of the entire
function `ζ₁` is bounded by `C (log(T+3)+1)³` on the strip `1/8 ≤ σ ≤ 1/2`.

The strip is covered in two pieces:

* `σ ≤ 3/8`: the existing left-strip bound `zeta_logDeriv_left_strip_bound` (functional
  equation + right-strip bound), which needs no gap hypothesis;
* `3/8 ≤ σ ≤ 1/2`: the functional equation in logarithmic-derivative form
  `zeta_logDeriv_fe_expanded` expresses `ζ'/ζ(s)` through `ζ'/ζ(1−s)`, `ψ(1−s)` and
  `tan(π(1−s)/2)`.  The reflected point `1−s` has real part in `[1/2,5/8]`, where the
  ball/Borel–Carathéodory bound `zeta1_logDeriv_goodHeight` applies (via the conjugation
  symmetry `logDeriv ζ₁ (conj s) = conj (logDeriv ζ₁ s)` to turn the height `−T` into `T`).
-/

/-! ## Elementary conjugation symmetry of `ζ₁` -/

/-- Conjugation symmetry of the entire completion `ζ₀`. -/
private lemma riemannZeta₀_conj (s : ℂ) : riemannZeta₀ (conj s) = conj (riemannZeta₀ s) := by
  by_cases hs : s = 1
  · subst s
    simp [riemannZeta₀]
  · unfold riemannZeta₀
    rw [if_neg hs, if_neg (by exact (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hs)]
    rw [riemannZeta_conj]
    simp

/-- Conjugation symmetry of the entire completion `ζ₁`. -/
private lemma riemannZeta₁_conj (s : ℂ) : riemannZeta₁ (conj s) = conj (riemannZeta₁ s) := by
  unfold riemannZeta₁
  simp [riemannZeta₀_conj]

/-- `ζ₁` equals `conj ∘ ζ₁ ∘ conj` (functional form of the symmetry). -/
private lemma riemannZeta₁_conj_comp : riemannZeta₁ = conj ∘ riemannZeta₁ ∘ conj := by
  funext s
  calc
    riemannZeta₁ s = conj (conj (riemannZeta₁ s)) := by simp
    _ = conj (riemannZeta₁ (conj s)) := by rw [← riemannZeta₁_conj]
    _ = (conj ∘ riemannZeta₁ ∘ conj) s := by simp

/-- Derivative conjugation symmetry of `ζ₁`. -/
private lemma deriv_riemannZeta₁_conj (s : ℂ) :
    deriv riemannZeta₁ (conj s) = conj (deriv riemannZeta₁ s) := by
  have hsymm : riemannZeta₁ = conj ∘ riemannZeta₁ ∘ conj := riemannZeta₁_conj_comp
  have hd := deriv_conj_conj (f := riemannZeta₁)
  have hmain : deriv riemannZeta₁ s = conj (deriv riemannZeta₁ (conj s)) := by
    calc
      deriv riemannZeta₁ s = deriv (conj ∘ riemannZeta₁ ∘ conj) s := by rw [← hsymm]
      _ = (conj ∘ deriv riemannZeta₁ ∘ conj) s := by rw [hd]
      _ = conj (deriv riemannZeta₁ (conj s)) := by simp
  calc
    deriv riemannZeta₁ (conj s) = conj (conj (deriv riemannZeta₁ (conj s))) := by simp
    _ = conj (deriv riemannZeta₁ s) := by rw [hmain]

/-- Log-derivative conjugation symmetry of `ζ₁`. -/
private lemma logDeriv_riemannZeta₁_conj (s : ℂ) :
    logDeriv riemannZeta₁ (conj s) = conj (logDeriv riemannZeta₁ s) := by
  unfold logDeriv
  change deriv riemannZeta₁ (conj s) / riemannZeta₁ (conj s) =
      conj (deriv riemannZeta₁ s / riemannZeta₁ s)
  rw [deriv_riemannZeta₁_conj, riemannZeta₁_conj, map_div₀]

/-! ## The multiplicative relation between `ζ` and `ζ₁` -/

/-- `ζ₁ = (s−1)·ζ` in logarithmic-derivative form (for `s ≠ 1` with `ζ s ≠ 0`). -/
private lemma zeta1_logDeriv_eq (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := by
  have hEq : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hzne
    have hz := riemannZeta_eq_inv_sub_mul hzne
    calc
      riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hzne)]
        simp
      _ = (z - 1) * riemannZeta z := by rw [hz]
  have hcong := logDeriv_congr_nhds hEq
  have hval : logDeriv riemannZeta₁ s = logDeriv (fun z => (z - 1) * riemannZeta z) s :=
    hcong.self_of_nhds
  rw [hval]
  have hmul := logDeriv_mul (x := s) (f := fun z => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζs (by fun_prop) (differentiableAt_riemannZeta hs1)
  simp only [Pi.mul_def] at hmul
  rw [hmul]
  have hld_id : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => z - 1) s = 1 := by
      simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
    rw [hd]
    simp
  rw [hld_id, logDeriv_apply]
  ring

/-! ## Small auxiliary facts -/

/-- If `0 < re w` then `w` avoids the non-positive integers. -/
private lemma ne_neg_nat_of_re_pos {w : ℂ} (hw : (0 : ℝ) < w.re) : ∀ n : ℕ, w ≠ -(n : ℂ) := by
  intro n hn
  have hre := congrArg Complex.re hn
  have hren : (-(n : ℂ)).re = -((n : ℝ)) := by simp
  rw [hren] at hre
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hnn : -((n : ℝ)) ≤ 0 := by linarith
  linarith

/-- A complex cosine vanishes only at real points. -/
private lemma cos_ne_zero_of_im_ne_zero {u : ℂ} (hu : u.im ≠ 0) : Complex.cos u ≠ 0 := by
  intro hz
  rcases Complex.cos_eq_zero_iff.mp hz with ⟨k, hk⟩
  have hz_im0 : u.im = 0 := by
    rw [hk]
    simp
  exact hu hz_im0

private lemma norm_log_two_pi :
    ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ = Real.log (2 * Real.pi) := by
  have h0le : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hclog : Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) :=
    (Complex.ofReal_log h0le).symm
  rw [hclog]
  exact Complex.norm_of_nonneg (Real.log_nonneg (by nlinarith [Real.two_le_pi]))

/-! ## The main bound -/

theorem zeta1_logDeriv_left_mid_nodelta (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ T δ : ℝ, 5 ≤ T → 0 < δ → 1 ≤ (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1/8 : ℝ) ≤ σ → σ ≤ (1/2 : ℝ) →
        ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := zeta_logDeriv_left_strip_bound h
  obtain ⟨C₂, hC₂pos, hC₂⟩ := zeta1_logDeriv_goodHeight h
  refine ⟨max C₁ (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5), ?_, ?_⟩
  · exact lt_of_lt_of_le hC₁pos (le_max_left _ _)
  intro T δ hT hδ0 hδprod hgap σ hσlo hσhi
  set L : ℝ := Real.log (T + 3) + 1 with hLdef
  have hTpos : 0 < T := by linarith
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hT2 : (2 : ℝ) ≤ |T| := by rw [hTabs]; linarith
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    linarith
  have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hL3nn : 0 ≤ L ^ 3 := le_trans zero_le_one hL3
  by_cases hle : σ ≤ (3 / 8 : ℝ)
  · -- left compact piece
    have hb := hC₁ σ T hσlo hle hT2
    calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖
        ≤ C₁ * (Real.log (|T| + 3) + 1) ^ 3 := hb
      _ = C₁ * L ^ 3 := by rw [hTabs, hLdef]
      _ ≤ max C₁ (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5) * L ^ 3 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hL3nn
  · -- functional-equation piece
    have hlt : (3 / 8 : ℝ) < σ := lt_of_not_ge hle
    set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hsdef
    have hsre : s.re = σ := by rw [hsdef]; simp
    have hsim : s.im = T := by rw [hsdef]; simp
    have hs0 : s ≠ 0 := by
      intro h0
      have hh := congrArg Complex.re h0
      rw [hsre] at hh
      simp at hh
      linarith
    have hs1 : s ≠ 1 := by
      intro h1
      have hh := congrArg Complex.re h1
      rw [hsre] at hh
      simp at hh
      linarith
    have hζ1s : riemannZeta₁ s ≠ 0 := by
      intro h0
      have hh := hgap s h0
      rw [hsim] at hh
      simp at hh
      linarith
    have hζs : riemannZeta s ≠ 0 := by
      rw [riemannZeta_eq_inv_sub_mul hs1]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hζ1s
    -- reflected point
    have hrew_re : (1 - s).re = 1 - σ := by
      rw [Complex.sub_re, hsre, Complex.one_re]
    have hrew_im : (1 - s).im = -T := by
      rw [Complex.sub_im, hsim, Complex.one_im]
      ring
    have hζw : riemannZeta (1 - s) ≠ 0 := by
      intro hw0
      by_cases hlt' : (1 / 2 : ℝ) < (1 - s).re
      · exact zeta_ne_zero_of_rh_gt_half h hlt' hw0
      · have hre12 : (1 - s).re = 1 / 2 :=
          le_antisymm (le_of_not_gt hlt') (by rw [hrew_re]; linarith)
        have himc : (conj (1 - s)).im = T := by
          rw [Complex.conj_im, hrew_im]
          ring
        have hconj0 : riemannZeta (conj (1 - s)) = 0 := by
          rw [riemannZeta_conj, hw0, map_zero]
        have hne1 : conj (1 - s) ≠ 1 := by
          intro hh
          have him := congrArg Complex.im hh
          rw [himc] at him
          simp at him
          linarith
        have hz1 : riemannZeta₁ (conj (1 - s)) = 0 := by
          have hrel := riemannZeta_eq_inv_sub_mul (s := conj (1 - s)) hne1
          rw [hrel] at hconj0
          rcases mul_eq_zero.mp hconj0 with h2 | h2
          · exact absurd h2 (inv_ne_zero (sub_ne_zero.mpr hne1))
          · exact h2
        have hh := hgap (conj (1 - s)) hz1
        rw [himc] at hh
        simp at hh
        linarith
    have hre_w_pos : (0 : ℝ) < (1 - s).re := by rw [hrew_re]; linarith
    have hΓ : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := ne_neg_nat_of_re_pos hre_w_pos
    have him_arg : (↑Real.pi * (1 - s) / 2).im = -(Real.pi / 2) * T := by
      have heq : (↑Real.pi * (1 - s) / 2) = ((Real.pi / 2 : ℝ) : ℂ) * (1 - s) := by
        push_cast
        ring
      rw [heq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hrew_im]
      ring
    have him_no : (↑Real.pi * (1 - s) / 2).im ≠ 0 := by
      rw [him_arg]
      exact mul_ne_zero
        (neg_ne_zero.mpr (ne_of_gt (by positivity : (0 : ℝ) < Real.pi / 2)))
        (by linarith : T ≠ 0)
    have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 :=
      cos_ne_zero_of_im_ne_zero him_no
    have hFE := zeta_logDeriv_fe_expanded hζs hζw hs0 hs1 hΓ hcos
    -- bound the constant term
    have hbnd_log : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ ≤ Real.log (2 * Real.pi) * L ^ 3 := by
      rw [norm_log_two_pi]
      exact le_mul_of_one_le_right (Real.log_nonneg (by nlinarith [Real.two_le_pi])) hL3
    -- bound the digamma term
    have hbnd_dg : ‖Complex.digamma (1 - s)‖ ≤ 3 * L ^ 3 := by
      have hmid := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
        (1 - σ) (-T) (by linarith) (by linarith)
      have harg : ((1 - σ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I = 1 - s := by
        rw [hsdef]
        apply Complex.ext <;> simp <;> ring
      have hb : ‖Complex.digamma (1 - s)‖ ≤ Real.log (2 + |T|) + 2 := by
        rw [← harg]
        simpa using hmid
      have hlog0 : (0 : ℝ) ≤ Real.log (|T| + 3) := Real.log_nonneg (by linarith [abs_nonneg T])
      have hmono : Real.log (2 + |T|) ≤ Real.log (|T| + 3) :=
        Real.log_le_log (by positivity) (by linarith [abs_nonneg T])
      calc ‖Complex.digamma (1 - s)‖ ≤ Real.log (2 + |T|) + 2 := hb
        _ ≤ 3 * (Real.log (|T| + 3) + 1) := by linarith
        _ = 3 * L := by rw [hTabs, hLdef]
        _ ≤ 3 * L ^ 3 := by
            have hLle3 : L ≤ L ^ 3 := by
              simpa using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 3)
            exact mul_le_mul_of_nonneg_left hLle3 (by norm_num)
    -- bound the tangent term
    have hbnd_T : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤
        2 * Real.pi * L ^ 3 := by
      have himabs : (1 : ℝ) ≤ |(↑Real.pi * (1 - s) / 2).im| := by
        rw [him_arg, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2)]
        nlinarith [Real.pi_gt_three, hT]
      have htan :=
        Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge
          (↑Real.pi * (1 - s) / 2) himabs
      calc ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖
          = (Real.pi / 2) * ‖Complex.tan (↑Real.pi * (1 - s) / 2)‖ := by
            rw [norm_mul, Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
        _ ≤ (Real.pi / 2) * 4 := mul_le_mul_of_nonneg_left htan (by positivity)
        _ = 2 * Real.pi := by ring
        _ ≤ 2 * Real.pi * L ^ 3 := le_mul_of_one_le_right (by positivity) hL3
    -- bound the reflected `ζ'/ζ`
    have hbnd_R : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ (C₂ + 1) * L ^ 3 := by
      have hw1 : (1 - s) ≠ 1 := by
        intro hh
        have hre := congrArg Complex.re hh
        rw [hrew_re] at hre
        simp at hre
        linarith
      have hld1 := zeta1_logDeriv_eq (1 - s) hw1 hζw
      have hsplit : deriv riemannZeta (1 - s) / riemannZeta (1 - s) =
          logDeriv riemannZeta₁ (1 - s) - ((1 - s) - 1)⁻¹ := by
        rw [hld1]
        ring
      -- conjugation turns the height `-T` into `+T`
      have hconj_eq : (1 - s) = conj (((1 - σ : ℝ) : ℂ) + Complex.I * (T : ℂ)) := by
        apply Complex.ext <;> simp [hrew_re, hrew_im] <;> ring
      have hbd1 : ‖logDeriv riemannZeta₁ (1 - s)‖ ≤ C₂ * L ^ 3 := by
        rw [hconj_eq, logDeriv_riemannZeta₁_conj]
        simp only [norm_conj]
        have hb := hC₂ T δ hT hδ0 hδprod hgap (1 - σ) (by linarith) (by linarith)
        simpa [hLdef] using hb
      have hinv1 : ‖((1 - s) - 1)⁻¹‖ ≤ 1 := by
        have h1 : (1 : ℝ) ≤ ‖(1 - s) - 1‖ := by
          have him : ((1 - s) - 1).im = -T := by
            rw [Complex.sub_im, hrew_im, Complex.one_im]
            ring
          calc (1 : ℝ) ≤ |T| := by rw [hTabs]; linarith
            _ = |((1 - s) - 1).im| := by rw [him, abs_neg]
            _ ≤ ‖(1 - s) - 1‖ := Complex.abs_im_le_norm _
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ h1
      calc ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
          = ‖logDeriv riemannZeta₁ (1 - s) - ((1 - s) - 1)⁻¹‖ := by rw [hsplit]
        _ ≤ ‖logDeriv riemannZeta₁ (1 - s)‖ + ‖((1 - s) - 1)⁻¹‖ := norm_sub_le _ _
        _ ≤ C₂ * L ^ 3 + 1 := add_le_add hbd1 hinv1
        _ ≤ (C₂ + 1) * L ^ 3 := by
            rw [add_mul, one_mul]
            linarith [hL3]
    -- assemble
    have hmain : ‖deriv riemannZeta s / riemannZeta s‖ ≤
        (Real.log (2 * Real.pi) + 3 + 2 * Real.pi + (C₂ + 1)) * L ^ 3 := by
      rw [hFE]
      have htri : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
              deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
              ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
        have ha := norm_sub_le (Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2))
            (deriv riemannZeta (1 - s) / riemannZeta (1 - s))
        have hb := norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s))
            (((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2))
        have hc := norm_sub_le (Complex.log ((2 * Real.pi : ℝ) : ℂ)) (Complex.digamma (1 - s))
        linarith
      have hsum : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
              ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
          Real.log (2 * Real.pi) * L ^ 3 + 3 * L ^ 3 + 2 * Real.pi * L ^ 3 +
            (C₂ + 1) * L ^ 3 := by linarith
      have hring : Real.log (2 * Real.pi) * L ^ 3 + 3 * L ^ 3 + 2 * Real.pi * L ^ 3 +
            (C₂ + 1) * L ^ 3 =
          (Real.log (2 * Real.pi) + 3 + 2 * Real.pi + (C₂ + 1)) * L ^ 3 := by ring
      linarith [htri, hsum, hring.le, hring.ge]
    have hfinal : ‖logDeriv riemannZeta₁ s‖ ≤
        (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5) * L ^ 3 := by
      have hld_eq := zeta1_logDeriv_eq s hs1 hζs
      have hinvs : ‖(s - 1)⁻¹‖ ≤ 1 := by
        have h1 : (1 : ℝ) ≤ ‖s - 1‖ := by
          have him : (s - 1).im = T := by
            rw [Complex.sub_im, hsim, Complex.one_im]
            ring
          calc (1 : ℝ) ≤ |T| := by rw [hTabs]; linarith
            _ = |(s - 1).im| := by rw [him]
            _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ h1
      have hchain : ‖logDeriv riemannZeta₁ s‖ ≤
          (Real.log (2 * Real.pi) + 3 + 2 * Real.pi + (C₂ + 1)) * L ^ 3 + 1 := by
        rw [hld_eq]
        calc ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
            ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
          _ ≤ (Real.log (2 * Real.pi) + 3 + 2 * Real.pi + (C₂ + 1)) * L ^ 3 + 1 :=
              add_le_add hmain hinvs
      have hdecomp : (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5) * L ^ 3 =
          (Real.log (2 * Real.pi) + 3 + 2 * Real.pi + (C₂ + 1)) * L ^ 3 + L ^ 3 := by
        ring
      have hstep : (Real.log (2 * Real.pi) + 3 + 2 * Real.pi + (C₂ + 1)) * L ^ 3 + 1 ≤
          (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5) * L ^ 3 := by
        rw [hdecomp]
        linarith [hL3]
      linarith [hchain, hstep]
    calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖
        = ‖logDeriv riemannZeta₁ s‖ := by rw [hsdef]
      _ ≤ (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5) * L ^ 3 := hfinal
      _ ≤ max C₁ (Real.log (2 * Real.pi) + 2 * Real.pi + C₂ + 5) * L ^ 3 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hL3nn

end Commons.NumberTheory.Zeta
