import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.testfun_basic
import Submission.Work.LinnikAreas.Density4.testfun_conv
import Submission.Work.LinnikAreas.Density4.testfun_lapl_pos
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Density4.fTcond2
import Submission.Work.LinnikAreas.Density4.fTregular
import Submission.Work.LinnikAreas.Density4.exists_log_threshold

/-!
# Area 4 / HB §12 — the per-character `K`-bound with the §7 test function (HB Lemma 5.2)

`Work.LinnikAreas.Density4.Kbound_discharge` discharges the `hK1` hypothesis of
`Commons.NumberTheory.Linnik.hb_lemma12_1` (the Cauchy–Schwarz core of HB's Lemma 12.1) for the
extreme test function `fT` of HB §7: for every primitive non-principal character `χ mod q`, every
zero `ρ` of `L(·,χ)` with `|Im ρ| ≤ 1` and `λ(ρ) ≤ λ₀(q) = logloglog q / 3`, and under the
zero-free hypothesis `λ(ρ') ≥ λ₁` for every non-trivial zero `ρ'` of a non-principal character with
`|Im ρ'| ≤ 2`,

`K(β₁ + iγ, χ) ≤ -𝓛 F(λ(ρ) - λ₁) + f(0)(1/6 + ε)𝓛`,  `β₁ = 1 - λ₁/𝓛`, `𝓛 = log q`.

The three analytic inputs are

* `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_*` (HB Lemma 5.2), used here through its
  packaged form `Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi` (which already performs the
  window reduction `Σ_{|1+iγ-ρ'|≤δ} Re F((s-ρ')𝓛) ≥ Re F((s-ρ)𝓛)` using
  `Commons.NumberTheory.Linnik.le_windowSum_of_mem` and HB's Condition 2 for the test function);
* `Work.LinnikAreas.l31free.lemma3_1_free_gen` (HB Lemma 3.1, the log-derivative bound), which
  supplies `L52Hyp` using Area 1 (the Burgess bound) as its only input;
* the two facts about the §7 test function itself: HB's Condition 2 (`fTcond2`) and the
  regularity/`C²`-bound data (`fTregular`).

Everything else (the identification of `Kgen` with the `s`-parametrised `K`-sum, of the complex
Laplace integral at a real argument with `Lapl`, the bookkeeping of the window hypotheses and the
logarithmic thresholds) is done here.
-/

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-! ## Two elementary identifications -/

/-- `Kgen` is the `s = β + it`-parametrised HB §6 `K`-sum, in the shape in which Lemma 5.2 states
its conclusion: `Kgen q L β t f χ = Σ_n Λ(n) Re(χ(n)/n^{β+it}) f(log n / L)`. -/
lemma Kgen_eq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (L β t : ℝ) (f : ℝ → ℝ) :
    Kgen q L β t f χ =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I)).re) *
          f (Real.log n / L) := by
  rw [Kgen]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h2 : χ (n : ZMod q) * (n:ℂ) ^ (-(β:ℂ) - (t:ℂ)*Complex.I)
        = χ (n : ZMod q) / (n:ℂ) ^ ((β:ℂ)+(t:ℂ)*Complex.I) := by
      rw [show -(β:ℂ) - (t:ℂ)*Complex.I = -((β:ℂ)+(t:ℂ)*Complex.I) by ring, Complex.cpow_neg]
      exact (div_eq_mul_inv _ _).symm
    rw [h2]

/-- The real part of the complex Laplace integral `∫₀^{x₀} e^{-ct} f(t) dt` at a **real** argument
`c` is the real Laplace transform `Lapl x₀ f c`. -/
lemma re_laplace_eq_Lapl {x₀ c : ℝ} (f : ℝ → ℝ) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) * (t : ℂ)))) * ((f t : ℝ) : ℂ)).re
      = Lapl x₀ f c := by
  have hpt : ∀ t : ℝ, Complex.exp (-(((c : ℂ) * (t : ℂ)))) * ((f t : ℝ) : ℂ)
      = ((Real.exp (-(c * t)) * f t : ℝ) : ℂ) := by
    intro t
    rw [show -(((c : ℂ) * (t : ℂ))) = ((-(c*t) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]
  simp only [hpt]
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re, Lapl]

/-! ## The discharge -/

theorem Kbound_discharge (h1 : Work.LinnikContract.Area1) :
    ∀ ε : ℝ, 0 < ε → ∀ (lam₁ θ lamhat : ℝ), 0 < lamhat → Real.pi / 2 < θ → θ < Real.pi →
      ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
        (χ : DirichletCharacter ℂ q) (ρ : ℂ),
          χ ≠ 1 → χ.IsPrimitive → Work.LinnikContract.IsZ χ ρ →
          Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q →
          (∀ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ), χ' ≠ 1 →
              Work.LinnikContract.zeroMult χ' ρ' ≠ 0 → |ρ'.im| ≤ 2 →
              lam₁ ≤ Work.LinnikContract.lamOf q ρ') →
          Work.LinnikAreas.Density4.Kgen q (Real.log q) (1 - lam₁/Real.log q) ρ.im
              (Work.LinnikAreas.Density4.fT θ lamhat) χ
            ≤ -Real.log q * Work.LinnikAreas.Density4.Lapl
                (2 * Work.LinnikAreas.Density4.gammaT θ lamhat)
                (Work.LinnikAreas.Density4.fT θ lamhat)
                (Work.LinnikContract.lamOf q ρ - lam₁)
              + Work.LinnikAreas.Density4.fT θ lamhat 0 * ((1/6:ℝ) + ε) * Real.log q := by
  intro ε hε lam₁ θ lamhat hlamhat hθ1 hθ2
  -- HB §7 test function: regularity (Condition 1 data) and Condition 2
  obtain ⟨hcont, hf0pos, hf2, B, hBnn, hBnd⟩ := fTregular hθ1 hθ2 hlamhat
  have hsupp : ∀ t : ℝ, 2 * gammaT θ lamhat ≤ t → fT θ lamhat t = 0 :=
    fun t ht => fT_eq_zero_of_two_gammaT_le θ lamhat hθ1 hθ2 hlamhat t ht
  have hF := fTcond2 hθ1 hθ2 hlamhat
  have hx₀pos : 0 < 2 * gammaT θ lamhat := by
    have := gammaT_pos hθ1 hθ2 hlamhat; linarith
  -- HB Lemma 3.1 (log-derivative bound) from Area 1, with the slack `ε/4` of `L52Hyp`
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1:ℝ)/3) (by norm_num) (ε := ε/4)
      (by positivity) h1.1
  -- HB Lemma 5.2 + the window reduction, at `x₀ = 2γ` and `c = 1/6`
  obtain ⟨q₀K, hq₀K⟩ :=
    Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi (x₀ := 2 * gammaT θ lamhat) (B := B)
      (c := 1/6) hx₀pos hBnn hcont hsupp hf2 hBnd hf0pos hF hε hδ0 hδ1
  -- logarithmic thresholds
  obtain ⟨q₀log, hq₀log⟩ := exists_log_threshold (A := lam₁) (δ := δ) hδ0
  refine ⟨max (max q₀K q₀log) (max (Nat.ceil (Real.exp L₀) + 3) 3), ?_⟩
  intro q hq _inst χ ρ hχne hχprim hZ hlamMax hzero
  obtain ⟨hlogq1, hsqrt, hlamle⟩ :=
    hq₀log q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hqK : q₀K ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqceil : Nat.ceil (Real.exp L₀) + 3 ≤ q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hLpos : 0 < Real.log (q:ℝ) := by linarith
  -- the primitive character induced by `χ` is `χ`'s own primitive part; its conductor is `q`
  have hcond : χ.conductor = q := hχprim
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχprimchar_ne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχne
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := hZ.2.1
  have him1 : |ρ.im| ≤ 1 := hZ.2.2
  have h0an : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      ρ ≠ 0 := by
    simpa [Work.LinnikContract.zeroMult] using hzm
  -- `ρ` is a zero of the completed `L`-function, hence in the critical strip
  have hρstrip : 0 < ρ.re ∧ ρ.re < 1 :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hχprimchar_ne
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero h0an)
  have hL₀le : L₀ ≤ Real.log (q:ℝ) := by
    have h2 : Real.exp L₀ ≤ (Nat.ceil (Real.exp L₀) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp L₀) : ℝ) ≤ ((Nat.ceil (Real.exp L₀) + 3 : ℕ) : ℝ) := by
      push_cast; linarith
    have h4 : ((Nat.ceil (Real.exp L₀) + 3 : ℕ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast hqceil
    calc L₀ = Real.log (Real.exp L₀) := (Real.log_exp L₀).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos L₀) (by linarith)
  -- the evaluation point of Lemma 5.2
  set s : ℂ := ((1 - lam₁ / Real.log (q:ℝ) : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I with hsdef
  have hsre : s.re = 1 - lam₁/Real.log (q:ℝ) := by
    rw [hsdef]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hsim : s.im = ρ.im := by
    rw [hsdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
  have hsre1 : |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : s.re - 1 = -(lam₁ / Real.log (q:ℝ)) := by rw [hsre]; ring
    rw [h, abs_neg, abs_div, abs_of_pos hLpos]
    exact div_le_div_of_nonneg_right hsqrt hLpos.le
  have hsre2 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ s.re := by
    rw [hsre]
    have : lam₁ / Real.log (q:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right (le_trans (le_abs_self lam₁) hsqrt) hLpos.le
    linarith
  have hsim10 : |s.im| ≤ 10 * Real.log (q:ℝ) := by
    rw [hsim]
    have : (1:ℝ) ≤ 10 * Real.log (q:ℝ) := by linarith
    linarith [him1]
  -- the three window hypotheses of `Ksum_le_single_of_L52_phi`
  have hρball : ρ ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    have h2 : |ρ.re| < 1 := by rw [abs_of_pos hρstrip.1]; exact hρstrip.2
    have h3 : |ρ.im| = |s.im| := by rw [hsim]
    linarith
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχprimchar_ne).analyticAt z
  have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0 := by
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hρball]
    exact_mod_cast h0an
  have hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ := by
    have h1 : (1:ℂ) + (s.im : ℂ) * Complex.I - ρ = ((1 - ρ.re : ℝ) : ℂ) := by
      refine Complex.ext ?_ ?_
      · simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      · simp [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, hsim]
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hρstrip.2])]
    have h4 : (1 - ρ.re) * Real.log (q:ℝ) ≤ Work.LinnikContract.lamMax q := hlamMax
    exact le_trans ((le_div_iff₀ hLpos).mpr h4) hlamle
  have hzw : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
    intro u hdu hwu
    have hu_ball : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := by
      by_contra hu
      have h0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall (0:ℂ) (|s.im| + 2)) u = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        exact fun hc => hu hc.2
      exact hdu h0
    have hu_an : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        u ≠ 0 := by
      have h := hdu
      rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu_ball] at h
      exact_mod_cast h
    have hzu : Work.LinnikContract.zeroMult χ u ≠ 0 := by
      simpa [Work.LinnikContract.zeroMult] using hu_an
    have huim : |u.im| ≤ 2 := by
      have h1 : |s.im - u.im| ≤ δ := by
        have h2 : ((1:ℂ) + (s.im:ℂ)*Complex.I - u).im = s.im - u.im := by simp
        calc |s.im - u.im| = |((1:ℂ) + (s.im:ℂ)*Complex.I - u).im| := by rw [h2]
          _ ≤ ‖(1:ℂ) + (s.im:ℂ)*Complex.I - u‖ := Complex.abs_im_le_norm _
          _ ≤ δ := hwu
      have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
        calc |u.im| = |s.im + (u.im - s.im)| := by congr 1; ring
          _ ≤ |s.im| + |u.im - s.im| := abs_add_le _ _
          _ = |s.im| + |s.im - u.im| := by rw [abs_sub_comm]
      have h4 : |s.im| ≤ 1 := by rw [hsim]; exact him1
      linarith
    have hu := hzero χ u hχne hzu huim
    rw [Work.LinnikContract.lamOf] at hu
    rw [hsre]
    have h2 : lam₁ / Real.log (q:ℝ) ≤ 1 - u.re := by
      rw [div_le_iff₀ hLpos]; linarith
    linarith
  -- the Lemma 3.1 input for `χ.primitiveCharacter`
  have hH : Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε δ := by
    intro s' hs1 hs2 hs3
    have h3q : 3 ≤ χ.conductor := by rw [hcond]; exact hq3
    have h := hmain (N := χ.conductor) h3q (χ.primitiveCharacter) hχprimchar_ne
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) (L := Real.log (q:ℝ)) hL₀le
      (by rw [hcond]) s' hs1 hs2 hs3
    rw [show (1:ℝ)/3/2 + ε/4 = (1:ℝ)/6 + ε/4 by norm_num] at h
    exact h
  have hsingle := hq₀K hqK χ hχne (s := s) (ρ := ρ) hsre1 hsim10 hsre2 hH hdiv hwin hzw
  -- the single-zero term is `Lapl (2γ) (fT) (λ(ρ) - λ₁)`
  have hsρ1 : s - ρ = ((1 - lam₁ / Real.log (q:ℝ) - ρ.re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · show s.re - ρ.re = 1 - lam₁ / Real.log (q:ℝ) - ρ.re
      rw [hsre]
    · show s.im - ρ.im = 0
      rw [hsim, sub_self]
  have hsρ : (s - ρ) * (Real.log (q:ℝ) : ℂ) = ((Work.LinnikContract.lamOf q ρ - lam₁ : ℝ) : ℂ) := by
    rw [hsρ1, ← Complex.ofReal_mul]
    congr 1
    rw [Work.LinnikContract.lamOf]
    field_simp
    ring
  have hlapl : (∫ t in (0:ℝ)..(2 * gammaT θ lamhat),
        Complex.exp (-((s - ρ) * (Real.log (q:ℝ) : ℂ) * (t : ℂ))) * ((fT θ lamhat t : ℝ) : ℂ)).re
      = Lapl (2 * gammaT θ lamhat) (fT θ lamhat) (Work.LinnikContract.lamOf q ρ - lam₁) := by
    rw [hsρ]
    exact re_laplace_eq_Lapl _
  rw [hlapl] at hsingle
  rw [hsdef] at hsingle
  rw [Kgen_eq_sum]
  exact hsingle

end Work.LinnikAreas.Density4
