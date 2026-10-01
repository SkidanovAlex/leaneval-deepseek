import Mathlib
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_supply
import Submission.Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re
import Submission.Work.LinnikAreas.re_logDeriv_LFunction_le_vonMangoldtTsum
import Submission.Work.LinnikAreas.OtherCharRepel.gammaFactorLogDerivReLe
import Submission.Work.ZeroDensity.Jutila.neg_zeta_logDeriv_re_le

namespace Work.ZeroDensity.Jutila

open Complex DirichletCharacter Metric
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.LinnikAreas.DhRepel (firstSum secondSum kernSum tendsto_kernSum kernSum_mono
  kernel_conj divisor_nonneg kernel_first_nonneg le_of_monotone_tendsto finiteSupport_first
  finiteSupport_second mem_of_divisor_ne_zero re_mem_Ioo_of_divisor_ne_zero divisor_refl
  divisor_hasFiniteSupport)

/-! ## Stand-in statements for the three delegated analytic inputs -/

/-- The real majorant `Λ(n)·n^{-σ}` is summable for `σ > 1`. -/
private lemma summable_vonMangoldt_mul_rpow_neg_ks (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

/-- Norm bound for the twisted von Mangoldt series: for `Re s > 1`,
`‖(L'/L)(s,χ)‖ ≤ Σ_n Λ(n) n^{-Re s}`. -/
private lemma norm_logDeriv_LFunction_le_tsum_ks {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
  rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs,
    norm_neg]
  have hfsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) s := by
    have hg : LSeriesSummable
        ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
          fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    refine (LSeriesSummable_congr s (f := fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      (g := (fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
        fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ?_).mpr hg
    intro n _
    simp only [Pi.mul_apply]
    ring
  have hsummN : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s n‖) := hfsumm.norm
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s n‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
    intro n
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0; simp [LSeries.term_zero]
    · rw [LSeries.norm_term_eq, if_neg hn0]
      have hnormχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hΛnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hmul : ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [norm_mul, Complex.norm_of_nonneg hΛnn]
        exact mul_le_of_le_one_right hΛnn hnormχ
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)‖ / (n : ℝ) ^ s.re
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right hmul hpow
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  calc ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsummN
    _ ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) :=
        Summable.tsum_le_tsum hterm hsummN (summable_vonMangoldt_mul_rpow_neg_ks s.re hs)

/-- Complex-argument von Mangoldt bound for the logarithmic derivative of a Dirichlet `L`-series:
for `Re s > 1`, `Re (L'/L)(s,χ) ≤ Σ_n Λ(n) n^{-Re s}`. -/
theorem logDeriv_LFunction_complex_re_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    (logDeriv (DirichletCharacter.LFunction χ) s).re ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) :=
  le_trans (Complex.re_le_norm _) (norm_logDeriv_LFunction_le_tsum_ks χ hs)

/-- `Re (logDeriv Γℝ z) ≤ (1/2)·log (2 + |τ|) + 1` for `1 ≤ Re z ≤ 16` and `z.im = τ`. -/
private theorem gammaR_logDeriv_re_le_ks (z : ℂ) (τ : ℝ) (hz1 : 1 ≤ z.re) (hz2 : z.re ≤ 16)
    (hzim : z.im = τ) :
    (logDeriv Complex.Gammaℝ z).re ≤ (1 / 2) * Real.log (2 + |τ|) + 1 := by
  have hzpos : 0 < z.re := by linarith
  have hformula := Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_formula z hzpos
  rw [hformula]
  have hsplit : (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2).re
      = -(Real.log Real.pi) / 2 + (Complex.digamma (z / 2)).re / 2 := by
    rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
    simp [Complex.add_re]
  rw [hsplit]
  have hx1 : (1 : ℝ) / 2 ≤ (z / 2).re := by
    rw [Commons.NumberTheory.DirichletCharacter.re_div_two]; linarith
  have hx2 : (z / 2).re ≤ 8 := by
    rw [Commons.NumberTheory.DirichletCharacter.re_div_two]; linarith
  have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
    (z / 2).re (z / 2).im hx1 hx2
  have harg : (((z / 2).re : ℂ) + ((z / 2).im : ℂ) * Complex.I) = z / 2 := by
    rw [Complex.re_add_im]
  rw [harg] at hdg
  have hwim : |(z / 2).im| = |τ| / 2 := by
    rw [Commons.NumberTheory.DirichletCharacter.im_div_two, hzim, abs_div]
    norm_num
  rw [hwim] at hdg
  have hlogle : Real.log (2 + |τ| / 2) ≤ Real.log (2 + |τ|) := by
    apply Real.log_le_log (by positivity)
    linarith [abs_nonneg τ]
  have hre : (Complex.digamma (z / 2)).re ≤ Real.log (2 + |τ|) + 2 :=
    le_trans (Complex.re_le_norm _) (by linarith)
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

/-- Real-part bound for the logarithmic derivative of the archimedean factor on `1 ≤ σ ≤ 3`
with the explicit constant `1`. -/
theorem gammaFactor_logDeriv_re_le_three {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ τ : ℝ} (hσ1 : 1 ≤ σ) (hσ3 : σ ≤ 3) :
    (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |τ|) + 1 := by
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ :=
      funext fun z => hE.gammaFactor_def z
    rw [hfun]
    exact gammaR_logDeriv_re_le_ks _ τ (by simp; linarith) (by simp; linarith) (by simp)
  · have hfun : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext fun z => hO.gammaFactor_def z
    rw [hfun]
    have hld : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1))
          ((σ : ℂ) + Complex.I * (τ : ℂ))
        = logDeriv Complex.Gammaℝ (((σ : ℂ) + Complex.I * (τ : ℂ)) + 1) := by
      simp only [logDeriv, Pi.div_apply, deriv_comp_add_const]
    rw [hld]
    exact gammaR_logDeriv_re_le_ks _ τ (by simp [Complex.add_re]; linarith)
      (by simp [Complex.add_re]; linarith) (by simp)

/-! ## Elementary kernel facts -/

lemma one_div_sub_re (s u : ℂ) :
    (1 / (s - u)).re = (s.re - u.re) / Complex.normSq (s - u) := by
  rw [one_div, Complex.inv_re, Complex.sub_re]

lemma one_div_sub_re_pos {s u : ℂ} (hs : 1 < s.re) (hu : u.re < 1) :
    0 < (1 / (s - u)).re := by
  rw [one_div_sub_re]
  have hpos : 0 < s.re - u.re := by linarith
  have hns : 0 < Complex.normSq (s - u) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (s.im - u.im), hpos]
  exact div_pos hpos hns

/-! ## The first half is monotone in the truncation radius -/

lemma firstSum_mono {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    Monotone (fun R : ℝ => firstSum χ s R) := by
  intro R₁ R₂ h12
  have han : AnalyticOnNhd ℂ (completedLFunction χ)
      (Metric.closedBall (0:ℂ) R₁ ∪ Metric.closedBall (0:ℂ) R₂) :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  refine finsum_le_finsum' (finiteSupport_first χ hχ (s := s) (R := R₁))
    (finiteSupport_first χ hχ (s := s) (R := R₂)) ?_
  intro u
  show (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) *
      (1/(s-u)).re ≤
    (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) *
      (1/(s-u)).re
  by_cases hD : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) = 0
  · have hD' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) = 0 := by
      rw [hD]; simp
    rw [hD', zero_mul]
    by_cases hE : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) = 0
    · have hE' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) = 0 := by
        rw [hE]; simp
      rw [hE', zero_mul]
    · exact mul_nonneg (divisor_nonneg χ hχ R₂ u) (kernel_first_nonneg χ hχ hχprim hs hE)
  · have hu1 : u ∈ Metric.closedBall (0:ℂ) R₁ := mem_of_divisor_ne_zero hD
    have hu2 : u ∈ Metric.closedBall (0:ℂ) R₂ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hu1 ⊢
      linarith
    have hEq : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁) u =
        MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂) u :=
      Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset han hu1 hu2
    have hEq' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) =
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) := by
      rw [hEq]
    rw [hEq']

/-! ## Reflection of the second half -/

/-- The reflection `w ↦ 1 - conj w` as an involutive equivalence of `ℂ`. -/
def reflEquiv : ℂ ≃ ℂ where
  toFun := fun v => 1 - (starRingEnd ℂ) v
  invFun := fun v => 1 - (starRingEnd ℂ) v
  left_inv := fun v => by simp [map_sub]
  right_inv := fun v => by simp [map_sub]

@[simp] lemma reflEquiv_apply (v : ℂ) : reflEquiv v = 1 - (starRingEnd ℂ) v := rfl

/-- The second half of the truncated symmetric kernel sum, reindexed by the reflection
`u ↦ 1 - conj u`. -/
lemma secondSum_eq_refl {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (R : ℝ) :
    secondSum χ s R = ∑ᶠ w : ℂ,
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R))
        (1 - (starRingEnd ℂ) w) : ℤ) : ℝ) * (1/(s-w)).re := by
  classical
  have h1 : secondSum χ s R = ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
        (1/((starRingEnd ℂ) s + u - 1)).re := rfl
  rw [h1, ← finsum_comp_equiv reflEquiv (f := fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
        (1/((starRingEnd ℂ) s + u - 1)).re)]
  refine finsum_congr (fun w => ?_)
  show (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R))
      (reflEquiv w) : ℤ) : ℝ) * (1/((starRingEnd ℂ) s + reflEquiv w - 1)).re =
    (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R))
        (1 - (starRingEnd ℂ) w) : ℤ) : ℝ) * (1/(s-w)).re
  rw [reflEquiv_apply]
  congr 1
  exact (kernel_conj (s := s) (u := w)).symm

/-! ## The cross inequality -/

/-- The ball sum about `0` at radius `R` is dominated by the reflected ball sum (the second half
of the symmetric kernel sum) at any radius `R' ≥ R + 1`. -/
lemma firstSum_le_secondSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) {R R' : ℝ} (hRR : R + 1 ≤ R') :
    firstSum χ s R ≤ secondSum χ s R' := by
  classical
  rw [secondSum_eq_refl]
  refine finsum_le_finsum' (finiteSupport_first χ hχ (s := s) (R := R)) ?_ ?_
  · rw [Function.HasFiniteSupport]
    have hfin : (Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R')) u : ℤ)))).Finite :=
      divisor_hasFiniteSupport χ hχ R'
    refine (hfin.image (reflEquiv : ℂ → ℂ)).subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    refine ⟨reflEquiv w, ?_, ?_⟩
    · rw [Function.mem_support]
      intro h0
      have h0' : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R'))
          (1 - (starRingEnd ℂ) w) = 0 := by
        simpa only [reflEquiv_apply] using h0
      exact hw (by rw [h0']; simp)
    · simp
  · intro w
    show (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) : ℝ) *
        (1/(s-w)).re ≤
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R'))
        (1 - (starRingEnd ℂ) w) : ℤ) : ℝ) * (1/(s-w)).re
    by_cases hD : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) = 0
    · have hD' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) : ℝ) = 0 := by
        rw [hD]; simp
      rw [hD', zero_mul]
      by_cases hE : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R'))
          (1 - (starRingEnd ℂ) w) : ℤ) = 0
      · have hE' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R'))
            (1 - (starRingEnd ℂ) w) : ℤ) : ℝ) = 0 := by rw [hE]; simp
        rw [hE', zero_mul]
      · refine mul_nonneg (divisor_nonneg χ hχ R' _) (le_of_lt ?_)
        have hstrip := re_mem_Ioo_of_divisor_ne_zero χ hχ hχprim hE
        have hw1 : w.re < 1 := by
          have hh : (1 - (starRingEnd ℂ) w).re = 1 - w.re := by simp
          linarith [hstrip.2]
        exact one_div_sub_re_pos hs hw1
    · have hw1 : w ∈ Metric.closedBall (0:ℂ) R := mem_of_divisor_ne_zero hD
      have hw2 : 1 - (starRingEnd ℂ) w ∈ Metric.closedBall (0:ℂ) R' := by
        rw [Metric.mem_closedBall, dist_zero_right] at hw1 ⊢
        have hnorm : ‖1 - (starRingEnd ℂ) w‖ = ‖1 - w‖ := by
          rw [show (1 : ℂ) - (starRingEnd ℂ) w = starRingEnd ℂ (1 - w) from by simp [map_sub]]
          exact Complex.norm_conj _
        calc ‖1 - (starRingEnd ℂ) w‖ = ‖1 - w‖ := hnorm
          _ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_sub_le 1 w
          _ = 1 + ‖w‖ := by simp
          _ ≤ R + 1 := by linarith
          _ ≤ R' := hRR
      have hEq := divisor_refl χ hχ hχprim hw1 hw2
      rw [hEq]

/-! ## The two-fold bound -/

lemma kernSum_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (R : ℝ) :
    kernSum χ s R = firstSum χ s R + secondSum χ s R := by
  have hf : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
        (1/(s-u)).re) := finiteSupport_first χ hχ (s := s) (R := R)
  have hg : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
        (1/((starRingEnd ℂ) s + u - 1)).re) := finiteSupport_second χ hχ (s := s) (R := R)
  have hfun : (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
        ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re)) =
      (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
            (1/(s-u)).re +
          (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
            (1/((starRingEnd ℂ) s + u - 1)).re) := by
    funext u; ring
  rw [show kernSum χ s R = ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
        ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re) from rfl]
  rw [hfun, finsum_add_distrib hf hg]
  simp only [firstSum, secondSum]

/-- `2 * firstSum` is dominated by `2 * Re (Λ'/Λ) + log N`. -/
lemma two_mul_firstSum_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) (R : ℝ) :
    2 * firstSum χ s R ≤ 2 * (logDeriv (completedLFunction χ) s).re + Real.log N := by
  have htend := tendsto_kernSum χ hχ hχprim hs
  have hmono := kernSum_mono χ hχ hχprim hs
  set R' : ℝ := max (R + 1) 0 with hR'def
  have hR' : R + 1 ≤ R' := le_max_left _ _
  have h1 : firstSum χ s R ≤ firstSum χ s R' := firstSum_mono χ hχ hχprim hs (by linarith)
  have h2 : firstSum χ s R ≤ secondSum χ s R' := firstSum_le_secondSum χ hχ hχprim hs hR'
  have h3 : kernSum χ s R' ≤ 2 * (logDeriv (completedLFunction χ) s).re + Real.log N :=
    le_of_monotone_tendsto hmono htend R'
  rw [kernSum_split χ hχ R'] at h3
  linarith

/-! ## The logarithmic derivative bound -/

lemma completedLogDeriv_re_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {σ τ : ℝ} (hσ1 : 1 < σ) (hσ3 : σ ≤ 3) :
    (logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≤
      1 / (σ - 1) + (1/2) * Real.log (2 + |τ|) + 4 := by
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hsdef
  have hsre : 0 < s.re := by rw [hsdef]; simp; linarith
  have hsre1 : 1 < s.re := by rw [hsdef]; simp; linarith
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := s) (Or.inl hχ)
      (le_of_lt hsre1)
  have hdec := Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add
    χ hχ s hsre hLs
  rw [hdec, Complex.add_re]
  have hA : (logDeriv (DirichletCharacter.LFunction χ) s).re ≤ 1 / (σ - 1) + 1 := by
    refine le_trans (logDeriv_LFunction_complex_re_le χ hsre1) ?_
    rw [show s.re = σ by rw [hsdef]; simp]
    rw [Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re σ hσ1]
    exact neg_zeta_logDeriv_re_le σ hσ1 hσ3
  have hB : (logDeriv (DirichletCharacter.gammaFactor χ) s).re ≤
      (1/2) * Real.log (2 + |τ|) + 1 := by
    rw [hsdef]
    exact gammaFactor_logDeriv_re_le_three χ (le_of_lt hσ1) hσ3
  linarith

/-! ## The main theorem -/

/-- Sharp kernel-sum bound: for a primitive non-trivial `χ mod N`, `1 < σ ≤ 3`, `τ ∈ ℝ`
and every `R`, the divisor-weighted sum of `Re (1/(σ+iτ-u))` over the zeros `u` of
`Λ = completedLFunction χ` in the ball of radius `R` is at most
`1/(σ-1) + (1/2) log N + (1/2) log (2+|τ|) + 4`. -/
theorem kernelSumHalf {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ τ : ℝ} (hσ1 : 1 < σ) (hσ3 : σ ≤ 3) :
    ∀ R : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        (1 / ((σ : ℂ) + Complex.I * (τ : ℂ) - u)).re)
      ≤ 1 / (σ - 1) + (1 / 2) * Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 4 := by
  intro R
  change firstSum χ ((σ : ℂ) + Complex.I * (τ : ℂ)) R ≤
    1 / (σ - 1) + (1 / 2) * Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 4
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hsdef
  have hsre : 1 < s.re := by rw [hsdef]; simp; linarith
  have h1 := two_mul_firstSum_le χ hχ hχprim hsre R
  have h2 := completedLogDeriv_re_le (χ := χ) hχ (σ := σ) (τ := τ) hσ1 hσ3
  rw [← hsdef] at h2
  linarith

end Work.ZeroDensity.Jutila
