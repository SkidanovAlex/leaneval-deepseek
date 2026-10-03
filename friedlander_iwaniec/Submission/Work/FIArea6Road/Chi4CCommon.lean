/-
# Common facts about the `L`-function of the character `χ₄` (mod 4)

Interface file for the development of `Work.FIArea6Road.Lchi4InvSharp`.  It collects

* the character-theoretic facts about `Work.FIArea6Hecke.R.chi4C` (non-trivial, odd, primitive);
* the bound on the real part of the log-derivative of the archimedean factor `gammaFactor χ₄`;
* the (public copy of the) Hadamard partial fraction for the completed `L`-function;
* the elementary lower bound `1/‖L(σ+it,χ)‖ ≤ 1 + 1/(σ-1)` for `1 < σ ≤ 2`;
* the specialisation of the uniform zero-free region to `χ₄`;
* the one-sided bound at `Re s = 2`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.Sharp.Chi4LSeriesOffAxisLogDerivReBound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ZetaValues
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight
import Submission.Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Road

open Complex Filter Metric
open scoped BigOperators Topology

noncomputable section

/-! ## Character-theoretic facts -/

lemma chi4C_apply_three : Work.FIArea6Hecke.R.chi4C (3 : ZMod 4) = -1 := by
  have h : ZMod.χ₄ (3 : ZMod 4) = (-1 : ℤ) := by decide
  simp only [Work.FIArea6Hecke.R.chi4C, MulChar.ringHomComp_apply, h]
  norm_num

lemma chi4C_ne_one : Work.FIArea6Hecke.R.chi4C ≠ (1 : DirichletCharacter ℂ 4) := by
  intro h
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  rw [chi4C_apply_three] at h3
  have h1u : IsUnit (3 : ZMod 4) := by
    have h : (3 : ZMod 4) = -1 := by decide
    rw [h]; exact isUnit_one.neg
  rw [MulChar.one_apply h1u] at h3
  norm_num at h3

lemma chi4C_odd : Work.FIArea6Hecke.R.chi4C.Odd := by
  rw [DirichletCharacter.Odd]
  have h : ((-1 : ZMod 4)) = 3 := by decide
  rw [h]
  exact chi4C_apply_three

theorem chi4C_isPrimitive : Work.FIArea6Hecke.R.chi4C.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : Work.FIArea6Hecke.R.chi4C.conductor ∣ 4 :=
    DirichletCharacter.conductor_dvd_level _
  have hne1 : Work.FIArea6Hecke.R.chi4C.conductor ≠ 1 := by
    intro h
    have : Work.FIArea6Hecke.R.chi4C = (1 : DirichletCharacter ℂ 4) :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h
    exact chi4C_ne_one this
  have hne2 : Work.FIArea6Hecke.R.chi4C.conductor ≠ 2 := by
    intro h
    have hfac : DirichletCharacter.FactorsThrough Work.FIArea6Hecke.R.chi4C 2 := by
      rw [← h]; exact DirichletCharacter.conductor_mem_conductorSet _
    obtain ⟨hd, χ₀, hχ⟩ := hfac
    have h1 : (DirichletCharacter.changeLevel hd χ₀) ((3 : ℤ) : ZMod 4)
        = χ₀ ((3 : ℤ) : ZMod 2) :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := χ₀) hd (by norm_num)
    have h2 : χ₀ (((3 : ℤ)) : ZMod 2) = (1 : ℂ) := by
      have : (((3 : ℤ)) : ZMod 2) = 1 := by decide
      rw [this, MulChar.map_one]
    have h3 : Work.FIArea6Hecke.R.chi4C (3 : ZMod 4) = 1 := by
      rw [hχ]; exact h1.trans h2
    rw [chi4C_apply_three] at h3
    norm_num at h3
  obtain ⟨n, hn, hc⟩ : ∃ n ≤ 2, Work.FIArea6Hecke.R.chi4C.conductor = 2 ^ n :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num)).mp (by simpa using hdvd)
  interval_cases n
  · exact absurd hc hne1
  · exact absurd hc hne2
  · rw [hc]; norm_num

/-! ## The archimedean factor -/

/-- The real part of the log-derivative of the archimedean factor of `χ₄` is `O(log(|t|+2))`
uniformly on the strip `0 ≤ Re s ≤ 2`. -/
theorem gammaFactor_chi4C_logDeriv_re_abs_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 2 →
      |(logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C)
        ((σ : ℂ) + (t : ℂ) * Complex.I)).re| ≤ C * Real.log (4 * (|t| + 2)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro σ t hσ0 hσ2
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hs1re : 0 < (s + 1).re := by rw [hs]; simp [Complex.add_re]; linarith
  set L : ℝ := Real.log (4 * (|t| + 2)) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hLge : (2 : ℝ) ≤ L := by
    rw [hL]
    have hexp : Real.exp 2 ≤ 4 * (|t| + 2) := by
      have h8 : Real.exp 2 < 8 := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      have h2 : (8 : ℝ) ≤ 4 * (|t| + 2) := by linarith [abs_nonneg t]
      linarith
    have := Real.log_le_log (Real.exp_pos 2) hexp
    rwa [Real.log_exp] at this
  have hlogpi0 : (0 : ℝ) ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogpi2 : Real.log Real.pi ≤ 2 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  -- rewrite the archimedean factor through `Gammaℝ (s+1)`
  have hfun : DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C
      = fun z : ℂ => Complex.Gammaℝ (z + 1) :=
    funext (DirichletCharacter.Odd.gammaFactor_def chi4C_odd)
  rw [hfun]
  have hld : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s
      = logDeriv Complex.Gammaℝ (s + 1) := by
    have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) :=
      Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ (s + 1) hs1re
    have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
    have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
    have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
    rw [hder] at h
    simpa [Function.comp_def, mul_comm] using h
  rw [hld, Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_formula (s + 1) hs1re]
  set z : ℂ := (s + 1) / 2 with hz
  have hzre : z.re = (σ + 1) / 2 := by rw [hz, hs]; simp [Complex.add_re]
  have hzim : z.im = t / 2 := by rw [hz, hs]; simp [Complex.add_im]
  have hψ : ‖Complex.digamma z‖ ≤ Real.log (2 + |t / 2|) + 2 := by
    have hx1 : (1 : ℝ) / 2 ≤ z.re := by rw [hzre]; linarith
    have hx2 : z.re ≤ 8 := by rw [hzre]; linarith
    have h0 : ‖Complex.digamma z‖ ≤ Real.log (2 + |z.im|) + 2 := by
      have h1 := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le z.re z.im hx1 hx2
      rwa [Complex.re_add_im] at h1
    rw [hzim] at h0
    exact h0
  have hlogt : Real.log (2 + |t / 2|) ≤ L := by
    rw [hL]
    apply Real.log_le_log (by positivity)
    have h2 : |t / 2| ≤ |t| := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith [abs_nonneg t]
    linarith [abs_nonneg t, h2]
  have hsplit : (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma z / 2).re
      = -(Real.log Real.pi) / 2 + (Complex.digamma z).re / 2 := by
    have hlogR : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
      (Complex.ofReal_log (x := Real.pi) (le_of_lt Real.pi_pos)).symm
    rw [hlogR, Complex.add_re, Commons.NumberTheory.DirichletCharacter.re_div_two,
      Commons.NumberTheory.DirichletCharacter.re_div_two, Complex.neg_re, Complex.ofReal_re]
  rw [hsplit]
  have hψre : |(Complex.digamma z).re| ≤ Real.log (2 + |t / 2|) + 2 :=
    le_trans (abs_re_le_norm _) hψ
  have hlo := (abs_le.mp hψre).1
  have hhi := (abs_le.mp hψre).2
  have h4 : Real.log (2 + |t / 2|) + 2 ≤ 2 * L := by linarith
  rw [abs_le]
  constructor
  · have h1 : -(Real.log Real.pi) / 2 ≥ -1 := by linarith
    have h2 : (Complex.digamma z).re / 2 ≥ -L := by linarith
    linarith
  · have h1 : (Complex.digamma z).re / 2 ≤ L := by linarith
    have h2 : -(Real.log Real.pi) / 2 ≤ 0 := by linarith
    linarith

/-! ## The partial fraction of the completed `L`-function -/

/-- Hadamard partial fraction for the completed `L`-function: the logarithmic derivative is the
limit of the sum of the kernels `1/(s-u) - 1/(s₁-u)` against the divisor of zeros. -/
theorem completedL_pf_diff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s s₁ : ℂ)
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hs₁ : DirichletCharacter.completedLFunction χ s₁ ≠ 0) :
    Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u)))
      atTop (nhds (logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) s₁)) := by
  have h1 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hs
  have h2 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s₁ hs₁
  have hsub := h1.sub h2
  have hgoal : (deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
          DirichletCharacter.completedLFunction χ 0) -
      (deriv (DirichletCharacter.completedLFunction χ) s₁ /
          DirichletCharacter.completedLFunction χ s₁ -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
          DirichletCharacter.completedLFunction χ 0) =
      deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) s₁ /
          DirichletCharacter.completedLFunction χ s₁ := by ring
  simp only [logDeriv_apply]
  rw [← hgoal]
  refine hsub.congr' ?_
  filter_upwards with R
  have hfs : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  have hfs₁ : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s₁ - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  rw [← finsum_sub_distrib hfs hfs₁]
  exact finsum_congr fun u => by ring

/-! ## The elementary upper bound for `1/‖L‖` on `Re s > 1` -/

/-- For `1 < σ ≤ 2`, `1/‖L(σ+it,χ)‖ ≤ 1 + 1/(σ-1)`, from the Möbius-series representation of
`1/L` and the trivial bound `Σ_{n} n^{-σ} ≤ 1 + 1/(σ-1)`. -/
theorem LFunction_inv_le_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ t : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    1 / ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 + 1 / (σ - 1) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : 1 < s.re := by rw [hs]; simp; exact hσ
  have hsumμ : LSeriesSummable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsre
  have hsumg : LSeriesSummable
      ((fun n : ℕ => χ (n : ZMod N)) * (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))) s :=
    DirichletCharacter.LSeriesSummable_mul (χ := χ) hsumμ
  have hprod := DirichletCharacter.LSeries.mul_mu_eq_one (χ := χ) hsre
  have hL : DirichletCharacter.LFunction χ s = LSeries (fun n : ℕ => χ (n : ZMod N)) s :=
    DirichletCharacter.LFunction_eq_LSeries χ hsre
  have hdiff : ‖DirichletCharacter.LFunction χ s‖ *
      ‖LSeries ((fun n : ℕ => χ (n : ZMod N)) *
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))) s‖ = 1 := by
    rw [hL, ← norm_mul, hprod, norm_one]
  set g : ℕ → ℂ := (fun n : ℕ => χ (n : ZMod N)) *
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) with hg
  have hgnorm : ‖LSeries g s‖ ≤ 1 + 1 / (s.re - 1) := by
    have hsummable_norm : Summable (fun n : ℕ => ‖LSeries.term g s n‖) := hsumg.norm
    have hsummable_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hterm : ∀ n : ℕ, ‖LSeries.term g s n‖ ≤ (n : ℝ) ^ (-s.re) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term_zero, Real.zero_rpow (by linarith : (-s.re) ≠ 0)]
      · rw [LSeries.norm_term_eq, if_neg hn]
        have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hgn : ‖g n‖ ≤ 1 := by
          rw [hg, Pi.mul_apply, norm_mul]
          refine mul_le_one₀ (DirichletCharacter.norm_le_one χ (n : ZMod N)) (norm_nonneg _) ?_
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hpos : (0:ℝ) < (n:ℝ) ^ s.re := Real.rpow_pos_of_pos hn1 _
        rw [Real.rpow_neg hn1.le s.re, div_le_iff₀ hpos, inv_mul_cancel₀ hpos.ne']
        exact hgn
    calc ‖LSeries g s‖ = ‖∑' n : ℕ, LSeries.term g s n‖ := by rw [LSeries]
      _ ≤ ∑' n : ℕ, ‖LSeries.term g s n‖ := norm_tsum_le_tsum_norm hsummable_norm
      _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) :=
            Summable.tsum_le_tsum hterm hsummable_norm hsummable_rpow
      _ ≤ 1 + 1 / (s.re - 1) := Commons.NumberTheory.LSeries.tsum_nat_rpow_neg_le_inv s.re hsre
  have hnormpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction χ s)) with h | h
    · rw [← h, zero_mul] at hdiff; norm_num at hdiff
    · exact h
  have hkey : 1 / ‖DirichletCharacter.LFunction χ s‖ = ‖LSeries g s‖ := by
    rw [div_eq_iff hnormpos.ne']
    rw [mul_comm]; exact hdiff.symm
  rw [hkey]
  have hsre' : s.re = σ := by rw [hs]; simp
  simpa only [hsre'] using hgnorm

/-! ## The zero-free region for `χ₄` -/

/-- Uniform zero-free region for the `L`-function of `χ₄`, off the real axis. -/
theorem chi4C_zeroFree_offAxis :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ |t| →
      1 - c / Real.log (4 * (|t| + 2)) ≤ σ → σ ≤ 2 →
        DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c, hc, h⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  refine ⟨c, hc, ?_⟩
  intro σ t ht hσ hσ2
  refine h (N := 4) Work.FIArea6Hecke.R.chi4C chi4C_isPrimitive chi4C_ne_one σ t ?_ hσ
  intro h0
  rw [h0] at ht
  norm_num at ht

/-! ## The one-sided bound at `Re s = 2` -/

/-- `Re (Λ'/Λ)(2 + it) ≥ -C·log(4(|t|+2))` for the completed `L`-function of `χ₄`. -/
theorem completedL_logDeriv_re_at_two_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      -(C * Real.log (4 * (|t| + 2))) ≤
        (logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          ((2 : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨Cg, hCg, hgbf⟩ := gammaFactor_chi4C_logDeriv_re_abs_le
  obtain ⟨CL, hCL, hLb⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re
  refine ⟨CL + Cg + 1, by linarith, ?_⟩
  intro t
  set T : ℝ := Real.log (4 * (|t| + 2)) with hT
  have hTpos : 0 < T := by rw [hT]; exact Real.log_pos (by linarith [abs_nonneg t])
  set s : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : 1 < s.re := by rw [hs]; simp
  have hsre0 : 0 < s.re := by linarith
  have hLs : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _
      (Or.inl chi4C_ne_one) (le_of_lt hsre)
  have hdec := Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add
    Work.FIArea6Hecke.R.chi4C chi4C_ne_one s hsre0 hLs
  have hLbd : ‖logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s‖ ≤ 1 + CL := by
    have h := hLb 4 Work.FIArea6Hecke.R.chi4C s hsre
    have h1 : 1 / (s.re - 1) = 1 := by rw [hs]; norm_num
    rw [h1] at h
    linarith
  have hg : |(logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s).re|
      ≤ Cg * T := by
    have h := hgbf 2 t (by norm_num) (by norm_num)
    have hs' : s = (2 : ℂ) + (t : ℂ) * Complex.I := hs
    rw [hs', hT]
    exact h
  have hre : (logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s).re
      = (logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s).re
        + (logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s).re := by
    rw [hdec, Complex.add_re]
  rw [hre]
  have h1 : -(1 + CL) ≤ (logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s).re := by
    have h := Complex.re_le_norm
      (-(logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s))
    rw [Complex.neg_re, norm_neg] at h
    linarith [hLbd, h]
  have h2 : -(Cg * T) ≤
      (logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s).re := by
    have := (abs_le.mp hg).1
    linarith
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hT]; exact Real.le_log_iff_exp_le (by linarith [abs_nonneg t]) |>.mpr (by
      have : Real.exp 1 < 8 := lt_trans Real.exp_one_lt_three (by norm_num)
      linarith [abs_nonneg t])
  have h3 : -(CL + Cg + 1) * T ≤ -(1 + CL) + -(Cg * T) := by
    nlinarith [hT1, hTpos, hCL, hCg]
  linarith [h1, h2, h3]

end

end Work.FIArea6Road
