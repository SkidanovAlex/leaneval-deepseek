import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.char_large_sieve_twisted_rpow
import Submission.Commons.Analysis.Integral.inv_sqrt_sq_sum_integral_le

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators Interval

noncomputable section

open Classical MeasureTheory

/-- The norm of `c + i t` for real `c`, `t`. -/
lemma norm_add_mul_I_sq (c t : ℝ) :
    ‖(c : ℂ) + (t : ℂ) * Complex.I‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
  have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp [Complex.add_re, Complex.mul_re]
  have him : ((c : ℂ) + (t : ℂ) * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_im]
  have hsq : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Continuity in `t` of the Dirichlet--twisted exponential sum. -/
lemma continuous_twistSum (M : ℕ) (a : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℝ) :
    Continuous (fun t : ℝ => ∑ m ∈ Finset.Icc 1 M,
      a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) := by
  refine continuous_finsetSum _ (fun m hm => ?_)
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hterm : Continuous (fun t : ℝ => ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) := by
    have hfun : (fun t : ℝ => ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
        = fun t : ℝ => (m : ℂ) ^ (-(c : ℂ)) *
            Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) := by
      funext t
      exact twist_cpow_neg_add_mul_I m hm1 c t
    rw [hfun]
    fun_prop
  exact Continuous.mul (continuous_const.mul continuous_const) hterm

/-- The set of primitive Dirichlet characters modulo `q`. -/
private def chiSet (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  @Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ

private def cq (q : ℕ) : ℝ := (q : ℝ) / (q.totient : ℝ)

private def SM (M : ℕ) (a : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))

private def SN (N : ℕ) (b : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))

private def wInt (M N : ℕ) (a b : ℕ → ℂ) (c : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ‖SM M a q χ c t * SN N b q χ c t‖ / ‖(c : ℂ) + (t : ℂ) * Complex.I‖

private lemma continuous_SM (M : ℕ) (a : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℝ) :
    Continuous (fun t : ℝ => SM M a q χ c t) := by
  simp only [SM]
  exact continuous_twistSum M a q χ c

private lemma continuous_SN (N : ℕ) (b : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℝ) :
    Continuous (fun t : ℝ => SN N b q χ c t) := by
  simp only [SN]
  exact continuous_twistSum N b q χ c

private lemma continuous_norm_denom (c : ℝ) :
    Continuous (fun t : ℝ => ‖(c : ℂ) + (t : ℂ) * Complex.I‖) := by
  apply Continuous.norm
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

private lemma norm_denom_pos (c : ℝ) (hc : 0 < c) (t : ℝ) :
    0 < ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
  rw [norm_add_mul_I_sq]
  apply Real.sqrt_pos.mpr
  have : 0 < c ^ 2 := by positivity
  nlinarith [sq_nonneg t]

private lemma continuous_wInt (M N : ℕ) (a b : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => wInt M N a b c q χ t) := by
  simp only [wInt]
  exact Continuous.div ((continuous_SM M a q χ c).mul (continuous_SN N b q χ c)).norm
    (continuous_norm_denom c) (fun t => ne_of_gt (norm_denom_pos c hc t))

theorem bilinear_main_term_integral :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q M N : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hN : 1 ≤ N)
      (c : ℝ) (hc : 0 < c) (a b : ℕ → ℂ),
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                  (Classical.decPred _) Finset.univ),
            (∫ t in (-((M : ℝ) * (N : ℝ)))..((M : ℝ) * (N : ℝ)),
              ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) *
               (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))‖
              / ‖(c : ℂ) + (t : ℂ) * Complex.I‖))
      ≤ C * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
          Real.log (2 * ((M : ℝ) * (N : ℝ)) / c + 2) := by
  classical
  obtain ⟨C0, hC0pos, hC0bound⟩ := Commons.Analysis.Integral.inv_sqrt_sq_sum_integral_le
  refine ⟨C0, hC0pos, ?_⟩
  intro Q M N hQ hM hN c hc a b
  set T : ℝ := (M : ℝ) * (N : ℝ) with hT
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hT]
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [hM1, hN1]
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hab : -T ≤ T := by linarith
  -- Rewrite the goal with the abbreviations.
  change (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q,
      ∫ t in (-T)..T, wInt M N a b c q χ t) ≤
    C0 * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
      Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
      Real.log (2 * T / c + 2)
  have hwint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntervalIntegrable (wInt M N a b c q χ) volume (-T) T :=
    fun q χ => (continuous_wInt M N a b c hc q χ).intervalIntegrable (-T) T
  -- Fubini: swap the finite sums with the interval integral.
  have hstep1 : (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q,
        ∫ t in (-T)..T, wInt M N a b c q χ t)
      = ∑ q ∈ Finset.Icc 1 Q, cq q * ∫ t in (-T)..T, ∑ χ ∈ chiSet q, wInt M N a b c q χ t := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (s := chiSet q)
      (f := fun χ t => wInt M N a b c q χ t) (fun χ hχ => hwint q χ)]
  have hstep2 : (∑ q ∈ Finset.Icc 1 Q, cq q * ∫ t in (-T)..T, ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      = ∑ q ∈ Finset.Icc 1 Q, ∫ t in (-T)..T, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul]
  have hii : ∀ q ∈ Finset.Icc 1 Q,
      IntervalIntegrable (fun t : ℝ => cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t) volume (-T) T := by
    intro q hq
    simpa only [Finset.sum_apply] using
      IntervalIntegrable.const_mul (IntervalIntegrable.sum (chiSet q) (fun χ hχ => hwint q χ)) (cq q)
  have hstep3 : (∑ q ∈ Finset.Icc 1 Q, ∫ t in (-T)..T, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      = ∫ t in (-T)..T, ∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t :=
    (intervalIntegral.integral_finsetSum (s := Finset.Icc 1 Q)
      (f := fun q t => cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t) hii).symm
  have hLHS : (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q,
        ∫ t in (-T)..T, wInt M N a b c q χ t)
      = ∫ t in (-T)..T, ∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t :=
    hstep1.trans (hstep2.trans hstep3)
  rw [hLHS]
  -- Pointwise bound at each `t`.
  have hkey : ∀ t : ℝ, (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      = (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, ‖SM M a q χ c t * SN N b q χ c t‖)
          / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    intro t
    calc (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
        = ∑ q ∈ Finset.Icc 1 Q, (cq q * ∑ χ ∈ chiSet q,
            ‖SM M a q χ c t * SN N b q χ c t‖) * (‖(c : ℂ) + (t : ℂ) * Complex.I‖)⁻¹ := by
          apply Finset.sum_congr rfl
          intro q hq
          simp only [wInt, div_eq_mul_inv]
          rw [← Finset.sum_mul, mul_assoc]
      _ = (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q,
            ‖SM M a q χ c t * SN N b q χ c t‖) * (‖(c : ℂ) + (t : ℂ) * Complex.I‖)⁻¹ := by
          rw [← Finset.sum_mul]
      _ = (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q,
            ‖SM M a q χ c t * SN N b q χ c t‖) / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
          rw [div_eq_mul_inv]
  have hbdd : ∀ t : ℝ, (∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      ≤ (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2))
        / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    intro t
    rw [hkey t]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact char_large_sieve_twisted_rpow Q M N hQ c hc a b t
  have hint1 : IntervalIntegrable
      (fun t : ℝ => ∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      volume (-T) T := by
    have h := IntervalIntegrable.sum (Finset.Icc 1 Q) (fun q hq => hii q hq)
    have hfun : (∑ i ∈ Finset.Icc 1 Q,
          (fun t : ℝ => cq i * ∑ χ ∈ chiSet i, wInt M N a b c i χ t))
        = (fun t : ℝ => ∑ i ∈ Finset.Icc 1 Q, cq i * ∑ χ ∈ chiSet i, wInt M N a b c i χ t) := by
      funext t
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2))
        / ‖(c : ℂ) + (t : ℂ) * Complex.I‖) volume (-T) T :=
    (Continuous.div continuous_const (continuous_norm_denom c)
      (fun t => ne_of_gt (norm_denom_pos c hc t))).intervalIntegrable (-T) T
  have hmono : (∫ t in (-T)..T, ∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      ≤ ∫ t in (-T)..T, (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2))
        / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ :=
    intervalIntegral.integral_mono hab hint1 hint2 hbdd
  have hconst : (∫ t in (-T)..T, (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2))
        / ‖(c : ℂ) + (t : ℂ) * Complex.I‖)
      = (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) *
        ∫ t in (-T)..T, 1 / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [div_eq_mul_inv, one_mul]
  have hnorm : (∫ t in (-T)..T, 1 / ‖(c : ℂ) + (t : ℂ) * Complex.I‖)
      = ∫ t in (-T)..T, 1 / Real.sqrt (c ^ 2 + t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [norm_add_mul_I_sq]
  have hint3 : (∫ t in (-T)..T, 1 / Real.sqrt (c ^ 2 + t ^ 2))
      ≤ C0 * Real.log (2 * T / c + 2) := hC0bound c T hc hT1
  calc (∫ t in (-T)..T, ∑ q ∈ Finset.Icc 1 Q, cq q * ∑ χ ∈ chiSet q, wInt M N a b c q χ t)
      ≤ ∫ t in (-T)..T, (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2))
        / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := hmono
    _ = (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) *
        ∫ t in (-T)..T, 1 / ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := hconst
    _ = (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) *
        ∫ t in (-T)..T, 1 / Real.sqrt (c ^ 2 + t ^ 2) := by rw [hnorm]
    _ ≤ (Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) *
        (C0 * Real.log (2 * T / c + 2)) :=
        mul_le_mul_of_nonneg_left hint3 (by positivity)
    _ = C0 * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
          Real.log (2 * T / c + 2) := by ring

end

end Commons.NumberTheory.BombieriVinogradov
