import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Solutions.iterC_qpow
import Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob
import Submission.Work.TMComp.LocCantor.periodic_defect_bound
import Submission.Work.TMC7Core.Scale.rat_rate_arith

open MeasureTheory

namespace Work.TMC7Core.Scale

noncomputable section

open Work.TMC7Core
open Work.TMComp.LocCantor

/-! ## The Chebyshev bound on powers of an `SL(2,ℝ)`-matrix -/

/-- The Chebyshev polynomial of the second kind evaluated at `t/2` is bounded by
`(n+1) * rhoSL t ^ n`, where `rhoSL t` is the spectral radius of an `SL(2,ℝ)`-matrix of
trace `t`.

If `lam, mu : ℂ` are the roots of `X² - tX + 1` then `U_n(t/2) = ∑_{j≤n} lam^(n-j) mu^j`;
the claim follows since `‖lam‖, ‖mu‖ ≤ rhoSL t ≥ 1`. -/
theorem chebU_eval_abs_le_rhoSL (t : ℝ) (n : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2)| ≤ ((n:ℝ)+1) * rhoSL t ^ n := by
  obtain ⟨w, hw⟩ := (isSquare_iff_exists_sq ((t:ℂ)^2 - 4)).mp (Complex.isSquare _)
  set lam : ℂ := ((t:ℂ)+w)/2 with hlam
  set mu : ℂ := ((t:ℂ)-w)/2 with hmu
  have hsum : lam + mu = (t:ℂ) := by rw [hlam, hmu]; ring
  have hprod : lam * mu = 1 := by
    rw [hlam, hmu, show (((t:ℂ)+w)/2) * (((t:ℂ)-w)/2) = ((t:ℂ)^2 - w^2)/4 by ring, ← hw]
    ring
  have hρeq : max ‖lam‖ ‖mu‖ = rhoSL t := Solutions.max_norm_roots_eq_rhoSL t hsum hprod
  set M : ℝ := max ‖lam‖ ‖mu‖ with hM
  have hM1 : 1 ≤ M := by
    have h : ‖lam‖ * ‖mu‖ = 1 := by rw [← norm_mul, hprod]; simp
    have h1 : ‖lam‖ ≤ M := le_max_left _ _
    have h2 : ‖mu‖ ≤ M := le_max_right _ _
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg lam, norm_nonneg mu]
  set c : ℕ → ℂ := fun k => (((Polynomial.Chebyshev.U ℝ (k:ℤ)).eval (t/2) : ℝ) : ℂ) with hc
  have hc0 : c 0 = 1 := by
    simp only [hc, Nat.cast_zero, Polynomial.Chebyshev.U_zero, Polynomial.eval_one,
      Complex.ofReal_one]
  have hc1 : c 1 = (t:ℂ) := by
    simp only [hc, Nat.cast_one, Polynomial.Chebyshev.U_one, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X]
    push_cast; ring
  have hcrec : ∀ k : ℕ, c (k+2) = (t:ℂ) * c (k+1) - c k := by
    intro k
    simp only [hc]
    have h := Polynomial.Chebyshev.U_add_two ℝ (k:ℤ)
    rw [show ((k:ℤ)+2) = (((k+2:ℕ)):ℤ) by push_cast; ring] at h
    rw [show ((k:ℤ)+1) = (((k+1:ℕ)):ℤ) by push_cast; ring] at h
    have h' := congrArg (fun p : Polynomial ℝ => p.eval (t/2)) h
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat] at h'
    rw [h']; push_cast; ring
  have hrel : ∀ k : ℕ, c (k+1) - lam * c k = mu ^ (k+1) := by
    intro k
    induction k with
    | zero => rw [hc1, hc0, pow_one, ← hsum]; ring
    | succ k ih =>
      rw [hcrec k, ← hsum, pow_succ', ← ih]
      have hmul : mu * lam = 1 := by rw [mul_comm, hprod]
      rw [mul_sub, ← mul_assoc, hmul, one_mul]
      ring
  have hsum_formula : ∀ k : ℕ, c k = ∑ j ∈ Finset.range (k+1), lam^(k-j) * mu^j := by
    intro k
    induction k with
    | zero => rw [hc0]; simp
    | succ k ih =>
      have hstep : c (k+1) = lam * c k + mu^(k+1) := by rw [← hrel k]; ring
      have hA : lam * (∑ j ∈ Finset.range (k+1), lam^(k-j)*mu^j)
          = ∑ j ∈ Finset.range (k+1), lam^(k+1-j)*mu^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [← mul_assoc, ← pow_succ']
        congr 2
        omega
      have hB : lam^(k+1-(k+1)) * mu^(k+1) = mu^(k+1) := by simp
      rw [hstep, ih, hA]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [hB]
  have hbound : ‖c n‖ ≤ ((n:ℝ)+1) * M^n := by
    rw [hsum_formula n]
    have h2 : ∀ j ∈ Finset.range (n+1), ‖lam^(n-j)*mu^j‖ ≤ M^n := by
      intro j hj
      have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [norm_mul, norm_pow, norm_pow]
      have hlam : ‖lam‖^(n-j) ≤ M^(n-j) := pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _
      have hmu : ‖mu‖^j ≤ M^j := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      calc ‖lam‖^(n-j) * ‖mu‖^j
          ≤ M^(n-j) * M^j := mul_le_mul hlam hmu (by positivity)
              (pow_nonneg (by linarith [hM1]) _)
        _ = M^((n-j)+j) := (pow_add M (n-j) j).symm
        _ = M^n := by rw [Nat.sub_add_cancel hjle]
    calc ‖∑ j ∈ Finset.range (n+1), lam^(n-j)*mu^j‖
        ≤ ∑ j ∈ Finset.range (n+1), M^n :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum h2)
      _ = ((n:ℝ)+1) * M^n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  have hcn : ‖c n‖ = |(Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2)| := by
    simp only [hc]
    have h1 : ‖(((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2) : ℝ) : ℂ)‖^2
        = ((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2))^2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    calc ‖(((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2) : ℝ) : ℂ)‖
        = Real.sqrt (‖(((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2) : ℝ) : ℂ)‖^2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2))^2) := by rw [h1]
      _ = |(Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (t/2)| := Real.sqrt_sq_eq_abs _
  rw [hcn, hρeq] at hbound
  exact hbound

/-- For a real `SL(2,ℝ)`-matrix `A` (determinant `1`) and `m ≥ 1`,
`log ‖A ^ m‖_F ≤ m · log (rhoSL (tr A)) + log m + log ‖A‖_F + log 2`,
where the Frobenius norm and the power are taken after complexifying `A`.

This is the quantitative "no super-exponential growth" statement: combining the exact
formula `‖A^m‖_F² = 2 + (‖A‖_F² - 2) · U_{m-1}(tr A / 2)²`
(`Work.TMComp.LocCantor.frob_pow_sl2_rt`) with the Chebyshev bound
`|U_{m-1}(t/2)| ≤ m · rhoSL t ^ (m-1)` (`chebU_eval_abs_le_rhoSL`) gives
`‖A^m‖_F ≤ 2 · m · rhoSL(tr A)^(m-1) · ‖A‖_F`, whose logarithm is the claim. -/
theorem frob_pow_log_growth (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ)
    (hm : 1 ≤ m) :
    Real.log (frob ((A.map Complex.ofRealHom) ^ m))
      ≤ (m : ℝ) * Real.log (rhoSL A.trace) + Real.log (m : ℝ)
        + Real.log (frob (A.map Complex.ofRealHom)) + Real.log 2 := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set ρ : ℝ := rhoSL A.trace with hρdef
  have hρ1 : 1 ≤ ρ := rhoSL_one_le A.trace
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  set F : ℝ := frob (A.map Complex.ofRealHom) with hFdef
  have hFnn : 0 ≤ F := frob_nonneg _
  have hFsq : F^2 = A 0 0^2 + A 0 1^2 + A 1 0^2 + A 1 1^2 := by
    rw [hFdef, show A.map Complex.ofRealHom = A.map (fun x : ℝ => (x:ℂ)) from rfl]
    exact frob_map_ofReal_sq A
  have hF2 : 2 ≤ F^2 := by
    rw [hFsq]
    exact Work.TMComp.LocCantor.two_le_sum_sq_of_det_one A hdet
  have hFpos : 0 < F := by nlinarith [hFnn, hF2]
  have hFm2 : 0 ≤ F^2 - 2 := by linarith
  have hcheb' : |(Polynomial.Chebyshev.U ℝ ((m:ℤ)-1)).eval (A.trace/2)| ≤ (m:ℝ) * ρ^(m-1) := by
    have hidx : ((m:ℤ)-1) = (((m-1:ℕ)):ℤ) := by omega
    rw [hidx, hρdef]
    have h := chebU_eval_abs_le_rhoSL A.trace (m-1)
    have hcast : (((m-1:ℕ):ℝ) + 1) = (m:ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
    rwa [hcast] at h
  have hpow := Work.TMComp.LocCantor.frob_pow_sl2_rt A hdet m hm
  rw [← hFsq] at hpow
  have hPsq : ((Polynomial.Chebyshev.U ℝ ((m:ℤ)-1)).eval (A.trace/2))^2
      ≤ ((m:ℝ)*ρ^(m-1))^2 := by
    have h := abs_le.mp hcheb'
    nlinarith [h.1, h.2]
  have hmρ : 1 ≤ (m:ℝ)^2 * ρ^(2*(m-1)) := by
    have h1 : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith [hm1]
    have h2 : (1:ℝ) ≤ ρ^(2*(m-1)) := one_le_pow₀ hρ1
    nlinarith [h1, h2]
  have hsq : frob ((A.map Complex.ofRealHom)^m)^2 ≤ (2*F*(m:ℝ)*ρ^(m-1))^2 := by
    have hmain : frob ((A.map Complex.ofRealHom)^m)^2
        ≤ 2 + (F^2 - 2) * ((m:ℝ)*ρ^(m-1))^2 := by
      rw [hpow]; nlinarith [hFm2, hPsq]
    have h3 : 2 ≤ (3*F^2+2) * ((m:ℝ)^2 * ρ^(2*(m-1))) := by nlinarith [hF2, hmρ]
    have h4 : (2:ℝ) ≤ (3*F^2+2) * ((m:ℝ)*ρ^(m-1))^2 := by
      have heq : ((m:ℝ)*ρ^(m-1))^2 = (m:ℝ)^2 * ρ^(2*(m-1)) := by
        rw [mul_pow, ← pow_mul]; ring_nf
      rw [heq]; exact h3
    nlinarith [hmain, h4, hF2]
  have hle : frob ((A.map Complex.ofRealHom)^m) ≤ 2*F*(m:ℝ)*ρ^(m-1) := by
    have h0 : (0:ℝ) ≤ 2*F*(m:ℝ)*ρ^(m-1) := by positivity
    calc frob ((A.map Complex.ofRealHom)^m)
        = Real.sqrt (frob ((A.map Complex.ofRealHom)^m)^2) := (Real.sqrt_sq (frob_nonneg _)).symm
      _ ≤ Real.sqrt ((2*F*(m:ℝ)*ρ^(m-1))^2) := Real.sqrt_le_sqrt hsq
      _ = 2*F*(m:ℝ)*ρ^(m-1) := Real.sqrt_sq h0
  have hXpos : 0 < frob ((A.map Complex.ofRealHom)^m) := by
    have h2 : 2 ≤ frob ((A.map Complex.ofRealHom)^m)^2 := by
      rw [hpow]
      nlinarith [mul_nonneg hFm2
        (sq_nonneg ((Polynomial.Chebyshev.U ℝ ((m:ℤ)-1)).eval (A.trace/2)))]
    nlinarith [frob_nonneg ((A.map Complex.ofRealHom)^m)]
  have hlog := Real.log_le_log hXpos hle
  have hlog2 : Real.log (2*F*(m:ℝ)*ρ^(m-1))
      = Real.log 2 + Real.log F + Real.log (m:ℝ) + (((m-1:ℕ)):ℝ)*Real.log ρ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (ne_of_gt hFpos), Real.log_pow]
  rw [hlog2] at hlog
  have hlogρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ1
  have hcast : (((m-1:ℕ)):ℝ) = (m:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
  have hfin : (((m - 1 : ℕ)) : ℝ) * Real.log ρ ≤ (m:ℝ) * Real.log ρ := by
    rw [hcast]; nlinarith [hlogρ]
  have hlogF : Real.log F = Real.log (frob (A.map Complex.ofRealHom)) := by rw [hFdef]
  have hlogρ' : Real.log ρ = Real.log (rhoSL A.trace) := by rw [hρdef]
  rw [hlogF, hlogρ'] at hlog
  linarith [hlog, hfin]

theorem rat_excess_rate_explicit (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (E : ℝ)
    (C₀ : ℝ) (hC₀pos : 0 < C₀)
    (hbound : ∀ (N : ℕ) (x : ℝ), uAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) N x ≤ C₀) :
    ∀ m : ℕ, 1 ≤ m →
      lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) - lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
        ≤ (C₀ * ((q : ℝ) + 1) + 1) * (1 + Real.log ((m : ℝ) * (q : ℝ)))
            / ((m : ℝ) * (q : ℝ)) := by
  intro m hm
  have hqne : ((q : ℕ) : ℝ) ≠ 0 := by positivity
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmqpos : (0 : ℝ) < (m : ℝ) * (q : ℝ) := mul_pos hmpos hqpos
  -- The real trace of the `q`-block is the real part of the complex trace.
  have hTrEq : ∀ x : ℝ, (blk p q lam E x).trace
      = ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re := by
    intro x
    have h := congrArg Complex.re (Solutions.trace_map_ofReal (blk p q lam E x))
    simp only [Complex.ofReal_re] at h
    rw [blk_map p q lam E x] at h
    exact h.symm
  -- continuity of the trace of the complex `q`-step matrix
  have htrace_cont : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.trace) := by
    simp only [Matrix.trace_fin_two]
    fun_prop
  have hcntr : Continuous (fun x : ℝ => (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace) :=
    htrace_cont.comp (continuous_iterC _ _ _ q)
  -- the three integrands
  set g1 : ℝ → ℝ := fun x => Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x))
    with hg1
  set g2 : ℝ → ℝ := fun x => Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x))
    with hg2
  set g3 : ℝ → ℝ := fun x => Real.log (rhoSL ((blk p q lam E x).trace)) with hg3
  have hc1 : Continuous g1 := by
    rw [hg1]; exact Lyap.continuous_log_frob_iterC _ _ _ (m * q)
  have hc2 : Continuous g2 := by
    rw [hg2]; exact Lyap.continuous_log_frob_iterC _ _ _ q
  have hc3 : Continuous g3 := by
    rw [hg3]
    have h : (fun x : ℝ => Real.log (rhoSL ((blk p q lam E x).trace)))
        = fun x : ℝ =>
            Real.log (rhoSL (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)) := by
      funext x; rw [hTrEq x]
    rw [h]
    exact (continuous_rhoSL.comp (Complex.continuous_re.comp hcntr)).log
      (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (rhoSL_one_le _)))
  -- the pointwise bound
  have hpoint : ∀ x : ℝ, g1 x
      ≤ (m : ℝ) * g3 x + Real.log (m : ℝ) + g2 x + Real.log 2 := by
    intro x
    have hP := frob_pow_log_growth (blk p q lam E x) (blk_det p q lam E x) m hm
    rw [blk_map p q lam E x] at hP
    simp only [hg1, hg2, hg3]
    rw [iterC_blk_pow p q hq lam E m x, blk_map p q lam E x]
    exact hP
  -- integrability
  have hi1 : IntervalIntegrable g1 volume (0 : ℝ) 1 := hc1.intervalIntegrable _ _
  have hi2 : IntervalIntegrable g2 volume (0 : ℝ) 1 := hc2.intervalIntegrable _ _
  have hi3 : IntervalIntegrable g3 volume (0 : ℝ) 1 := hc3.intervalIntegrable _ _
  have hia : IntervalIntegrable (fun x : ℝ => (m : ℝ) * g3 x) volume (0 : ℝ) 1 :=
    hi3.const_mul _
  have hib : IntervalIntegrable (fun x : ℝ => (m : ℝ) * g3 x + Real.log (m : ℝ))
      volume (0 : ℝ) 1 := hia.add intervalIntegrable_const
  have hic : IntervalIntegrable (fun x : ℝ => (m : ℝ) * g3 x + Real.log (m : ℝ) + g2 x)
      volume (0 : ℝ) 1 := hib.add hi2
  have hid : IntervalIntegrable
      (fun x : ℝ => (m : ℝ) * g3 x + Real.log (m : ℝ) + g2 x + Real.log 2)
      volume (0 : ℝ) 1 := hic.add intervalIntegrable_const
  -- the integral inequality
  have hInt : (∫ x in (0 : ℝ)..1, g1 x)
      ≤ (m : ℝ) * (∫ x in (0 : ℝ)..1, g3 x) + Real.log (m : ℝ)
        + (∫ x in (0 : ℝ)..1, g2 x) + Real.log 2 := by
    have hmono : (∫ x in (0 : ℝ)..1, g1 x)
        ≤ ∫ x in (0 : ℝ)..1, ((m : ℝ) * g3 x + Real.log (m : ℝ) + g2 x + Real.log 2) :=
      intervalIntegral.integral_mono (by norm_num) hi1 hid hpoint
    rw [intervalIntegral.integral_add hic intervalIntegrable_const,
        intervalIntegral.integral_add hib hi2,
        intervalIntegral.integral_add hia intervalIntegrable_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, intervalIntegral.integral_const] at hmono
    simp only [sub_zero, one_smul] at hmono
    exact hmono
  -- value of the integral of `g3`
  have hg3val : (∫ x in (0 : ℝ)..1, g3 x)
      = (q : ℝ) * lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ) := by
    rw [hg3]
    rw [lam_eq p q hq lam E, one_div]
    rw [← mul_assoc, mul_inv_cancel₀ hqne, one_mul]
  -- value of the integral of `g2`
  have hg2val : (∫ x in (0 : ℝ)..1, g2 x)
      = (q : ℝ) * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q := by
    rw [lyapAvg, ← mul_div_assoc]
    exact (mul_div_cancel_left₀ (∫ x in (0 : ℝ)..1, g2 x) hqne).symm
  -- the average at scale `q` is bounded by `C₀`
  have hqC₀ : lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q ≤ C₀ := by
    rw [lyapAvg_eq_integral_uAvg]
    have hcont : Continuous (fun x : ℝ => uAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) := by
      simp only [uAvg]
      exact (Lyap.continuous_log_frob_iterC _ _ _ q).div_const _
    have hint1 : IntervalIntegrable
        (fun x : ℝ => uAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) volume (0 : ℝ) 1 :=
      hcont.intervalIntegrable 0 1
    have hint2 : IntervalIntegrable (fun _ : ℝ => C₀) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hmono : (∫ x in (0 : ℝ)..1, uAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x)
        ≤ ∫ x in (0 : ℝ)..1, C₀ :=
      intervalIntegral.integral_mono (by norm_num) hint1 hint2 (fun x => hbound q x)
    have h2 : (∫ x in (0 : ℝ)..1, C₀) = C₀ := by
      rw [intervalIntegral.integral_const]; ring
    rwa [h2] at hmono
  -- combine
  have hkey : (∫ x in (0 : ℝ)..1, g1 x)
      ≤ (m : ℝ) * (q : ℝ) * lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
        + Real.log (m : ℝ) + (q : ℝ) * C₀ + Real.log 2 := by
    rw [hg3val, hg2val] at hInt
    have h2 : (q : ℝ) * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q ≤ (q : ℝ) * C₀ :=
      mul_le_mul_of_nonneg_left hqC₀ (le_of_lt hqpos)
    nlinarith [hInt, h2]
  have hmain : lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
        - lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
      ≤ (Real.log (m : ℝ) + (q : ℝ) * C₀ + Real.log 2) / ((m : ℝ) * (q : ℝ)) := by
    have hval : lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
        = (∫ x in (0 : ℝ)..1, g1 x) / ((m : ℝ) * (q : ℝ)) := by
      rw [hg1, lyapAvg]
      congr 1
      push_cast
      ring
    have heq : (∫ x in (0 : ℝ)..1, g1 x) / ((m : ℝ) * (q : ℝ))
          - lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
        = ((∫ x in (0 : ℝ)..1, g1 x)
            - ((m : ℝ) * (q : ℝ)) * lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ))
          / ((m : ℝ) * (q : ℝ)) := by
      rw [sub_div]
      congr 1
      rw [mul_div_cancel_left₀ _ (ne_of_gt hmqpos)]
    rw [hval, heq]
    exact div_le_div_of_nonneg_right (by linarith [hkey]) (le_of_lt hmqpos)
  calc lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
        - lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
      ≤ (Real.log (m : ℝ) + (q : ℝ) * C₀ + Real.log 2) / ((m : ℝ) * (q : ℝ)) := hmain
    _ ≤ ((C₀ * ((q : ℝ) + 1) + 1) * (1 + Real.log ((m : ℝ) * (q : ℝ))))
          / ((m : ℝ) * (q : ℝ)) :=
        div_le_div_of_nonneg_right
          (rat_rate_arith C₀ (q : ℝ) (m : ℝ) hC₀pos (by exact_mod_cast hq)
            (by exact_mod_cast hm))
          (le_of_lt hmqpos)

end

end Work.TMC7Core.Scale
