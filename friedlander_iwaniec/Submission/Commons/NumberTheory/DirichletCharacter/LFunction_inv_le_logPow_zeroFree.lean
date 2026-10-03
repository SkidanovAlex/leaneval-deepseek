import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

/-- For `1 < σ ≤ 2` the Dirichlet `L`-function is bounded below by `(σ-1)/2`:
`1/L(σ+it) = Σ_n μ(n)χ(n) n^{-σ-it}`, and the tail sum is bounded by the `p`-series
`Σ n^{-σ} ≤ 1 + 1/(σ-1)`. -/
private lemma norm_LFunction_ge_near_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    (s.re - 1) / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hsumμ : LSeriesSummable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hsumg : LSeriesSummable
      ((fun n : ℕ => χ (n : ZMod N)) * (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))) s :=
    DirichletCharacter.LSeriesSummable_mul (χ := χ) hsumμ
  have hprod := DirichletCharacter.LSeries.mul_mu_eq_one (χ := χ) hs
  have hL : DirichletCharacter.LFunction χ s = LSeries (fun n : ℕ => χ (n : ZMod N)) s :=
    DirichletCharacter.LFunction_eq_LSeries χ hs
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
      _ ≤ 1 + 1 / (s.re - 1) := Commons.NumberTheory.LSeries.tsum_nat_rpow_neg_le_inv s.re hs
  have hgpos : 0 < ‖LSeries g s‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (LSeries g s)) with h | h
    · rw [← h, mul_zero] at hdiff; norm_num at hdiff
    · exact h
  have hLval : ‖DirichletCharacter.LFunction χ s‖ = 1 / ‖LSeries g s‖ := by
    rw [eq_div_iff hgpos.ne']
    linarith [hdiff]
  rw [hLval]
  have hthis : ‖LSeries g s‖ ≤ s.re / (s.re - 1) := by
    have h1 : 1 + 1/(s.re - 1) = s.re/(s.re - 1) := by
      have hne : s.re - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [← h1]; exact hgnorm
  have hge : 1 / (s.re / (s.re - 1)) ≤ 1 / ‖LSeries g s‖ :=
    one_div_le_one_div_of_le hgpos hthis
  have hsimp : 1 / (s.re / (s.re - 1)) = (s.re - 1)/s.re := by rw [one_div_div]
  rw [hsimp] at hge
  have h2 : (s.re - 1)/s.re ≥ (s.re - 1)/2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) hs2
  linarith

theorem LFunction_inv_le_logPow_zeroFree {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ t : ℝ, 1 ≤ |t| →
      1 - c / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ → σ ≤ 2 →
        1 / ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (Real.log ((N : ℝ) * (|t| + 2)) + 1) ^ C := by
  obtain ⟨cz, hczpos, hzfr⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  set δ : ℝ := min cz 1 / 8 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 / 8 := by
    rw [hδdef]; have : min cz 1 ≤ 1 := min_le_right _ _; linarith
  have h8δ : 8 * δ ≤ cz := by
    rw [hδdef]; have : min cz 1 ≤ cz := min_le_left _ _; linarith
  set K₀ : ℝ := Real.log (160000 / δ) / Real.log 2 with hK₀def
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2nonneg : 0 ≤ Real.log 2 := le_of_lt hlog2pos
  have hK₀nonneg : 0 ≤ K₀ := by
    rw [hK₀def]
    apply div_nonneg _ hlog2pos.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hδpos]; nlinarith [hδle]
  set Ck : ℝ := max (8 / δ) (max (1 + (18/7) * (K₀ + 2)) 1) with hCkdef
  have hCkpos : 0 < Ck := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCk8 : 8 / δ ≤ Ck := le_max_left _ _
  have hCkK : 1 + (18/7) * (K₀ + 2) ≤ Ck :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCk1 : (1:ℝ) ≤ Ck := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨δ, Ck, hδpos, hCkpos, ?_⟩
  intro σ t ht hσ hσ2
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  set ℓ : ℝ := Real.log ((N : ℝ) * (|t| + 2)) with hℓdef
  set ℓ₂ : ℝ := ℓ + 1 with hℓ₂def
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hlog3 : Real.log 3 ≤ ℓ := by
    rw [hℓdef]
    apply Real.log_le_log (by norm_num)
    have h3 : (3:ℝ) ≤ |t| + 2 := by linarith [ht]
    calc (3:ℝ) = 1 * 3 := by ring
      _ ≤ (N:ℝ) * (|t| + 2) := by
            apply mul_le_mul <;> linarith [abs_nonneg t]
  have hℓgt1 : 1 < ℓ := by
    have h4 : (1:ℝ) < Real.log 3 := by
      have h5 : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h5
    linarith
  have hℓ₂2 : 2 ≤ ℓ₂ := by rw [hℓ₂def]; linarith
  have hℓ₂pos : 0 < ℓ₂ := by linarith
  have hℓ₂_one : (1:ℝ) ≤ ℓ₂ := by linarith
  have hℓ_le : ℓ ≤ ℓ₂ := by rw [hℓ₂def]; linarith
  have hℓ₂_le : ℓ₂ ≤ 2 * ℓ := by rw [hℓ₂def]; linarith
  have hlogℓ₂ : Real.log 2 ≤ Real.log ℓ₂ := Real.log_le_log (by norm_num) hℓ₂2
  have hlogℓ₂pos : 0 < Real.log ℓ₂ := Real.log_pos (by linarith)
  have hlogℓ₂nonneg : 0 ≤ Real.log ℓ₂ := le_of_lt hlogℓ₂pos
  set x : ℝ := δ / (4 * ℓ₂) with hxdef
  set Rc : ℝ := 4 * δ / ℓ₂ with hRcdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hRcpos : 0 < Rc := by rw [hRcdef]; positivity
  have hRcle : Rc ≤ 1 / 4 := by
    rw [hRcdef, div_le_iff₀ hℓ₂pos]; nlinarith [hδle]
  have hxle : x ≤ 1 / 8 := by
    rw [hxdef, div_le_iff₀ (by positivity : (0:ℝ) < 4 * ℓ₂)]
    nlinarith [hδle, hℓ₂2]
  have hxRcle : x + Rc ≤ 1 / 2 := by linarith
  -- δ/ℓ₂ multiples
  have hxℓ₂ : x * ℓ₂ = δ / 4 := by rw [hxdef]; field_simp
  have hRcℓ₂ : Rc * ℓ₂ = 4 * δ := by rw [hRcdef]; field_simp
  rcases le_or_gt (1 + x) σ with hcase | hcase
  · -- Case 1: σ ≥ 1 + x.  Use the series bound.
    have hs1 : 1 < s.re := by rw [hsre]; linarith
    have hs2 : s.re ≤ 2 := by rw [hsre]; linarith
    have hlow := norm_LFunction_ge_near_one χ (s := s) hs1 hs2
    rw [hsre] at hlow
    have hstep1 : 1 / ‖DirichletCharacter.LFunction χ s‖ ≤ 2 / (σ - 1) := by
      have h := one_div_le_one_div_of_le (by linarith : (0:ℝ) < (σ - 1)/2) hlow
      rwa [one_div_div] at h
    have hstep2 : 2 / (σ - 1) ≤ 8 * ℓ₂ / δ := by
      have h1 : 1 / (σ - 1) ≤ 1 / x := one_div_le_one_div_of_le hxpos (by linarith)
      have h2 : 1 / x = 4 * ℓ₂ / δ := by rw [hxdef]; field_simp
      rw [h2] at h1
      have h3 : 2 / (σ - 1) = 2 * (1 / (σ - 1)) := by ring
      rw [h3]
      calc 2 * (1 / (σ - 1)) ≤ 2 * (4 * ℓ₂ / δ) := by linarith
        _ = 8 * ℓ₂ / δ := by ring
    calc 1 / ‖DirichletCharacter.LFunction χ s‖ ≤ 2 / (σ - 1) := hstep1
      _ ≤ 8 * ℓ₂ / δ := hstep2
      _ = (8 / δ) * ℓ₂ := by ring
      _ ≤ Ck * ℓ₂ ^ Ck := by
            have h2 : ℓ₂ ^ (1:ℝ) ≤ ℓ₂ ^ Ck :=
              Real.rpow_le_rpow_of_exponent_le hℓ₂_one hCk1
            calc (8 / δ) * ℓ₂ = (8 / δ) * ℓ₂ ^ (1:ℝ) := by rw [Real.rpow_one]
              _ ≤ Ck * ℓ₂ ^ Ck := by
                    apply mul_le_mul hCk8 h2
                    · exact (Real.rpow_pos_of_pos hℓ₂pos _).le
                    · exact hCkpos.le
  · -- Case 2: σ < 1 + x.  Borel--Caratheodory on a ball centred at `1+x+it`.
    set c₀ : ℂ := (1 + x : ℂ) + (t : ℂ) * Complex.I with hc₀def
    have hc₀re : c₀.re = 1 + x := by simp [hc₀def]
    have hc₀im : c₀.im = t := by simp [hc₀def]
    have hsnorm : ‖s - c₀‖ = 1 + x - σ := by
      have hsc : s - c₀ = (((σ - (1+x) : ℝ)) : ℂ) := by
        rw [hsdef, hc₀def]; apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im] <;> ring
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hd_le : (1 + x - σ) * ℓ₂ ≤ (9/4) * δ := by
      have h1 : 1 + x - σ ≤ x + δ / ℓ := by
        have h := hσ; rw [hℓdef] at h; linarith
      have h2 : (x + δ / ℓ) * ℓ₂ ≤ (9/4) * δ := by
        have h3 : δ / ℓ * ℓ₂ ≤ 2 * δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < ℓ)]
          nlinarith [hℓ₂_le, hδpos]
        have h4 : (x + δ / ℓ) * ℓ₂ = x * ℓ₂ + δ/ℓ * ℓ₂ := by ring
        rw [h4, hxℓ₂]; nlinarith [h3]
      calc (1 + x - σ) * ℓ₂ ≤ (x + δ / ℓ) * ℓ₂ :=
            mul_le_mul_of_nonneg_right h1 hℓ₂pos.le
        _ ≤ (9/4) * δ := h2
    have hd_lt : ‖s - c₀‖ < Rc := by
      rw [hsnorm, hRcdef, lt_div_iff₀ hℓ₂pos]
      nlinarith [hd_le, hδpos]
    have hs_mem : s ∈ Metric.ball c₀ Rc := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hd_lt
    -- The ball is zero-free.
    have hzne : ∀ w ∈ Metric.ball c₀ Rc, DirichletCharacter.LFunction χ w ≠ 0 := by
      intro w hw
      have hwlt : ‖w - c₀‖ < Rc := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hwre : w.re - (1+x) = (w - c₀).re := by simp [hc₀def, Complex.sub_re]
      have hwim : w.im - t = (w - c₀).im := by simp [hc₀def, Complex.sub_im]
      have hre_abs : |w.re - (1+x)| ≤ Rc := by
        rw [hwre]; exact le_trans (Complex.abs_re_le_norm _) hwlt.le
      have him_abs : |w.im - t| ≤ Rc := by
        rw [hwim]; exact le_trans (Complex.abs_im_le_norm _) hwlt.le
      have hwre_lo : 1 - cz / ℓ₂ ≤ w.re := by
        have h1 : -(Rc) ≤ w.re - (1+x) := (abs_le.mp hre_abs).1
        have hcz : (15/4) * δ ≤ cz := by nlinarith [h8δ]
        have h2 : 1 + x - Rc = 1 - (15/4) * δ / ℓ₂ := by
          rw [hxdef, hRcdef]; field_simp; ring
        have h3 : 1 - cz / ℓ₂ ≤ 1 - (15/4) * δ / ℓ₂ := by
          have h4 : (15/4) * δ / ℓ₂ ≤ cz / ℓ₂ := by
            rw [div_le_div_iff₀ hℓ₂pos hℓ₂pos]; nlinarith [hcz]
          linarith
        linarith [h1, h2, h3]
      have him_abs_le : |w.im| ≤ |t| + Rc := by
        have h : |w.im| = |t + (w.im - t)| := by congr 1; ring
        calc |w.im| = |t + (w.im - t)| := h
          _ ≤ |t| + |w.im - t| := abs_add_le _ _
          _ ≤ |t| + Rc := by linarith [him_abs]
      have hwim_ge : (3/4 : ℝ) ≤ |w.im| := by
        have htri : |t| ≤ |w.im| + |w.im - t| := by
          have h1 : |t| = |w.im - (w.im - t)| := by congr 1; ring
          calc |t| = |w.im - (w.im - t)| := h1
            _ = |w.im + (-(w.im - t))| := by rw [sub_eq_add_neg]
            _ ≤ |w.im| + |-(w.im - t)| := abs_add_le _ _
            _ = |w.im| + |w.im - t| := by rw [abs_neg]
        linarith [ht, hRcle, htri, him_abs]
      have hwim_ne : w.im ≠ 0 := by
        intro h; rw [h, abs_zero] at hwim_ge; norm_num at hwim_ge
      have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      have hNne : (N:ℝ) ≠ 0 := hNpos.ne'
      have hlogw : Real.log ((N:ℝ) * (|w.im| + 2)) ≤ ℓ₂ := by
        have h1 : |w.im| + 2 ≤ 2 * (|t| + 2) := by
          nlinarith [him_abs_le, hRcle, ht, abs_nonneg t]
        have habslog : Real.log (|w.im| + 2) ≤ Real.log (2 * (|t| + 2)) :=
          Real.log_le_log (by positivity) h1
        rw [Real.log_mul (by norm_num) (by positivity : (|t| + 2) ≠ 0)] at habslog
        have hlog2le : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have h2 : Real.log ((N:ℝ) * (|t| + 2)) = Real.log (N:ℝ) + Real.log (|t| + 2) :=
          Real.log_mul hNne (by positivity : (|t|+2) ≠ 0)
        rw [Real.log_mul hNne (by positivity : (|w.im|+2) ≠ 0), hℓ₂def, hℓdef, h2]
        linarith [habslog, hlog2le]
      have hcond : 1 - cz / Real.log ((N:ℝ) * (|w.im| + 2)) ≤ w.re := by
        have hpos : 0 < Real.log ((N:ℝ) * (|w.im| + 2)) :=
          Real.log_pos (by nlinarith [hN1, abs_nonneg w.im])
        have hcle := div_le_div_of_nonneg_left hczpos.le hpos hlogw
        linarith [hcle, hwre_lo]
      have hz' := hzfr χ hχprim hχ (w.re) (w.im) hwim_ne hcond
      rwa [Complex.re_add_im w] at hz'
    -- upper bound `M` on the ball
    have hMbound : ∀ w ∈ Metric.ball c₀ Rc, ‖DirichletCharacter.LFunction χ w‖ ≤ 10000 * ℓ₂ := by
      intro w hw
      have hwlt : ‖w - c₀‖ < Rc := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hwre : w.re - (1+x) = (w - c₀).re := by simp [hc₀def, Complex.sub_re]
      have hwim : w.im - t = (w - c₀).im := by simp [hc₀def, Complex.sub_im]
      have hre_abs : |w.re - (1+x)| ≤ Rc := by
        rw [hwre]; exact le_trans (Complex.abs_re_le_norm _) hwlt.le
      have him_abs : |w.im - t| ≤ Rc := by
        rw [hwim]; exact le_trans (Complex.abs_im_le_norm _) hwlt.le
      have hwre_lo : 0 ≤ w.re := by
        have h1 : -(Rc) ≤ w.re - (1+x) := (abs_le.mp hre_abs).1
        have h2 : (0:ℝ) ≤ 1 + x - Rc := by linarith [hxpos, hRcle]
        linarith
      have him_abs_le : |w.im| ≤ |t| + Rc := by
        have h : |w.im| = |t + (w.im - t)| := by congr 1; ring
        calc |w.im| = |t + (w.im - t)| := h
          _ ≤ |t| + |w.im - t| := abs_add_le _ _
          _ ≤ |t| + Rc := by linarith [him_abs]
      have hNne : (N:ℝ) ≠ 0 := by
        exact_mod_cast (NeZero.ne N)
      have hlogw' : Real.log (N:ℝ) + Real.log (2 + |w.im|) ≤ ℓ₂ := by
        have h1 : 2 + |w.im| ≤ 2 * (|t| + 2) := by
          nlinarith [him_abs_le, hRcle, ht, abs_nonneg t]
        have habslog : Real.log (2 + |w.im|) ≤ Real.log (2 * (|t| + 2)) :=
          Real.log_le_log (by positivity) h1
        rw [Real.log_mul (by norm_num) (by positivity : (|t| + 2) ≠ 0)] at habslog
        have hlog2le : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have h2 : Real.log ((N:ℝ) * (|t| + 2)) = Real.log (N:ℝ) + Real.log (|t| + 2) :=
          Real.log_mul hNne (by positivity : (|t|+2) ≠ 0)
        rw [hℓ₂def, hℓdef, h2]
        linarith [habslog, hlog2le]
      have hexp8 : Real.exp 8 ≤ 10000 := by
        have h1 : Real.exp 8 = (Real.exp 1) ^ 8 := by simpa using Real.exp_nat_mul 1 8
        rw [h1]
        have h2 : (Real.exp 1) ^ 8 ≤ (3:ℝ) ^ 8 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 8
        have h3 : (3:ℝ)^8 = 6561 := by norm_num
        linarith
      rcases le_or_gt 1 w.re with hge1 | hlt1
      · have hb := Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
          χ hχ w hge1
        calc ‖DirichletCharacter.LFunction χ w‖ ≤ Real.log (N:ℝ) + Real.log (2 + |w.im|) + 6 := hb
          _ ≤ ℓ₂ + 6 := by linarith [hlogw']
          _ ≤ 10000 * ℓ₂ := by nlinarith [hℓ₂2]
      · have hb := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
          χ hχ hχprim (σ := w.re) (T := w.im) hwre_lo hlt1.le
        have heq : (↑w.re : ℂ) + Complex.I * ↑w.im = w := by
          rw [mul_comm Complex.I (↑w.im : ℂ), Complex.re_add_im]
        rw [heq] at hb
        have hcoef : (1 - w.re) / 2 * (Real.log (N:ℝ) + Real.log (2 + |w.im|)) ≤ 1/2 := by
          have h1 : (1 - w.re)/2 ≤ Rc/2 := by
            have h2 : 1 - w.re ≤ Rc := by
              have h3 : -(Rc) ≤ w.re - (1+x) := (abs_le.mp hre_abs).1
              linarith
            linarith
          have hpos2 : 0 ≤ Real.log (N:ℝ) + Real.log (2 + |w.im|) := by
            have h4 := Real.log_nonneg hN1
            have h5 := Real.log_nonneg (by nlinarith [abs_nonneg w.im] : (1:ℝ) ≤ 2 + |w.im|)
            linarith
          calc (1 - w.re) / 2 * (Real.log (N:ℝ) + Real.log (2 + |w.im|))
              ≤ (Rc/2) * ℓ₂ := mul_le_mul h1 hlogw' hpos2 (by linarith [hRcpos])
            _ = 2 * δ := by rw [hRcdef]; field_simp; ring
            _ ≤ 1/2 := by nlinarith [hδle]
        have hlogw2 : Real.log (Real.log ((N:ℝ) * (2 + |w.im|)) + 2) ≤ 1 + Real.log ℓ₂ := by
          have hB : Real.log ((N:ℝ) * (2 + |w.im|)) ≤ ℓ₂ := by
            rw [Real.log_mul hNne (by positivity : (2+|w.im|) ≠ 0)]
            exact hlogw'
          have h1 : Real.log ((N:ℝ) * (2 + |w.im|)) + 2 ≤ 2 * ℓ₂ := by linarith [hB, hℓ₂2]
          have h2 : 0 < Real.log ((N:ℝ) * (2 + |w.im|)) + 2 := by
            have h3 : 0 ≤ Real.log ((N:ℝ) * (2 + |w.im|)) :=
              Real.log_nonneg (by nlinarith [hN1, abs_nonneg w.im])
            linarith
          have h3 := Real.log_le_log h2 h1
          rw [Real.log_mul (by norm_num) (by positivity : (ℓ₂) ≠ 0)] at h3
          linarith [h3, Real.log_two_lt_d9]
        have hlogbound : Real.log ‖DirichletCharacter.LFunction χ w‖ ≤ Real.log ℓ₂ + 8 := by
          linarith [hb, hcoef, hlogw2]
        calc ‖DirichletCharacter.LFunction χ w‖
            = Real.exp (Real.log ‖DirichletCharacter.LFunction χ w‖) :=
              (Real.exp_log (norm_pos_iff.mpr (hzne w hw))).symm
          _ ≤ Real.exp (Real.log ℓ₂ + 8) := Real.exp_le_exp.mpr hlogbound
          _ = Real.exp 8 * ℓ₂ := by rw [Real.exp_add, Real.exp_log hℓ₂pos]; ring
          _ ≤ 10000 * ℓ₂ := mul_le_mul_of_nonneg_right hexp8 hℓ₂pos.le
    -- the lower bound at the centre
    have hLc₀ : δ / (8 * ℓ₂) ≤ ‖DirichletCharacter.LFunction χ c₀‖ := by
      have h1 : 1 < c₀.re := by rw [hc₀re]; linarith [hxpos]
      have h2 : c₀.re ≤ 2 := by rw [hc₀re]; linarith
      have hb := norm_LFunction_ge_near_one χ (s := c₀) h1 h2
      rw [hc₀re] at hb
      have heq : (1 + x - 1)/2 = δ/(8*ℓ₂) := by rw [hxdef]; field_simp; ring
      rwa [heq] at hb
    set M : ℝ := 10000 * ℓ₂ with hMdef
    set m : ℝ := δ / (8 * ℓ₂) with hmdef
    have hmpos : 0 < m := by rw [hmdef]; positivity
    have hLc₀' : m ≤ ‖DirichletCharacter.LFunction χ c₀‖ := by rw [hmdef]; exact hLc₀
    have hlogLc0 : Real.log m ≤ Real.log ‖DirichletCharacter.LFunction χ c₀‖ :=
      Real.log_le_log hmpos hLc₀'
    have hMm : m ≤ M := by
      rw [hmdef, hMdef]
      have h1 : δ / (8*ℓ₂) ≤ 1 / 8 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hδle]
      nlinarith [h1, hℓ₂2]
    have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      DirichletCharacter.differentiable_LFunction hχ
    obtain ⟨F, hFdiff, _hFder, hFcre, hFre⟩ :=
      Commons.Analysis.Complex.logPrimitiveOnBall hLdiff hRcpos hzne
    have hFle : ∀ w ∈ Metric.ball c₀ Rc, (F w).re ≤ Real.log M := by
      intro w hw
      rw [hFre w hw]
      exact Real.log_le_log (norm_pos_iff.mpr (hzne w hw)) (hMbound w hw)
    have hFc : Real.log m ≤ (F c₀).re := by
      rw [hFcre]; exact hlogLc0
    have hb := Commons.Analysis.Complex.normSubLeOfReLeOnBall
      (F := F) (c := c₀) (w := s) (R := Rc) (m := m) (M := M)
      hRcpos hmpos hMm hFdiff hFle hFc hs_mem
    have hosc : Real.log ‖DirichletCharacter.LFunction χ s‖ -
        Real.log ‖DirichletCharacter.LFunction χ c₀‖ ≥ -‖F s - F c₀‖ := by
      have h3 : -‖F s - F c₀‖ ≤ (F s - F c₀).re := by
        have h4 := Complex.re_le_norm (-(F s - F c₀))
        rw [Complex.neg_re, norm_neg] at h4
        linarith
      have h1 : (F s - F c₀).re = Real.log ‖DirichletCharacter.LFunction χ s‖ -
          Real.log ‖DirichletCharacter.LFunction χ c₀‖ := by
        rw [Complex.sub_re, hFre s hs_mem, hFcre]
      rwa [h1] at h3
    have hratio : ‖s - c₀‖ / (Rc - ‖s - c₀‖) ≤ 9/7 := by
      rw [hsnorm]
      have hden : 0 < Rc - (1 + x - σ) := by
        have := hd_lt; rw [hsnorm] at this; linarith
      rw [div_le_iff₀ hden]
      have hkey : (1 + x - σ) * ℓ₂ ≤ (9/7) * (Rc - (1 + x - σ)) * ℓ₂ := by
        have h4 : (9/7) * (Rc - (1 + x - σ)) * ℓ₂
            = (9/7) * (Rc * ℓ₂ - (1 + x - σ) * ℓ₂) := by ring
        rw [h4, hRcℓ₂]
        nlinarith [hd_le, hδpos]
      exact (mul_le_mul_iff_of_pos_right hℓ₂pos).mp hkey
    have hlogdiff : Real.log (2 * M) - Real.log m ≤ (K₀ + 2) * Real.log ℓ₂ := by
      have hEq : Real.log (2 * M) - Real.log m = Real.log (160000/δ) + 2 * Real.log ℓ₂ := by
        have e1 : Real.log (2 * M) - Real.log m = Real.log ((2*M)/m) :=
          (Real.log_div (by positivity) (by positivity)).symm
        rw [e1]
        have e2 : (2*M)/m = 160000/δ * ℓ₂^2 := by rw [hMdef, hmdef]; field_simp; ring
        rw [e2, Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast; ring
      have h3 : Real.log (160000 / δ) = K₀ * Real.log 2 := by
        rw [hK₀def, div_mul_cancel₀ _ hlog2pos.ne']
      have h4 : K₀ * Real.log 2 ≤ K₀ * Real.log ℓ₂ :=
        mul_le_mul_of_nonneg_left hlogℓ₂ hK₀nonneg
      rw [hEq, h3]
      linarith [h4]
    have hbound : ‖F s - F c₀‖ ≤ (18/7) * (K₀ + 2) * Real.log ℓ₂ := by
      have hlogdiffnn : 0 ≤ Real.log (2 * M) - Real.log m := by
        have h1 : m ≤ 2 * M := by rw [hMdef, hmdef]; nlinarith [hδle, hℓ₂2, hδpos]
        exact sub_nonneg.mpr (Real.log_le_log hmpos h1)
      rw [mul_div_assoc] at hb
      calc ‖F s - F c₀‖
          ≤ 2 * (Real.log (2 * M) - Real.log m) * (‖s - c₀‖ / (Rc - ‖s - c₀‖)) := hb
        _ ≤ 2 * ((K₀ + 2) * Real.log ℓ₂) * (9/7) := by
              have h0 : 0 ≤ 2 * (Real.log (2 * M) - Real.log m) := by linarith
              calc 2 * (Real.log (2*M) - Real.log m) * (‖s-c₀‖/(Rc - ‖s-c₀‖))
                  ≤ 2 * (Real.log (2*M) - Real.log m) * (9/7) :=
                    mul_le_mul_of_nonneg_left hratio h0
                _ ≤ 2 * ((K₀+2)*Real.log ℓ₂) * (9/7) :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hlogdiff (by norm_num)) (by norm_num)
        _ = (18/7) * (K₀ + 2) * Real.log ℓ₂ := by ring
    have hfinal : Real.log (δ/8) - (1 + (18/7) * (K₀ + 2)) * Real.log ℓ₂
        ≤ Real.log ‖DirichletCharacter.LFunction χ s‖ := by
      have hm_expand : Real.log m = Real.log (δ/8) - Real.log ℓ₂ := by
        rw [hmdef]
        have he : δ / (8 * ℓ₂) = (δ/8) / ℓ₂ := by ring
        rw [he, Real.log_div (by positivity : (δ/8) ≠ 0) hℓ₂pos.ne']
      linarith [hosc, hbound, hlogLc0, hm_expand]
    have hLspos : 0 < ‖DirichletCharacter.LFunction χ s‖ :=
      norm_pos_iff.mpr (hzne s hs_mem)
    have hexp : Real.exp (Real.log (δ/8) - (1 + (18/7) * (K₀ + 2)) * Real.log ℓ₂)
        ≤ ‖DirichletCharacter.LFunction χ s‖ :=
      (Real.le_log_iff_exp_le hLspos).mp hfinal
    have hexpval : Real.exp (Real.log (δ/8) - (1 + (18/7) * (K₀ + 2)) * Real.log ℓ₂)
        = (δ/8) * ℓ₂ ^ (-(1 + (18/7) * (K₀ + 2))) := by
      rw [Real.exp_sub, Real.exp_log (by positivity : (0:ℝ) < δ/8)]
      have hB : Real.exp ((1 + (18/7) * (K₀ + 2)) * Real.log ℓ₂)
          = ℓ₂ ^ (1 + (18/7) * (K₀ + 2)) := by
        rw [Real.rpow_def_of_pos hℓ₂pos, mul_comm]
      rw [hB, Real.rpow_neg hℓ₂pos.le, div_eq_mul_inv]
    rw [hexpval] at hexp
    have hinv : 1 / ‖DirichletCharacter.LFunction χ s‖ ≤
        (8/δ) * ℓ₂ ^ (1 + (18/7) * (K₀ + 2)) := by
      rw [div_le_iff₀ hLspos]
      have h1 : ℓ₂ ^ (1 + (18/7)*(K₀+2)) * ℓ₂ ^ (-(1 + (18/7)*(K₀+2))) = 1 := by
        rw [← Real.rpow_add hℓ₂pos, show 1 + (18/7)*(K₀+2) + -(1 + (18/7)*(K₀+2)) = 0 by ring,
          Real.rpow_zero]
      have h2 : (8/δ) * ℓ₂ ^ (1 + (18/7)*(K₀+2)) * ((δ/8) * ℓ₂ ^ (-(1 + (18/7)*(K₀+2)))) = 1 := by
        calc (8/δ) * ℓ₂ ^ (1 + (18/7)*(K₀+2)) * ((δ/8) * ℓ₂ ^ (-(1 + (18/7)*(K₀+2))))
            = (8/δ) * (δ/8) * (ℓ₂ ^ (1 + (18/7)*(K₀+2)) * ℓ₂ ^ (-(1 + (18/7)*(K₀+2)))) := by ring
          _ = 1 := by rw [h1]; field_simp
      calc (1:ℝ) = (8/δ) * ℓ₂ ^ (1 + (18/7)*(K₀+2)) *
              ((δ/8) * ℓ₂ ^ (-(1 + (18/7)*(K₀+2)))) := h2.symm
        _ ≤ (8/δ) * ℓ₂ ^ (1 + (18/7)*(K₀+2)) * ‖DirichletCharacter.LFunction χ s‖ :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
    calc 1 / ‖DirichletCharacter.LFunction χ s‖
        ≤ (8/δ) * ℓ₂ ^ (1 + (18/7) * (K₀ + 2)) := hinv
      _ ≤ Ck * ℓ₂ ^ Ck := by
            have h2 : ℓ₂ ^ (1 + (18/7) * (K₀ + 2)) ≤ ℓ₂ ^ Ck :=
              Real.rpow_le_rpow_of_exponent_le hℓ₂_one hCkK
            calc (8/δ) * ℓ₂ ^ (1 + (18/7) * (K₀ + 2))
                ≤ Ck * ℓ₂ ^ Ck := by
                  apply mul_le_mul hCk8 h2
                  · exact (Real.rpow_pos_of_pos hℓ₂pos _).le
                  · exact hCkpos.le

end Commons.NumberTheory.DirichletCharacter
