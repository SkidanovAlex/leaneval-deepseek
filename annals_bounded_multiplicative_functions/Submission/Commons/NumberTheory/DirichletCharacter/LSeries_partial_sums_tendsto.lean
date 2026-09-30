import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.NumberTheory.DirichletCharacter.partial_sum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Complex Filter

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- Difference bound for consecutive terms of the Dirichlet series kernel. -/
lemma norm_cpow_nat_sub_succ_cpow_le (s : ℂ) (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-(s.re + 1)) := by
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ (-s) with hf_def
  have hsne : s ≠ 0 := fun h => by simp [h] at hs
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hdiff : ∀ x ∈ Set.Icc (n : ℝ) ((n:ℝ) + 1), DifferentiableAt ℝ f x := by
    intro x hx
    have hx0 : (x:ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le hnpos hx.1)
    exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hsne)).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (n : ℝ) ((n:ℝ) + 1),
      ‖deriv f x‖ ≤ ‖s‖ * (n : ℝ) ^ (-(s.re + 1)) := by
    intro x hx
    have hx0 : (x:ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le hnpos hx.1)
    rw [hf_def, Complex.deriv_ofReal_cpow_const hx0 (neg_ne_zero.mpr hsne)]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hnpos hx.1)]
    have hre : ((-s - 1 : ℂ)).re = -(s.re + 1) := by
      simp only [sub_re, neg_re, one_re]; ring
    rw [hre]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos hnpos hx.1 (by linarith)
  have hmtv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _)
      (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  have h1 : ‖(n:ℝ) + 1 - ↑n‖ = 1 := by norm_num
  rw [h1, mul_one, norm_sub_rev] at hmtv
  rw [hf_def] at hmtv
  simpa using hmtv

/-- `∑ n, n^{-(σ+1)}` converges for `σ > 0`. -/
lemma summable_nat_rpow_neg_add_one (σ : ℝ) (hσ : 0 < σ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(σ + 1))) := by
  have h := (Real.summable_nat_rpow_inv (p := σ + 1)).mpr (by linarith)
  refine h.congr (fun n => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

/-- Abel summation: a Dirichlet series with bounded partial sums converges on `re s > 0`,
to the (absolutely convergent) "summation by parts" series. -/
lemma abel_partial_sums_tendsto {a : ℕ → ℂ} {B : ℝ}
    (hB : ∀ M, ‖∑ n ∈ Finset.range M, a n‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n * (n : ℂ) ^ (-s)) Filter.atTop
      (nhds (∑' n : ℕ, ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))
        * (∑ k ∈ Finset.range (n + 1), a k))) := by
  have hsne : s ≠ 0 := fun h => by simp [h] at hs
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  set S : ℕ → ℂ := fun N => ∑ k ∈ Finset.range N, a k with hS
  set c : ℕ → ℂ := fun n => (f n - f (n + 1)) * S (n + 1) with hc
  have hcsum : Summable c := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n => ‖s‖ * (n : ℝ) ^ (-(s.re + 1)) * max B 0)
      ((summable_nat_rpow_neg_add_one s.re hs).mul_left ‖s‖ |>.mul_right (max B 0)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [hc, hf, hS, norm_mul]
    refine mul_le_mul (norm_cpow_nat_sub_succ_cpow_le s hs hn)
      (le_trans (hB (n+1)) (le_max_left B 0)) (norm_nonneg _) ?_
    positivity
  have habel : ∀ N : ℕ,
      ∑ n ∈ Finset.range (N + 1), a n * f n = f N * S (N + 1) + ∑ n ∈ Finset.range N, c n := by
    intro N
    have hkey := Finset.sum_Ico_by_parts (fun n => f n) (fun n => a n) (Nat.succ_pos N)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel] at hkey
    rw [← Finset.range_eq_Ico (N+1), ← Finset.range_eq_Ico N] at hkey
    have hf0 : f 0 = 0 := by rw [hf]; simpa using zero_cpow (neg_ne_zero.mpr hsne)
    rw [hf0, zero_mul, sub_zero] at hkey
    simp only [show ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) = S n from fun n => by rw [hS]] at hkey
    calc ∑ n ∈ Finset.range (N + 1), a n * f n
        = ∑ n ∈ Finset.range (N + 1), f n * a n := Finset.sum_congr rfl (fun n _ => mul_comm _ _)
      _ = f N * S (N + 1) - ∑ x ∈ Finset.range N, (f (x + 1) - f x) * S (x + 1) := hkey
      _ = f N * S (N + 1) + ∑ x ∈ Finset.range N, c x := by
            have hcc : ∑ x ∈ Finset.range N, c x
                = - ∑ x ∈ Finset.range N, (f (x + 1) - f x) * S (x + 1) := by
              rw [hc, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun n _ => by ring)
            rw [hcc]; ring
  have hbnd : Tendsto (fun N : ℕ => f N * S (N + 1)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ => (n:ℝ) ^ (-s.re) * max B 0)
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · simp only [hf, hS]
      obtain rfl | hn := Nat.eq_zero_or_pos n
      · simp only [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr hsne), norm_zero, zero_mul,
          Real.zero_rpow (by linarith : -s.re ≠ 0)]
        exact le_refl 0
      · rw [norm_mul, norm_natCast_cpow_of_pos hn]
        refine mul_le_mul_of_nonneg_left (le_trans (hB (n+1)) (le_max_left B 0)) ?_
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · have h1 : Tendsto (fun n : ℕ => (n:ℝ) ^ (-s.re)) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
      have hc' : Tendsto (fun _ : ℕ => max B 0) atTop (nhds (max B 0)) := tendsto_const_nhds
      have := h1.mul hc'
      simpa using this
  have hser : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, c n) atTop (nhds (∑' n, c n)) :=
    hcsum.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1), a n * f n) atTop
      (nhds (∑' n, c n)) := by
    have h := hbnd.add hser
    rw [zero_add] at h
    exact Tendsto.congr (fun N => (habel N).symm) h
  have hfinal : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n * f n) atTop
      (nhds (∑' n, c n)) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun N : ℕ => ∑ n ∈ Finset.range N, a n * f n) 1).mp hcomb
  simpa [hf, hS, hc] using hfinal

/-- The "summation by parts" series is differentiable on the half-plane `re > 0`. -/
lemma differentiableOn_tsum_cpow_nat_diff_bounded {S : ℕ → ℂ} {B : ℝ}
    (hB : ∀ n, ‖S n‖ ≤ B) :
    DifferentiableOn ℂ
      (fun w : ℂ => ∑' n : ℕ, ((n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)) * S (n + 1))
      {w : ℂ | 0 < w.re} := by
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set σ₀ := s.re / 2 with hσ₀
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀]; linarith
  set T := ‖s‖ + 1 with hT
  have hTs : ‖s‖ < T := by rw [hT]; linarith
  have hTnn : 0 ≤ T := by rw [hT]; positivity
  set U : Set ℂ := {w : ℂ | σ₀ < w.re ∧ ‖w‖ < T} with hU
  have hUopen : IsOpen U := by
    rw [hU]
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    rw [hU]; exact ⟨by rw [hσ₀]; linarith, hTs⟩
  have hwne : ∀ w ∈ U, w ≠ 0 := by
    intro w hw h0; rw [h0, hU] at hw; simp at hw; linarith [hσ₀pos, hw.1]
  set u : ℕ → ℝ := fun n => T * (n : ℝ) ^ (-(σ₀ + 1)) * max B 0
      + (if n = 0 then max B 0 else 0) with hu
  have husum : Summable u := by
    have h1 : Summable (fun n : ℕ => T * (n : ℝ) ^ (-(σ₀ + 1)) * max B 0) := by
      have := ((summable_nat_rpow_neg_add_one σ₀ hσ₀pos).mul_right (max B 0)).mul_left T
      exact this.congr (fun n => by ring)
    have h2 : Summable (fun n : ℕ => if n = 0 then max B 0 else (0:ℝ)) :=
      summable_of_ne_finset_zero (s := {0}) (fun b hb => by
        rw [Finset.mem_singleton] at hb; exact if_neg hb)
    exact (h1.add h2).congr (fun n => by rw [hu])
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun w : ℂ => ((n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)) * S (n + 1)) U := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine (differentiableOn_const (((0:ℂ) - 1) * S 1)).congr (fun w hw => ?_)
      simp only [Nat.cast_zero, Nat.reduceAdd, Nat.cast_one]
      rw [zero_cpow (neg_ne_zero.mpr (hwne w hw)), one_cpow]
    · have hc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hc1 : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      have h1 : DifferentiableOn ℂ (fun w : ℂ => (n:ℂ)^(-w)) U := fun w _ =>
        (DifferentiableAt.const_cpow (f := fun w : ℂ => -w) (by fun_prop) (Or.inl hc)).differentiableWithinAt
      have h2 : DifferentiableOn ℂ (fun w : ℂ => ((n+1:ℕ):ℂ)^(-w)) U := fun w _ =>
        (DifferentiableAt.const_cpow (f := fun w : ℂ => -w) (by fun_prop) (Or.inl hc1)).differentiableWithinAt
      exact (h1.sub h2).mul (differentiableOn_const _)
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖((n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)) * S (n + 1)‖ ≤ u n := by
    intro n w hw
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, Nat.reduceAdd, Nat.cast_one]
      rw [zero_cpow (neg_ne_zero.mpr (hwne w hw)), one_cpow]
      have hu0 : u 0 = max B 0 := by
        show T * ((0:ℕ):ℝ) ^ (-(σ₀+1)) * max B 0 + (if (0:ℕ) = 0 then max B 0 else 0) = max B 0
        simp only [Nat.cast_zero, if_true]
        rw [Real.zero_rpow (by linarith : -(σ₀+1) ≠ 0)]
        ring
      rw [hu0, show ((0:ℂ) - 1) * S 1 = - S 1 by ring, norm_neg]
      exact le_trans (hB 1) (le_max_left B 0)
    · have hne : w ≠ 0 := hwne w hw
      have hwre : 0 < w.re := lt_trans hσ₀pos hw.1
      have hn1 : 1 ≤ n := hn
      rw [norm_mul]
      have e1 : ‖(n:ℂ)^(-w) - ((n+1:ℕ):ℂ)^(-w)‖ ≤ ‖w‖ * (n:ℝ)^(-(w.re + 1)) :=
        norm_cpow_nat_sub_succ_cpow_le w hwre hn1
      have e2 : (n:ℝ)^(-(w.re+1)) ≤ (n:ℝ)^(-(σ₀+1)) := by
        refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
        · exact_mod_cast hn1
        · linarith [hw.1]
      have e3 : ‖S (n+1)‖ ≤ max B 0 := le_trans (hB (n+1)) (le_max_left B 0)
      have e4 : ‖w‖ ≤ T := le_of_lt hw.2
      have hun : u n = T * (n:ℝ)^(-(σ₀+1)) * max B 0 := by
        rw [hu]; simp [hn.ne']
      rw [hun]
      calc ‖(n:ℂ)^(-w) - ((n+1:ℕ):ℂ)^(-w)‖ * ‖S (n+1)‖
          ≤ (‖w‖ * (n:ℝ)^(-(w.re+1))) * max B 0 := by
            refine mul_le_mul e1 e3 (norm_nonneg _) (by positivity)
        _ ≤ (T * (n:ℝ)^(-(σ₀+1))) * max B 0 := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul e4 e2 (Real.rpow_nonneg (Nat.cast_nonneg n) _) hTnn) (le_max_right B 0)
        _ = T * (n:ℝ)^(-(σ₀+1)) * max B 0 := by ring
  have hd := differentiableOn_tsum_of_summable_norm (F := fun (n : ℕ) (w : ℂ) =>
      ((n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)) * S (n + 1)) husum hdiff hUopen hle
  exact (hd.differentiableAt (hUopen.mem_nhds hsU)).differentiableWithinAt

theorem LSeries_partial_sums_tendsto {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, (ψ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds (ψ.LFunction s)) := by
  have hq : q ≠ 1 := fun h => hψ (DirichletCharacter.level_one' ψ h)
  have hsne : s ≠ 0 := fun h => by simp [h] at hs
  set a : ℕ → ℂ := fun n => (ψ (n : ZMod q) : ℂ) with ha
  have ha0 : a 0 = 0 := by
    show ψ ((0 : ℕ) : ZMod q) = 0
    rw [Nat.cast_zero]
    exact ψ.map_zero' hq
  set S : ℕ → ℂ := fun N => ∑ k ∈ Finset.range N, a k with hS
  have hB : ∀ M, ‖S M‖ ≤ (q : ℝ) := by
    intro M
    rw [hS]
    simpa [ha] using partial_sum_bound ψ hψ M
  set H : ℂ → ℂ := fun w => ∑' n : ℕ, ((n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)) * S (n + 1)
    with hHdef
  have hH : ∀ w : ℂ, 0 < w.re →
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n * (n:ℂ)^(-w)) atTop (nhds (H w)) := by
    intro w hw
    have hthis := abel_partial_sums_tendsto (a := a) (B := (q:ℝ)) hB hw
    simpa [H, hS] using hthis
  have hH_eq_gt1 : ∀ w : ℂ, 1 < w.re → H w = ψ.LFunction w := by
    intro w hw
    have hL : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * (n:ℂ)^(-w)) atTop
        (nhds (ψ.LFunction w)) := by
      have hsumm : LSeriesSummable a w :=
        LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
          rw [ha]; simpa using DirichletCharacter.norm_le_one ψ (n : ZMod q)) hw
      have hhs := hsumm.LSeriesHasSum
      have hLG : ψ.LFunction w = LSeries a w := by
        rw [ha]; exact DirichletCharacter.LFunction_eq_LSeries ψ hw
      rw [hLG]
      refine Tendsto.congr (fun N => ?_) hhs.tendsto_sum_nat
      exact Finset.sum_congr rfl (fun n _ => LSeries.term_def₀ ha0 w n)
    exact tendsto_nhds_unique (hH w (lt_trans zero_lt_one hw)) hL
  have hHeqAll : ∀ w : ℂ, 0 < w.re → H w = ψ.LFunction w := by
    have hUopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    have hHan : AnalyticOnNhd ℂ H {w : ℂ | 0 < w.re} :=
      (differentiableOn_tsum_cpow_nat_diff_bounded (S := S) hB).analyticOnNhd hUopen
    have hLan : AnalyticOnNhd ℂ (ψ.LFunction) {w : ℂ | 0 < w.re} :=
      ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn).analyticOnNhd hUopen
    have hpre : IsPreconnected {w : ℂ | 0 < w.re} := by
      have h : {w : ℂ | 0 < w.re} = Complex.reCLM.toLinearMap ⁻¹' Set.Ioi (0:ℝ) := rfl
      rw [h]
      exact (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap |>.isPreconnected
    have hz₀ : (2:ℂ) ∈ {w : ℂ | 0 < w.re} := by
      simp only [Set.mem_ofPred_eq]
      norm_num
    have hev : H =ᶠ[nhds (2:ℂ)] ψ.LFunction :=
      Filter.eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp only [Set.mem_ofPred_eq]; norm_num))
        (fun w hw => hH_eq_gt1 w hw)
    intro w hw
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHan hLan hpre hz₀ hev) hw
  have hfin : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n * (n:ℂ)^(-s)) atTop
      (nhds (ψ.LFunction s)) := by
    rw [← hHeqAll s hs]
    exact hH s hs
  have hsplit : ∀ M : ℕ, ∑ n ∈ Finset.range (M+1), a n * (n:ℂ)^(-s)
      = ∑ n ∈ Finset.Icc 1 M, a n * (n:ℂ)^(-s) := by
    intro M
    have hr : Finset.range (M+1) = insert 0 (Finset.Icc 1 M) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hr, Finset.sum_insert (by simp [Finset.mem_Icc])]
    simp only [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr hsne), mul_zero, zero_add]
  have hfin2 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M+1), a n * (n:ℂ)^(-s)) atTop
      (nhds (ψ.LFunction s)) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun N : ℕ => ∑ n ∈ Finset.range N, a n * (n:ℂ)^(-s)) 1).mpr hfin
  refine Tendsto.congr (fun M => ?_) hfin2
  rw [hsplit M, ha]

end

end Commons.NumberTheory.DirichletCharacter