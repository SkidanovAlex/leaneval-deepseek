import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea6Hecke.R.DiscDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- Only `z = 0` has norm `0`. -/
lemma gnorm_eq_zero {z : GaussianInt} (h : Work.FIPlan.gnorm z = 0) : z = 0 := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 0 := by
    have h2 : (Zsqrtd.norm z).natAbs = 0 := h
    rw [Zsqrtd.norm_def] at h2
    have : z.re * z.re - -1 * z.im * z.im = z.re ^ 2 + z.im ^ 2 := by ring
    rw [this] at h2
    exact Int.natAbs_eq_zero.mp h2
  have h1 : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have h2 : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  ext <;> assumption

/-- `heckeLam chi 0 0 = 0`. -/
lemma heckeLam_zero (chi : GaussianInt → ℂ) : Work.FIArea5.S16Hecke.heckeLam chi 0 0 = 0 := by
  classical
  rw [Work.FIArea5.S16Hecke.heckeLam]
  apply Finset.sum_eq_zero
  intro z hz
  exfalso
  rw [Finset.mem_filter] at hz
  obtain ⟨_, hprim, hgn⟩ := hz
  rw [gnorm_eq_zero hgn] at hprim
  simp only [Work.FIPlan.IsPrimary] at hprim
  exact (by decide : ¬ Odd (0:ℤ)) hprim.1

/-- The `range`-form of the head bound. -/
lemma head_range {chi : GaussianInt → ℂ} {Kh : ℝ} (hKh : 0 < Kh)
    (hHead : ∀ M : ℕ, ∑ n ∈ Finset.Icc 1 M, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ)
          ≤ Kh * Real.log (M + 2))
    {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ)
      ≤ Kh * Real.log (N + 1) := by
  have hsplit : ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ)
      = (‖Work.FIArea5.S16Hecke.heckeLam chi 0 0‖ / ((0:ℕ):ℝ))
        + ∑ n ∈ Finset.Ico 1 N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (f := fun n => ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ))
        (by norm_num : (0:ℕ) ≤ 1) hN]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [hsplit, heckeLam_zero, norm_zero, zero_div, zero_add]
  rw [show Finset.Ico 1 N = Finset.Icc 1 (N - 1) by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
  have hlog : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by
    have : N - 1 + 2 = N + 1 := by omega
    exact_mod_cast this
  have := hHead (N - 1)
  rwa [hlog] at this

/-- **The sharp polylogarithmic bound on `re s > 1`** for the Hecke `L`-series, from the
mean-zero disc-sum bound (`Cd ≥ 1`), the head bound (`Kh`) and the Abel estimate (`Ka`). -/
theorem heckeLSeries_ReGtOne_bound
    {Cd Kh Ka : ℝ} (hCd1 : 1 ≤ Cd) (hKh : 0 < Kh) (hKa : 0 < Ka)
    (hPart : ∀ (chi : GaussianInt → ℂ) (N : ℕ),
        ∑ n ∈ Finset.range (N + 1), Work.FIArea5.S16Hecke.heckeLam chi 0 n
          = Work.FIArea6Hecke.R.discSum (N : ℝ) chi)
    (hDisc : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ X : ℝ, 1 ≤ X →
          ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ Cd * (d : ℝ) * Real.sqrt X)
    (hHead : ∀ (chi : GaussianInt → ℂ), (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ M : ℕ, ∑ n ∈ Finset.Icc 1 M, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ)
          ≤ Kh * Real.log (M + 2))
    (hAbel : ∀ {a : ℕ → ℂ} {C : ℝ}, 0 < C →
        (∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Finset.range N, a n‖ ≤ C * (N : ℝ) ^ (1/2 : ℝ)) →
        ∀ (s : ℂ) (N M : ℕ), 1 ≤ N → N ≤ M → (1/2 : ℝ) < s.re →
          ‖(∑ n ∈ Finset.range M, a n / (n : ℂ) ^ s)
            - (∑ n ∈ Finset.range N, a n / (n : ℂ) ^ s)‖
            ≤ Ka * C * (1 + ‖s‖ / (s.re - 1/2)) * (N : ℝ) ^ ((1/2 : ℝ) - s.re))
    (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hex : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1)
    (s : ℂ) (hs1 : 1 < s.re) :
    ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 s‖
      ≤ (10 * (Kh + 1) * (Ka + 1) + 10) * Real.log (4 * Cd * (d : ℝ) * (2 + ‖s‖)) := by
  have hchib : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hsre : 0 < s.re := by linarith
  have hne_S : s ≠ 0 := by intro h; rw [h] at hsre; simp at hsre
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hCdpos : 0 < Cd := by linarith
  have hbasepos : 0 < Cd * (d:ℝ) * (1 + ‖s‖) := by positivity
  have hbase1 : 1 ≤ Cd * (d:ℝ) * (1 + ‖s‖) := by
    calc (1:ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ Cd * (d:ℝ) * (1 + ‖s‖) := by gcongr <;> linarith [norm_nonneg s]
  have hnorm : ∀ n : ℕ, ‖(n:ℂ)^s‖ = (n:ℝ)^s.re := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      push_cast
      rw [Complex.zero_cpow hne_S, Real.zero_rpow (ne_of_gt hsre), norm_zero]
    · exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s
  -- partial sums of `heckeLam chi 0` are `discSum`, bounded by `Cd·d·√N`
  have hAbelHyp : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n‖
        ≤ (Cd * (d:ℝ)) * (N : ℝ) ^ (1/2 : ℝ) := by
    intro N hN
    rcases eq_or_lt_of_le hN with hN1 | hN2
    · subst hN1
      rw [Finset.sum_range_one, heckeLam_zero, norm_zero]
      positivity
    · have hsum : ∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n
          = Work.FIArea6Hecke.R.discSum ((N - 1 : ℕ) : ℝ) chi := by
        rw [show N = (N - 1) + 1 from (Nat.sub_add_cancel hN).symm]
        exact hPart chi (N - 1)
      rw [hsum]
      have hX : (1:ℝ) ≤ ((N-1:ℕ):ℝ) := by
        have : 1 ≤ N - 1 := by omega
        exact_mod_cast this
      refine le_trans (hDisc d hd chi hchi hex ((N-1:ℕ):ℝ) hX) ?_
      have hsqrt : Real.sqrt ((N-1:ℕ):ℝ) ≤ ((N:ℝ))^(1/2:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.sub_le N 1) (by norm_num)
      exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
  -- the cut-off and `B`
  set M : ℕ := ⌈(Cd * (d:ℝ) * (1 + ‖s‖))^2⌉₊ + 2 with hMdef
  have hMge : (Cd * (d:ℝ) * (1 + ‖s‖))^2 ≤ (M:ℝ) := by
    have h := Nat.le_ceil ((Cd * (d:ℝ) * (1 + ‖s‖))^2)
    rw [hMdef]; push_cast; linarith
  have hMpos : 1 ≤ M := by rw [hMdef]; omega
  have hMposR : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  set B : ℝ := Kh * Real.log (M + 1)
      + Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (M:ℝ)^((1/2:ℝ) - s.re) with hBdef
  have hhead_step : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖
        ≤ Kh * Real.log (N + 1) := by
    intro N hN
    have hterm : ∀ n ∈ Finset.range N,
        ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖
          ≤ ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^s.re := by
      intro n _
      rw [norm_div, hnorm n]
    calc ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖
        ≤ ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖ :=
          norm_sum_le (Finset.range N) _
      _ ≤ ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^s.re :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rcases eq_or_ne n 0 with hn | hn
          · subst hn
            push_cast
            rw [Real.zero_rpow (ne_of_gt hsre), div_zero]
          · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
            have hle : (n:ℝ) ≤ (n:ℝ)^s.re := by
              have h1 : (1:ℝ) ≤ (n:ℝ)^(s.re - 1) := Real.one_le_rpow hn1 (by linarith)
              calc (n:ℝ) = (n:ℝ)^(1:ℝ) * 1 := by rw [Real.rpow_one, mul_one]
                _ ≤ (n:ℝ)^(1:ℝ) * (n:ℝ)^(s.re-1) :=
                    mul_le_mul_of_nonneg_left h1 (by positivity)
                _ = (n:ℝ)^(1 + (s.re - 1)) := (Real.rpow_add (by positivity) 1 (s.re-1)).symm
                _ = (n:ℝ)^s.re := by ring_nf
            exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hle
      _ ≤ Kh * Real.log (N + 1) := head_range hKh (fun M' => hHead chi hchib M') hN
  have hSbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖ ≤ B := by
    intro N hN
    rcases lt_or_ge N M with hNM | hMN
    · -- N < M: head only
      have hle : Real.log ((N:ℝ) + 1) ≤ Real.log ((M:ℝ) + 1) := by
        refine Real.log_le_log (by positivity) ?_
        have : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM.le
        linarith
      have h0 : (0:ℝ) ≤ Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2))
          * (M:ℝ)^((1/2:ℝ) - s.re) := by
        have h1 : 0 ≤ (1 + ‖s‖ / (s.re - 1/2)) := by
          have : 0 ≤ ‖s‖ / (s.re - 1/2) := div_nonneg (norm_nonneg s) (by linarith)
          linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hKa.le (by positivity)) h1)
          (Real.rpow_nonneg hMposR.le _)
      rw [hBdef]
      linarith [hhead_step N hN, mul_le_mul_of_nonneg_left hle hKh.le, h0]
    · -- M ≤ N: head at M + Abel
      have hsplit : ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖
          ≤ ‖∑ n ∈ Finset.range M, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s‖
            + ‖(∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)
                - (∑ n ∈ Finset.range M, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)‖ := by
        have heq : (∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)
            = (∑ n ∈ Finset.range M, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)
              + ((∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)
                - (∑ n ∈ Finset.range M, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)) := by
          ring
        conv_lhs => rw [heq]
        exact norm_add_le _ _
      refine le_trans hsplit ?_
      have h1 := hhead_step M hMpos
      have h2 := hAbel (a := fun n => Work.FIArea5.S16Hecke.heckeLam chi 0 n) (C := Cd * (d:ℝ))
        (by positivity) hAbelHyp s M N hMpos hMN (by linarith [hs1])
      rw [hBdef]
      linarith [h1, h2]
  -- pass to the limit
  have hsummable : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam chi 0) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi 0 hchib)
        (EReal.coe_lt_coe_iff.mpr hs1))
  have hhas : HasSum (fun n : ℕ => Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s)
      (Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) := by
    have h := hsummable.LSeriesHasSum
    have h' : HasSum (fun n : ℕ => LSeries.term (Work.FIArea5.S16Hecke.heckeLam chi 0) s n)
        (LSeries (Work.FIArea5.S16Hecke.heckeLam chi 0) s) := h
    have hfun : (fun n : ℕ => LSeries.term (Work.FIArea5.S16Hecke.heckeLam chi 0) s n)
        = (fun n : ℕ => Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^s) := by
      funext n
      rw [LSeries.term]
      rcases eq_or_ne n 0 with hn | hn
      · subst hn; simp [Complex.zero_cpow hne_S]
      · rw [if_neg hn]
    rw [hfun] at h'
    exact h'
  have hlim : ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 s‖ ≤ B := by
    refine le_of_tendsto_of_tendsto hhas.tendsto_sum_nat.norm tendsto_const_nhds ?_
    filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun b hb => hb⟩] with N hN
    exact hSbound N hN
  refine le_trans hlim ?_
  -- bound `B`
  have hX8 : (8:ℝ) ≤ 4 * Cd * (d:ℝ) * (2 + ‖s‖) := by nlinarith [norm_nonneg s]
  have hlog8 : (1:ℝ) ≤ Real.log 8 := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num : (3:ℝ) < 8)))
    rwa [Real.log_exp] at h
  have hlogX : (1:ℝ) ≤ Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) :=
    le_trans hlog8 (Real.log_le_log (by norm_num) hX8)
  have hlogbase : Real.log (Cd * (d:ℝ) * (1 + ‖s‖))
      ≤ Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) := by
    refine Real.log_le_log hbasepos ?_
    nlinarith [norm_nonneg s]
  have hlog5 : Real.log 5 ≤ Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) :=
    Real.log_le_log (by norm_num) (by linarith [hX8])
  have hheadB : Kh * Real.log ((M:ℝ) + 1)
      ≤ 3 * Kh * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) := by
    have hMb : (M:ℝ) + 1 ≤ 5 * (Cd * (d:ℝ) * (1 + ‖s‖))^2 := by
      have hMle : (M:ℝ) ≤ (Cd * (d:ℝ) * (1 + ‖s‖))^2 + 3 := by
        have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (Cd * (d:ℝ) * (1 + ‖s‖))^2 by positivity)
        rw [hMdef]; push_cast; linarith
      nlinarith [hMle, hbase1]
    have hlogM : Real.log ((M:ℝ) + 1)
        ≤ Real.log 5 + 2 * Real.log (Cd * (d:ℝ) * (1 + ‖s‖)) := by
      calc Real.log ((M:ℝ) + 1) ≤ Real.log (5 * (Cd * (d:ℝ) * (1 + ‖s‖))^2) :=
            Real.log_le_log (by positivity) hMb
        _ = Real.log 5 + Real.log ((Cd * (d:ℝ) * (1 + ‖s‖))^2) :=
            Real.log_mul (by norm_num) (by positivity)
        _ = Real.log 5 + 2 * Real.log (Cd * (d:ℝ) * (1 + ‖s‖)) := by
            rw [Real.log_pow]; ring
    nlinarith [hlogM, hlog5, hlogbase, hlogX, hKh]
  have htailB : Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (M:ℝ)^((1/2:ℝ) - s.re)
      ≤ 2 * Ka := by
    have he : (M:ℝ)^((1/2:ℝ) - s.re) ≤ (Cd * (d:ℝ) * (1 + ‖s‖))^(-1:ℝ) := by
      have h1 : (M:ℝ)^((1/2:ℝ) - s.re)
          ≤ ((Cd * (d:ℝ) * (1 + ‖s‖))^2)^((1/2:ℝ) - s.re) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hMge (by linarith [hs1])
      refine le_trans h1 ?_
      rw [show ((Cd * (d:ℝ) * (1 + ‖s‖))^2)^((1/2:ℝ) - s.re)
            = (Cd * (d:ℝ) * (1 + ‖s‖))^(2 * ((1/2:ℝ) - s.re)) from by
          rw [← Real.rpow_natCast]
          exact (Real.rpow_mul (le_of_lt hbasepos) 2 ((1/2:ℝ) - s.re)).symm]
      refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
      linarith [hs1]
    have hfac : (Cd * (d:ℝ)) * (Cd * (d:ℝ) * (1 + ‖s‖))^(-1:ℝ) = (1 + ‖s‖)^(-1:ℝ) := by
      rw [show Cd * (d:ℝ) * (1 + ‖s‖) = (Cd * (d:ℝ)) * (1 + ‖s‖) from by ring,
        Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg_one, Real.rpow_neg_one,
        ← mul_assoc, mul_inv_cancel₀ (by positivity : Cd * (d:ℝ) ≠ 0), one_mul]
    have h2 : (1 + ‖s‖ / (s.re - 1/2)) * (1 + ‖s‖)^(-1:ℝ) ≤ 2 := by
      have h3 : ‖s‖ / (s.re - 1/2) ≤ 2 * ‖s‖ := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg s]
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖s‖)]
      linarith
    have hstep : Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (M:ℝ)^((1/2:ℝ) - s.re)
        ≤ Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (Cd * (d:ℝ) * (1 + ‖s‖))^(-1:ℝ) := by
      refine mul_le_mul_of_nonneg_left he ?_
      exact mul_nonneg (mul_nonneg hKa.le (by positivity)) (by
        have : 0 ≤ ‖s‖ / (s.re - 1/2) := div_nonneg (norm_nonneg s) (by linarith)
        linarith)
    calc Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (M:ℝ)^((1/2:ℝ) - s.re)
        ≤ Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (Cd * (d:ℝ) * (1 + ‖s‖))^(-1:ℝ) := hstep
      _ = Ka * ((1 + ‖s‖ / (s.re - 1/2)) * (1 + ‖s‖)^(-1:ℝ)) := by
          rw [show Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2))
                * (Cd * (d:ℝ) * (1 + ‖s‖))^(-1:ℝ)
              = Ka * (1 + ‖s‖ / (s.re - 1/2))
                * ((Cd * (d:ℝ)) * (Cd * (d:ℝ) * (1 + ‖s‖))^(-1:ℝ)) from by ring,
            hfac]
          ring
      _ ≤ Ka * 2 := mul_le_mul_of_nonneg_left h2 hKa.le
      _ = 2 * Ka := by ring
  have hK : 3 * Kh + 2 * Ka ≤ 10 * (Kh + 1) * (Ka + 1) + 10 := by nlinarith [hKh, hKa]
  calc B = Kh * Real.log ((M:ℝ) + 1)
        + Ka * (Cd * (d:ℝ)) * (1 + ‖s‖ / (s.re - 1/2)) * (M:ℝ)^((1/2:ℝ) - s.re) := rfl
    _ ≤ 3 * Kh * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) + 2 * Ka := add_le_add hheadB htailB
    _ ≤ 3 * Kh * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖))
          + 2 * Ka * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) := by
        have : 2 * Ka ≤ 2 * Ka * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) := by
          nlinarith [hKa.le, hlogX]
        linarith
    _ = (3 * Kh + 2 * Ka) * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) := by ring
    _ ≤ (10 * (Kh + 1) * (Ka + 1) + 10) * Real.log (4 * Cd * (d:ℝ) * (2 + ‖s‖)) :=
        mul_le_mul_of_nonneg_right hK (by linarith [hlogX])

end

end Work.FIArea6Hecke.R
