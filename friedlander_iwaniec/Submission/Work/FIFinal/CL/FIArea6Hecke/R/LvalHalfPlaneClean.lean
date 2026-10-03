import Mathlib
import Submission.Work.FIArea6Hecke.R.LHBSetup
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.LHBHead
import Submission.Work.FIArea6Hecke.R.LHBPartialSum
import Submission.Work.FIArea6Hecke.R.LHBReGtOne
import Submission.Work.FIArea6Hecke.R.LHBDisc
import Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs
import Submission.Work.FIArea6Hecke.R.classCount_discrepancy_sqrt
import Submission.Work.FIArea6Hecke.R.discSum_trivial_bound
import Submission.Work.FIArea6Hecke.R.sum_eq_classSum
import Submission.Work.FIArea6Hecke.R.DiscDefs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.LHBHead2V
import Submission.Work.FIArea6Hecke.R.abelThetaHalf

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

/-- The sharp polylogarithmic bound for the continuation of the Hecke `L`-function on the closed
half-plane `re s ≥ 1`: `‖L(s,χ)‖ ≤ C (log(4d(2+|Im s|)))^k` with `C,k` absolute in `d`.  This is
the `head + Abel tail` estimate from the disc-sum bound `Σ_{Nz ≤ X} χ(z) ≪ d^10 X^θ` for some
`θ < 1`, and is exactly the `σ = 1` boundary datum needed for the Phragmén–Lindelöf step that
produces the sharp strip bound.  (It is *not* the convexity bound: the exponent of `d` is 0.) -/
theorem LvalHalfPlaneClean :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ z : ℂ, 1 ≤ z.re →
          ‖Work.FIArea6Hecke.Lval d 0 Lam z‖
            ≤ C * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k := by
  obtain ⟨Cd0, _hCd0pos, hDisc0⟩ := LHBDisc
  obtain ⟨Kh, hKhpos, hHead⟩ := LHBHead
  obtain ⟨Kh2, hKh2pos, hHead2⟩ := LHBHead2V
  obtain ⟨Ka, hKapos, hAbelRaw⟩ := abelThetaHalf
  set Cd : ℝ := max Cd0 1 with hCddef
  have hCd1 : 1 ≤ Cd := le_max_right _ _
  have hCdpos : 0 < Cd := lt_of_lt_of_le zero_lt_one hCd1
  have hDisc : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
      ∀ X : ℝ, 1 ≤ X →
        ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ Cd * (d : ℝ) * Real.sqrt X := by
    intro d hd chi hchi hex X hX
    refine le_trans (hDisc0 d hd chi hchi hex X hX) ?_
    have h0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hd0 : 0 ≤ (d:ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cd0 1) hd0) h0
  set K1 : ℝ := 10 * (Kh + 1) * (Ka + 1) + 10 with hK1def
  have hK1pos : 0 < K1 := by rw [hK1def]; positivity
  set K3 : ℝ := Real.log (16 * Cd) / Real.log 2 + 1 with hK3def
  have hK3pos : 0 < K3 := by
    rw [hK3def]
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ Real.log (16 * Cd) := Real.log_nonneg (by nlinarith [hCd1])
    positivity
  refine ⟨K1 * K3 + Kh2 + 1, 1, by positivity, by norm_num, ?_⟩
  intro d hd chi hchi hex Lam hAn hagree z hz
  rw [Real.rpow_one]
  have hchib : ∀ w : GaussianInt, ‖chi w‖ ≤ 1 := hchi.1.2.2.1
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  have h8 : (1:ℝ) ≤ Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by
    have h8' : (8:ℝ) ≤ 4 * (d:ℝ) * (2 + |z.im|) := by nlinarith [abs_nonneg z.im]
    have hlog8 : (1:ℝ) ≤ Real.log 8 := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num : (3:ℝ) < 8)))
      rwa [Real.log_exp] at h
    exact le_trans hlog8 (Real.log_le_log (by norm_num) h8')
  have hReGt1 : ∀ (w : ℂ), 1 < w.re → ‖Work.FIArea6Hecke.Lval d 0 Lam w‖
      ≤ K1 * Real.log (4 * Cd * (d:ℝ) * (2 + ‖w‖)) := by
    intro w hw
    have hb := heckeLSeries_ReGtOne_bound (Cd := Cd) (Kh := Kh) (Ka := Ka) hCd1 hKhpos hKapos
      (fun c N => LHBPartialSum c N) hDisc hHead hAbelRaw d hd chi hchi hex w hw
    rw [Lval_eq_heckeLSeries_of_one_lt_re hd hagree hw, hK1def]
    exact hb
  have hlogc : ∀ (w : ℂ), |w.re| ≤ 2 → Real.log (4 * Cd * (d:ℝ) * (2 + ‖w‖))
      ≤ K3 * Real.log (4 * (d:ℝ) * (2 + |w.im|)) := by
    intro w hwr
    have huz : ‖w‖ ≤ 2 + |w.im| := by
      have h1 := Complex.norm_le_abs_re_add_abs_im w
      linarith
    have hb := log_bookkeeping (C := Cd) (d := (d:ℝ)) (u := ‖w‖) (w := |w.im|)
      hCd1 hd1 (norm_nonneg w) (abs_nonneg w.im) huz
    rwa [← hK3def] at hb
  have hσ2 : ∀ (w : ℂ), 2 ≤ w.re → ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 w‖ ≤ Kh2 := by
    intro w hw
    have hw1 : 1 < w.re := by linarith
    have hwne : w ≠ 0 := by
      intro h; rw [h] at hw1; norm_num at hw1
    have hsummable : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam chi 0) w :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re
        (lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi 0 hchib)
          (EReal.coe_lt_coe_iff.mpr hw1))
    have hhas : HasSum (fun n : ℕ => Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^w)
        (Work.FIArea5.S16Hecke.heckeLSeries chi 0 w) := by
      have h := hsummable.LSeriesHasSum
      have h' : HasSum (fun n : ℕ => LSeries.term (Work.FIArea5.S16Hecke.heckeLam chi 0) w n)
          (LSeries (Work.FIArea5.S16Hecke.heckeLam chi 0) w) := h
      have hfun : (fun n : ℕ => LSeries.term (Work.FIArea5.S16Hecke.heckeLam chi 0) w n)
          = (fun n : ℕ => Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^w) := by
        funext n
        rw [LSeries.term]
        rcases eq_or_ne n 0 with hn | hn
        · subst hn; simp [Complex.zero_cpow hwne]
        · rw [if_neg hn]
      rw [hfun] at h'
      exact h'
    have hnorm : ∀ n : ℕ, ‖(n:ℂ)^w‖ = (n:ℝ)^w.re := by
      intro n
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        push_cast
        rw [Complex.zero_cpow hwne, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < w.re)), norm_zero]
      · exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) w
    have hpartial : ∀ N : ℕ, 1 ≤ N →
        ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^w‖ ≤ Kh2 := by
      intro N hN
      have hterm : ∀ n ∈ Finset.range N,
          ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^w‖
            ≤ ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^w.re := by
        intro n _; rw [norm_div, hnorm n]
      have hterm2 : ∀ n ∈ Finset.range N,
          ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^w.re
            ≤ ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^2 := by
        intro n _
        rcases eq_or_ne n 0 with hn | hn
        · subst hn; push_cast
          rw [Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < w.re))]; simp
        · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          have hle : (n:ℝ)^2 ≤ (n:ℝ)^w.re := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hle
      calc ‖∑ n ∈ Finset.range N, Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^w‖
          ≤ ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n / (n:ℂ)^w‖ :=
            norm_sum_le (Finset.range N) _
        _ ≤ ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^w.re :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ n ∈ Finset.range N, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^2 :=
            Finset.sum_le_sum hterm2
        _ = ∑ n ∈ Finset.Icc 1 (N - 1), ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n:ℝ)^2 :=
            sum_range_eq_Icc _ (by rw [heckeLam_zero, norm_zero]; simp) hN
        _ ≤ Kh2 := hHead2 chi hchib (N - 1)
    exact le_of_tendsto_of_tendsto hhas.tendsto_sum_nat.norm tendsto_const_nhds
      (Filter.eventually_atTop.mpr ⟨1, fun b hb => hpartial b hb⟩)
  rcases lt_or_ge z.re 2 with h2 | h2
  · have hzre2 : |z.re| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    rcases eq_or_lt_of_le hz with hz1 | hz1
    · have hzeq : z = (1:ℂ) + (z.im:ℂ) * Complex.I := by
        have h := Complex.re_add_im z
        rw [← hz1] at h
        simpa using h.symm
      have hcont : ContinuousAt (fun w : ℂ => Work.FIArea6Hecke.Lval d 0 Lam w)
          ((1:ℂ) + (z.im:ℂ)*Complex.I) := by
        have hfun : (fun w : ℂ => Work.FIArea6Hecke.Lval d 0 Lam w)
            = Work.FIArea5.S16Hecke.Lcont d Lam 0 := funext (fun w => Lval_eq_Lcont d Lam w)
        rw [hfun]
        exact (Work.FIArea5.S16Hecke.differentiable_Lcont hd hdiff 0).continuous.continuousAt
      have hmap : Filter.Tendsto (fun σ : ℝ => (σ:ℂ) + (z.im:ℂ)*Complex.I) (nhdsWithin (1:ℝ) (Set.Ioi 1))
          (𝓝 ((1:ℂ) + (z.im:ℂ)*Complex.I)) := by
        have h1 : ContinuousAt (fun σ : ℝ => (σ:ℂ) + (z.im:ℂ)*Complex.I) 1 := by fun_prop
        exact h1.tendsto.mono_left (inf_le_left : nhdsWithin (1:ℝ) (Set.Ioi 1) ≤ 𝓝 (1:ℝ))
      have htend : Filter.Tendsto
          (fun σ : ℝ => ‖Work.FIArea6Hecke.Lval d 0 Lam ((σ:ℂ) + (z.im:ℂ)*Complex.I)‖)
          (nhdsWithin (1:ℝ) (Set.Ioi 1)) (𝓝 ‖Work.FIArea6Hecke.Lval d 0 Lam ((1:ℂ) + (z.im:ℂ)*Complex.I)‖) :=
        (hcont.tendsto.comp hmap).norm
      have hev : Filter.Eventually
          (fun σ : ℝ => ‖Work.FIArea6Hecke.Lval d 0 Lam ((σ:ℂ) + (z.im:ℂ)*Complex.I)‖
            ≤ K1 * K3 * Real.log (4 * (d:ℝ) * (2 + |z.im|)))
          (nhdsWithin (1:ℝ) (Set.Ioi 1)) := by
        filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (1:ℝ) < 2)]
          with σ hσ1 hσ2
        have hs1 : 1 < ((σ:ℂ) + (z.im:ℂ)*Complex.I).re := by simpa using hσ1
        have habs : |((σ:ℂ) + (z.im:ℂ)*Complex.I).re| ≤ 2 := by
          rw [abs_le]; constructor <;> simp <;> linarith [hσ2.1, hσ2.2]
        calc ‖Work.FIArea6Hecke.Lval d 0 Lam ((σ:ℂ) + (z.im:ℂ)*Complex.I)‖
            ≤ K1 * Real.log (4 * Cd * (d:ℝ) * (2 + ‖((σ:ℂ) + (z.im:ℂ)*Complex.I)‖)) :=
              hReGt1 _ hs1
          _ ≤ K1 * (K3 * Real.log (4 * (d:ℝ) * (2 + |z.im|))) := by
              refine mul_le_mul_of_nonneg_left ?_ hK1pos.le
              simpa using hlogc _ habs
          _ = K1 * K3 * Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by ring
      have hzre1 : ‖Work.FIArea6Hecke.Lval d 0 Lam z‖
          ≤ K1 * K3 * Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by
        conv_lhs => rw [hzeq]
        exact le_of_tendsto_of_tendsto htend tendsto_const_nhds hev
      refine le_trans hzre1 ?_
      have h0 : 0 ≤ Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by linarith [h8]
      exact mul_le_mul_of_nonneg_right (by linarith [hKh2pos]) h0
    · have hstep : K1 * Real.log (4 * Cd * (d:ℝ) * (2 + ‖z‖))
          ≤ K1 * (K3 * Real.log (4 * (d:ℝ) * (2 + |z.im|))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK1pos.le
        simpa using hlogc z hzre2
      refine le_trans (le_trans (hReGt1 z hz1) hstep) ?_
      have h0 : 0 ≤ Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by linarith [h8]
      have hmono : K1 * K3 ≤ K1 * K3 + Kh2 + 1 := by linarith [hKh2pos]
      calc K1 * (K3 * Real.log (4 * (d:ℝ) * (2 + |z.im|)))
          = (K1 * K3) * Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by ring
        _ ≤ (K1 * K3 + Kh2 + 1) * Real.log (4 * (d:ℝ) * (2 + |z.im|)) :=
            mul_le_mul_of_nonneg_right hmono h0
  · have hzre : 1 < z.re := by linarith
    rw [Lval_eq_heckeLSeries_of_one_lt_re hd hagree hzre]
    refine le_trans (hσ2 z h2) ?_
    have h0 : 0 ≤ Real.log (4 * (d:ℝ) * (2 + |z.im|)) := by linarith [h8]
    calc Kh2 = Kh2 * 1 := by ring
      _ ≤ Kh2 * Real.log (4 * (d:ℝ) * (2 + |z.im|)) :=
          mul_le_mul_of_nonneg_left h8 hKh2pos.le
      _ ≤ (K1 * K3 + Kh2 + 1) * Real.log (4 * (d:ℝ) * (2 + |z.im|)) :=
          mul_le_mul_of_nonneg_right (by nlinarith [hK1pos, hK3pos, hKh2pos]) h0

end

end Work.FIArea6Hecke.R

