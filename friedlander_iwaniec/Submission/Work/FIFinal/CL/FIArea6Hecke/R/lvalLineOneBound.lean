
/-
# Submission.Work.FIArea6Hecke.R.lvalLineOneBound

The L-value on the line re s = 1 is bounded by a power of log(4d(2+|im s|)), with an absolute
constant and an explicit dependence on the constant C0 of the primary disc-sum bound

  ||sum_{z primary, |z|^2<=X} chi(z)|| <= C0.d.sqrt(X):

  ||L(1+i t)|| <= 625.C.(C0+1).log(4d(2+|t|))^4.

Chain: the disc sums give, by Abel summation, ||L(s)|| <= C(C0+1) log(4d(||s||+3)) on re s > 1
(R/heckeLSeries_re_gt_one_log_bound); the continuation is continuous at 1+i t, so the bound passes
to the line re s = 1; the comparison constants stripKL d 0 and log(2+|t|) are then absorbed into
log(4d(2+|t|)).  The explicit constant is needed because the final strip bound must be uniform in d.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.lhbLogBoundA
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- LambdaHecke at weight 0 is the archimedean factor times the L-series. -/
lemma LambdaHecke_zero_eq' (d : ℕ) (chi : GaussianInt → ℂ) (s : ℂ) :
    Work.FIArea5.S16Hecke.LambdaHecke d chi 0 s
      = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
  unfold Work.FIArea5.S16Hecke.LambdaHecke Work.FITop4.Bridge.heckeArch
  norm_num

/-- Lval at weight 0 is Lcont at weight 0. -/
lemma Lval_eq_Lcont_zero (d : ℕ) (Lam : ℂ → ℂ) :
    Work.FIArea6Hecke.Lval d 0 Lam = Work.FIArea5.S16Hecke.Lcont d Lam 0 := by
  funext z
  unfold Work.FIArea6Hecke.Lval Work.FIArea5.S16Hecke.Lcont
    Work.FIArea5.S16Hecke.completeDenom Work.FITop4.Bridge.heckeArch
  norm_num

/-- log (4.d.(2+|t|)) is at least 1. -/
lemma one_le_log_four_d_two_add (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    (1 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + |t|)) := by
  have h8 : (8 : ℝ) ≤ 4 * (d : ℝ) * (2 + |t|) := by
    have h2t : (2 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hlog8 : (1 : ℝ) < Real.log 8 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_three]
  exact le_trans (le_of_lt hlog8) (Real.log_le_log (by norm_num) h8)

/-- The comparison constant of the logarithmic bound: stripKL d 0 <= 5 log (4 d (2+|t|)). -/
lemma stripKL_zero_le (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    Work.FIArea5.S16Hecke.stripKL d 0 ≤ 5 * Real.log (4 * (d : ℝ) * (2 + |t|)) := by
  have hlogt := one_le_log_four_d_two_add d hd t
  have hlog2 : (0.6 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2t : (2 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
  have hLpos : (0 : ℝ) < 4 * (d : ℝ) * (2 + |t|) := by positivity
  have hlog16 : Real.log (4 * (d : ℝ) * (((0 : ℕ) : ℝ) + 4))
      ≤ 2 * Real.log (4 * (d : ℝ) * (2 + |t|)) := by
    have e1 : 4 * (d : ℝ) * (((0 : ℕ) : ℝ) + 4) = (4 * (d : ℝ)) * 4 := by push_cast; ring
    rw [e1, Real.log_mul (by positivity) (by norm_num : (4 : ℝ) ≠ 0)]
    have h1 : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (2 + |t|)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log (4 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + |t|)) :=
      Real.log_le_log (by norm_num) (by nlinarith [hd1, h2t])
    linarith
  unfold Work.FIArea5.S16Hecke.stripKL
  have h1 : Real.log (4 * (d : ℝ) * (((0 : ℕ) : ℝ) + 4)) / Real.log 2
      ≤ 2 * Real.log (4 * (d : ℝ) * (2 + |t|)) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog16 (le_of_lt hlog2pos)
  have h2 : 2 * Real.log (4 * (d : ℝ) * (2 + |t|)) / Real.log 2
      ≤ 4 * Real.log (4 * (d : ℝ) * (2 + |t|)) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [hlogt, hlog2]
  linarith

theorem lvalLineOneBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ (C₀ : ℝ), 0 < C₀ →
        (∀ X : ℝ, 1 ≤ X →
          ‖∑ z ∈ Work.FIArea6Hecke.R.primaryBox d X, chi z‖ ≤ C₀ * (d : ℝ) * Real.sqrt X) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ t : ℝ,
          ‖Work.FIArea6Hecke.Lval d 0 Lam ((1 : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ 625 * C * (C₀ + 1) * (Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (4 : ℕ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FIArea6Hecke.R.heckeLSeriesReGtOneBoundA
  refine ⟨C₁, hC₁pos, ?_⟩
  intro d hd chi hchi hnt C₀ hC₀ hdisc Lam hAn hagr t
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2t : (2 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
  have hdisc' : ∀ X : ℝ, 1 ≤ X →
      ‖∑ z ∈ Work.FIPlan.gBox ⌈X⌉₊,
          (if Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X then chi z else 0)‖
        ≤ C₀ * (d : ℝ) * Real.sqrt X := by
    intro X hX
    rw [← Work.FIArea6Hecke.R.primaryBox_sum_eq d X chi]
    exact hdisc X hX
  set Clim : ℝ := C₁ * (C₀ + 1) with hClimdef
  have hClimpos : 0 < Clim := by rw [hClimdef]; positivity
  have hlimb : ∀ s : ℂ, 1 < s.re → ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 s‖
      ≤ Clim * (Real.log (4 * (d : ℝ) * (‖s‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ) := by
    intro s hs
    have h1 : ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 s‖
        ≤ C₁ * Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := hC₁ d hd chi hchi hnt s hs
    have hsub : ‖s‖ + ((0 : ℕ) : ℝ) + 3 = ‖s‖ + 3 := by norm_num
    have hL1 : (1 : ℝ) ≤ Real.log (4 * (d : ℝ) * (‖s‖ + 3)) := by
      have h12 : (12 : ℝ) ≤ 4 * (d : ℝ) * (‖s‖ + 3) := by
        have h3 : (3 : ℝ) ≤ ‖s‖ + 3 := by have := norm_nonneg s; linarith
        nlinarith
      have hlog12 : (1 : ℝ) < Real.log 12 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_three]
      exact le_trans (le_of_lt hlog12) (Real.log_le_log (by norm_num) h12)
    have harg : Real.log (4 * (d : ℝ) * (2 + ‖s‖)) ≤ Real.log (4 * (d : ℝ) * (‖s‖ + 3)) := by
      refine Real.log_le_log (by positivity) ?_
      nlinarith [norm_nonneg s]
    have hL1nn : (0 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := by
      apply Real.log_nonneg
      have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
      nlinarith
    have hC1le : C₁ ≤ Clim := by
      rw [hClimdef]
      nlinarith [hC₀, hC₁pos]
    have h2 : C₁ * Real.log (4 * (d : ℝ) * (2 + ‖s‖))
        ≤ Clim * Real.log (4 * (d : ℝ) * (‖s‖ + 3)) :=
      mul_le_mul hC1le harg hL1nn (le_of_lt hClimpos)
    have hsq : Real.log (4 * (d : ℝ) * (‖s‖ + 3))
        ≤ (Real.log (4 * (d : ℝ) * (‖s‖ + 3))) ^ (2 : ℕ) := by
      nlinarith [hL1]
    rw [hsub]
    calc ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 s‖
        ≤ C₁ * Real.log (4 * (d : ℝ) * (2 + ‖s‖)) := h1
      _ ≤ Clim * Real.log (4 * (d : ℝ) * (‖s‖ + 3)) := h2
      _ ≤ Clim * (Real.log (4 * (d : ℝ) * (‖s‖ + 3))) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hsq (le_of_lt hClimpos)
  have hagree : ∀ s : ℂ, 1 + ((0 : ℕ) : ℝ) / 2 < s.re →
      Lam s = Work.FIArea5.S16Hecke.LambdaHecke d chi 0 s := by
    intro s hs
    rw [LambdaHecke_zero_eq' d chi s]
    exact hagr s (by simpa using hs)
  have hdiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  have hkey : ‖Work.FIArea5.S16Hecke.Lcont d Lam 0 ((1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Clim * (Real.log (4 * (d : ℝ)
        * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ) := by
    have hcont : ContinuousAt (Work.FIArea5.S16Hecke.Lcont d Lam 0)
        ((1 : ℂ) + (t : ℂ) * Complex.I) :=
      (Work.FIArea5.S16Hecke.differentiable_Lcont hd hdiff 0).continuous.continuousAt
    have hmap : Filter.Tendsto (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (𝓝[>] (1 : ℝ))
        (𝓝 ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
      have h1 : ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) 1 := by fun_prop
      exact h1.tendsto.mono_left (inf_le_left : 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ))
    have htend : Filter.Tendsto
        (fun σ : ℝ => Work.FIArea5.S16Hecke.Lcont d Lam 0 ((σ : ℂ) + (t : ℂ) * Complex.I))
        (𝓝[>] (1 : ℝ))
        (𝓝 (Work.FIArea5.S16Hecke.Lcont d Lam 0 ((1 : ℂ) + (t : ℂ) * Complex.I))) :=
      hcont.tendsto.comp hmap
    have hgt : ContinuousAt (fun w : ℂ => Clim *
        (Real.log (4 * (d : ℝ) * (‖w‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ))
        ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      refine ContinuousAt.mul continuousAt_const ?_
      refine ContinuousAt.pow ?_ 2
      refine (Real.continuousAt_log ?_).comp ?_
      · have hpos : (0 : ℝ)
            < 4 * (d : ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3) := by
          have hn := norm_nonneg ((1 : ℂ) + (t : ℂ) * Complex.I)
          have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
          rw [h0]
          nlinarith [hd1]
        exact ne_of_gt hpos
      · exact ContinuousAt.mul continuousAt_const
          (ContinuousAt.add (continuous_norm.continuousAt.add continuousAt_const)
            continuousAt_const)
    have hrt : Filter.Tendsto (fun σ : ℝ => Clim *
        (Real.log (4 * (d : ℝ) * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3)))
          ^ (2 : ℕ))
        (𝓝[>] (1 : ℝ)) (𝓝 (Clim *
        (Real.log (4 * (d : ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3)))
          ^ (2 : ℕ))) := by
      have hh := hgt.tendsto.comp hmap
      simpa [Function.comp_def] using hh
    have hev : Filter.Eventually (fun σ : ℝ =>
        ‖Work.FIArea5.S16Hecke.Lcont d Lam 0 ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          Clim * (Real.log (4 * (d : ℝ)
            * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ))
        (𝓝[>] (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, mul_zero, sub_zero, Complex.I_im, mul_one, add_zero]
        exact hσ
      rw [Work.FIArea5.S16Hecke.Lcont_eq_heckeLSeries_of_one_lt_re hd hAn hb hagree hσ1]
      exact hlimb _ hσ1
    exact le_of_tendsto_of_tendsto htend.norm hrt hev
  have hLval : Work.FIArea6Hecke.Lval d 0 Lam ((1 : ℂ) + (t : ℂ) * Complex.I)
      = Work.FIArea5.S16Hecke.Lcont d Lam 0 ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [Lval_eq_Lcont_zero]
  rw [hLval]
  have hlogt := one_le_log_four_d_two_add d hd t
  have hnorm1 : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ 2 * (2 + |t|) := by
    have h := Complex.norm_le_abs_re_add_abs_im ((1 : ℂ) + (t : ℂ) * Complex.I)
    have hre : ((1 : ℂ) + (t : ℂ) * Complex.I).re = 1 := by simp
    have him : ((1 : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hre, him] at h
    have h1 : |(1 : ℝ)| = 1 := by norm_num
    rw [h1] at h
    have h2 : (1 : ℝ) + |t| ≤ 2 * (2 + |t|) := by linarith [abs_nonneg t]
    linarith
  have hlogle : Real.log (4 * (d : ℝ)
        * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3))
      ≤ 3 * Real.log (4 * (d : ℝ) * (2 + |t|)) := by
    have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
    rw [h0]
    simp only [add_zero]
    have hn : (0 : ℝ) ≤ ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + 3 := by
      have := norm_nonneg ((1 : ℂ) + (t : ℂ) * Complex.I); linarith
    have hposn : (0 : ℝ) < ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + 3 := by
      have := norm_nonneg ((1 : ℂ) + (t : ℂ) * Complex.I); linarith
    have hnz : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + 3 ≠ 0 := ne_of_gt hposn
    have h4d : (0 : ℝ) < 4 * (d : ℝ) := by positivity
    have hLpos : (0 : ℝ) < 4 * (d : ℝ) * (2 + |t|) := by positivity
    have hsplit : 4 * (d : ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + 3)
        = (4 * (d : ℝ)) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + 3) := by ring
    rw [hsplit, Real.log_mul (ne_of_gt h4d) hnz]
    have h1 : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (2 + |t|)) :=
      Real.log_le_log h4d (by nlinarith [h2t])
    have h2 : Real.log (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + 3)
        ≤ Real.log (4 * (2 + |t|)) := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith [hnorm1, h2t, abs_nonneg t]
    have h3 : Real.log (4 * (2 + |t|)) ≤ 2 * Real.log (4 * (d : ℝ) * (2 + |t|)) := by
      rw [show (4 : ℝ) * (2 + |t|) = 4 * (2 + |t|) from rfl,
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity)]
      have h4 : Real.log (4 : ℝ) ≤ Real.log (4 * (d : ℝ) * (2 + |t|)) :=
        Real.log_le_log (by norm_num) (by nlinarith [hd1, h2t])
      have h5 : Real.log (2 + |t|) ≤ Real.log (4 * (d : ℝ) * (2 + |t|)) :=
        Real.log_le_log (by positivity) (by nlinarith [hd1])
      linarith
    linarith
  have hmiddle : Clim * (Real.log (4 * (d : ℝ)
        * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ)
      ≤ Clim * (3 * Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (2 : ℕ) := by
    have hn := norm_nonneg ((1 : ℂ) + (t : ℂ) * Complex.I)
    have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
    have hpos : 0 ≤ Real.log (4 * (d : ℝ)
        * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3)) := by
      apply Real.log_nonneg
      rw [h0]
      nlinarith [hd1, hn]
    have hp : (Real.log (4 * (d : ℝ)
          * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ)
        ≤ (3 * Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hpos hlogle 2
    exact mul_le_mul_of_nonneg_left hp (le_of_lt hClimpos)
  have hfinal : 9 * Clim * (Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (2 : ℕ)
      ≤ 625 * C₁ * (C₀ + 1) * (Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (4 : ℕ) := by
    set L : ℝ := Real.log (4 * (d : ℝ) * (2 + |t|)) with hLdef
    have hL1 : (1 : ℝ) ≤ L := hlogt
    have hsq : L ^ (2 : ℕ) ≤ L ^ (4 : ℕ) := by
      have h0 : (0 : ℝ) ≤ L := le_of_lt (lt_of_lt_of_le zero_lt_one hL1)
      have h4 : L ^ (4 : ℕ) = L ^ (2 : ℕ) * L ^ (2 : ℕ) := by ring
      rw [h4]
      have hL2 : (1 : ℝ) ≤ L ^ (2 : ℕ) := one_le_pow₀ hL1
      nlinarith [hL2, h0]
    have h9 : 9 * Clim ≤ 625 * C₁ * (C₀ + 1) := by
      rw [hClimdef]
      nlinarith [hC₁pos, hC₀]
    calc 9 * Clim * L ^ (2 : ℕ)
        = (9 * Clim) * L ^ (2 : ℕ) := by ring
      _ ≤ (625 * C₁ * (C₀ + 1)) * L ^ (2 : ℕ) := by
          have h0 : (0 : ℝ) ≤ L ^ (2 : ℕ) := by positivity
          exact mul_le_mul_of_nonneg_right h9 h0
      _ ≤ (625 * C₁ * (C₀ + 1)) * L ^ (4 : ℕ) := by
          have h0 : (0 : ℝ) ≤ 625 * C₁ * (C₀ + 1) := by positivity
          exact mul_le_mul_of_nonneg_left hsq h0
      _ = 625 * C₁ * (C₀ + 1) * L ^ (4 : ℕ) := by ring
  calc ‖Work.FIArea5.S16Hecke.Lcont d Lam 0 ((1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Clim * (Real.log (4 * (d : ℝ)
          * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ((0 : ℕ) : ℝ) + 3))) ^ (2 : ℕ) := hkey
    _ ≤ Clim * (3 * Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (2 : ℕ) := hmiddle
    _ = 9 * Clim * (Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (2 : ℕ) := by ring
    _ ≤ 625 * C₁ * (C₀ + 1) * (Real.log (4 * (d : ℝ) * (2 + |t|))) ^ (4 : ℕ) := hfinal

end

end Work.FIArea6Hecke.R
