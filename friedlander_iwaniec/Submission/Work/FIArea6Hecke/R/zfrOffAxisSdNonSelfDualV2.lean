import Mathlib
import Submission.Work.FIArea6Hecke.R.HeckeLDerivRe341
import Submission.Work.FIArea6Hecke.R.HeckeAxisLogDerivBound
import Submission.Work.FIArea6Hecke.R.HeckeZFRCoreMain
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.conductorFECleanNoDep
import Submission.Work.FIArea6Hecke.R.pfacBaseLowerUniform
import Submission.Work.FIArea6Hecke.R.zerosInStrip
import Submission.Work.FIArea6Hecke.R.lamGrowth
import Submission.Work.FIArea6Hecke.R.lamPartialFraction
import Submission.Work.FIArea6Hecke.R.re_logDeriv_rebase_negTwo
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-! ## Elementary helpers -/

/-- The square of a strict character modulo `4d` is again strict modulo `4d`. -/
private lemma isCharMod4dStrict_sq_local {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (fun z => chi z * chi z) := by
  obtain ⟨⟨h1, hmul, hb, hper, hvanish⟩, hstrict⟩ := hchi
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show chi 1 * chi 1 = 1
    rw [h1]; norm_num
  · intro z w
    show chi (z * w) * chi (z * w) = chi z * chi z * (chi w * chi w)
    rw [hmul z w]; ring
  · intro z
    rw [norm_mul]
    exact mul_le_one₀ (hb z) (norm_nonneg _) (hb z)
  · intro z w hzw
    show chi z * chi z = chi w * chi w
    rw [hper z w hzw]
  · intro z hz
    show chi z * chi z = 0
    rw [hvanish z hz, zero_mul]
  · intro z hz
    show chi z * chi z = 0
    rw [hstrict z hz, zero_mul]

private lemma re_finsum_of_finiteSupport_lz (g : ℂ → ℂ)
    (hfs : Function.HasFiniteSupport g) : (∑ᶠ u, g u).re = ∑ᶠ u, (g u).re := by
  have h := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) hfs
  simpa using h

/-- **The one-sided rebasing inequality with base point `-2`.** -/
theorem re_logDeriv_le_re_of_pf_negTwo_local (Lam : ℂ → ℂ) (hDiff : Differentiable ℂ Lam)
    (hpf : ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
        (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)))
    (hzeros : ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    {σ γ : ℝ} (hσ : 1 < σ)
    (hs : Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0)
    (hs₁ : Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0) :
    (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
        / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
          / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ Lam (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hDiff _
  have hupper : ∀ u : ℂ, Lam u = 0 → u.re ≤ σ := fun u hu => by
    have := (hzeros u hu).2
    linarith
  have hlower : ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re := fun u hu => (hzeros u hu).1
  have hpoint : ∀ (R : ℝ) (u : ℂ),
      0 ≤ ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))).re := by
    intro R u
    by_cases hD : (MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u = 0
    · rw [hD]; simp
    · have hzero : Lam u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R) hD
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im
          = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      exact mul_nonneg (Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) u)
        (re_rebase_nonneg_negTwo (σ := σ) (γ := γ) (u := u) hσ
          (hlower u hzero) (hupper u hzero))
  have hfsAll : ∀ R : ℝ, Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))) := by
    intro R
    refine ((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hd
    exact hu (by rw [hd]; simp)
  have hnonneg : ∀ R : ℝ, 0 ≤ (∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u)))).re := by
    intro R
    have hfs := hfsAll R
    have hfs' : Function.HasFiniteSupport (fun u : ℂ =>
        ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
              - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))).re) :=
      hfs.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp))
    have hle := single_le_finsum ((0 : ℂ)) hfs' (fun j => hpoint R j)
    have h0 := hpoint R (0 : ℂ)
    rw [re_finsum_of_finiteSupport_lz _ hfs]
    linarith
  have hlim : Filter.Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u)))).re) Filter.atTop
      (nhds ((deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
          / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
        - deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
            / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (hpf ((σ : ℂ) + (γ : ℂ) * Complex.I) ((-2 : ℂ) + (γ : ℂ) * Complex.I) hs hs₁)
  have hge : 0 ≤ (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
        / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
      - deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
          / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re :=
    ge_of_tendsto hlim (Eventually.of_forall hnonneg)
  rw [Complex.sub_re] at hge
  linarith

/-- The conductor-normalised functional equation, from the collision-free clean provider. -/
private theorem condFE_local :
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      Work.FIArea6Hecke.R.HasConductorFE d chi m :=
  fun d chi m hd hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt

/-- **The one-sided lower bound for `Re (Λ'/Λ)` in `1 < re s ≤ 2`.** -/
theorem logDerivOneSidedPF_local :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
        Work.FIArea6Hecke.R.IsCompleted d chi m Lam →
        ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
          -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |τ| + 3)))
            ≤ (deriv Lam ((σ : ℂ) + (τ : ℂ) * Complex.I) /
                Lam ((σ : ℂ) + (τ : ℂ) * Complex.I)).re := by
  obtain ⟨C, hCpos, hbase⟩ := pfacBaseLowerUniform condFE_local
  refine ⟨C, hCpos, ?_⟩
  intro d chi m Lam hadm σ τ hσ _
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  have hadm' : Work.FIArea6Hecke.R.IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hDiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  have hpf := lamPartialFraction d chi m Lam hadm' (lamGrowth d chi m Lam hadm')
  have hzeros := zerosInStrip_of_conductorFE condFE_local d chi m Lam hadm'
  have hs : Lam ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 :=
    lam_ne_zero_of_one_lt_re_zz hd hAn h1 hmul hb hagr (by simpa using hσ)
  have hs₁ : Lam ((-2 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have h := (hzeros _ h0).1
    simp at h
  have hineq := re_logDeriv_le_re_of_pf_negTwo_local Lam hDiff hpf hzeros hσ hs hs₁
  have hbase' := hbase d chi m Lam hadm' τ
  linarith

/-- **The near-zero lower bound for `Re (Λ'/Λ)`, `0 < β ≤ 1`.** -/
theorem logDerivNearZeroPF_local :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
        Work.FIArea6Hecke.R.IsCompleted d chi m Lam →
        ∀ σ β γ : ℝ, 1 < σ → σ ≤ 2 → 0 < β → β ≤ 1 →
          Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
          1 / (σ - β) - C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) ≤
            (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) /
              Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨C, hCpos, hbase⟩ := pfacBaseLowerUniform condFE_local
  refine ⟨C, hCpos, ?_⟩
  intro d chi m Lam hadm σ β γ hσ hσ2 hβ0 hβ1 hzero
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hadm' : Work.FIArea6Hecke.R.IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
  have hDiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  have hpf := lamPartialFraction d chi m Lam hadm' (lamGrowth d chi m Lam hadm')
  have hzeros := zerosInStrip_of_conductorFE condFE_local d chi m Lam hadm'
  have hσre : (1 : ℝ) < ((σ : ℂ) + (γ : ℂ) * Complex.I).re := by simpa using hσ
  have hs : Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
    lam_ne_zero_of_one_lt_re_zz hd hAn h1 hmul hb hagr hσre
  have hs₁ : Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have h := (hzeros _ h0).1
    simp at h
  have hρ : Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := hzero
  have hreb := re_logDeriv_rebase_negTwo Lam hDiff hpf hzeros hσ hβ0 hβ1 hρ hs hs₁
  have hbase' := hbase d chi m Lam hadm' γ
  linarith

/-! ## The target -/

/-- **The non-self-dual case of *FI* (16.20).**  The de la Vallee Poussin zero-free region
`re s > 1 - c/log(4d + |m| + |im s|)` (`re s <= 2`) for an entire completion `Lam` of the Hecke
`L`-function of a strict character `chi` mod `4d`, *in the case that the pair is not self-dual*
(`¬ SelfDual d chi m`, i.e. `psi_{chi,m}(z)^2 != 1` for some primary unit `z` mod `4d`).

In this case there is no exceptional real zero (the classical (16.20) admits an exception only for
an `L`-function with real Dirichlet coefficients, i.e. for a self-dual pair), so no exception
appears: the claim is uniform in all the data.

This is the complement of `Work.FIArea6Hecke.R.zfrOffAxisSdSelfDual` (the self-dual case, already
proved), so that the two together give `Work.FIArea6Hecke.R.ZFRoffAxisSd`. -/
theorem zfrOffAxisSdNonSelfDualV2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ¬ Work.FIArea6Hecke.R.SelfDual d chi m →
        ∀ s : ℂ,
          1 - c / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
  obtain ⟨C₁, hC₁nn, hAxis⟩ := HeckeAxisLogDerivBound
  obtain ⟨Cnz, hCnzpos, hNz⟩ := logDerivNearZeroPF_local
  obtain ⟨Cone, hConepos, hOne⟩ := logDerivOneSidedPF_local
  set C₀ : ℝ := 3 * C₁ + 4 * Cnz + 160 + 2 * Cone + 80 + 1 with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀1 : 1 ≤ C₀ := by rw [hC₀def]; linarith
  refine ⟨1 / (28 * C₀), by positivity, ?_⟩
  intro d chi m Lam hd hchi hAn hagr hnsd s hreg hsle2
  have hne2 : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      (Work.FIArea5.S16Hecke.psi chi m z) ^ 2 ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
        Work.FIArea5.S16Hecke.IsUnitMod4d d z →
        (Work.FIArea5.S16Hecke.psi chi m z) ^ 2 = 1 := by
      intro z hzp hzu
      by_contra hne
      exact hcon ⟨z, hzp, hzu, hne⟩
    exact hnsd hcon'
  by_cases hs1 : 1 < s.re
  · exact div_ne_zero
      (lam_ne_zero_of_one_lt_re_zz hd hAn hchi.1.1 hchi.1.2.1 hchi.1.2.2.1 hagr hs1)
      (heckeArch_ne_zero_of_pos_re d hd m (by linarith))
  · have hsle1 : s.re ≤ 1 := le_of_not_gt hs1
    intro hLval0
    set β : ℝ := s.re with hβdef
    set γ : ℝ := s.im with hγdef
    have hs_eq : s = (β : ℂ) + (γ : ℂ) * Complex.I := by
      rw [hβdef, hγdef]; apply Complex.ext <;> simp
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hγ0 : (0 : ℝ) ≤ |γ| := abs_nonneg γ
    set L : ℝ := Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) with hLdef
    set L₀ : ℝ := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |γ|) with hL₀def
    have hLpos : 0 < L := by
      rw [hLdef]; exact Real.log_pos (by nlinarith)
    have hL1 : 1 ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le (by nlinarith)]
      have h3 := Real.exp_one_lt_three
      nlinarith [hd1, hm0, hγ0]
    have hL₀pos : 0 < L₀ := by
      rw [hL₀def]; exact Real.log_pos (by nlinarith)
    have hL_le : L ≤ 2 * L₀ := by
      rw [hLdef, hL₀def]
      have hsq : 4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)
          ≤ (4 * (d : ℝ) + |(m : ℝ)| + |γ|) ^ 2 := by
        nlinarith [hd1, hm0, hγ0, sq_nonneg (m : ℝ), sq_nonneg γ]
      calc Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))
          ≤ Real.log ((4 * (d : ℝ) + |(m : ℝ)| + |γ|) ^ 2) :=
            Real.log_le_log (by positivity) hsq
        _ = 2 * Real.log (4 * (d : ℝ) + |(m : ℝ)| + |γ|) := by rw [Real.log_pow]; ring
    have hreg' : 1 - (1 / (28 * C₀)) / L₀ < β := by
      rw [hL₀def, hγdef, hβdef]
      exact hreg
    have hβpos : 0 < β := by
      have hclt : (1 / (28 * C₀)) / L₀ < 1 := by
        rw [div_lt_one hL₀pos]
        have hle : 1 / (28 * C₀) ≤ 1 / 28 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith
      linarith [hreg', hclt]
    have hsre_pos : 0 < s.re := by rw [hβdef] at hβpos; exact hβpos
    have hβ1 : β ≤ 1 := by rw [hβdef]; exact hsle1
    set x : ℝ := 1 / (2 * C₀ * L) with hxdef
    have hxpos : 0 < x := by rw [hxdef]; positivity
    have hxle1 : x ≤ 1 := by
      rw [hxdef, div_le_one (by positivity)]
      nlinarith [hC₀1, hL1]
    set σ : ℝ := 1 + x with hσdef
    have hσ1 : 1 < σ := by rw [hσdef]; linarith
    have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
    have hσβpos : 0 < σ - β := by linarith [hβ1, hσ1]
    have hArchne : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
      heckeArch_ne_zero_of_pos_re d hd m hsre_pos
    have hLams : Lam s = 0 := by
      have h0 : Lam s / Work.FITop4.Bridge.heckeArch d m s = 0 := by
        simpa only [Work.FIArea6Hecke.Lval] using hLval0
      exact (div_eq_zero_iff.mp h0).resolve_right hArchne
    have hρ : Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
      rw [← hs_eq]; exact hLams
    have hAdm : Work.FIArea6Hecke.R.IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
    have h341 := HeckeLDerivRe341 d chi m hd hchi (σ := σ) (t := γ) hσ1
    have hre1 : ((σ : ℂ) + (γ : ℂ) * Complex.I).re = σ := by simp
    have him1 : ((σ : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have hA : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries
            (Work.FIArea6Hecke.principalStrict d) 0) ((σ : ℂ)) /
          Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 ((σ : ℂ))).re
        ≤ 1 / x + C₁ := by
      have h := hAxis d hd σ hσ1 hσ2
      have hx' : σ - 1 = x := by rw [hσdef]; ring
      rwa [hx'] at h
    have hB : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m)
            ((σ : ℂ) + (γ : ℂ) * Complex.I) /
          Work.FIArea5.S16Hecke.heckeLSeries chi m ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ -(1 / (σ - β)) + Cnz * L + 40 * L := by
      have hid := neg_re_L_eq d hd hAn hchi.1.1 hchi.1.2.1 hchi.1.2.2.1 hagr
        (s := ((σ : ℂ) + (γ : ℂ) * Complex.I)) (by rw [hre1]; exact hσ1)
      rw [hid]
      have hnz := hNz d chi m Lam hAdm σ β γ hσ1 hσ2 hβpos hβ1 hρ
      rw [← hLdef] at hnz
      have harch := archLogDeriv_re_le d hd m (s := ((σ : ℂ) + (γ : ℂ) * Complex.I))
        (by rw [hre1]; linarith) (by rw [hre1]; linarith)
      rw [him1, ← hLdef] at harch
      linarith [hnz, harch]
    have hchi₂ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (fun z => chi z * chi z) :=
      isCharMod4dStrict_sq_local hchi
    have hne₂ : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2 * m) z ≠ 1 := by
      obtain ⟨z, hzp, hzu, hz⟩ := hne2
      refine ⟨z, hzp, hzu, ?_⟩
      rw [show Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2 * m) z
            = (Work.FIArea5.S16Hecke.psi chi m z) ^ 2 from by rw [psi_sq, pow_two]]
      exact hz
    obtain ⟨Lam₂, hAn₂, hagr₂⟩ :=
      heckeCompletionImprimitive d (fun z => chi z * chi z) (2 * m) hd hchi₂ hne₂
    have hAdm₂ : Work.FIArea6Hecke.R.IsCompleted d (fun z => chi z * chi z) (2 * m) Lam₂ :=
      ⟨hd, hchi₂, hAn₂, hagr₂⟩
    have hre2 : ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I).re = σ := by simp
    have him2 : ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I).im = 2 * γ := by simp
    set L' : ℝ := Real.log (4 * (d : ℝ) * (|(((2 * m : ℤ)) : ℝ)| + |(2 * γ)| + 3)) with hL'def
    have hs₂re : 1 < ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I).re := by
      rw [hre2]; exact hσ1
    have hC : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2 * m))
            ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I) /
          Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2 * m)
            ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I)).re
        ≤ Cone * L' + 40 * L' := by
      have hid₂ := neg_re_L_eq d hd (chi := fun z => chi z * chi z) (m := 2 * m)
        hAn₂ hchi₂.1.1 hchi₂.1.2.1 hchi₂.1.2.2.1 hagr₂
        (s := ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I)) hs₂re
      rw [hid₂]
      have hone := hOne d (fun z => chi z * chi z) (2 * m) Lam₂ hAdm₂ σ (2 * γ) hσ1 hσ2
      rw [← hL'def] at hone
      have harch₂ := archLogDeriv_re_le d hd (2 * m)
        (s := ((σ : ℂ) + (((2 * γ : ℝ)) : ℂ) * Complex.I))
        (by rw [hre2]; linarith) (by rw [hre2]; linarith)
      rw [him2, ← hL'def] at harch₂
      linarith [hone, harch₂]
    have hL'le : L' ≤ 2 * L := by
      have habs2m : |(((2 * m : ℤ)) : ℝ)| = 2 * |(m : ℝ)| := by
        rw [show (((2 * m : ℤ)) : ℝ) = 2 * (m : ℝ) by push_cast; ring, abs_mul]
        norm_num
      have habs2γ : |(2 * γ)| = 2 * |γ| := by rw [abs_mul]; norm_num
      have hle : 4 * (d : ℝ) * (|(((2 * m : ℤ)) : ℝ)| + |(2 * γ)| + 3)
          ≤ 2 * (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
        rw [habs2m, habs2γ]; nlinarith [hd1, hm0, hγ0]
      rw [hL'def]
      have h1 : Real.log (4 * (d : ℝ) * (|(((2 * m : ℤ)) : ℝ)| + |(2 * γ)| + 3))
          ≤ Real.log (2 * (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))) :=
        Real.log_le_log (by positivity) hle
      have h2 : Real.log (2 * (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          = Real.log 2 + L := by
        rw [Real.log_mul (by norm_num) (by positivity), ← hLdef]
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      linarith [h1, h2.le, h2.ge, hlog2, hL1]
    have hkey : 4 * (1 / (σ - β))
        ≤ 3 * (1 / x) + 3 * C₁ + 4 * (Cnz * L + 40 * L) + (Cone * L' + 40 * L') := by
      linarith [h341, hA, hB, hC]
    have hkey' : 4 * (1 / (σ - β)) ≤ 7 * C₀ * L := by
      have hxinv : 3 * (1 / x) = 6 * C₀ * L := by rw [hxdef]; field_simp; ring
      have hC₁bd : 3 * C₁ ≤ 3 * C₁ * L := by nlinarith [hC₁nn, hL1]
      have hL'bd : Cone * L' + 40 * L' ≤ (Cone + 40) * (2 * L) := by
        nlinarith [hL'le, hConepos]
      have hC₀bd : 3 * C₁ + 4 * Cnz + 160 + 2 * Cone + 80 ≤ C₀ := by
        rw [hC₀def]; linarith
      nlinarith [hkey, hxinv, hC₁bd, hL'bd, hC₀bd, hLpos, hC₀pos]
    have hσβne : σ - β ≠ 0 := ne_of_gt hσβpos
    have h7pos : 0 < 7 * C₀ * L := by positivity
    have hge : 4 / (7 * C₀ * L) ≤ σ - β := by
      rw [div_le_iff₀ h7pos]
      have h := mul_le_mul_of_nonneg_right hkey' hσβpos.le
      have hc : 4 * (1 / (σ - β)) * (σ - β) = 4 := by
        rw [mul_assoc, one_div_mul_cancel hσβne, mul_one]
      rw [show (7 * C₀ * L) * (σ - β) = (σ - β) * (7 * C₀ * L) by ring] at h
      linarith [h, hc]
    have h1β : 1 - β ≥ 1 / (14 * C₀ * L) := by
      have hsub : 1 - β = (σ - β) - x := by rw [hσdef]; ring
      have harith : 4 / (7 * C₀ * L) - 1 / (2 * C₀ * L) = 1 / (14 * C₀ * L) := by
        field_simp; ring
      rw [hsub, ← harith]
      linarith [hge, hxdef]
    have hfin : 1 / (28 * C₀ * L₀) ≤ 1 / (14 * C₀ * L) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hL_le]
    have hreg'' : 1 - β < 1 / (28 * C₀ * L₀) := by
      have he : (1 / (28 * C₀)) / L₀ = 1 / (28 * C₀ * L₀) := by rw [div_div]
      linarith [hreg', he]
    linarith [h1β, hfin, hreg'']

end

end Work.FIArea6Hecke.R
