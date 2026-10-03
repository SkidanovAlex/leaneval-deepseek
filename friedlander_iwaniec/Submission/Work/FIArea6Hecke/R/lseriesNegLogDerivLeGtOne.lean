/-
# `Submission.Work.FIArea6Hecke.R.lseriesNegLogDerivLeGtOne`

**The one-sided lower bound for `-Re (L'/L)` of the Hecke `L`-series itself**, uniformly in the
data, in the elementary region `1 < re s ≤ 2`:

  `-Re ((L(s,ψ))′/L(s,ψ)) ≤ C·log(4d(|m|+|s.im|+3))`

for every strict character `χ` mod `4d` (`1 ≤ d`), every `m : ℤ` and every `s` with
`1 < re s ≤ 2`, with one constant `C` valid simultaneously for all data.  This is the shape in
which the one-sided bound of *FI* (16.20) restricted to the *elementary* half-plane `re s > 1` (no
zero-free region needed) is consumed downstream.

The proof has three ingredients, none of which requires new analysis:

* `heckeCompletionImprimitive` produces an entire completion `Λ` of the Hecke `L`-series of
  `ψ_m(z) = χ(z)(z/|z|)^m` from the non-degeneracy hypothesis
  `∃ z primary, z a unit mod 4d, ψ_m(z) ≠ 1` (which is exactly what makes `ψ_m` a non-principal
  Größencharacter, so that `L(·,ψ_m)` is entire);
* the one-sided bound for *any* such completion, `lseriesNLD_oneSided` below: the Hadamard partial
  fraction at the pair `(σ+iγ, -2+iγ)` (`lamPartialFraction_of_growth`, fed by the circle growth
  `lamGrowth`), every zero of `Λ` lying in `[-1,1]` (`zerosInStrip_of_conductorFE`, fed by the
  conductor-normalised functional equation `RC.conductorFECleanNoDep`), so that every summand of the
  partial fraction has nonnegative real part, reduces the bound at `σ+iγ` to the uniform base bound
  at `-2+iγ` (`pfacBaseLowerUniform`);
* the transport from the completion to the `L`-series: `Lval d m Λ = Λ/heckeArch` agrees with
  `heckeLSeries χ m` on `re s > 1` (`Lam_eq_heckeArch_mul_of_one_lt_re`, the identity theorem for
  the `L`-series), so `(heckeLSeries)′/heckeLSeries = Λ′/Λ − (heckeArch)′/heckeArch` at `s`
  (`lval_logDeriv_eq`), the archimedean term costing at most `7·log(4d(|m|+|s.im|+3))`
  (`logDeriv_heckeArch_re_le`) in the strip `1/2 ≤ re s ≤ 2`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.re_logDeriv_rebase_negTwo
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.lamGrowth
import Submission.Work.FIArea6Hecke.R.zerosInStrip
import Submission.Work.FIArea6Hecke.R.pfacBaseLowerUniform
import Submission.Work.FIArea6Hecke.R.conductorFECleanNoDep

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped BigOperators Topology

noncomputable section

/-! ## The one-sided rebasing inequality at the base point `-2` -/

/-- Real part of a finitely supported `finsum`. -/
private lemma lseriesNLD_re_finsum {g : ℂ → ℂ} (hfs : Function.HasFiniteSupport g) :
    (∑ᶠ u, g u).re = ∑ᶠ u, (g u).re := by
  have h := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) hfs
  simpa using h

/-- **The one-sided rebasing inequality with base point `-2`.**  If `Λ` admits the Hadamard
partial fraction and all of its zeros satisfy `-1 ≤ re u ≤ 1`, then for `1 < σ` the logarithmic
derivative at `σ + iγ` dominates the one at `-2 + iγ`: at every zero `u` of `Λ` the rebasing kernel

  `Re (1/(σ+iγ-u) - 1/(-2+iγ-u)) = (σ - re u)/|σ+iγ-u|² + (2 + re u)/|-2+iγ-u|²`

has both terms `≥ 0`, because `re u ≤ 1 < σ` and `re u ≥ -1`. -/
private theorem lseriesNLD_re_logDeriv_le_re_of_pf (Lam : ℂ → ℂ) (hDiff : Differentiable ℂ Lam)
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
  -- pointwise nonnegativity of every summand
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
    rw [lseriesNLD_re_finsum hfs]
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

/-! ## The one-sided bound for an arbitrary completion -/

private theorem lseriesNLD_oneSided :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ σ γ : ℝ, 1 < σ → σ ≤ 2 →
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
              / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨C, hCpos, hbase⟩ := pfacBaseLowerUniform
    (fun d chi m hd hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt)
  refine ⟨C, hCpos, ?_⟩
  intro d chi m Lam hadm σ γ hσ hσ2
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  have hadm' : IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hDiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  -- `Λ` does not vanish on `re s > 1`
  have hs : Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
    lam_ne_zero_of_one_lt_re_zz (Λ := Lam) hd hAn h1 hmul hb hagr
      (s := (σ : ℂ) + (γ : ℂ) * Complex.I) (by simpa using hσ)
  -- nor at `2 + iγ`, so a Hadamard partial fraction is available
  have h2 : Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
    lam_ne_zero_of_one_lt_re_zz (Λ := Lam) hd hAn h1 hmul hb hagr
      (s := (2 : ℂ) + (γ : ℂ) * Complex.I) (by simp)
  have hpf := lamPartialFraction_of_growth Lam hDiff
    ⟨(2 : ℂ) + (γ : ℂ) * Complex.I, h2⟩ (lamGrowth d chi m Lam hadm')
  -- the zeros of `Λ` lie in `[-1,1]` (conductor-normalised functional equation)
  have hzeros := zerosInStrip_of_conductorFE
    (fun d chi m hd hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt) d chi m Lam hadm'
  -- the base point `-2 + iγ` lies outside the strip of the zeros
  have hs₁ : Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have h := (hzeros _ h0).1
    simp at h
  have hineq := lseriesNLD_re_logDeriv_le_re_of_pf Lam hDiff hpf hzeros hσ hs hs₁
  have hbase' := hbase d chi m Lam hadm' γ
  linarith

/-! ## The Hecke `L`-series itself -/

theorem lseriesNegLogDerivLeGtOne :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      ∀ σ γ : ℝ, 1 < σ → σ ≤ 2 →
        -((deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) ((σ : ℂ) + (γ : ℂ) * Complex.I) /
          Work.FIArea5.S16Hecke.heckeLSeries chi m ((σ : ℂ) + (γ : ℂ) * Complex.I)).re)
        ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
  obtain ⟨C, hCpos, hC⟩ := lseriesNLD_oneSided
  refine ⟨C + 7, by linarith, ?_⟩
  intro d chi m hd hchi hne σ γ hσ hσ2
  obtain ⟨Lam, hAn, hagr⟩ := heckeCompletionImprimitive d chi m hd hchi hne
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hlog : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg γ
    nlinarith
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hsdef
  have hsr : s.re = σ := by simp [hsdef]
  have hsi : s.im = γ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsr]; exact hσ
  by_cases hL0 : Work.FIArea5.S16Hecke.heckeLSeries chi m s = 0
  · -- `L(s,ψ) = 0`: the left-hand side is `0` (`x/0 = 0`), the right-hand side is nonnegative
    rw [hL0, div_zero, Complex.zero_re, neg_zero]
    exact mul_nonneg (by linarith) hlog
  · -- the completion, its one-sided bound at `s`, and the archimedean log-derivative
    have hmain := hC d chi m Lam ⟨hd, hchi, hAn, hagr⟩ σ γ hσ hσ2
    rw [← hsdef] at hmain
    have harch := logDeriv_heckeArch_re_le d hd m (s := s)
      (by rw [hsr]; linarith) (by rw [hsr]; exact hσ2)
    rw [logDeriv_apply] at harch
    rw [hsi] at harch
    -- `Lval d m Lam` *is* the `L`-series near `s` (`re s > 1`)
    have hEv : Work.FIArea6Hecke.Lval d m Lam =ᶠ[𝓝 s] Work.FIArea5.S16Hecke.heckeLSeries chi m := by
      refine Filter.eventually_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1)
        (fun z hz => ?_)
      rw [Work.FIArea6Hecke.Lval,
        Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hz]
      exact mul_div_cancel_left₀ _ (heckeArch_ne_zero_of_one_lt_re hd m hz)
    have hLval_ne : Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
      rw [Filter.EventuallyEq.eq_of_nhds hEv]; exact hL0
    have hLam_ne : Lam s ≠ 0 := by
      intro h0
      exact hLval_ne (by rw [Work.FIArea6Hecke.Lval, h0, zero_div])
    have hident := lval_logDeriv_eq d hd (m := m) hAn (s := s)
      (by rw [hsr]; linarith) hLam_ne
    have hcongr : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        = logDeriv (Work.FIArea6Hecke.Lval d m Lam) s :=
      (logDeriv_congr_nhds hEv).eq_of_nhds.symm
    -- `(L)′/L = Λ′/Λ − (heckeArch)′/heckeArch` at `s`
    have hLlog : deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s /
          Work.FIArea5.S16Hecke.heckeLSeries chi m s
        = deriv Lam s / Lam s - deriv (fun z => Work.FITop4.Bridge.heckeArch d m z) s /
            Work.FITop4.Bridge.heckeArch d m s := by
      rw [← logDeriv_apply, hcongr, logDeriv_apply, hident]
    rw [hLlog, Complex.sub_re]
    nlinarith [hmain, harch]

end

end Work.FIArea6Hecke.R

