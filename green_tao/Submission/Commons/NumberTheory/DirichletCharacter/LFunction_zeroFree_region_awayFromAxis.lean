import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_logDeriv_re_regular_bound
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound

open Complex DirichletCharacter MeromorphicOn Filter Set
open scoped Real BigOperators Topology

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Zero-free region of `L(s,χ)` off the real axis

Target: for a primitive non-trivial Dirichlet character `χ` modulo `N` there is `c > 0`
with `L(χ, σ + it) ≠ 0` whenever `|t| ≥ 1` and `σ ≥ 1 - c / log (N * (|t|+2))`.

Analytic engine: the divisor-decomposition bound
`Commons.Analysis.Complex.logDeriv_sub_divisor_le` for the completed `L`-function on a disk
centred at `2 + iτ`, the growth bound `completedL_growth_circle` on circles about `0`, and a
lower bound for `‖completedLFunction ψ (2 + iτ)‖` obtained from a sharp lower bound for the
Archimedean Gamma factor.
-/

private lemma re_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ S, f i).re = ∑ i ∈ S, (f i).re := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a A' ha ih; rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

private lemma one_div_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (1 / z).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz (Complex.normSq_nonneg z)

private theorem completedLFunction_logDeriv_re_pole_bound {M : ℕ} [NeZero M]
    (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1) (hψprim : ψ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ β : ℝ, 1 < σ → σ ≤ 5 / 4 → 1 ≤ |τ| → 0 < β → β < 1 →
      DirichletCharacter.completedLFunction ψ ((β : ℂ) + Complex.I * (τ : ℂ)) = 0 →
      (logDeriv (DirichletCharacter.completedLFunction ψ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≥
      1 / (σ - β) - C * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction ψ
  let B : ℂ := logDeriv Λ 0
  refine ⟨‖B‖ + 2, by positivity, ?_⟩
  intro σ τ β hσ1 hσ2 hτ hβ0 hβ1 hzero
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hsdef
  set ρ : ℂ := (β : ℂ) + Complex.I * (τ : ℂ) with hρdef
  have hsr : s.re = σ := by simp [hsdef]
  have hsi : s.im = τ := by simp [hsdef]
  have hρr : ρ.re = β := by simp [hρdef]
  have hΛs : Λ s ≠ 0 := by
    intro hz
    have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip ψ hψ hψprim hz
    rw [hsr] at hstrip
    linarith [hstrip.2]
  have hΛ0 : Λ 0 ≠ 0 := by
    simpa [Λ] using Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero ψ hψ hψprim
  have hΛne : Λ ≠ 0 := fun hcon => hΛ0 (congrFun hcon 0)
  have hbound : ∀ R : ℝ, max ‖ρ‖ 2 ≤ R →
      1 / (σ - β) ≤ ((∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))).re := by
    intro R hR
    let d : ℂ → ℤ := fun u => (MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u
    have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall (0:ℂ) R) :=
      fun z _ => (differentiable_completedLFunction hψ).analyticAt z
    have hsupp : (Function.support d).Finite := by
      show (Function.support (fun u => (MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u)).Finite
      exact MeromorphicOn.divisor_support_finite_of_subset
        (f := Λ) (U := Metric.closedBall (0:ℂ) R) (V := Metric.closedBall (0:ℂ) R)
        hAn.meromorphicOn (isCompact_closedBall (0:ℂ) R) (fun z hz => hz)
    let S : Finset ℂ := hsupp.toFinset
    have hS_mem : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
      intro u; dsimp [S]; rw [Set.Finite.mem_toFinset]; rfl
    have hsub : Function.support (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))
        ⊆ (S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS_mem u).mpr (fun hd0 => hu (by simp [hd0]))
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℂ) *
      (1 / (s - u) + 1 / u)) hsub, re_sum]
    have hρS : ρ ∈ S := by
      have hρball : ρ ∈ Metric.closedBall (0:ℂ) R := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hρR : ‖ρ‖ ≤ R := le_trans (le_max_left _ _) hR
        simpa using hρR
      have hdρ : d ρ ≠ 0 := by
        show (MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) ρ ≠ 0
        exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero
          (differentiable_completedLFunction hψ) hΛne hρball (by simpa [Λ, hρdef] using hzero)
      exact (hS_mem ρ).mpr hdρ
    refine le_trans ?_ (Finset.single_le_sum (f := fun u => (((d u : ℤ) : ℂ) *
      (1 / (s - u) + 1 / u)).re) (fun u hu => ?_) hρS)
    · -- the `ρ` term
      have hdρ1 : (1 : ℝ) ≤ ((d ρ : ℤ) : ℝ) := by
        have hnnR : (0 : ℝ) ≤ ((d ρ : ℤ) : ℝ) :=
          Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn ρ
        have hne : ((d ρ : ℤ) : ℝ) ≠ 0 := by
          intro h0
          exact (hS_mem ρ).mp hρS (by exact_mod_cast h0)
        have h1 : (0:ℝ) < ((d ρ : ℤ) : ℝ) := lt_of_le_of_ne hnnR (Ne.symm hne)
        have h2 : (1:ℤ) ≤ d ρ := by exact_mod_cast h1
        exact_mod_cast h2
      have hsp : s - ρ = ((σ - β : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [hsr, hρr]
        · simp [hsi, hρdef]
      have hρne : ρ ≠ 0 := by
        intro h
        have h2 : τ = 0 := by
          have := congrArg Complex.im h
          simpa [hρdef] using this
        rw [h2] at hτ
        norm_num at hτ
      have hpos : 0 < σ - β := by linarith
      have h1m : (1 / (s - ρ)).re = 1 / (σ - β) := by
        rw [hsp, one_div, Complex.inv_re, Complex.ofReal_re, Complex.normSq_ofReal]
        field_simp
      have hre : (((d ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)).re
          = ((d ρ : ℤ) : ℝ) * (1 / (σ - β) + (1 / ρ).re) := by
        rw [Complex.mul_re]
        have hdre : (((d ρ : ℤ) : ℂ).re) = ((d ρ : ℤ) : ℝ) := by simp
        have hdim : (((d ρ : ℤ) : ℂ).im) = 0 := by simp
        rw [hdre, hdim, zero_mul, sub_zero, Complex.add_re, h1m]
      have hβn : 0 ≤ (1 / ρ).re := one_div_re_nonneg (by rw [hρr]; exact hβ0.le)
      rw [hre]
      have h2 : (1 : ℝ) * (1 / (σ - β) + (1 / ρ).re)
          ≤ ((d ρ : ℤ) : ℝ) * (1 / (σ - β) + (1 / ρ).re) :=
        mul_le_mul_of_nonneg_right hdρ1 (by positivity)
      calc 1 / (σ - β) ≤ 1 * (1 / (σ - β) + (1 / ρ).re) := by
            rw [one_mul]; linarith
        _ ≤ ((d ρ : ℤ) : ℝ) * (1 / (σ - β) + (1 / ρ).re) := h2
    · -- every term is nonnegative
      have hdu : d u ≠ 0 := (hS_mem u).mp hu
      have hzu : Λ u = 0 := Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn hdu
      have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip ψ hψ hψprim hzu
      have hdnn : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := by
        exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn u
      have hK : 0 ≤ (1 / (s - u) + 1 / u).re := by
        rw [Complex.add_re]
        refine add_nonneg (one_div_re_nonneg ?_) (one_div_re_nonneg ?_)
        · rw [Complex.sub_re, hsr]; linarith [hstrip.2]
        · linarith [hstrip.1]
      rw [Complex.mul_re]
      have hdre : (((d u : ℤ) : ℂ).re) = ((d u : ℤ) : ℝ) := by simp
      have hdim : (((d u : ℤ) : ℂ).im) = 0 := by simp
      rw [hdre, hdim, zero_mul, sub_zero]
      exact mul_nonneg hdnn hK
  -- pass to the limit
  have hpf := Commons.NumberTheory.Linnik.partialFraction_eq ψ hψ hψprim s hΛs
  have hpf' : Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) *
        (1 / (s - u) + 1 / u)) atTop (𝓝 (logDeriv Λ s - B)) := by
    have heq : deriv Λ s / Λ s - deriv Λ 0 / Λ 0 = logDeriv Λ s - B := by
      simp only [logDeriv_apply, B, Λ]
    exact heq ▸ hpf
  have hlim : Tendsto (fun R : ℝ => ((∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) *
        (1 / (s - u) + 1 / u))).re) atTop (𝓝 ((logDeriv Λ s - B).re)) :=
    (Complex.continuous_re.tendsto _).comp hpf'
  have hge : 1 / (σ - β) ≤ (logDeriv Λ s - B).re :=
    isClosed_Ici.mem_of_tendsto hlim
      (Filter.eventually_atTop.mpr ⟨max ‖ρ‖ 2, fun R hR => hbound R hR⟩)
  have hBre : B.re ≥ -(‖B‖) := by
    have := Complex.abs_re_le_norm B
    rw [abs_le] at this
    linarith [this.1]
  have hfin : (logDeriv Λ s).re ≥ 1 / (σ - β) - ‖B‖ := by
    have : (logDeriv Λ s).re = (logDeriv Λ s - B).re + B.re := by
      rw [Complex.sub_re]; ring
    rw [this]; linarith
  have hlogfac : (1:ℝ) ≤ Real.log ((M : ℝ) * (|τ| + 2)) + 1 := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have hMn : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne M))
      exact_mod_cast hMn
    have hprod : (3:ℝ) ≤ (M : ℝ) * (|τ| + 2) := by
      have h1 : (1:ℝ) * 3 ≤ (M:ℝ) * (|τ| + 2) := by
        apply mul_le_mul <;> linarith [abs_nonneg τ]
      linarith
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ (M:ℝ) * (|τ| + 2))
    linarith
  have hC : ‖B‖ + 2 ≤ (‖B‖ + 2) * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
    have h0 : (0:ℝ) ≤ ‖B‖ + 2 := by positivity
    calc ‖B‖ + 2 = (‖B‖ + 2) * 1 := by ring
      _ ≤ (‖B‖ + 2) * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) :=
          mul_le_mul_of_nonneg_left hlogfac h0
  linarith


private lemma bracket_nonneg {w z : ℂ} (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hcase : z = w ^ 2 ∨ w = 0) : 0 ≤ 3 + 4 * w.re + z.re := by
  rcases hcase with h | h
  · rw [h, sq]
    have hns : (w * w).re = w.re * w.re - w.im * w.im := by
      rw [Complex.mul_re]
    have hnorm : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (1 + w.re), hw, hnorm, norm_nonneg w]
  · rw [h, Complex.zero_re]
    have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have h2 : -(1:ℝ) ≤ z.re := by
      have h3 := Complex.re_le_norm (-z)
      rw [Complex.neg_re] at h3
      have h4 : ‖(-z : ℂ)‖ = ‖z‖ := norm_neg z
      rw [h4] at h3
      linarith
    linarith

private lemma summable_LSeries_term {N : ℕ} (χ : DirichletCharacter ℂ N) {σ τ : ℝ}
    (hσ : 1 < σ) :
    Summable (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) ((σ : ℂ) + Complex.I * (τ : ℂ))) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
      (n : ℝ) ^ σ) ?_ ?_
  · exact Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hσ
  · intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hre : (((σ : ℂ) + Complex.I * (τ : ℂ))).re = σ := by simp
      rw [hre, if_neg hn]
      have hval : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := norm_le_one χ (n : ZMod N)
      have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      have hpos : (0:ℝ) < (n:ℝ) ^ σ := Real.rpow_pos_of_pos (by linarith) σ
      calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod N)‖ / (n:ℝ) ^ σ
          ≤ ArithmeticFunction.vonMangoldt n * 1 / (n:ℝ) ^ σ := by
            gcongr
        _ = ArithmeticFunction.vonMangoldt n / (n:ℝ) ^ σ := by ring

/-- The termwise inequality behind the three-four-one method: the combined `n`-th term of the
three Dirichlet series has nonnegative real part. -/
private lemma termwise_nonneg {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hval : ∀ a : ℤ, IsCoprime a (N : ℤ) → (ψ (a : ZMod M)) = ((χ (a : ZMod N)) : ℂ) ^ 2)
    {σ τ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
      + 4 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
          ((σ : ℂ) + Complex.I * (τ : ℂ)) n
      + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ))
          ((σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ)) n).re := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn
    have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    set s₁ : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs1
    set s₂ : ℂ := (σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ) with hs2
    set c : ℂ := (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) with hc
    set e : ℝ := (n : ℝ) ^ (-σ) with he
    have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    have h0 : (n : ℂ) ^ (-(σ : ℂ)) = ((e : ℝ) : ℂ) := by
      have hneg : (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
      rw [he, hbase, hneg, ← Complex.ofReal_cpow (le_of_lt hpos)]
    have h1 : (n : ℂ) ^ (-s₁) = ((e : ℝ) : ℂ) * c := by
      have harg : -s₁ = -(σ : ℂ) + (-(Complex.I * (τ : ℂ))) := by rw [hs1]; push_cast; ring
      calc (n : ℂ) ^ (-s₁) = (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) := by
            rw [harg, Complex.cpow_add _ _ hn0]
        _ = ((e : ℝ) : ℂ) * c := by rw [h0, hc]
    have h2 : (n : ℂ) ^ (-s₂) = ((e : ℝ) : ℂ) * c ^ 2 := by
      have harg : -s₂ = -(σ : ℂ) + (-(Complex.I * (τ : ℂ))) + (-(Complex.I * (τ : ℂ))) := by
        rw [hs2]; push_cast; ring
      calc (n : ℂ) ^ (-s₂)
          = (n : ℂ) ^ (-(σ : ℂ) + (-(Complex.I * (τ : ℂ)))) *
              (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) := by
            rw [harg, Complex.cpow_add _ _ hn0]
        _ = ((n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(Complex.I * (τ : ℂ)))) *
              (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) := by
            rw [Complex.cpow_add _ _ hn0]
        _ = ((e : ℝ) : ℂ) * c ^ 2 := by rw [h0, hc]; ring
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    rw [← Complex.cpow_neg, ← Complex.cpow_neg, ← Complex.cpow_neg]
    rw [h0, h1, h2]
    have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hfac : 3 * ((ArithmeticFunction.vonMangoldt n : ℂ) * ((e : ℝ) : ℂ))
        + 4 * ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * (((e : ℝ) : ℂ) * c))
        + (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ) * (((e : ℝ) : ℂ) * c ^ 2)
        = (((e : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
            (3 + 4 * ((χ (n : ZMod N) : ℂ) * c) + (ψ (n : ZMod M) : ℂ) * c ^ 2))) := by
      ring
    rw [hfac, Complex.mul_re, Complex.mul_re]
    simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero]
    have hw : ‖(χ (n : ZMod N) : ℂ) * c‖ ≤ 1 := by
      rw [norm_mul]
      have h1 : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := norm_le_one χ (n : ZMod N)
      have h2 : ‖c‖ = 1 := by
        rw [hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simp
      rw [h2, mul_one]
      exact h1
    have hz : ‖(ψ (n : ZMod M) : ℂ) * c ^ 2‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      have h1 : ‖(ψ (n : ZMod M) : ℂ)‖ ≤ 1 := norm_le_one ψ (n : ZMod M)
      have h2 : ‖c‖ = 1 := by
        rw [hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simp
      rw [h2, one_pow, mul_one]
      exact h1
    have hcase : (ψ (n : ZMod M) : ℂ) * c ^ 2 = ((χ (n : ZMod N) : ℂ) * c) ^ 2
        ∨ (χ (n : ZMod N) : ℂ) * c = 0 := by
      by_cases hcop : IsCoprime (n : ℤ) (N : ℤ)
      · left
        have h := hval (n : ℤ) hcop
        simp only [Int.cast_natCast] at h
        rw [h]; ring
      · right
        have : (χ (n : ZMod N) : ℂ) = 0 := by
          have hcast : (n : ZMod N) = ((n : ℤ) : ZMod N) := by push_cast; ring
          rw [hcast, DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)]
          exact hcop
        rw [this, zero_mul]
    have hZ : 0 ≤ (3 + 4 * ((χ (n : ZMod N) : ℂ) * c) + (ψ (n : ZMod M) : ℂ) * c ^ 2).re := by
      simpa [Complex.add_re] using bracket_nonneg hw hz hcase
    have he0 : 0 ≤ e := by
      rw [he]; positivity
    have hprod : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
        (3 + 4 * ((χ (n : ZMod N) : ℂ) * c) + (ψ (n : ZMod M) : ℂ) * c ^ 2).re :=
      mul_nonneg hΛ hZ
    have := mul_nonneg he0 hprod
    simpa using this

private lemma three_four_one_nonneg {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hval : ∀ a : ℤ, IsCoprime a (N : ℤ) → (ψ (a : ZMod M)) = ((χ (a : ZMod N)) : ℂ) ^ 2)
    {σ τ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re
      + (-logDeriv (DirichletCharacter.LFunction ψ)
          ((σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ))).re := by
  classical
  set s₁ : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs1
  set s₂ : ℂ := (σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ) with hs2
  have hs1re : s₁.re = σ := by simp [hs1]
  have hs2re : s₂.re = σ := by simp [hs2]
  have hs1im : s₁.im = τ := by simp [hs1]
  have hs2im : s₂.im = 2 * τ := by simp [hs2]
  have hσ1 : (1:ℝ) < s₁.re := hs1re ▸ hσ
  have hσ2 : (1:ℝ) < s₂.re := hs2re ▸ hσ
  -- the three series identities
  have hζ : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) := by
    have h := LFunction_logDeriv_eq_neg_LSeries_vonMangoldt (1 : DirichletCharacter ℂ 1)
      (s := (σ : ℂ)) (by simpa using hσ)
    rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply] at h
    have h2 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 : DirichletCharacter ℂ 1) (n : ZMod 1))
        = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      have h1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
        have : (n : ZMod 1) = 1 := Subsingleton.elim _ _
        rw [this, map_one]
      rw [h1, mul_one]
    rw [h2] at h
    have h3 := congrArg Neg.neg h
    simp only [neg_neg] at h3
    simpa [neg_div] using h3
  have hχ : -logDeriv (DirichletCharacter.LFunction χ) s₁
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s₁ := by
    rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ (s := s₁) hσ1, neg_neg]
  have hψ : -logDeriv (DirichletCharacter.LFunction ψ) s₂
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ)) s₂ := by
    rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt ψ (s := s₂) hσ2, neg_neg]
  rw [hζ, hχ, hψ]
  -- summability of the three series
  have hsζ : Summable (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      (σ : ℂ)) := by
    have h := summable_LSeries_term (1 : DirichletCharacter ℂ 1) (τ := 0) hσ
    have h2 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 : DirichletCharacter ℂ 1) (n : ZMod 1))
        = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      have h1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
        have : (n : ZMod 1) = 1 := Subsingleton.elim _ _
        rw [this, map_one]
      rw [h1, mul_one]
    rw [h2] at h
    simpa using h
  have hsχ : Summable (LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s₁) := by
    have := summable_LSeries_term χ (σ := σ) (τ := τ) hσ
    simpa [s₁] using this
  have hsψ : Summable (LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ)) s₂) := by
    have := summable_LSeries_term ψ (σ := σ) (τ := 2 * τ) hσ
    simpa [s₂] using this
  -- combine into one complex number
  have hsplit : 3 * (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re
      + 4 * (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s₁).re
      + (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (ψ (n : ZMod M) : ℂ)) s₂).re
      = ((3 : ℂ) * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)
        + 4 * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ (n : ZMod N) : ℂ)) s₁
        + LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ψ (n : ZMod M) : ℂ)) s₂).re := by
    simp [Complex.add_re, Complex.mul_re]
  rw [hsplit]
  have hstep : (3 : ℂ) * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)
      + 4 * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s₁
      + LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (ψ (n : ZMod M) : ℂ)) s₂
      = ∑' n : ℕ, (3 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (σ : ℂ) n
        + 4 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ (n : ZMod N) : ℂ)) s₁ n
        + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ψ (n : ZMod M) : ℂ)) s₂ n) := by
    have h1 := Summable.tsum_add (hsζ.mul_left (3:ℂ)) (hsχ.mul_left (4:ℂ))
    have h2 := Summable.tsum_add ((hsζ.mul_left (3:ℂ)).add (hsχ.mul_left (4:ℂ))) hsψ
    have h3 := tsum_mul_left (L := SummationFilter.unconditional ℕ) (a := (3:ℂ))
      (f := fun n : ℕ => LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ) n)
    have h4 := tsum_mul_left (L := SummationFilter.unconditional ℕ) (a := (4:ℂ))
      (f := fun n : ℕ => LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s₁ n)
    simp only [LSeries]
    calc (3 : ℂ) * (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ : ℂ) n)
        + 4 * (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ (n : ZMod N) : ℂ)) s₁ n)
        + (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ψ (n : ZMod M) : ℂ)) s₂ n)
        = (∑' n : ℕ, (3:ℂ) * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
              (σ : ℂ) n)
          + (∑' n : ℕ, (4:ℂ) * LSeries.term (fun n : ℕ =>
              (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s₁ n)
          + (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (ψ (n : ZMod M) : ℂ)) s₂ n) := by rw [h3, h4]
      _ = (∑' n : ℕ, ((3:ℂ) * LSeries.term (fun n : ℕ =>
              (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
            + (4:ℂ) * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ (n : ZMod N) : ℂ)) s₁ n))
          + (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (ψ (n : ZMod M) : ℂ)) s₂ n) := by rw [h1]
      _ = ∑' n : ℕ, ((3:ℂ) * LSeries.term (fun n : ℕ =>
              (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
            + (4:ℂ) * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ (n : ZMod N) : ℂ)) s₁ n
            + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (ψ (n : ZMod M) : ℂ)) s₂ n) := by rw [h2]
  rw [hstep]
  have hsumm : Summable (fun n : ℕ => 3 * LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
      + 4 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s₁ n
      + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (ψ (n : ZMod M) : ℂ)) s₂ n) :=
    ((hsζ.mul_left (3:ℂ)).add (hsχ.mul_left (4:ℂ))).add hsψ
  rw [Complex.re_tsum hsumm]
  exact tsum_nonneg (fun n => termwise_nonneg χ ψ hval hσ n)




/-! ### Two elementary logarithmic-derivative bounds -/

/-- Real-axis bound for the logarithmic derivative of `ζ`. -/
private lemma zeta_logDeriv_re_axis_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨C₂, δ₂, hC₂, hδ₂, hbound⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
  refine ⟨C₂ + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2
  have h := hbound 0 σ (by norm_num) (by linarith) (by linarith) hσ2
  have harg : ((σ : ℂ) + Complex.I * ((0:ℝ) : ℂ)) = (σ : ℂ) := by simp
  rw [harg] at h
  have h2 : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [h2] at h
  have hdiff : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      ≤ ‖deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    have h1 : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))
        = -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) := neg_div _ _
    rw [h1, Complex.neg_re]
    refine le_trans (le_abs_self _) ?_
    simpa using Complex.abs_re_le_norm (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))
  linarith [hdiff, h]

/-- Bound for the logarithmic derivative of the Archimedean gamma factor on the strip
`1 < σ ≤ 5/4`. -/
private lemma norm_logDeriv_gammaFactor_le_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ τ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 5 / 4) :
    ‖logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + Complex.I * (τ : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2) * (Real.log (2 + |τ / 2|) + 8) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hsdef
  have hsre : 0 < s.re := by simp [hsdef]; linarith
  have hlogpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log (x := Real.pi) (by positivity : (0:ℝ) ≤ Real.pi)).symm
  have hlog : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, hlogpi, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    norm_num
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun, logDeriv_Gammaℝ_formula s hsre]
    have htri : ‖-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2‖
        ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
    have hdig : ‖Complex.digamma (s / 2) / 2‖ ≤ (1 / 2) * (Real.log (2 + |τ / 2|) + 8) := by
      have harg : s / 2 = (((σ / 2 : ℝ)) : ℂ) + (((τ / 2 : ℝ)) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hsdef]
      have h2 : ‖Complex.digamma (s / 2)‖ ≤ Real.log (2 + |τ / 2|) + 8 := by
        rw [harg]
        exact Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound (σ/2) (τ/2)
          (by linarith) (by linarith)
      rw [norm_div]
      have h2n : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [h2n]
      calc ‖Complex.digamma (s / 2)‖ / 2 ≤ (Real.log (2 + |τ / 2|) + 8) / 2 :=
            div_le_div_of_nonneg_right h2 (by norm_num)
        _ = (1 / 2) * (Real.log (2 + |τ / 2|) + 8) := by ring
    rw [hlog] at htri
    linarith [htri, hdig]
  · have hfun : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) :=
      funext hO.gammaFactor_def
    have hs1re : 0 < (s + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      simp [hsdef]
      linarith
    rw [hfun]
    have hshift : logDeriv (fun z => Complex.Gammaℝ (z + 1)) s
        = logDeriv Complex.Gammaℝ (s + 1) := by
      rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]
    rw [hshift, logDeriv_Gammaℝ_formula (s+1) hs1re]
    have htri : ‖-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s+1)/2) / 2‖
        ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖Complex.digamma ((s+1)/2) / 2‖ :=
      norm_add_le _ _
    have hdig : ‖Complex.digamma ((s + 1) / 2) / 2‖
        ≤ (1 / 2) * (Real.log (2 + |τ / 2|) + 8) := by
      have harg : (s + 1) / 2 = ((((σ + 1) / 2 : ℝ)) : ℂ) +
          (((τ / 2 : ℝ)) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hsdef]
      have h2 : ‖Complex.digamma ((s + 1) / 2)‖ ≤ Real.log (2 + |τ / 2|) + 8 := by
        rw [harg]
        exact Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound ((σ+1)/2) (τ/2)
          (by linarith) (by linarith)
      rw [norm_div]
      have h2n : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [h2n]
      calc ‖Complex.digamma ((s + 1) / 2)‖ / 2 ≤ (Real.log (2 + |τ / 2|) + 8) / 2 :=
            div_le_div_of_nonneg_right h2 (by norm_num)
        _ = (1 / 2) * (Real.log (2 + |τ / 2|) + 8) := by ring
    rw [hlog] at htri
    linarith [htri, hdig]


/-! ### Logarithmic-derivative bounds for `L`-functions -/

/-- **Third-term bound.**  For a primitive non-trivial `ψ` modulo `M` the real part of
`-(logDeriv L)(σ + i·2τ)` is bounded by `C·(log (M(|τ|+2)) + 1)`. -/
private lemma LFunction_logDeriv_re_regular {M : ℕ} [NeZero M]
    (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1) (hψprim : ψ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → 1 ≤ |τ| →
      (-logDeriv (DirichletCharacter.LFunction ψ)
        ((σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ))).re ≤
        C * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
  obtain ⟨C₁, hC₁, hreg⟩ := completedLFunction_logDeriv_re_regular_bound ψ hψ hψprim
  refine ⟨2 * C₁ + 7, by positivity, ?_⟩
  intro σ τ hσ1 hσ2 hτ
  set s : ℂ := (σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ) with hsdef
  have hsre : 0 < s.re := by simp [hsdef]; linarith
  have hLne : DirichletCharacter.LFunction ψ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
      (by simp [hsdef]; linarith)
  have hdec := logDeriv_completedLFunction_eq_add ψ hψ s hsre hLne
  have h2τ : (1:ℝ) ≤ |2 * τ| := by
    rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
    nlinarith [abs_nonneg τ, hτ]
  have hreg' := hreg σ (2 * τ) hσ1 hσ2 h2τ
  have hg' := norm_logDeriv_gammaFactor_le_strip ψ hσ1 hσ2 (τ := 2 * τ)
  have hg2 : ‖logDeriv (DirichletCharacter.gammaFactor ψ) s‖ ≤
      Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |τ|) + 8) := by
    have h2abs : |2 * τ / 2| = |τ| := by rw [show 2 * τ / 2 = τ by ring]
    rwa [h2abs] at hg'
  have hlogL : (logDeriv (DirichletCharacter.LFunction ψ) s).re
      = (logDeriv (DirichletCharacter.completedLFunction ψ) s).re
        - (logDeriv (DirichletCharacter.gammaFactor ψ) s).re := by
    rw [hdec, Complex.add_re]
    ring
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by
    have : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne M))
    exact_mod_cast this
  have hlogM : (0:ℝ) ≤ Real.log ((M : ℝ) * (|τ| + 2)) := by
    apply Real.log_nonneg
    nlinarith [abs_nonneg τ, hM1]
  have hlogτ : Real.log (2 + |τ|) ≤ Real.log ((M : ℝ) * (|τ| + 2)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [abs_nonneg τ, hM1]
  have hbound : Real.log ((M : ℝ) * (|2 * τ| + 2)) + 1
      ≤ 2 * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
    have hle : |2 * τ| + 2 ≤ 2 * (|τ| + 2) := by
      rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
      nlinarith [abs_nonneg τ]
    have h0 : (0:ℝ) < (M : ℝ) * (|τ| + 2) := by nlinarith [abs_nonneg τ, hM1]
    have h1 : (M:ℝ) * (|2 * τ| + 2) ≤ 2 * ((M:ℝ) * (|τ| + 2)) := by
      have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
      nlinarith [hle, hM0]
    have h2 := Real.log_le_log (by positivity : (0:ℝ) < (M:ℝ) * (|2*τ|+2)) h1
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt h0)] at h2
    have hlog2 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    nlinarith [h2, hlog2, hlogM]
  have hpi : Real.log Real.pi / 2 ≤ 1 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  calc (-logDeriv (DirichletCharacter.LFunction ψ) s).re
      = -((logDeriv (DirichletCharacter.completedLFunction ψ) s).re)
        + (logDeriv (DirichletCharacter.gammaFactor ψ) s).re := by
        rw [Complex.neg_re, hlogL]; ring
    _ ≤ C₁ * (Real.log ((M:ℝ) * (|2*τ| + 2)) + 1)
        + (Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |τ|) + 8)) := by
        have h1 : -((logDeriv (DirichletCharacter.completedLFunction ψ) s).re)
            ≤ C₁ * (Real.log ((M:ℝ) * (|2*τ| + 2)) + 1) := by linarith [hreg']
        have h2 : (logDeriv (DirichletCharacter.gammaFactor ψ) s).re
            ≤ ‖logDeriv (DirichletCharacter.gammaFactor ψ) s‖ := Complex.re_le_norm _
        linarith [h1, h2, hg2]
    _ ≤ (2 * C₁ + 7) * (Real.log ((M:ℝ) * (|τ| + 2)) + 1) := by
        nlinarith [hbound, hlogM, hlogτ, hpi, hC₁.le, abs_nonneg τ]

/-- **Pole bound for `L`-functions.**  Above a zero `β + iτ` of `L(·,ψ)` the real part of
`-(logDeriv L)(σ + iτ)` is bounded by `-1/(σ-β)` plus a logarithmic error. -/
private lemma LFunction_logDeriv_re_pole {M : ℕ} [NeZero M]
    (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1) (hψprim : ψ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ β : ℝ, 1 < σ → σ ≤ 5 / 4 → 1 ≤ |τ| → 0 < β → β < 1 →
      DirichletCharacter.LFunction ψ ((β : ℂ) + Complex.I * (τ : ℂ)) = 0 →
      (-logDeriv (DirichletCharacter.LFunction ψ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≤
        -1 / (σ - β) + C * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
  obtain ⟨C₁, hC₁, hpole⟩ := completedLFunction_logDeriv_re_pole_bound ψ hψ hψprim
  refine ⟨C₁ + 6, by positivity, ?_⟩
  intro σ τ β hσ1 hσ2 hτ hβ0 hβ1 hz
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hsdef
  have hsre : 0 < s.re := by simp [hsdef]; linarith
  have hLne : DirichletCharacter.LFunction ψ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
      (by simp [hsdef]; linarith)
  have hdec := logDeriv_completedLFunction_eq_add ψ hψ s hsre hLne
  have hΛz : DirichletCharacter.completedLFunction ψ ((β : ℂ) + Complex.I * (τ : ℂ)) = 0 := by
    have hfac := Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos ψ
      (s := (β : ℂ) + Complex.I * (τ : ℂ)) (by simp; linarith)
    rw [hfac, hz, zero_mul]
  have hpole' := hpole σ τ β hσ1 hσ2 hτ hβ0 hβ1 hΛz
  have hlogL : (logDeriv (DirichletCharacter.LFunction ψ) s).re
      = (logDeriv (DirichletCharacter.completedLFunction ψ) s).re
        - (logDeriv (DirichletCharacter.gammaFactor ψ) s).re := by
    rw [hdec, Complex.add_re]
    ring
  have hg2 : ‖logDeriv (DirichletCharacter.gammaFactor ψ) ((σ:ℂ) + Complex.I*(τ:ℂ))‖
      ≤ Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |τ|) + 8) := by
    have h := norm_logDeriv_gammaFactor_le_strip ψ hσ1 hσ2 (τ := τ)
    have h2 : Real.log (2 + |τ / 2|) ≤ Real.log (2 + |τ|) := by
      apply Real.log_le_log (by positivity)
      have h3 : |τ / 2| ≤ |τ| := by
        rw [abs_div]
        have h4 := abs_nonneg τ
        norm_num
      linarith
    linarith
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by
    have : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne M))
    exact_mod_cast this
  have hlogM : (0:ℝ) ≤ Real.log ((M : ℝ) * (|τ| + 2)) := by
    apply Real.log_nonneg
    nlinarith [abs_nonneg τ, hM1]
  have hlogτ : Real.log (2 + |τ|) ≤ Real.log ((M : ℝ) * (|τ| + 2)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [abs_nonneg τ, hM1]
  have hpi : Real.log Real.pi / 2 ≤ 1 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hspos : 0 < σ - β := by linarith
  rw [hsdef] at hdec hlogL ⊢
  calc (-logDeriv (DirichletCharacter.LFunction ψ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re
      = -((logDeriv (DirichletCharacter.completedLFunction ψ) ((σ:ℂ) + Complex.I * (τ:ℂ))).re)
        + (logDeriv (DirichletCharacter.gammaFactor ψ) ((σ:ℂ) + Complex.I * (τ:ℂ))).re := by
        rw [Complex.neg_re, hlogL]; ring
    _ ≤ -1 / (σ - β) + C₁ * (Real.log ((M:ℝ) * (|τ| + 2)) + 1)
        + (Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |τ|) + 8)) := by
        have h1 : -((logDeriv (DirichletCharacter.completedLFunction ψ)
            ((σ:ℂ) + Complex.I * (τ:ℂ))).re)
            ≤ -1 / (σ - β) + C₁ * (Real.log ((M:ℝ) * (|τ| + 2)) + 1) := by
          have hdiv : (-1:ℝ) / (σ - β) = -(1 / (σ - β)) := by ring
          rw [hdiv]
          linarith [hpole']
        have h2 : (logDeriv (DirichletCharacter.gammaFactor ψ) ((σ:ℂ) + Complex.I*(τ:ℂ))).re
            ≤ ‖logDeriv (DirichletCharacter.gammaFactor ψ) ((σ:ℂ) + Complex.I*(τ:ℂ))‖ :=
          Complex.re_le_norm _
        linarith [h1, h2, hg2]
    _ ≤ -1 / (σ - β) + (C₁ + 6) * (Real.log ((M:ℝ) * (|τ| + 2)) + 1) := by
        nlinarith [hlogM, hlogτ, hpi, hC₁.le, hspos, abs_nonneg τ]


/-- **Third-term bound**, including the trivial-character case (where `L(·,ψ) = ζ`). -/
private lemma third_term_bound {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M)
    (hψprim : ψ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 < T ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → T ≤ |τ| →
      (-logDeriv (DirichletCharacter.LFunction ψ)
        ((σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ))).re ≤
        C * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
  by_cases hψ1 : ψ = 1
  · have hM1 : M = 1 := by
      have h := hψprim
      rw [DirichletCharacter.isPrimitive_def] at h
      rw [hψ1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hM1
    obtain ⟨C, hC, H, hH2, hbound⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_upper
    refine ⟨4 * C + 4, by positivity, max 1 (H / 2), by positivity, ?_⟩
    intro σ τ hσ1 hσ2 hT
    have hH : H ≤ |2 * τ| := by
      have h1 : H / 2 ≤ |τ| := le_trans (le_max_right _ _) hT
      rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
      linarith
    have hb : -(deriv riemannZeta ((σ : ℂ) + Complex.I * ((2*τ : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + Complex.I * ((2*τ : ℝ) : ℂ))).re
        ≤ C * (Real.log (|2 * τ| + 3) + 1) := by
      have h' := hbound (2 * τ) hH σ (by linarith) (by linarith)
      have hc : ((σ:ℂ) + ((2*τ:ℝ):ℂ) * Complex.I) = ((σ:ℂ) + Complex.I*((2*τ:ℝ):ℂ)) := by
        rw [mul_comm]
      rw [hc] at h'
      have h1 : (-deriv riemannZeta ((σ:ℂ) + Complex.I*((2*τ:ℝ):ℂ)) /
          riemannZeta ((σ:ℂ) + Complex.I*((2*τ:ℝ):ℂ))) =
          -(deriv riemannZeta ((σ:ℂ) + Complex.I*((2*τ:ℝ):ℂ)) /
          riemannZeta ((σ:ℂ) + Complex.I*((2*τ:ℝ):ℂ))) := neg_div _ _
      rw [h1, Complex.neg_re] at h'
      exact h'
    rw [DirichletCharacter.LFunction_modOne_eq]
    have hlogL : (logDeriv riemannZeta ((σ : ℂ) + Complex.I * ((2*τ : ℝ) : ℂ))).re
        = (deriv riemannZeta ((σ : ℂ) + Complex.I * ((2*τ : ℝ) : ℂ)) /
            riemannZeta ((σ : ℂ) + Complex.I * ((2*τ : ℝ) : ℂ))).re := by
      rw [logDeriv_apply]
    rw [Complex.neg_re, hlogL]
    have hM1' : (1:ℝ) ≤ (1:ℝ) := le_rfl
    have hlogM : (0:ℝ) ≤ Real.log ((1:ℝ) * (|τ| + 2)) := by
      rw [one_mul]
      exact Real.log_nonneg (by linarith [abs_nonneg τ])
    have hle : Real.log (|2 * τ| + 3) ≤ Real.log ((1:ℝ) * (|τ| + 2)) + 1 := by
      rw [one_mul]
      have h1 : |2 * τ| + 3 ≤ 2 * (|τ| + 2) := by
        rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
        nlinarith [abs_nonneg τ]
      have h2 : (0:ℝ) < |τ| + 2 := by positivity
      have h3 := Real.log_le_log (by positivity : (0:ℝ) < |2*τ| + 3) h1
      rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt h2)] at h3
      have h4 : Real.log (2:ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    nlinarith [hb, hle, hlogM, hC.le]
  · obtain ⟨C, hC, hbound⟩ := LFunction_logDeriv_re_regular ψ hψ1 hψprim
    exact ⟨C, hC, 1, by norm_num, fun σ τ hσ1 hσ2 hT => hbound σ τ hσ1 hσ2 (le_trans (by norm_num) hT)⟩

/-- The archimedean gamma factor of a Dirichlet character does not vanish off the real axis. -/
private lemma gammaFactor_ne_zero_of_im_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.im ≠ 0) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    intro hzero
    rw [Complex.Gammaℝ_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    exact hs (by rw [hn]; simp)
  · rw [Odd.gammaFactor_def hO]
    intro hzero
    rw [Complex.Gammaℝ_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    exact hs (by
      have := congrArg Complex.im hn
      simpa using this)

/-- **Compactness: a zero-free region for bounded imaginary part.**  For every `T ≥ 1` there is
`ε > 0` such that `L(σ + it, χ) ≠ 0` whenever `χ ≠ 1`, `|t| ≤ T` and `1 - ε ≤ σ ≤ 2`. -/
private lemma LFunction_zeroFree_compact {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ∀ σ t : ℝ, |t| ≤ T → 1 - ε ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let ρ : ℝ := Real.sqrt (4 + T ^ 2)
  have hρ2 : 2 ≤ ρ := by
    rw [show ρ = Real.sqrt (4 + T ^ 2) from rfl,
      ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg T])
  have hρ0 : 0 ≤ ρ := by linarith
  have hΛdiff : Differentiable ℂ Λ := by
    simpa [Λ] using (differentiable_completedLFunction hχ)
  have hΛan : AnalyticOnNhd ℂ Λ (Metric.closedBall (0 : ℂ) ρ) :=
    fun z _ => hΛdiff.analyticAt z
  have hnotzero : ∀ z : ℂ, analyticOrderAt Λ z ≠ ⊤ := by
    intro z hz
    have hev : Λ =ᶠ[nhds z] 0 := analyticOrderAt_eq_top.mp hz
    have heq : Set.EqOn Λ 0 Set.univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (U := Set.univ) (fun w _ => hΛdiff.analyticAt w) isPreconnected_univ
        (Set.mem_univ z) hev
    have h1 : Λ 1 = 0 := heq (Set.mem_univ 1)
    have hL : DirichletCharacter.completedLFunction χ 1 ≠ 0 :=
      Commons.NumberTheory.Linnik.completedLFunction_one_ne_zero χ hχ
    exact hL (by simpa [Λ] using h1)
  have horder : ∀ u : Metric.closedBall (0 : ℂ) ρ, meromorphicOrderAt Λ u ≠ ⊤ := by
    intro u hcontra
    rw [AnalyticAt.meromorphicOrderAt_eq (hΛdiff.analyticAt (u : ℂ))] at hcontra
    cases h : analyticOrderAt Λ (u : ℂ) with
    | top => exact hnotzero (u : ℂ) h
    | coe n => rw [h] at hcontra; simp at hcontra
  have hZfin : (Metric.closedBall (0 : ℂ) ρ ∩ Λ ⁻¹' {0}).Finite := by
    rw [MeromorphicNFOn.zero_set_eq_divisor_support hΛan.meromorphicNFOn horder]
    exact Commons.Analysis.Complex.divisor_support_finite_closedBall hΛan
  let Z : Finset ℂ := hZfin.toFinset
  have hZmem : ∀ z : ℂ, z ∈ Z ↔ z ∈ Metric.closedBall (0 : ℂ) ρ ∧ Λ z = 0 := by
    intro z
    rw [hZfin.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  let A : Finset ℂ := Z.filter (fun z => (1 / 2 : ℝ) ≤ z.re)
  have hA_lt_one : ∀ z : ℂ, z ∈ A → z.re < 1 := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzZ, hzhalf⟩ := hz
    obtain ⟨-, hΛz⟩ := (hZmem z).1 hzZ
    by_contra hcon
    push Not at hcon
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hcon; exact absurd hcon (by norm_num)
    have hLz : DirichletCharacter.LFunction χ z = 0 := by
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
      rw [h, show DirichletCharacter.completedLFunction χ z = 0 from by simpa [Λ] using hΛz,
        zero_div]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon hLz
  have hA_ge : ∀ z : ℂ, z ∈ A → (1 / 2 : ℝ) ≤ z.re := by
    intro z hz
    rw [Finset.mem_filter] at hz
    exact hz.2
  have hstep : ∀ σ t : ℝ, |t| ≤ T → 0 < σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) = 0 →
      ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ Z := by
    intro σ t ht hσ0 hσ2 hL0
    rw [hZmem]
    obtain ⟨htlo, hthi⟩ := abs_le.mp ht
    constructor
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hsq : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 ≤ ρ ^ 2 := by
        have hsre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
        have hsim : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
        rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim,
          show ρ ^ 2 = 4 + T ^ 2 from Real.sq_sqrt (by positivity)]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T - t) (by linarith : (0:ℝ) ≤ T + t),
          sq_nonneg σ]
      nlinarith [norm_nonneg ((σ : ℂ) + (t : ℂ) * Complex.I), hρ0]
    · have hs0 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
        simp at this
        linarith
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ
        ((σ : ℂ) + (t : ℂ) * Complex.I) (Or.inl hs0)
      rw [h] at hL0
      have hγ : DirichletCharacter.gammaFactor χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        rcases χ.even_or_odd with hE | hO
        · rw [Even.gammaFactor_def hE]
          exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; exact hσ0)
        · rw [Odd.gammaFactor_def hO]
          exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
      rw [div_eq_zero_iff] at hL0
      rcases hL0 with h' | h'
      · simpa [Λ] using h'
      · exact absurd h' hγ
  by_cases hAe : A = ∅
  · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    intro σ t ht hσlo hσhi hL0
    have hσ0 : 0 < σ := by linarith
    have hsZ := hstep σ t ht hσ0 hσhi hL0
    have hsg : (1 / 2 : ℝ) ≤ σ := by linarith
    have : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ A := by
      rw [Finset.mem_filter]
      exact ⟨hsZ, by simpa using hsg⟩
    rw [hAe] at this
    exact absurd this (Finset.notMem_empty _)
  · have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAe
    let g : Finset ℝ := A.image (fun z : ℂ => 1 - z.re)
    have hgne : g.Nonempty := by
      rw [Finset.image_nonempty]; exact hAne
    let d : ℝ := g.min' hgne
    have hdmem : d ∈ g := by
      dsimp [d]; exact Finset.min'_mem _ hgne
    obtain ⟨z₀, hz₀A, hz₀eq⟩ := Finset.mem_image.mp hdmem
    have hdpos : 0 < d := by
      have hz₀ : z₀.re < 1 := hA_lt_one z₀ hz₀A
      have : d = 1 - z₀.re := hz₀eq.symm
      rw [this]; linarith
    have hdle : d ≤ 1 / 2 := by
      have hz₀ : (1 / 2 : ℝ) ≤ z₀.re := hA_ge z₀ hz₀A
      have : d = 1 - z₀.re := hz₀eq.symm
      rw [this]; linarith
    have hd_le : ∀ z : ℂ, z ∈ A → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le g (1 - z.re) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    refine ⟨d / 2, by positivity, by linarith, ?_⟩
    intro σ t ht hσlo hσhi hL0
    have hσ0 : 0 < σ := by linarith
    have hsZ := hstep σ t ht hσ0 hσhi hL0
    have hsg : (1 / 2 : ℝ) ≤ σ := by linarith
    have hsA : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ A := by
      rw [Finset.mem_filter]
      exact ⟨hsZ, by simpa using hsg⟩
    have h1 : d ≤ 1 - σ := by
      have := hd_le ((σ : ℂ) + (t : ℂ) * Complex.I) hsA
      simpa using this
    have h2 : 1 - σ ≤ d / 2 := by linarith
    linarith
/-- **Analytic estimate: the zero-free region for large `|t|`.** -/
private lemma LFunction_zeroFree_largeHeight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (σ t : ℝ), T₀ ≤ |t| →
      1 - c / (Real.log ((N : ℝ) * (|t| + 2)) + 1) ≤ σ →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  classical
  obtain ⟨C₁, hC₁, hbound₁⟩ := LFunction_logDeriv_re_pole χ hχ hχprim
  obtain ⟨C₂, hC₂, hbound₂⟩ := zeta_logDeriv_re_axis_le
  set χ₂ : DirichletCharacter ℂ N := χ * χ with hχ₂
  let M : ℕ := χ₂.conductor
  haveI : NeZero M := ⟨χ₂.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ M := χ₂.primitiveCharacter with hψ
  have hψprim : ψ.IsPrimitive := χ₂.primitiveCharacter_isPrimitive
  obtain ⟨C₃, hC₃, T₃, hT₃, hbound₃⟩ := third_term_bound ψ hψprim
  have hMN : M ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ₂.conductor_dvd_level
  have hval : ∀ a : ℤ, IsCoprime a (N : ℤ) → (ψ (a : ZMod M)) = ((χ (a : ZMod N)) : ℂ) ^ 2 := by
    intro a ha
    have hcl := DFunLike.congr_fun
      (DirichletCharacter.changeLevel_primitiveCharacter χ₂) (a : ZMod N)
    have hcast := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₂.primitiveCharacter
      χ₂.conductor_dvd_level ha
    rw [hcast] at hcl
    rw [hcl]
    show (χ * χ) (a : ZMod N) = ((χ (a : ZMod N)) : ℂ) ^ 2
    rw [MulChar.mul_apply]
    ring
  set K : ℝ := 3 * C₂ + 4 * C₁ + C₃ with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  set A : ℝ := 2 * K + 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hAK : 2 * K < A := by rw [hAdef]; linarith
  refine ⟨1 / (7 * A), by positivity, max 1 T₃, le_max_left _ _, ?_⟩
  intro σ t hTt hσ hz0
  have hT1 : 1 ≤ |t| := le_trans (le_max_left _ _) hTt
  have hT3 : T₃ ≤ |t| := le_trans (le_max_right _ _) hTt
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at hT1; norm_num at hT1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  set ℓ : ℝ := Real.log ((N : ℝ) * (|t| + 2)) + 1 with hℓdef
  have hlogN : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg t, hN1])
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith
  have hℓpos : 0 < ℓ := by linarith
  have hℓ2 : 2 ≤ ℓ := by
    rw [hℓdef]
    have h3 : Real.log 3 ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_le_log (by norm_num)
      nlinarith [abs_nonneg t, hN1]
    have h4 : (1 : ℝ) < Real.log 3 := by
      have h5 : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h5
    linarith
  -- the alleged zero, expressed with the other ordering of the imaginary part
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    apply ht0
    have := congrArg Complex.im h
    simpa [hsdef] using this
  have hΛ0 : DirichletCharacter.completedLFunction χ s = 0 := by
    have hγ : DirichletCharacter.gammaFactor χ s ≠ 0 :=
      gammaFactor_ne_zero_of_im_ne_zero χ (by rw [hsim]; exact ht0)
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
    rw [h] at hz0
    rcases div_eq_zero_iff.mp hz0 with h' | h'
    · exact h'
    · exact absurd h' hγ
  have hstrip := zerosInStrip χ hχ hχprim s hΛ0
  have hβ0 : 0 < σ := by rw [← hsre]; exact hstrip.1
  have hβ1 : σ < 1 := by rw [← hsre]; exact hstrip.2
  -- the evaluation point `1 + x`
  set x : ℝ := 1 / (A * ℓ) with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hAℓ4 : 4 ≤ A * ℓ := by
    have h2 : 2 ≤ A := by rw [hAdef]; linarith
    nlinarith [hℓ2]
  have hσ'1 : 1 < 1 + x := by linarith
  have hσ'2 : 1 + x ≤ 5 / 4 := by
    have h4 : 1 / (A * ℓ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hAℓ4
    rw [hxdef]; linarith
  -- the three-term inequality
  have hthree := three_four_one_nonneg χ ψ hval (σ := 1 + x) (τ := t) hσ'1
  -- the three individual bounds
  have hb1 : (-deriv riemannZeta (((1 + x : ℝ)) : ℂ) /
      riemannZeta (((1 + x : ℝ)) : ℂ)).re ≤ 1 / x + C₂ := by
    have h := hbound₂ (1 + x) hσ'1 (by linarith)
    have hxe : (1 + x) - 1 = x := by ring
    rwa [hxe] at h
  have hz0' : DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) = 0 := by
    simpa [s, hsdef, mul_comm] using hz0
  have hb2 : (-logDeriv (DirichletCharacter.LFunction χ)
        (((1 + x : ℝ) : ℂ) + Complex.I * (t : ℂ))).re
      ≤ -(1 / ((1 + x) - σ)) + C₁ * ℓ := by
    have h := hbound₁ (1 + x) t σ hσ'1 hσ'2 hT1 hβ0 hβ1 hz0'
    rw [← hℓdef] at h
    have hdiv : (-1 : ℝ) / ((1 + x) - σ) = -(1 / ((1 + x) - σ)) := by ring
    rwa [hdiv] at h
  have hb3 : (-logDeriv (DirichletCharacter.LFunction ψ)
        (((1 + x : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re ≤ C₃ * ℓ := by
    have h := hbound₃ (1 + x) t hσ'1 hσ'2 hT3
    have hMle : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hlogM : Real.log ((M : ℝ) * (|t| + 2)) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      have hMpos : (0 : ℝ) < (M : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne M))
      apply Real.log_le_log
      · nlinarith [abs_nonneg t]
      · nlinarith [abs_nonneg t, hMle]
    have hMle1 : (Real.log ((M : ℝ) * (|t| + 2)) + 1) ≤ ℓ := by
      rw [hℓdef]; linarith
    calc (-logDeriv (DirichletCharacter.LFunction ψ)
          (((1 + x : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re
        ≤ C₃ * (Real.log ((M : ℝ) * (|t| + 2)) + 1) := h
      _ ≤ C₃ * ℓ := mul_le_mul_of_nonneg_left hMle1 hC₃.le
  -- combine into an upper bound for `1/(x + δ)`
  set δ : ℝ := 1 - σ with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hd_eq : (1 + x) - σ = x + δ := by rw [hδdef]; ring
  have hkey : 4 * (1 / ((1 + x) - σ)) ≤ 3 * (1 / x) + 3 * C₂ + (4 * C₁ + C₃) * ℓ := by
    linarith [hthree, hb1, hb2, hb3]
  rw [hd_eq] at hkey
  have hxinv : 1 / x = A * ℓ := by
    rw [hxdef]; field_simp
  have hkey2 : 4 * (1 / (x + δ)) ≤ (3 * A + K) * ℓ := by
    have h1 : 3 * (1 / x) ≤ 3 * (A * ℓ) := by rw [hxinv]
    have h2 : 3 * C₂ + (4 * C₁ + C₃) * ℓ ≤ K * ℓ := by
      rw [hKdef]; nlinarith [hℓ1, hC₂.le]
    have h3 : (3 * A + K) * ℓ = 3 * (A * ℓ) + K * ℓ := by ring
    linarith [hkey, h1, h2, h3]
  have hxδpos : 0 < x + δ := by linarith
  have hkey3 : 4 ≤ (3 * A + K) * ℓ * (x + δ) := by
    have h := mul_le_mul_of_nonneg_right hkey2 (le_of_lt hxδpos)
    have h4 : 4 * (1 / (x + δ)) * (x + δ) = 4 := by
      rw [mul_assoc, one_div_mul_cancel (ne_of_gt hxδpos), mul_one]
    linarith [h, h4]
  -- conclusion: `δ ≥ 1/(7Aℓ)`
  have hδge : 1 / (7 * A * ℓ) < δ := by
    have hexp : (3 * A + K) * ℓ * (x + δ)
        = (3 * A + K) / A + (3 * A + K) * ℓ * δ := by
      rw [hxdef]
      field_simp
    have hden : 0 < (3 * A + K) * ℓ := by
      have h1 : 0 < 3 * A + K := by linarith
      positivity
    have hb : (4 - (3 * A + K) / A) / ((3 * A + K) * ℓ) ≤ δ := by
      rw [div_le_iff₀ hden]
      linarith [hkey3, hexp]
    have hnum : 1 / (7 * A * ℓ) < (4 - (3 * A + K) / A) / ((3 * A + K) * ℓ) := by
      rw [lt_div_iff₀ hden]
      have h1 : 1 / (7 * A * ℓ) * ((3 * A + K) * ℓ) = (3 * A + K) / (7 * A) := by
        field_simp
      rw [h1]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 7 * A)]
      have hid : (4 - (3 * A + K) / A) * (7 * A) = 28 * A - 7 * (3 * A + K) := by
        field_simp
        ring
      rw [hid]
      nlinarith [hAK, hApos, hKpos]
    linarith
  -- contradiction with the hypothesis
  have hδle : δ ≤ 1 / (7 * A * ℓ) := by
    rw [hδdef]
    have h1 : 1 / (7 * A) / ℓ = 1 / (7 * A * ℓ) := by field_simp
    rw [h1] at hσ
    linarith
  linarith [hδge, hδle]


/-- **Zero-free region of `L(s, χ)` off the real axis.**  For a primitive non-trivial Dirichlet
character `χ` modulo `N` there is `c > 0` such that `L(χ, σ + it) ≠ 0` whenever `|t| ≥ 1` and
`σ ≥ 1 - c / log (N (|t| + 2))`. -/
theorem LFunction_zeroFree_region_awayFromAxis {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (σ t : ℝ), 1 ≤ |t| →
      1 - c / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₁, hc₁, T₀, hT₀, hbig⟩ := LFunction_zeroFree_largeHeight χ hχprim hχ
  obtain ⟨ε, hε, hε2, hsmall⟩ := LFunction_zeroFree_compact χ hχ hT₀
  refine ⟨min (c₁ / 4) ε, lt_min (by linarith) hε, ?_⟩
  intro σ t ht hσ
  have hmc : min (c₁ / 4) ε ≤ c₁ / 4 := min_le_left _ _
  have hme : min (c₁ / 4) ε ≤ ε := min_le_right _ _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hlog1 : 1 ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
    have h3 : Real.log 3 ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_le_log (by norm_num)
      nlinarith [abs_nonneg t]
    have h4 : (1 : ℝ) < Real.log 3 := by
      have h5 : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h5
    linarith
  set ℓ : ℝ := Real.log ((N : ℝ) * (|t| + 2)) with hℓdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; linarith
  by_cases h2 : 2 ≤ σ
  · refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (s := ((σ : ℂ) + (t : ℂ) * Complex.I)) ?_
    simp
    linarith
  · push Not at h2
    by_cases hT : T₀ ≤ |t|
    · refine hbig σ t hT ?_
      have h1 : 1 - c₁ / (ℓ + 1) ≤ 1 - (min (c₁ / 4) ε) / ℓ := by
        apply sub_le_sub_left
        rw [div_le_iff₀ hℓpos, div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < ℓ + 1)]
        nlinarith [hmc, hc₁.le, hlog1]
      exact le_trans h1 hσ
    · push Not at hT
      refine hsmall σ t (le_of_lt hT) ?_ h2.le
      have h1 : 1 - ε ≤ 1 - (min (c₁ / 4) ε) / ℓ := by
        apply sub_le_sub_left
        rw [div_le_iff₀ hℓpos]
        nlinarith [hme, hℓpos]
      exact le_trans h1 hσ


end Commons.NumberTheory.DirichletCharacter
