import Mathlib

set_option linter.unusedVariables false

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped BigOperators Topology

noncomputable section

/-- `Re (1/((x : ℂ) + (T : ℂ) * I - u)) = (x - Re u)/((x - Re u)² + (T - Im u)²)`. -/
private lemma re_inv_shift (x T : ℝ) (u : ℂ) :
    (1 / (((x : ℂ) + (T : ℂ) * Complex.I) - u)).re
      = (x - u.re) / ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hz : (((x : ℂ) + (T : ℂ) * Complex.I) - u).re = x - u.re := by simp
  have hi : (((x : ℂ) + (T : ℂ) * Complex.I) - u).im = T - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hz, hi]
  ring

/-- The kernel of the pair `(2 + i t, -2 + i t)`, written in real coordinates. -/
private lemma kernelPairRe (t : ℝ) (u : ℂ) :
    (1 / (((2 : ℂ) + (t : ℂ) * Complex.I) - u)
        - 1 / (((-2 : ℂ) + (t : ℂ) * Complex.I) - u)).re
      = (2 - u.re) / ((2 - u.re) ^ 2 + (t - u.im) ^ 2)
        + (2 + u.re) / ((2 + u.re) ^ 2 + (t - u.im) ^ 2) := by
  have h2 : ((2 : ℂ) + (t : ℂ) * Complex.I) = ((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by norm_num
  have h2' : ((-2 : ℂ) + (t : ℂ) * Complex.I) = ((-2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    norm_num
  rw [h2, h2', Complex.sub_re, re_inv_shift 2 t u, re_inv_shift (-2) t u]
  ring

/-- The kernel lower bound: for a zero with real part `β ∈ [-1,1]` the real part of the pair kernel
is at least `1/(9 + δ²)`, where `δ` is the vertical distance to the evaluation point. -/
private lemma kernelPairLower (β δ : ℝ) (hβ : -1 ≤ β) (hβ1 : β ≤ 1) :
    1 / (9 + δ ^ 2)
      ≤ (2 - β) / ((2 - β) ^ 2 + δ ^ 2) + (2 + β) / ((2 + β) ^ 2 + δ ^ 2) := by
  have ha1 : 1 ≤ 2 - β := by linarith
  have ha3 : 2 - β ≤ 3 := by linarith
  have hden1 : (0:ℝ) < 9 + δ^2 := by positivity
  have hdena : (0:ℝ) < (2 - β)^2 + δ^2 := by positivity
  have hmain : 1 / (9 + δ^2) ≤ (2 - β) / ((2 - β)^2 + δ^2) := by
    rw [div_le_div_iff₀ hden1 hdena]
    nlinarith [sq_nonneg δ, sq_nonneg (2 - β), mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hβ1),
      mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha3)]
  have hbpos : 0 ≤ (2 + β) / ((2 + β)^2 + δ^2) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/-- A nonzero divisor value at `u` forces `Λ u = 0` when `Λ` is entire. -/
private lemma eqZero_divisor_ne_zero {Λ : ℂ → ℂ} (hΛ : AnalyticOn ℂ Λ Set.univ)
    {R : ℝ} {u : ℂ} (hd : (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u ≠ 0) :
    Λ u = 0 := by
  by_contra hu
  apply hd
  have hat : AnalyticAt ℂ Λ u := hΛ.analyticAt (by simp)
  have hAnNhd : AnalyticOnNhd ℂ Λ (Metric.closedBall (0:ℂ) R) :=
    fun z _ => hΛ.analyticAt (by simp)
  have hmer : MeromorphicOn Λ (Metric.closedBall 0 R) := hAnNhd.meromorphicOn
  by_cases humem : u ∈ Metric.closedBall (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply hmer humem]
    have hord : meromorphicOrderAt Λ u = 0 := by
      rw [hat.meromorphicOrderAt_eq, (hat.analyticOrderAt_eq_zero).2 hu, ENat.map_zero]
      rfl
    rw [hord]
    simp
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ humem]

/-- **The weighted zero sum from the Hadamard partial fraction.**  Let `Λ` be *entire* (so that
every divisor value on a closed ball is `≥ 0`), let its partial fraction be available, let its zeros
lie in `[-1,1]`, let the real part of `Λ'/Λ` be bounded above at `2 + iγ` and bounded below at
`-2 + iγ`.  Then the divisor-weighted zero sum is at most `13` times the sum of the two one-sided
bounds:  `Σ_u ord(u)/(1+(t−Im u)²) ≤ 13·(B2 t + Bm2 t)`.

(Proof: at the pair `(2+it, −2+it)` every kernel has nonnegative real part and is at least
`1/(9+δ_u²)` with `δ_u = t − Im u`; the partial sums are therefore *increasing* (all multiplicities
are `≥ 0` because `Λ` is entire) and bounded by
`Re (Λ'/Λ)(2+it) − Re (Λ'/Λ)(−2+it)`, which the two hypotheses control.  Finally
`1/(9+δ²) ≥ (1/13)/(1+δ²)`.) -/
theorem wzsOfPfDiff (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ)
    (hpf : ∀ s s₁ : ℂ, Λ s ≠ 0 → Λ s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u))) Filter.atTop
        (nhds (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁)))
    (hz : ∀ u : ℂ, Λ u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (B2 Bm2 : ℝ → ℝ)
    (hB2 : ∀ γ : ℝ,
      (deriv Λ ((2 : ℂ) + (γ : ℂ) * Complex.I) / Λ ((2 : ℂ) + (γ : ℂ) * Complex.I)).re ≤ B2 γ)
    (hBm2 : ∀ γ : ℝ,
      -Bm2 γ ≤ (deriv Λ ((-2 : ℂ) + (γ : ℂ) * Complex.I) / Λ ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (t R : ℝ) (hR : 1 ≤ R) :
    ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)
      ≤ 13 * (B2 t + Bm2 t) := by
  classical
  have hΛ : AnalyticOn ℂ Λ Set.univ := (analyticOn_univ_iff_differentiable).2 hDiff
  have hAnNhd : ∀ r : ℝ, AnalyticOnNhd ℂ Λ (Metric.closedBall 0 r) :=
    fun r z _ => hΛ.analyticAt (by simp)
  have hmer : ∀ r : ℝ, MeromorphicOn Λ (Metric.closedBall 0 r) :=
    fun r => (hAnNhd r).meromorphicOn
  have hdnn : ∀ (r : ℝ) (u : ℂ), 0 ≤ MeromorphicOn.divisor Λ (Metric.closedBall 0 r) u :=
    fun r u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAnNhd r) u
  have hdnnR : ∀ (r : ℝ) (u : ℂ),
      (0:ℝ) ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℝ) :=
    fun r u => Int.cast_nonneg (hdnn r u)
  set s : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hs
  set s₁ : ℂ := (-2 : ℂ) + (t : ℂ) * Complex.I with hs₁
  have hs_re : s.re = 2 := by simp [hs]
  have hs₁_re : s₁.re = -2 := by simp [hs₁]
  have hs_ne : Λ s ≠ 0 := by
    intro h0
    have h2 := (hz s h0).2
    rw [hs_re] at h2
    linarith
  have hs₁_ne : Λ s₁ ≠ 0 := by
    intro h0
    have h2 := (hz s₁ h0).1
    rw [hs₁_re] at h2
    linarith
  set K : ℂ → ℝ := fun u => (1 / (s - u) - 1 / (s₁ - u)).re with hK
  have hKfun : ∀ u : ℂ, K u = (2 - u.re) / ((2 - u.re) ^ 2 + (t - u.im) ^ 2)
      + (2 + u.re) / ((2 + u.re) ^ 2 + (t - u.im) ^ 2) := by
    intro u
    rw [hK]
    dsimp only
    rw [hs, hs₁]
    exact kernelPairRe t u
  have hKge : ∀ u : ℂ, Λ u = 0 → 1 / (9 + (t - u.im) ^ 2) ≤ K u := by
    intro u hu
    rw [hKfun u]
    exact kernelPairLower u.re (t - u.im) (hz u hu).1 (hz u hu).2
  have hfinC : ∀ r : ℝ, Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₁ - u))) := by
    intro r
    refine ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)).finiteSupport
      (isCompact_closedBall 0 r)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    exact hu (by rw [h, Int.cast_zero, zero_mul])
  have hfinR : ∀ r : ℝ, Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℝ) * K u) := by
    intro r
    refine ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)).finiteSupport
      (isCompact_closedBall 0 r)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    exact hu (by rw [h, Int.cast_zero, zero_mul])
  have hident : ∀ r : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₁ - u))).re
      = ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℝ) * K u := by
    intro r
    rw [← Complex.reCLM_apply, map_finsum Complex.reCLM (hfinC r)]
    refine finsum_congr fun u => ?_
    rw [Complex.reCLM_apply, Complex.mul_re]
    simp [hK]
  have hreK : Tendsto (fun r : ℝ =>
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℝ) * K u)
      atTop (𝓝 (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁).re) := by
    have h1 : Tendsto (fun r : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u))).re) atTop
        (𝓝 (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁).re) :=
      (Complex.continuous_re.tendsto _).comp (hpf s s₁ hs_ne hs₁_ne)
    exact h1.congr' (Eventually.of_forall fun r => hident r)
  have hmono : ∀ r r' : ℝ, r ≤ r' →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℝ) * K u)
        ≤ (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r')) u : ℝ) * K u) := by
    intro r r' hrr'
    refine finsum_le_finsum' (hfinR r) (hfinR r') ?_
    intro u
    show ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r)) u : ℝ) * K u
      ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 r')) u : ℝ) * K u
    by_cases hu : u ∈ Metric.closedBall (0:ℂ) r
    · have hu' : u ∈ Metric.closedBall (0:ℂ) r' :=
        Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp hu) hrr')
      have heq : MeromorphicOn.divisor Λ (Metric.closedBall 0 r) u
          = MeromorphicOn.divisor Λ (Metric.closedBall 0 r') u := by
        rw [MeromorphicOn.divisor_apply (hmer r) hu, MeromorphicOn.divisor_apply (hmer r') hu']
      rw [heq]
    · have h0 : MeromorphicOn.divisor Λ (Metric.closedBall 0 r) u = 0 :=
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
      rw [h0, Int.cast_zero, zero_mul]
      by_cases hd : MeromorphicOn.divisor Λ (Metric.closedBall 0 r') u = 0
      · rw [hd, Int.cast_zero, zero_mul]
      · have hzero : Λ u = 0 := eqZero_divisor_ne_zero hΛ hd
        exact mul_nonneg (hdnnR r' u) (le_trans (by positivity) (hKge u hzero))
  have hfin_le : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) * K u)
      ≤ (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁).re :=
    ge_of_tendsto hreK (Filter.eventually_atTop.2 ⟨R, fun c hc => hmono R c hc⟩)
  have hLb : (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁).re ≤ B2 t + Bm2 t := by
    rw [Complex.sub_re]
    have h1 : (deriv Λ s / Λ s).re ≤ B2 t := by rw [hs]; exact hB2 t
    have h2 : -Bm2 t ≤ (deriv Λ s₁ / Λ s₁).re := by rw [hs₁]; exact hBm2 t
    linarith
  have hI : (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2))
      ≤ 13 * (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)) := by
    have hfs9 : Function.HasFiniteSupport (fun u : ℂ =>
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)) := by
      refine ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, Int.cast_zero, zero_div])
    have hfs1 : Function.HasFiniteSupport (fun u : ℂ =>
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)) := by
      refine ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, Int.cast_zero, zero_div])
    have hfs13 : Function.HasFiniteSupport (fun u : ℂ =>
        13 * (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)
          / (9 + (t - u.im) ^ 2))) := by
      refine ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, Int.cast_zero, zero_div, mul_zero])
    rw [mul_finsum' (fun u : ℂ =>
      ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)) 13 hfs9]
    refine finsum_le_finsum' hfs1 hfs13 ?_
    intro u
    show ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)
      ≤ 13 * (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2))
    have hpos : (0:ℝ) ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) := hdnnR R u
    have h1 : (0:ℝ) < 1 + (t - u.im) ^ 2 := by positivity
    have h9 : (0:ℝ) < 9 + (t - u.im) ^ 2 := by positivity
    have h13 : (1:ℝ) / (1 + (t - u.im) ^ 2) ≤ 13 / (9 + (t - u.im) ^ 2) := by
      rw [div_le_div_iff₀ h1 h9]
      nlinarith [sq_nonneg (t - u.im)]
    calc ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)
        = ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)
            * (1 / (1 + (t - u.im) ^ 2)) := by ring
      _ ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)
            * (13 / (9 + (t - u.im) ^ 2)) := mul_le_mul_of_nonneg_left h13 hpos
      _ = 13 * (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)
            / (9 + (t - u.im) ^ 2)) := by ring
  have hII : (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2))
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) * K u := by
    have hfs9 : Function.HasFiniteSupport (fun u : ℂ =>
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)) := by
      refine ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, Int.cast_zero, zero_div])
    refine finsum_le_finsum' hfs9 (hfinR R) ?_
    intro u
    show ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)
      ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) * K u
    by_cases hd : MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u = 0
    · rw [hd, Int.cast_zero, zero_div, zero_mul]
    · have hzero : Λ u = 0 := eqZero_divisor_ne_zero hΛ hd
      have hpos : (0:ℝ) ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) := hdnnR R u
      calc ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)
          = ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)
              * (1 / (9 + (t - u.im) ^ 2)) := by ring
        _ ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) * K u :=
            mul_le_mul_of_nonneg_left (hKge u hzero) hpos
  calc (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2))
      ≤ 13 * (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) / (9 + (t - u.im) ^ 2)) := hI
    _ ≤ 13 * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ) * K u) :=
        mul_le_mul_of_nonneg_left hII (by norm_num)
    _ ≤ 13 * (B2 t + Bm2 t) :=
        mul_le_mul_of_nonneg_left (le_trans hfin_le hLb) (by norm_num)

end

end Work.FIArea6Hecke.R
