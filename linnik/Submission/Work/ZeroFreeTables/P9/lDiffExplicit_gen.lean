import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.P3.CompletedDerivPF
import Submission.Work.LinnikAreas.DhK.ZSBase
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Work.LinnikAreas.FarRepel.divisorSumBallTendsto
import Submission.Work.LinnikAreas.FarRepel.invSubPowLeInvSq
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open Complex DirichletCharacter Filter Metric
open scoped Topology BigOperators
open Work.LinnikAreas.FarRepel

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Work.ZeroFreeTables.P9

/-! ## Analyticity of the digamma function and the halving chain rule -/

private lemma isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma analyticAt_digamma {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Complex.digamma w := by
  have hball : Metric.ball w w.re ⊆ {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)} := by
    intro z hz m hzm
    have hzre : z.re = -((m : ℝ)) := by rw [hzm]; simp
    have hlt : ‖z - w‖ < w.re := by simpa [dist_eq_norm] using hz
    have hle : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, hzre] at hle
    have he : -((m : ℝ)) - w.re = -(w.re + (m : ℝ)) := by ring
    rw [he, abs_neg] at hle
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h1 : w.re ≤ |w.re + (m : ℝ)| := le_trans (le_add_of_nonneg_right hm) (le_abs_self _)
    linarith
  have hdiff : DifferentiableOn ℂ Complex.Gamma (Metric.ball w w.re) := fun z hz =>
    (Complex.differentiableAt_Gamma z (hball hz)).differentiableWithinAt
  have han : AnalyticAt ℂ Complex.Gamma w :=
    hdiff.analyticAt (Metric.ball_mem_nhds w hw)
  have hne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  rw [Complex.digamma_def, Work.ZeroFreeTables.P3.logDeriv_eq_div]
  exact (han.deriv).div han hne

private lemma iteratedDeriv_digamma_half (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv k (fun z : ℂ => Complex.digamma (((1 / 2 : ℝ) : ℂ) * z)) s
      = (((1 / 2 : ℝ) : ℂ)) ^ k * iteratedDeriv k Complex.digamma (((1 / 2 : ℝ) : ℂ) * s) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUnique : UniqueDiffOn ℂ U := hUopen.uniqueDiffOn
  have han : AnalyticOnNhd ℂ Complex.digamma U := fun z hz => analyticAt_digamma hz
  have hcont : ContDiffOn ℂ (↑k) Complex.digamma U := han.contDiffOn hUnique
  have hmaps : Set.MapsTo (fun z : ℂ => (((1 / 2 : ℝ) : ℂ)) * z) U U := by
    intro z hz
    have hz' : 0 < z.re := hz
    show 0 < ((((1 / 2 : ℝ) : ℂ)) * z).re
    rw [Complex.re_ofReal_mul]
    linarith
  have hmem : s ∈ U := hs
  have hcomp := iteratedDerivWithin_comp_const_smul (n := k) hmem hUnique hcont
      (((1 / 2 : ℝ) : ℂ)) hmaps
  have h1 : iteratedDerivWithin k (fun z : ℂ => Complex.digamma (((1 / 2 : ℝ) : ℂ) * z)) U s
      = iteratedDeriv k (fun z : ℂ => Complex.digamma (((1 / 2 : ℝ) : ℂ) * z)) s :=
    iteratedDerivWithin_of_isOpen hUopen hmem
  have h2 : iteratedDerivWithin k Complex.digamma U (((1 / 2 : ℝ) : ℂ) * s)
      = iteratedDeriv k Complex.digamma (((1 / 2 : ℝ) : ℂ) * s) :=
    iteratedDerivWithin_of_isOpen hUopen (hmaps hmem)
  rw [h1, h2] at hcomp
  simpa using hcomp

/-! ## The `Γ`-factor derivative series -/

private lemma half_mul_eq_div_two (z : ℂ) : (((1 / 2 : ℝ) : ℂ)) * z = z / 2 := by
  rw [show (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ by norm_num, div_eq_mul_inv, mul_comm]

private lemma logDeriv_GammaR_iteratedDeriv (k : ℕ) (hk : 1 ≤ k) {u : ℂ} (hu : 0 < u.re) :
    iteratedDeriv k (logDeriv Complex.Gammaℝ) u
      = (-1) ^ (k + 1) * (k.factorial : ℂ) *
          ∑' n : ℕ, (1 / (u + ((2 * n : ℕ) : ℂ))) ^ (k + 1) := by
  have hlog : logDeriv Complex.Gammaℝ =ᶠ[𝓝 u]
      fun z => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2 := by
    filter_upwards [isOpen_re_pos.mem_nhds hu] with z hz
    refine Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z (fun m hzm => ?_)
    have h1 : (z / 2).re = -((m : ℝ)) := by rw [hzm]; simp
    have h2 : 0 < (z / 2).re := by
      have h : (z / 2).re = z.re / 2 := by simp [Complex.div_re]
      rw [h]; linarith
    rw [h1] at h2
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hlog]
  rw [show (fun z : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2)
      = (fun z : ℂ => -(Complex.log (Real.pi : ℂ)) / 2
          + Complex.digamma (((1 / 2 : ℝ) : ℂ) * z) / 2) by
    funext z
    rw [half_mul_eq_div_two]]
  rw [iteratedDeriv_const_add (f := fun z : ℂ => Complex.digamma (((1 / 2 : ℝ) : ℂ) * z) / 2)
        (by omega : 0 < k) (-(Complex.log (Real.pi : ℂ)) / 2)]
  rw [show (fun z : ℂ => Complex.digamma (((1 / 2 : ℝ) : ℂ) * z) / 2)
      = (fun z : ℂ => (1 / 2 : ℂ) * Complex.digamma (((1 / 2 : ℝ) : ℂ) * z)) by
    funext z; ring]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_digamma_half k hu]
  have hu2 : 0 < ((((1 / 2 : ℝ) : ℂ)) * u).re := by
    rw [Complex.re_ofReal_mul]; linarith
  rw [← (digammaDerivSeries k hk hu2).tsum_eq]
  rw [tsum_mul_left]
  have hterm : ∀ n : ℕ, (1 / ((((1 / 2 : ℝ) : ℂ)) * u + (n : ℂ))) ^ (k + 1)
      = (2 : ℂ) ^ (k + 1) * (1 / (u + ((2 * n : ℕ) : ℂ))) ^ (k + 1) := by
    intro n
    have hd1 : u + 2 * (n : ℂ) ≠ 0 := by
      intro h
      have h' : u.re + 2 * (n : ℝ) = 0 := by
        have := congrArg Complex.re h
        simpa using this
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hden : (((1 / 2 : ℝ) : ℂ)) * u + (n : ℂ) = (u + 2 * (n : ℂ)) / 2 := by
      rw [show (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ by norm_num]
      ring
    have hden' : (u + 2 * (n : ℂ)) / 2 ≠ 0 := by
      rw [div_ne_zero_iff]
      exact ⟨hd1, by norm_num⟩
    have hmain : (2 : ℂ) * (1 / (u + 2 * (n : ℂ)))
        = 1 / (((1 / 2 : ℝ) : ℂ) * u + (n : ℂ)) := by
      rw [hden, mul_one_div, div_eq_div_iff hd1 hden']
      ring
    rw [show u + ((2 * n : ℕ) : ℂ) = u + 2 * (n : ℂ) by push_cast; ring]
    rw [← mul_pow, hmain]
  rw [tsum_congr hterm, tsum_mul_left]
  have hunit : (1 / 2 : ℂ) * (((1 / 2 : ℝ) : ℂ)) ^ k * (2 : ℂ) ^ (k + 1) = 1 := by
    rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num,
      show (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ by norm_num, inv_pow, pow_succ]
    rw [show (2 : ℂ)⁻¹ * ((2 : ℂ) ^ k)⁻¹ * ((2 : ℂ) ^ k * 2)
        = ((2 : ℂ) ^ k)⁻¹ * (2 : ℂ) ^ k * ((2 : ℂ)⁻¹ * 2) by ring]
    rw [inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0)), one_mul,
        inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [show (1 / 2 : ℂ) * ((((1 / 2 : ℝ) : ℂ)) ^ k * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) *
        ((2 : ℂ) ^ (k + 1) * ∑' n : ℕ, (1 / (u + ((2 * n : ℕ) : ℂ))) ^ (k + 1))))
      = ((1 / 2 : ℂ) * (((1 / 2 : ℝ) : ℂ)) ^ k * (2 : ℂ) ^ (k + 1)) *
        ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) *
          ∑' n : ℕ, (1 / (u + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) by ring]
  rw [hunit, one_mul]

private lemma gammaFactor_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (k : ℕ) (hk : 1 ≤ k) (a : ℕ) (ha0 : χ.Even → a = 0) (ha1 : χ.Odd → a = 1)
    {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv k (logDeriv (DirichletCharacter.gammaFactor χ)) s
      = (-1) ^ (k + 1) * (k.factorial : ℂ) *
          ∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ (k + 1) := by
  rcases χ.even_or_odd with hE | hO
  · have ha : a = 0 := ha0 hE
    subst ha
    rw [show logDeriv (DirichletCharacter.gammaFactor χ) = logDeriv Complex.Gammaℝ from
      funext (fun z => Work.LinnikAreas.DhK.logDeriv_gammaFactor_of_even χ hE z)]
    rw [logDeriv_GammaR_iteratedDeriv k hk hs]
    apply congrArg (fun x => (-1) ^ (k + 1) * (k.factorial : ℂ) * x)
    apply tsum_congr
    intro n
    simp only [Nat.zero_add]
  · have ha : a = 1 := ha1 hO
    subst ha
    have hfun : logDeriv (DirichletCharacter.gammaFactor χ)
        = fun z : ℂ => logDeriv Complex.Gammaℝ (z + 1) := by
      funext z
      rw [Work.LinnikAreas.DhK.logDeriv_gammaFactor_of_odd χ hO z,
        Work.ZeroFreeTables.P3.logDeriv_eq_div (fun w : ℂ => Complex.Gammaℝ (w + 1)),
        Work.ZeroFreeTables.P3.logDeriv_eq_div Complex.Gammaℝ]
      dsimp only
      rw [deriv_comp_add_const]
    rw [hfun, iteratedDeriv_comp_add_const k (logDeriv Complex.Gammaℝ) 1]
    dsimp only
    rw [logDeriv_GammaR_iteratedDeriv k hk
      (by simp only [Complex.add_re, Complex.one_re]; linarith)]
    apply congrArg (fun x => (-1) ^ (k + 1) * (k.factorial : ℂ) * x)
    apply tsum_congr
    intro n
    have h : (s + 1) + ((2 * n : ℕ) : ℂ) = s + ((1 + 2 * n : ℕ) : ℂ) := by push_cast; ring
    rw [h]

/-! ## Auxiliary facts about the `L`-function -/

private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases Work.LinnikAreas.DhK.gammaFactor_eq_Gammaℝ_or χ with h | h
  · rw [h]; exact Work.LinnikAreas.DhK.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h]
    exact Work.LinnikAreas.DhK.Gammaℝ_ne_zero_of_re_pos (s := s + 1)
      (by simp only [Complex.add_re, Complex.one_re]; linarith)

private lemma LFunction_ne_zero_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : DirichletCharacter.LFunction χ s ≠ 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs

private lemma completedLFunction_ne_zero_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hγ := gammaFactor_ne_zero_of_re_pos χ (by linarith : 0 < s.re)
  rw [Work.LinnikAreas.DhK.completedLFunction_eq_L_mul_gammaFactor χ hχ s hγ]
  exact mul_ne_zero (LFunction_ne_zero_of_one_lt_re χ hs) hγ

/-! ## The `Λ`-half of the differentiated explicit formula -/

private lemma lHalf {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (k + 1)) ∧
    ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (k + 1))
      = iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) s := by
  classical
  obtain ⟨A, hA, hAb⟩ := invSubPowLeInvSq hs k hk
  have hΦb : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ →
      ‖(1 / (s - u)) ^ (k + 1)‖ ≤ A / ‖u‖ ^ 2 := fun u h1 h2 h3 => hAb u h1 h2 h3
  obtain ⟨hsum, htend⟩ := divisorSumBallTendsto χ hχ hprim hA hΦb
  have hΛne := completedLFunction_ne_zero_of_one_lt_re χ hχ hs
  have hPF := Work.ZeroFreeTables.P3.CompletedDerivPF_identity χ hχ hprim k hk s hΛne
  have hlim := htend.const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
  have hkey := tendsto_nhds_unique hPF hlim
  have hdivu : ∀ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
      = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) := by
    intro u
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
      (Set.mem_univ u)
  have hcoe : ∀ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ)
        = (Work.LinnikContract.zeroMult χ u : ℂ) := by
    intro u
    rw [hdivu u, Int.cast_natCast, ← zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
  constructor
  · exact hsum.congr (fun u => by rw [hcoe u])
  · rw [Work.ZeroFreeTables.P3.logDeriv_eq_div (DirichletCharacter.completedLFunction χ)]
    rw [hkey]
    congr 1
    exact tsum_congr (fun u => by rw [hcoe u])

private lemma split_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s
      = iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) s
        - iteratedDeriv k (logDeriv (DirichletCharacter.gammaFactor χ)) s := by
  have hΛan : AnalyticAt ℂ (logDeriv (DirichletCharacter.completedLFunction χ)) s := by
    have hd : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
      DirichletCharacter.differentiable_completedLFunction hχ
    have hne := completedLFunction_ne_zero_of_one_lt_re χ hχ hs
    rw [Work.ZeroFreeTables.P3.logDeriv_eq_div]
    exact ((hd.analyticAt s).deriv).div (hd.analyticAt s) hne
  have hLan : AnalyticAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) s := by
    have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      DirichletCharacter.differentiable_LFunction hχ
    have hne := LFunction_ne_zero_of_one_lt_re χ hs
    rw [Work.ZeroFreeTables.P3.logDeriv_eq_div]
    exact ((hd.analyticAt s).deriv).div (hd.analyticAt s) hne
  have hsub := iteratedDeriv_fun_sub (n := k) (x := s) hΛan.contDiffAt hLan.contDiffAt
  have hev : (fun z => logDeriv (DirichletCharacter.completedLFunction χ) z
        - logDeriv (DirichletCharacter.LFunction χ) z) =ᶠ[𝓝 s]
      logDeriv (DirichletCharacter.gammaFactor χ) := by
    filter_upwards [Work.LinnikAreas.DhK.isOpen_re_gt_one.mem_nhds hs] with z hz
    have h := Work.LinnikAreas.DhK.completedLFunction_logDeriv χ hχ z hz
    rw [h]; ring
  have hγ : iteratedDeriv k (logDeriv (DirichletCharacter.gammaFactor χ)) s
      = iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) s
        - iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s := by
    rw [← Filter.EventuallyEq.iteratedDeriv_eq k hev]
    exact hsub
  rw [hγ]; ring

/-! ## The differentiated explicit formula for a Dirichlet `L`-function, general `k` -/

/-- **Differentiated explicit formula for a primitive Dirichlet `L`-function, tsum form, all `k ≥ 1`.**

For a non-principal primitive character `χ` mod `N`, `k ≥ 1`, `1 < Re s`, and `a ∈ {0,1}` the
parity shift of `χ` (`a = 0` if `χ` is even, `a = 1` if odd, i.e. the trivial zeros of `L(·,χ)` are
`-a, -a-2, -a-4, …`),

`(∑' u, ord_u(Λ_χ)·(1/(s-u))^{k+1}) + (∑' n, (1/(s + a + 2n))^{k+1})
   = (-1)^k ·(1/k!)·((logDeriv L(·,χ))^{(k)})(s)`,

(in particular the first family is summable), where `ord_u(Λ_χ) = Work.LinnikContract.zeroMult χ u`
is the multiplicity of `u` as a non-trivial zero of `L(·,χ)`.

This is the general-`k` form of `Work.LinnikAreas.FarRepel.lDiffExplicit` (there stated for odd `k`,
where `(-1)^k = -1`): the sign `(-1)^k` is carried by all three ingredient identities
`lHalf` (`(-1)^k k! · Σ_zeros = (Λ'/Λ)^{(k)}`), `gammaFactor_iteratedDeriv`
(`(logDeriv Γ-factor)^{(k)} = (-1)^{k+1} k! · Σ_trivial`) and `split_logDeriv`
(`(L'/L)^{(k)} = (Λ'/Λ)^{(k)} - (Γ'/Γ)^{(k)}`). -/
theorem lDiffExplicit_gen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k)
    (a : ℕ) (ha0 : χ.Even → a = 0) (ha1 : χ.Odd → a = 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (k + 1)) ∧
    (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (k + 1))
      + (∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ (k + 1))
      = (-1 : ℂ) ^ k * (1 / (k.factorial : ℂ)) *
          iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s := by
  classical
  obtain ⟨hsum, hkey⟩ := lHalf χ hχ hprim k hk hs
  have hsre : 0 < s.re := by linarith
  have hγk := gammaFactor_iteratedDeriv χ k hk a ha0 ha1 hsre
  have hsplit := split_logDeriv χ hχ k hs
  set T : ℂ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (k + 1) with hT
  set S : ℂ := ∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ (k + 1) with hS
  set Lk : ℂ := iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s with hLk
  set Lm : ℂ := iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) s with hLm
  set Gk : ℂ := iteratedDeriv k (logDeriv (DirichletCharacter.gammaFactor χ)) s with hGk
  have h1 : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * T = Lm := by
    rw [hT, hLm]; exact hkey
  have h2 : Gk = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * S := by
    rw [hGk, hS]; exact hγk
  have h3 : Lk = Lm - Gk := by
    rw [hLk, hLm, hGk]; exact hsplit
  have h2' : Gk = - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * S := by
    rw [h2]
    have hp : (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        = - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) := by
      rw [pow_succ]; ring
    rw [hp]
  have h4 : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (T + S) = Lk := by
    rw [h3, ← h1, h2']; ring
  have hcne : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
  have hcf : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
      ((-1 : ℂ) ^ k * (1 / (k.factorial : ℂ))) = 1 := by
    have hcone : (-1 : ℂ)^k * (-1 : ℂ)^k = 1 := by
      rw [← mul_pow, show (-1 : ℂ) * (-1 : ℂ) = 1 by norm_num, one_pow]
    have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [show ((-1 : ℂ)^k * (k.factorial : ℂ)) * ((-1 : ℂ)^k * (1 / (k.factorial : ℂ)))
        = ((-1 : ℂ)^k * (-1 : ℂ)^k) * ((k.factorial : ℂ) * (1 / (k.factorial : ℂ))) by ring,
      hcone, one_mul, mul_one_div, div_self hkf]
  have hthis : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
      ((-1 : ℂ) ^ k * (1 / (k.factorial : ℂ)) * Lk) = Lk := by
    rw [← mul_assoc, hcf, one_mul]
  have h6 : T + S = (-1 : ℂ) ^ k * (1 / (k.factorial : ℂ)) * Lk :=
    mul_left_cancel₀ hcne (h4.trans hthis.symm)
  exact ⟨hsum, h6⟩

end Work.ZeroFreeTables.P9
