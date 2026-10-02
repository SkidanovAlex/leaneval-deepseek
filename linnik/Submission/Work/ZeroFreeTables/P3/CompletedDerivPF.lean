/-
# ZeroFreeTables/P3/CompletedDerivPF — the partial-fraction expansion of the `k`-th derivative

This file proves `Work.ZeroFreeTables.P3.CompletedDerivPF`, the partial-fraction
("Mittag-Leffler") description of the `k`-th derivative of the logarithmic derivative of the
completed Dirichlet `L`-function.

For a non-trivial primitive character `χ` mod `N`, put `Λ = completedLFunction χ`; `Λ` is
entire, `Λ 0 ≠ 0`, and the divisor `d_R u = divisor Λ (closedBall 0 R) u` records the zero
multiplicities of `Λ` inside the disc of radius `R`.

The statement has two parts.

* **(PF identity)** For every `s` with `Λ s ≠ 0`,
  `(-1)^k k! Σᶠ_{|u| ≤ R} d_R u (1/(s-u))^(k+1) → (Λ'/Λ)^(k)(s)` as `R → ∞`
  (the `finsum` is a finite sum because the divisor has finite support).

* **(truncation error)** the closed-ball sum over `|u| ≤ T` approximates `(Λ'/Λ)^(k)(s)`
  with error `≲ L_N(N,A)²/A · (1 + ‖s‖)` for `A ≤ T ≤ 2A`, uniformly in `s` with `8‖s‖ ≤ T`,
  on the "good radii" `T` at which no zero of `Λ` comes within `1/L_N(N,A)²` of the circle
  `|z| = T`.

The argument is the standard cofactor decomposition.  Writing
`Λ = (∏_{|u| ≤ R} (z-u)^{d_R u}) · g_R` and differentiating the identity
`logDeriv Λ = Σᶠ_u d_R u /(z-u) + logDeriv g_R` `k` times gives
`(Λ'/Λ)^(k)(s) = (-1)^k k! Σᶠ_{|u| ≤ R} d_R u (1/(s-u))^(k+1) + (logDeriv g_R)^(k)(s)`,
so both parts reduce to estimating the "cofactor defect" `(logDeriv g_R)^(k)(s)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.Imports
import Submission.Work.ZeroFreeTables.P3.cofactorIteratedDeriv_le
import Submission.Work.ZeroFreeTables.P3.annulusKDSum_le

open Complex DirichletCharacter Metric MeromorphicOn Filter Function Set Topology
open scoped Real Topology BigOperators

open Commons.NumberTheory.Linnik (L_N logN_nonneg pf_L_ge_two pf_L_pos pf_L_mono pf_L_two_mul_le)

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Work.ZeroFreeTables.P3

/-! ## Auxiliary calculus lemmas -/

/-- `logDeriv` written as the quotient `f' / f`. -/
lemma logDeriv_eq_div (f : ℂ → ℂ) : logDeriv f = fun z => deriv f z / f z := by
  funext z; rw [logDeriv_apply]

/-- The `k`-th derivative of `1/(z-u)` at `x ≠ u` is `(-1)^k k! / (x-u)^(k+1)`. -/
lemma iteratedDeriv_inv_sub (k : ℕ) (x u : ℂ) (hxu : x ≠ u) :
    iteratedDeriv k (fun z : ℂ => 1/(z-u)) x = (-1)^k * (k.factorial : ℂ) * (1/(x-u))^(k+1) := by
  have h1 : iteratedDeriv k (fun z : ℂ => 1/(z-u)) x = iteratedDeriv k (fun w : ℂ => 1/w) (x-u) := by
    have := iteratedDeriv_comp_sub_const k (fun w : ℂ => 1/w) u
    exact congrFun this x
  rw [h1]
  have h2 : iteratedDeriv k (fun w : ℂ => 1/w) (x-u)
      = iteratedDerivWithin k (fun w : ℂ => 1/w) Set.univ (x-u) := by
    rw [iteratedDerivWithin_univ]
  rw [h2, iteratedDerivWithin_one_div k isOpen_univ (Set.mem_univ _)]
  simp only
  have : (x - u) ^ (-1 - (k:ℤ)) = (1/(x-u))^(k+1) := by
    rw [show (-1 - (k:ℤ)) = -(((k:ℤ)+1)) by ring, zpow_neg,
        show ((k:ℤ)+1) = ((k+1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, one_div_pow,
        inv_eq_one_div]
  rw [this]

/-- The `k`-th derivative of the finitely supported "principal part" sum
`z ↦ Σᶠ_u d_u / (z - u)` at `x` is `(-1)^k k! Σᶠ_u d_u / (x-u)^(k+1)`. -/
lemma iteratedDeriv_finsum_inv_sub (k : ℕ) (d : ℂ → ℤ) (hfin : (Function.support d).Finite)
    (x : ℂ) (hx : ∀ u ∈ Function.support d, x ≠ u) :
    iteratedDeriv k (fun z : ℂ => ∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z - u))) x
      = (-1)^k * (k.factorial : ℂ) * (∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(x-u))^(k+1)) := by
  classical
  have hS : ∀ u, u ∈ hfin.toFinset ↔ d u ≠ 0 := by
    intro u; rw [Set.Finite.mem_toFinset, Function.mem_support]
  have key_supp : ∀ (f0 : ℂ → ℂ),
      Function.support (fun u : ℂ => ((d u : ℤ) : ℂ) * f0 u) ⊆ (hfin.toFinset : Set ℂ) := by
    intro f0 u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0; exact hu (by simp [h0])
  have hfs : (fun z : ℂ => ∑ᶠ u, ((d u : ℤ) : ℂ) * (1/(z - u)))
      = (fun z : ℂ => ∑ u ∈ hfin.toFinset, ((d u : ℤ) : ℂ) * (1/(z - u))) := by
    funext z; exact finsum_eq_sum_of_support_subset _ (key_supp (fun u => 1/(z-u)))
  rw [hfs]
  have hsum : (fun z : ℂ => ∑ u ∈ hfin.toFinset, ((d u : ℤ) : ℂ) * (1/(z - u)))
      = (∑ u ∈ hfin.toFinset, fun z : ℂ => ((d u : ℤ) : ℂ) * (1/(z - u))) := by
    funext z; rw [Finset.sum_apply]
  rw [hsum, iteratedDeriv_sum]
  · rw [finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℂ) * (1/(x-u))^(k+1))
      (key_supp (fun u => (1/(x-u))^(k+1)))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro u hu
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_inv_sub k x u (hx u ((hS u).mp hu))]
    ring
  · intro u hu
    have hne : x - u ≠ 0 := sub_ne_zero.mpr (hx u ((hS u).mp hu))
    fun_prop (disch := exact hne)

/-! ## The cofactor decomposition of the `k`-th derivative -/

/-- If `f = (∏_{|u| ≤ R} (z-u)^{d_R u}) · g` on the disc of radius `R+ε` with `g` analytic and
non-zero there, then differentiating `logDeriv f = Σᶠ_u d_u/(z-u) + logDeriv g` `k` times gives
the partial-fraction decomposition of the `k`-th derivative of `logDeriv f`. -/
lemma iteratedDeriv_logDeriv_decompose {f g : ℂ → ℂ} {R ε : ℝ}
    (hfdiff : Differentiable ℂ f)
    (hfac : ∀ z, z ∈ Metric.ball (0 : ℂ) (R + ε) →
      f z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R) u)) * g z)
    (hg_an : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (R + ε)))
    {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (R + ε)) (hfs : f s ≠ 0) (k : ℕ) :
    iteratedDeriv k (logDeriv f) s =
      (-1)^k * (k.factorial : ℂ) *
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ)
          * (1/(s-u))^(k+1))
      + iteratedDeriv k (logDeriv g) s := by
  classical
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R) u with hd
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := fun z _ => hfdiff.analyticAt z
  have hsupp : (Function.support d).Finite := by
    rw [hd]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0:ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  have hdzero : ∀ u, d u ≠ 0 → f u = 0 := by
    intro u hdu
    have hdu' : MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R) u ≠ 0 := by simpa [hd] using hdu
    have huB : u ∈ Metric.closedBall (0:ℂ) R := by
      by_contra hout
      rw [MeromorphicOn.divisor_def] at hdu'
      simp [hout] at hdu'
    by_contra hfu
    have hord : meromorphicOrderAt f u = 0 :=
      Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hfB u huB) hfu
    have hdiv : MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R) u = 0 := by
      rw [MeromorphicOn.divisor_apply hfB.meromorphicOn huB]
      simp [hord]
    exact hdu' hdiv
  have hs_ne : ∀ u, d u ≠ 0 → s ≠ u := by
    intro u hdu hsu
    exact hfs (by rw [hsu]; exact hdzero u hdu)
  have hopen : ∀ᶠ z in 𝓝 s, z ∈ Metric.ball (0:ℂ) (R+ε) ∧ f z ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 s, z ∈ Metric.ball (0:ℂ) (R+ε) := isOpen_ball.mem_nhds hs
    have h2 : ∀ᶠ z in 𝓝 s, f z ≠ 0 := (hfdiff.continuous.continuousAt).eventually_ne hfs
    filter_upwards [h1, h2] with z hz1 hz2; exact ⟨hz1, hz2⟩
  have heq : logDeriv f =ᶠ[𝓝 s]
      (fun z => (∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u))) + logDeriv g z) := by
    filter_upwards [hopen] with z ⟨hzB, hfz⟩
    have hgz : g z ≠ 0 := by
      have h := hfac z hzB
      rw [h] at hfz
      exact (mul_ne_zero_iff.mp hfz).2
    have hgd : DifferentiableAt ℂ g z := (hg_an z hzB).differentiableAt
    have hdec := Commons.NumberTheory.Linnik.logDeriv_decompose (f := f) (g := g) (R := R) (ε := ε)
      hfdiff hfac hzB hfz hgd hgz
    rw [hdec, hd]
  have hLHS : iteratedDeriv k (logDeriv f) s
      = iteratedDeriv k (fun z => (∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u))) + logDeriv g z) s :=
    (Filter.EventuallyEq.iteratedDeriv heq k).eq_of_nhds
  rw [hLHS]
  have hAdiff : ContDiffAt ℂ (↑k) (fun z : ℂ => ∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u))) s := by
    have hfs_eq : (fun z : ℂ => ∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u)))
        = (fun z : ℂ => ∑ u ∈ hsupp.toFinset, (((d u : ℤ)) : ℂ) * (1/(z-u))) := by
      funext z
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0; exact hu (by simp [h0])
    rw [hfs_eq]
    apply ContDiffAt.sum
    intro u hu
    have hdu : d u ≠ 0 := by rw [Set.Finite.mem_toFinset, Function.mem_support] at hu; exact hu
    have hne : s - u ≠ 0 := sub_ne_zero.mpr (hs_ne u hdu)
    fun_prop (disch := exact hne)
  have hBdiff : ContDiffAt ℂ (↑k) (logDeriv g) s := by
    have hgs : g s ≠ 0 := by
      have h := hfac s hs
      rw [h] at hfs
      exact (mul_ne_zero_iff.mp hfs).2
    have hgB : AnalyticAt ℂ g s := hg_an s hs
    have hgd : AnalyticAt ℂ (deriv g) s := hgB.deriv
    rw [logDeriv_eq_div g]
    exact (hgd.div hgB hgs).contDiffAt
  rw [show (fun z : ℂ => (∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u))) + logDeriv g z)
        = (fun z : ℂ => ∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u))) + logDeriv g from rfl]
  rw [iteratedDeriv_add (f := (fun z : ℂ => ∑ᶠ u, (((d u : ℤ)) : ℂ) * (1/(z-u))))
        (g := logDeriv g) (x := s) (n := k) hAdiff hBdiff]
  congr 1
  exact iteratedDeriv_finsum_inv_sub k d hsupp s hs_ne

/-! ## Part 2 : the truncation error at good radii -/

/-- **Truncation error of the `k`-th derivative partial-fraction sum.**  There are constants
`C ≥ 0` and `A₁` such that for all `A ≥ A₁`, all `T` with `A ≤ T ≤ 2A` at which no zero of the
completed `L`-function comes within `1/L_N(N,A)²` of the circle `|z| = T`, and all `s` with
`Λ s ≠ 0` and `8‖s‖ ≤ T`, the closed-ball partial-fraction sum over the zeros of `Λ` with
`‖u‖ ≤ T` approximates the `k`-th derivative of `Λ'/Λ` at `s` within
`C · L_N(N,A)²/A · (1 + ‖s‖)`. -/
lemma CompletedDerivPF_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A₁ : ℝ, ∀ A : ℝ, A₁ ≤ A → ∀ T : ℝ, A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
        (L_N N A) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 → 8 * ‖s‖ ≤ T →
        ‖iteratedDeriv k (fun z => deriv (DirichletCharacter.completedLFunction χ) z /
              DirichletCharacter.completedLFunction χ z) s
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.closedBall 0 T)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1))‖
          ≤ C * (L_N N A) ^ 2 / A * (1 + ‖s‖) := by
  classical
  rcases Commons.NumberTheory.Linnik.completedL_zeroCount χ hχ hχprim with ⟨zc0, hzc0⟩
  rcases Commons.NumberTheory.Linnik.completedL_growth_circle χ hχ hχprim with ⟨gc0, hgc0⟩
  rcases Commons.NumberTheory.Linnik.pf_zeros_ge_delta χ hχ hχprim with ⟨δ₀, hδ₀pos, hδ₀le1, hδ₀⟩
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  have hΛdiff : Differentiable ℂ Λ := by
    rw [hΛdef]; exact DirichletCharacter.differentiable_completedLFunction hχ
  have hΛ0 : Λ 0 ≠ 0 := by
    rw [hΛdef]; exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  let zc : ℝ := max zc0 0
  let gc : ℝ := max gc0 0
  have hzcnn : 0 ≤ zc := le_max_right _ _
  have hgcnn : 0 ≤ gc := le_max_right _ _
  have hzc0le : zc0 ≤ zc := le_max_left _ _
  have hgc0le : gc0 ≤ gc := le_max_left _ _
  have hzc : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ))
        ≤ zc * R * L_N N R := by
    intro R hR
    have h' := hzc0 R hR
    have h : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ))
        ≤ zc0 * R * L_N N R := by simpa [Commons.NumberTheory.Linnik.L_N] using h'
    have hL0 : 0 ≤ L_N N R := le_of_lt (pf_L_pos (N := N) (by linarith only [hR]))
    have hR0 : 0 ≤ R := by linarith only [hR]
    have h1 : zc0 * R * L_N N R ≤ zc * R * L_N N R := by
      have h2 : zc0 * R ≤ zc * R := mul_le_mul_of_nonneg_right hzc0le hR0
      exact mul_le_mul_of_nonneg_right h2 hL0
    linarith only [h, h1]
  have hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖Λ z‖ ≤ Real.exp (gc * R * L_N N R) := by
    intro R hR z hz
    have h := hgc0 R hR z hz
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    have hL0 : 0 ≤ L_N N R := le_of_lt (pf_L_pos (N := N) (by linarith only [hR]))
    have hR0 : 0 ≤ R := by linarith only [hR]
    have h2 : gc0 * R ≤ gc * R := mul_le_mul_of_nonneg_right hgc0le hR0
    exact mul_le_mul_of_nonneg_right h2 hL0
  let K0 : ℝ := 4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1
  have hK0nn : 0 ≤ K0 := by
    dsimp [K0]; linarith only [hzcnn, hgcnn, abs_nonneg (Real.log ‖Λ 0‖)]
  have hK0one : 1 ≤ K0 := by
    dsimp [K0]; linarith only [hzcnn, hgcnn, abs_nonneg (Real.log ‖Λ 0‖)]
  have hK0pos : 0 < K0 := lt_of_lt_of_le one_pos hK0one
  let C : ℝ := (k.factorial : ℝ) * 192 * 16 ^ k * K0 * 2
  have hCnn : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hCnn, max (Real.exp |Real.log δ₀|) 2, ?_⟩
  intro A hA T hAT hT2A hmargin s hΛs hsT
  have hA2 : 2 ≤ A := le_trans (le_max_right _ _) hA
  have hA1 : 1 ≤ A := by linarith only [hA2]
  have hA0 : 0 ≤ A := by linarith only [hA2]
  have hApos : 0 < A := by linarith only [hA2]
  have hAexp : Real.exp |Real.log δ₀| ≤ A := le_trans (le_max_left _ _) hA
  have hTpos : 0 < T := by linarith only [hAT, hA2]
  have hT2 : 2 ≤ T := by linarith only [hAT, hA2]
  have hT0 : 0 ≤ T := le_of_lt hTpos
  have hLgeD : |Real.log δ₀| ≤ L_N N A := by
    have h1 : |Real.log δ₀| ≤ Real.log A := by
      have h := Real.log_le_log (Real.exp_pos _) hAexp
      rwa [Real.log_exp] at h
    have h2 : Real.log A ≤ L_N N A := by
      dsimp [L_N]
      have h3 : Real.log A ≤ Real.log (A + 2) := Real.log_le_log (by linarith only [hA2]) (by linarith only [])
      have h4 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
      linarith only [h3, h4]
    linarith only [h1, h2]
  -- cofactor
  obtain ⟨g, M0, hM0nn, hg_an_T, hg_nz_T, hfac_T, hfacs, hball, horigin, hM0le⟩ :=
    pf_cofactor_logbound χ hχ hχprim hA0 hA1 hTpos hT2 hT2A hmargin
      zc gc hzcnn hgcnn hzc hgc δ₀ hδ₀pos hLgeD hδ₀
  obtain ⟨ε, hε, hg_an_ε, hfac_ε⟩ := hfacs
  -- prepare the decomposition
  have hfac_decomp : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) (T + ε) →
      Λ z = (∏ᶠ u : ℂ, (z - u) ^
        (MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) T) u)) * g z := by
    intro z hz
    have h := hfac_ε z hz
    rw [← hΛdef] at h
    simpa [Commons.NumberTheory.Linnik.pfP] using h
  have hs_ball : s ∈ Metric.ball (0 : ℂ) (T + ε) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have : ‖s‖ ≤ T / 8 := by linarith only [hsT]
    linarith only [hAT, hsT, hA2, hε]
  have hdec := iteratedDeriv_logDeriv_decompose (f := Λ) (g := g) (R := T) (ε := ε)
    hΛdiff hfac_decomp hg_an_ε hs_ball hΛs k
  -- the Cauchy bound on the cofactor defect
  have hgd := cofactorIteratedDeriv_le hTpos k hk hg_an_T hg_nz_T hM0nn hball horigin hsT
  -- assemble
  rw [← logDeriv_eq_div Λ]
  have hgoal_eq : iteratedDeriv k (logDeriv Λ) s
      - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) T)) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1))
      = iteratedDeriv k (logDeriv g) s := by
    rw [hdec]; ring
  rw [hgoal_eq]
  -- final arithmetic
  have hm0 : max M0 1 ≤ K0 * (A * (L_N N A) ^ 2 + 1) := by
    have h1 : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1) * (A * (L_N N A) ^ 2 + 1) := by
      simpa [K0] using hM0le
    have h2 : (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1) * (A * (L_N N A) ^ 2 + 1)
        ≤ K0 * (A * (L_N N A) ^ 2 + 1) := le_of_eq rfl
    have h3 : 1 ≤ K0 * (A * (L_N N A) ^ 2 + 1) := by
      have h4 : 1 ≤ A * (L_N N A) ^ 2 + 1 := by
        have h5 : 0 ≤ (L_N N A) ^ 2 := sq_nonneg _
        nlinarith only [hAT, hT2A]
      nlinarith only [hK0one, h4, hK0nn]
    exact max_le (le_trans h1 h2) h3
  have hTpow : A * A ^ k ≤ T ^ (k + 1) := by
    have hAk : A ^ k ≤ T ^ k := pow_le_pow_left₀ hA0 hAT k
    have h1 : A * A ^ k ≤ A * T ^ k := mul_le_mul_of_nonneg_left hAk hA0
    have h2 : A * T ^ k ≤ T * T ^ k := mul_le_mul_of_nonneg_right hAT (pow_nonneg hT0 k)
    have h3 : T * T ^ k = T ^ (k + 1) := by rw [pow_succ]; ring
    linarith only [h1, h2, h3]
  have hden1 : (0:ℝ) < T ^ (k + 1) := pow_pos hTpos _
  have hden2 : (0:ℝ) < A * A ^ k := mul_pos hApos (pow_pos hApos k)
  have hAL2 : 1 ≤ (L_N N A) ^ 2 := by
    have h := pf_L_ge_two (N := N) hA0
    nlinarith only [h]
  have hAkge : A ≤ A ^ k := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hk
  have hAk1 : 1 ≤ A ^ k := le_trans hA1 hAkge
  have hkey : max M0 1 / T ^ (k + 1) ≤ 2 * K0 * (L_N N A) ^ 2 / A := by
    have s1 : max M0 1 / T ^ (k + 1) ≤ max M0 1 / (A * A ^ k) :=
      div_le_div_of_nonneg_left (by positivity) hden2 hTpow
    have s2 : max M0 1 / (A * A ^ k) ≤ K0 * (A * (L_N N A) ^ 2 + 1) / (A * A ^ k) :=
      div_le_div_of_nonneg_right hm0 (le_of_lt hden2)
    have s3 : K0 * (A * (L_N N A) ^ 2 + 1) / (A * A ^ k)
        ≤ K0 * (2 * (L_N N A) ^ 2 * A) / (A * A ^ k) := by
      have hnum : A * (L_N N A) ^ 2 + 1 ≤ 2 * (L_N N A) ^ 2 * A := by nlinarith only [hAL2, hA1, hA2]
      have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hK0nn) (le_of_lt hden2)
      simpa [mul_assoc] using this
    have s4 : K0 * (2 * (L_N N A) ^ 2 * A) / (A * A ^ k) = 2 * K0 * (L_N N A) ^ 2 / A ^ k := by
      rw [div_eq_div_iff (ne_of_gt hden2) (ne_of_gt (pow_pos hApos k))]
      ring
    have s5 : 2 * K0 * (L_N N A) ^ 2 / A ^ k ≤ 2 * K0 * (L_N N A) ^ 2 / A := by
      have hnum2 : 0 ≤ 2 * K0 * (L_N N A) ^ 2 := by positivity
      exact div_le_div_of_nonneg_left hnum2 hApos hAkge
    linarith only [s1, s2, s3, s4.le, s4.ge, s5, s4]
  have hCeq : C = (k.factorial : ℝ) * 192 * 16 ^ k * K0 * 2 := rfl
  have hstep : (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (L_N N A) ^ 2 / A) := by
    have hfac : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k := by positivity
    calc (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1)
        = (k.factorial : ℝ) * 192 * 16 ^ k * (max M0 1 / T ^ (k + 1)) := by ring
      _ ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (L_N N A) ^ 2 / A) :=
          mul_le_mul_of_nonneg_left hkey hfac
  refine le_trans hgd ?_
  refine le_trans hstep ?_
  rw [hCeq]
  have hpos : 1 ≤ 1 + ‖s‖ := by have := norm_nonneg s; linarith only [this]
  have hL2n : 0 ≤ (L_N N A) ^ 2 := sq_nonneg _
  have hAinv : 0 ≤ (L_N N A) ^ 2 / A := div_nonneg hL2n hA0
  have hbase : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (L_N N A) ^ 2 / A)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((L_N N A) ^ 2 / A * (1 + ‖s‖)) := by
    have hfac : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k := by positivity
    have hfac2 : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) := by positivity
    have he : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (L_N N A) ^ 2 / A)
        = (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((L_N N A) ^ 2 / A) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hAinv hpos) hfac2
  refine le_trans hbase ?_
  have heq2 : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((L_N N A) ^ 2 / A * (1 + ‖s‖))
      = C * (L_N N A) ^ 2 / A * (1 + ‖s‖) := by
    rw [hCeq]; ring
  rw [heq2]

/-! ## Difference of two ball sums -/

/-- The difference of the partial-fraction sums at radii `R ≤ R'` is the annulus sum. -/
lemma finsum_divisor_diff_eq {f : ℂ → ℂ} (hfmer : ∀ U : Set ℂ, MeromorphicOn f U)
    {R R' : ℝ} (hRR' : R ≤ R') (s : ℂ) (k : ℕ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall 0 R')) u : ℤ) : ℂ)
        * (1/(s-u))^(k+1))
      - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1/(s-u))^(k+1))
    = ∑ᶠ u : ℂ, ((((MeromorphicOn.divisor f (Metric.closedBall 0 R')) u
        - MeromorphicOn.divisor f (Metric.closedBall 0 R) u : ℤ)) : ℂ) * (1/(s-u))^(k+1) := by
  classical
  set d1 : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall 0 R) u with hd1
  set d2 : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall 0 R') u with hd2
  have hfin2 : (Function.support d2).Finite := by
    rw [hd2]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall 0 R')
      (hfmer _) (isCompact_closedBall 0 R') (by simp)
  let S := hfin2.toFinset
  have h2eq : ∀ u, u ∈ S ↔ d2 u ≠ 0 := by
    intro u
    rw [show (u ∈ S) = (u ∈ hfin2.toFinset) from rfl, Set.Finite.mem_toFinset, Function.mem_support]
  have hle1 : ∀ u, d1 u ≠ 0 → ‖u‖ ≤ R := by
    intro u hu
    by_contra hle
    have hout : u ∉ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using lt_of_not_ge hle
    exact hu (by rw [hd1]; exact Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem (f := f) hout)
  have h12 : ∀ u, d1 u ≠ 0 → d2 u = d1 u := by
    intro u hu
    have hle := hle1 u hu
    rw [hd1, hd2]
    exact (Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hfmer hle
      (le_trans hle hRR')).symm
  have hmem1 : ∀ u, d1 u ≠ 0 → u ∈ S := by
    intro u hu
    rw [h2eq]
    rw [h12 u hu]
    exact hu
  have hsupp1 : Function.support (fun u : ℂ => ((d1 u : ℤ) : ℂ) * (1/(s-u))^(k+1))
      ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    exact hmem1 u (fun h0 => hu (by simp [h0]))
  have hsupp2 : Function.support (fun u : ℂ => ((d2 u : ℤ) : ℂ) * (1/(s-u))^(k+1))
      ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    exact (h2eq u).mpr (fun h0 => hu (by simp [h0]))
  have hsupp3 : Function.support (fun u : ℂ => (((d2 u - d1 u : ℤ)) : ℂ) * (1/(s-u))^(k+1))
      ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hd2 : d2 u ≠ 0 := by
      intro h0
      have hne : d2 u - d1 u ≠ 0 := by
        intro hz; apply hu; rw [hz]; simp
      have hd1 : d1 u ≠ 0 := by
        intro hz; exact hne (by rw [h0, hz]; simp)
      exact hd1 ((h12 u hd1).symm.trans h0)
    exact (h2eq u).mpr hd2
  rw [finsum_eq_sum_of_support_subset (s := S) _ hsupp2,
      finsum_eq_sum_of_support_subset (s := S) _ hsupp1,
      finsum_eq_sum_of_support_subset (s := S) _ hsupp3,
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Int.cast_sub, sub_mul]

/-! ## Part 1 : the partial-fraction identity -/

/-- **Partial-fraction identity for the `k`-th derivative.**  For every `s` with `Λ s ≠ 0`,
the closed-ball sums `(-1)^k k! Σᶠ_{|u| ≤ R} d_R u (1/(s-u))^(k+1)` converge to the `k`-th
derivative of `Λ'/Λ` at `s` as `R → ∞`. -/
theorem CompletedDerivPF_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) :
    ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1)))
        Filter.atTop (nhds (iteratedDeriv k (fun z => deriv (DirichletCharacter.completedLFunction χ) z /
            DirichletCharacter.completedLFunction χ z) s)) := by
  classical
  intro s hΛs
  rcases Commons.NumberTheory.Linnik.goodRadius_geometric χ hχ hχprim with ⟨Ag, hAgpos, hgood⟩
  rcases CompletedDerivPF_bound χ hχ hχprim k hk with ⟨C2, hC2nn, A2, hbound2⟩
  rcases annulusKDSum_le χ hχ hχprim k hk with ⟨CB, hCBnn, hann⟩
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  have hΛdiff : Differentiable ℂ Λ := by
    rw [hΛdef]; exact DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  set eR : ℝ → ℝ := fun R => (k.factorial : ℝ) * (CB * (L_N N R) / R)
      + C2 * (L_N N R) ^ 2 / R * (1 + ‖s‖) with heRdef
  have h1 : Filter.Tendsto (fun R : ℝ => (L_N N R) / R) Filter.atTop (nhds 0) := by
    have h := Commons.NumberTheory.Linnik.log_add_two_add_const_div_self_tendsto_zero
      (Real.log (N : ℝ) + 2)
    refine h.congr' ?_
    filter_upwards with R
    simp only [Commons.NumberTheory.Linnik.L_N]
    ring
  have h2 : Filter.Tendsto (fun R : ℝ => (L_N N R) ^ 2 / R) Filter.atTop (nhds 0) :=
    Commons.NumberTheory.Linnik.pf_L_sq_div_self_tendsto_zero (N := N)
  have hterm1 : Filter.Tendsto (fun R : ℝ => (k.factorial : ℝ) * (CB * (L_N N R) / R))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => ((k.factorial : ℝ) * CB) * ((L_N N R) / R))
        Filter.atTop (nhds 0) := by
      simpa using h1.const_mul ((k.factorial : ℝ) * CB)
    refine h.congr' ?_
    filter_upwards with R
    ring
  have hterm2 : Filter.Tendsto (fun R : ℝ => C2 * (L_N N R) ^ 2 / R * (1 + ‖s‖))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => (C2 * (1 + ‖s‖)) * ((L_N N R) ^ 2 / R))
        Filter.atTop (nhds 0) := by
      simpa using h2.const_mul (C2 * (1 + ‖s‖))
    refine h.congr' ?_
    filter_upwards with R
    ring
  have heR0 : Filter.Tendsto eR Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => (k.factorial : ℝ) * (CB * (L_N N R) / R)
        + C2 * (L_N N R) ^ 2 / R * (1 + ‖s‖)) Filter.atTop (nhds 0) := by
      simpa using hterm1.add hterm2
    refine h.congr' ?_
    filter_upwards with R
    simp only [heRdef]
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        - iteratedDeriv k (fun z => deriv Λ z / Λ z) s‖ ≤ eR R := by
    filter_upwards [Filter.eventually_ge_atTop (max (max Ag A2) (max 2 (8 * ‖s‖ + 1)))] with R hR
    have hRAg : Ag ≤ R := le_trans (le_trans (le_max_left Ag A2) (le_max_left _ _)) hR
    have hRA2 : A2 ≤ R := le_trans (le_trans (le_max_right Ag A2) (le_max_left _ _)) hR
    have hR2 : 2 ≤ R := le_trans (le_trans (le_max_left 2 (8 * ‖s‖ + 1)) (le_max_right _ _)) hR
    have hRs : 8 * ‖s‖ + 1 ≤ R :=
      le_trans (le_trans (le_max_right 2 (8 * ‖s‖ + 1)) (le_max_right _ _)) hR
    have hsR : 8 * ‖s‖ ≤ R := by linarith only [hRs]
    obtain ⟨T, hRT, hT2R, hmargin_raw⟩ := hgood R hRAg
    have hmargin : ∀ u : ℂ, Λ u = 0 → (L_N N R) ^ 2 * |‖u‖ - T| ≥ 1 := by
      intro u hu
      have h := hmargin_raw u (by rwa [hΛdef] at hu)
      simpa [Commons.NumberTheory.Linnik.L_N] using h
    have hTR : 8 * ‖s‖ ≤ T := by linarith only [hRs, hRT]
    have hb2 := hbound2 R hRA2 T hRT hT2R hmargin s hΛs hTR
    set SR : ℂ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1) with hSR
    set ST : ℂ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1) with hST
    set VT : ℂ := iteratedDeriv k (fun z => deriv Λ z / Λ z) s with hVT
    have hb2' : ‖VT - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST‖
        ≤ C2 * (L_N N R) ^ 2 / R * (1 + ‖s‖) := by
      simpa [hST, hVT, hΛdef] using hb2
    have hann' : ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u
          - MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ)) : ℂ)
          * (1 / (s - u)) ^ (k + 1)‖ ≤ CB * (L_N N R) / R := by
      simpa [hΛdef] using hann s R T hR2 hRT hsR
    have hnormident : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u
            - MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ)) : ℂ)
          * (1 / (s - u)) ^ (k + 1))‖ ≤ (k.factorial : ℝ) * (CB * (L_N N R) / R) := by
      rw [norm_mul]
      have hnorm : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ))‖ = (k.factorial : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
        simp
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hann' (by positivity)
    have hsumdiff : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        = -(∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u
            - MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ)) : ℂ)
            * (1 / (s - u)) ^ (k + 1)) := by
      rw [← neg_sub, finsum_divisor_diff_eq hΛmer hRT s k]
    have hfirst : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
        - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST‖
        ≤ (k.factorial : ℝ) * (CB * (L_N N R) / R) := by
      have hid : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
          - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST
          = -(((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u
                  - MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ)) : ℂ)
                * (1 / (s - u)) ^ (k + 1))) := by
        rw [← mul_sub, hSR, hST, hsumdiff, mul_neg]
      rw [hid, norm_neg]
      exact hnormident
    have hsplit : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR - VT
        = (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST)
          + (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST - VT) := by ring
    have hsecond : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST - VT‖
        ≤ C2 * (L_N N R) ^ 2 / R * (1 + ‖s‖) := by
      rw [norm_sub_rev]
      exact hb2'
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    simp only [heRdef]
    linarith only [hfirst, hsecond]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) hev heR0

/-- **The partial-fraction description of the `k`-th derivative of `Λ'/Λ`** (Heath-Brown's
partial fraction expansion): the exact identity as a limit of closed-ball sums, together with
the truncation error at good radii. -/
theorem CompletedDerivPF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) :
    (∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1)))
        Filter.atTop (nhds (iteratedDeriv k (fun z => deriv (DirichletCharacter.completedLFunction χ) z /
            DirichletCharacter.completedLFunction χ z) s))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∃ A₁ : ℝ, ∀ A : ℝ, A₁ ≤ A → ∀ T : ℝ, A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
        (Commons.NumberTheory.Linnik.L_N N A) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 → 8 * ‖s‖ ≤ T →
        ‖iteratedDeriv k (fun z => deriv (DirichletCharacter.completedLFunction χ) z /
              DirichletCharacter.completedLFunction χ z) s
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.closedBall 0 T)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1))‖
          ≤ C * (Commons.NumberTheory.Linnik.L_N N A) ^ 2 / A * (1 + ‖s‖)) :=
  ⟨CompletedDerivPF_identity χ hχ hχprim k hk, CompletedDerivPF_bound χ hχ hχprim k hk⟩

end Work.ZeroFreeTables.P3
