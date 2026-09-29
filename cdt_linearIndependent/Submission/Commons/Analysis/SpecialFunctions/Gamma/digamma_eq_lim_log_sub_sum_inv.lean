import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Submission.Commons.Analysis.SpecialFunctions.Gamma.GammaSeq_tendstoUniformlyOn_closedBall

noncomputable section

open Complex Filter Set MeasureTheory Metric
open scoped Real Topology BigOperators Interval

namespace Commons.Analysis.SpecialFunctions.Gamma

/-! # `digamma s = lim (log (N+1) - ∑_{k=0}^{N} 1/(s+k))` for `0 < Re s`

We prove the classical Gauss limit formula for the complex digamma function.  The proof runs as
follows.

1. `GammaSeq_differentiableOn`: each Euler-product partial product `Γ_N(z)` is holomorphic
   on the right half-plane.
2. `GammaSeq_tendstoUniformlyOn_closedBall`: the Euler products `Γ_N` converge to `Γ`
   uniformly on balls inside the right half-plane (Euler's integral + dominated convergence,
   proved in the separate commons module `GammaSeq_tendstoUniformlyOn_closedBall`).
3. `digamma_tendsto_GammaSeq_logDeriv`: by Mathlib's locally-uniform-derivative machinery
   (`Complex.logDeriv_tendsto`), `logDeriv (z ↦ Γ_N(z)) s → logDeriv Γ s = digamma s`.
4. `logDeriv_GammaSeq_eq`: an explicit computation gives
   `logDeriv (z ↦ Γ_N(z)) s = log N - ∑_{k=0}^{N} (s+k)^{-1}`.
5. `digamma_eq_lim_log_sub_sum_inv`: the target statement follows since
   `log(N+1) = log N + o(1)`.
-/

section LogDerivAlgebra

/-- `logDeriv` of `z ↦ z + c`. -/
lemma logDeriv_id_add_const (c s : ℂ) : logDeriv (fun z : ℂ => z + c) s = (s + c)⁻¹ := by
  rw [logDeriv_apply]
  have hd : HasDerivAt (fun z : ℂ => z + c) 1 s := by
    simpa [add_comm] using (hasDerivAt_id s).add_const c
  rw [hd.deriv]
  ring

/-- `logDeriv` of `z ↦ c^z` for `c ∈ slitPlane`. -/
lemma logDeriv_const_cpow {c : ℂ} (hc : c ∈ Complex.slitPlane) (s : ℂ) :
    logDeriv (fun z : ℂ => c ^ z) s = Complex.log c := by
  rw [logDeriv_apply]
  have hc0 : c ≠ 0 := Complex.slitPlane_ne_zero hc
  have hd : HasDerivAt (fun z : ℂ => c ^ z) (c ^ s * Complex.log c) s := by
    exact (hasStrictDerivAt_const_cpow (x := c) (y := s) (Or.inl hc0)).hasDerivAt
  rw [hd.deriv]
  have hcs : c ^ s ≠ 0 := (Complex.cpow_ne_zero_iff.mpr (Or.inl hc0))
  field_simp [hcs]

/-- `z + j ≠ 0` for `0 < z.re`. -/
lemma complex_add_nat_ne_zero_of_re_pos {z : ℂ} {j : ℕ} (hz : 0 < z.re) : z + (j : ℂ) ≠ 0 := by
  intro h
  have hre : (z + (j : ℂ)).re = 0 := congrArg Complex.re h
  have : 0 < (z + (j : ℂ)).re := by
    rw [Complex.add_re]
    have hj0 : 0 ≤ ((j : ℂ).re) := by
      have : ((j : ℂ).re) = (j : ℝ) := by simp
      rw [this]
      exact_mod_cast (Nat.zero_le j)
    linarith
  linarith

/-- Differentiability of a pointwise finite product `z ↦ ∏ (z + k)`. -/
lemma den_differentiableAt (z : ℂ) (n : ℕ) :
    DifferentiableAt ℂ (fun w : ℂ => ∏ k ∈ Finset.range (n + 1), (w + (k : ℂ))) z := by
  have hF : DifferentiableAt ℂ (∏ k ∈ Finset.range (n + 1), (fun w : ℂ => w + (k : ℂ))) z := by
    exact DifferentiableAt.finset_prod (𝕜 := ℂ) (x := z) (u := Finset.range (n + 1))
      (f := fun (k : ℕ) (w : ℂ) => w + (k : ℂ))
      (fun k hk => (differentiableAt_id.add_const (k : ℂ)))
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards with w
  simp [Finset.prod_apply]

/-- Each Euler partial product is holomorphic on the right half-plane. -/
lemma GammaSeq_differentiableOn (n : ℕ) (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => Complex.GammaSeq z n) {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hpow : DifferentiableOn ℂ (fun z : ℂ => (n : ℂ) ^ z) U := by
    haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn⟩
    exact (differentiable_const_cpow_of_neZero (n : ℂ)).differentiableOn
  have hnum : DifferentiableOn ℂ (fun z : ℂ => (n : ℂ) ^ z * (n.factorial : ℂ)) U := by
    exact hpow.mul (differentiableOn_const (n.factorial : ℂ))
  have hden : DifferentiableOn ℂ (fun z : ℂ => ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) U := by
    intro z hz
    exact (den_differentiableAt z n).differentiableWithinAt
  have hden0 : ∀ z ∈ U, (∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) ≠ 0 := by
    intro z hz
    exact Finset.prod_ne_zero_iff.mpr (fun k hk => complex_add_nat_ne_zero_of_re_pos (j := k) hz)
  have hdiv : DifferentiableOn ℂ (fun z : ℂ =>
      ((n : ℂ) ^ z * (n.factorial : ℂ)) / (∏ k ∈ Finset.range (n + 1), (z + (k : ℂ)))) U :=
    hnum.div hden hden0
  simpa [Complex.GammaSeq] using hdiv

/-- Explicit logarithmic derivative of the Euler partial product:
`logDeriv (z ↦ Γ_N z) s = log N - ∑_{k=0}^{N} (s+k)⁻¹` for `0 < Re s` and `N ≠ 0`. -/
lemma logDeriv_GammaSeq_eq (s : ℂ) (n : ℕ) (hs : 0 < s.re) (hn : n ≠ 0) :
    logDeriv (fun z : ℂ => Complex.GammaSeq z n) s =
      (Real.log (n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), ((s + (k : ℂ))⁻¹) := by
  have hs_k : ∀ k : ℕ, s ≠ - (k : ℂ) := by
    intro k hk
    have : s.re ≤ 0 := by
      rw [hk]
      simp
    linarith
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  haveI : NeZero (n : ℂ) := ⟨hn0⟩
  have hn_slit : (n : ℂ) ∈ Complex.slitPlane := by
    exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (Nat.pos_of_ne_zero hn))
  let A : ℂ → ℂ := fun z => (n : ℂ) ^ z * (n.factorial : ℂ)
  let B : ℂ → ℂ := fun z => ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))
  have hdef : (fun z : ℂ => Complex.GammaSeq z n) = fun z => A z / B z := by
    funext z
    simp [Complex.GammaSeq, A, B]
  have hA0 : A s ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))
      (by exact_mod_cast (Nat.factorial_ne_zero n))
  have hBfac : ∀ k ∈ Finset.range (n + 1), (s + (k : ℂ)) ≠ 0 := by
    intro k hk h
    apply hs_k k
    exact (eq_neg_iff_add_eq_zero.mpr h)
  have hB0 : B s ≠ 0 := by
    dsimp [B]
    exact Finset.prod_ne_zero_iff.mpr hBfac
  have hdA : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact (differentiableAt_const_cpow_of_neZero (n : ℂ) s).mul (differentiableAt_const _)
  have hdB : DifferentiableAt ℂ B s := by
    dsimp [B]
    exact den_differentiableAt s n
  have hldB : logDeriv B s = ∑ k ∈ Finset.range (n + 1), ((s + (k : ℂ))⁻¹) := by
    calc logDeriv B s
        = ∑ k ∈ Finset.range (n + 1), logDeriv (fun z : ℂ => z + (k : ℂ)) s := by
            dsimp [B]
            rw [logDeriv_fun_prod (x := s) (f := fun (k : ℕ) (z : ℂ) => z + (k : ℂ))]
            · intro k hk
              exact hBfac k hk
            · intro k hk
              exact (differentiableAt_id.add_const (k : ℂ))
      _ = ∑ k ∈ Finset.range (n + 1), ((s + (k : ℂ))⁻¹) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact logDeriv_id_add_const (k : ℂ) s
  calc
    logDeriv (fun z : ℂ => Complex.GammaSeq z n) s
        = logDeriv (fun z => A z / B z) s := by rw [hdef]
    _ = logDeriv A s - logDeriv B s := by
        exact logDeriv_div s hA0 hB0 hdA hdB
    _ = logDeriv (fun z : ℂ => (n : ℂ) ^ z) s - logDeriv B s := by
        congr 1
        dsimp [A]
        exact logDeriv_mul_const s (n.factorial : ℂ) (by exact_mod_cast (Nat.factorial_ne_zero n))
    _ = Complex.log (n : ℂ) - logDeriv B s := by
        congr 1
        exact logDeriv_const_cpow hn_slit s
    _ = (Real.log (n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), ((s + (k : ℂ))⁻¹) := by
        rw [hldB]
        congr 1
        exact (Complex.ofReal_log (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (Nat.zero_le n))).symm

end LogDerivAlgebra

section EulerLimitUniform

/-- `log (N+1) - log N → 0`. -/
lemma tendsto_log_succ_sub_log :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun N => Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := f) (g := fun _ : ℕ => (0 : ℝ)) (h := fun N : ℕ => (N : ℝ)⁻¹)
    ?_ ?_ ?_ ?_
  · exact tendsto_const_nhds
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp [f]
    have hlogmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
      apply Real.log_le_log (by exact_mod_cast hN)
      linarith
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp [f]
    have hpos1 : 0 < (N : ℝ) := by exact_mod_cast hN
    have hpos2 : 0 < (N : ℝ) + 1 := by linarith
    have hid : Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) =
        Real.log (((N : ℝ) + 1) / (N : ℝ)) := by
      rw [← Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
    rw [hid]
    have hratio : ((N : ℝ) + 1) / (N : ℝ) = 1 + (N : ℝ)⁻¹ := by
      field_simp
    rw [hratio]
    have hx0 : 0 < 1 + (N : ℝ)⁻¹ := by positivity
    simpa using (Real.log_le_sub_one_of_pos hx0)

/-- `0 < z.re` for `z` in an open ball centred at `a` with `0 < a.re - r`. -/
lemma re_pos_of_mem_ball {a : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ Metric.ball a r)
    (hr : 0 < a.re - r) : 0 < z.re := by
  have hdist : dist z a < r := by simpa [dist_comm] using (mem_ball.mp hz)
  have hAbs : |z.re - a.re| ≤ ‖z - a‖ := by
    have := Complex.abs_re_le_norm (z - a)
    simpa [Complex.sub_re] using this
  have hle : -(‖z - a‖) ≤ z.re - a.re := (abs_le.mp hAbs).1
  have hlo : a.re - ‖z - a‖ ≤ z.re := by linarith
  have h2 : ‖z - a‖ < r := by simpa [dist_eq_norm] using hdist
  have hmid : a.re - r < a.re - ‖z - a‖ := by linarith
  linarith

end EulerLimitUniform

section MainProof

/-- `logDeriv (z ↦ Γ_N(z)) s → digamma s` for `0 < Re s`. -/
lemma digamma_tendsto_GammaSeq_logDeriv (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => logDeriv (fun z : ℂ => Complex.GammaSeq z N) s) atTop
      (𝓝 (Complex.digamma s)) := by
  let r : ℝ := s.re / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hsr : 0 < s.re - r := by dsimp [r]; linarith
  have hunif : TendstoUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      (closedBall s r) := GammaSeq_tendstoUniformlyOn_closedBall s r hr hsr
  have hloc : TendstoLocallyUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      (Metric.ball s r) :=
    (hunif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff : ∀ᶠ N : ℕ in atTop, DifferentiableOn ℂ (fun z : ℂ => Complex.GammaSeq z N)
      (Metric.ball s r) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    exact (GammaSeq_differentiableOn N hN0).mono (fun z hz => re_pos_of_mem_ball hz hsr)
  have hmem : s ∈ Metric.ball s r := by
    simp only [mem_ball, dist_self]
    exact hr
  have hg0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hres : Tendsto (fun N : ℕ => logDeriv (fun z : ℂ => Complex.GammaSeq z N) s) atTop
      (𝓝 (logDeriv Complex.Gamma s)) :=
    Complex.logDeriv_tendsto Metric.isOpen_ball hmem hloc hdiff hg0
  simpa [Complex.digamma] using hres

/-- Gauss' limit formula for the complex digamma function:
`digamma s = lim (log (N+1) - ∑_{k=0}^{N} 1/(s+k))` for `0 < Re s`. -/
theorem digamma_eq_lim_log_sub_sum_inv (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ((Real.log ((N : ℝ) + 1) : ℂ) -
      ∑ k ∈ Finset.range (N + 1), ((s + (k : ℂ))⁻¹))) atTop (𝓝 (Complex.digamma s)) := by
  have hc : Tendsto (fun N : ℕ => logDeriv (fun z : ℂ => Complex.GammaSeq z N) s) atTop
      (𝓝 (Complex.digamma s)) := digamma_tendsto_GammaSeq_logDeriv s hs
  have hc' : Tendsto (fun N : ℕ => (Real.log (N : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (N + 1), ((s + (k : ℂ))⁻¹)) atTop (𝓝 (Complex.digamma s)) := by
    refine hc.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    exact logDeriv_GammaSeq_eq s N hs hN0
  have hδr : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_log_succ_sub_log
  have hδc : Tendsto
      (ofReal ∘ (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto (0 : ℝ)).comp hδr
  have hδ : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) - (Real.log (N : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine hδc.congr' (Eventually.of_forall (fun N => by
      simp [Complex.ofReal_sub]))
  have hsum : Tendsto (fun N : ℕ =>
      ((Real.log (N : ℝ) : ℂ) - ∑ k ∈ Finset.range (N + 1), ((s + (k : ℂ))⁻¹))
      + ((Real.log ((N : ℝ) + 1) : ℂ) - (Real.log (N : ℝ) : ℂ))) atTop (𝓝 (Complex.digamma s)) := by
    simpa using hc'.add hδ
  refine hsum.congr' (Eventually.of_forall (fun N => by
    ring))

end MainProof

end Commons.Analysis.SpecialFunctions.Gamma