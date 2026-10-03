import Mathlib
import Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq

noncomputable section
open Complex Filter Metric Set
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

/-! # `xi_logDeriv_re_lower_general`

Deep classical core: the real part of the logarithmic derivative of the completed
zeta function `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)` — which agrees with the naive
product `(1/2)·s·(s−1)·Λ(s)` away from `s = 0, 1` — is uniformly bounded below on
the half-plane `Re s > 1`.

**Route.** (1) `Ξ` is entire (`differentiable_completedZeta₀`), with `Ξ(0) = 1/2 ≠ 0`.
(2) All zeros of `Ξ` lie in the critical strip `0 ≤ Re ρ ≤ 1`
(`xi_zeros_strip_LG`, via `riemannZeta_ne_zero_of_one_le_re` and the functional
equation `completedRiemannZeta_one_sub`).  (3) The Hadamard partial fraction of the
genus-one entire function `Ξ` (`Commons.NumberTheory.Zeta.xiE_partialFraction_eq`,
mirroring `Commons.NumberTheory.Linnik.partialFraction_eq`) gives

    logDeriv Ξ s - logDeriv Ξ 0 = lim_{R→∞} Σ_{u ∈ zeros of Ξ, |u| ≤ R}
        ord(u)·(1/(s−u) + 1/u)

whose real part is a limit of nonnegative terms: with `ρ = β + iγ` in the ball,
`0 ≤ β ≤ 1` and `1 < σ = Re s` give
`Re(1/(s−ρ)) = (σ−β)/|s−ρ|² ≥ 0` and `Re(1/ρ) = β/|ρ|² ≥ 0`.
Hence `Re(logDeriv Ξ s) ≥ Re(logDeriv Ξ 0)` on `Re s > 1`, i.e. the lower bound
`-C` with `C = ‖logDeriv Ξ 0‖ + 1`.  (4) Since `(1/2)s(s−1)Λ(s) = Ξ(s)` off
`{0,1}`, the same bound holds for the function in the statement on `Re s > 1`.
-/

/-- the entire completion Ξ(s) = 1/2 + (1/2)·s·(s-1)·Λ₀(s) -/
def xiE_LG (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

/-- g(s) = (1/2)s(s-1)Λ(s), the naive product (differs from xiE_LG at 0 and 1 only) -/
def xiG_LG (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

lemma xiG_LG_eq_xiE_LG_of_ne_zero_one {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    xiG_LG z = xiE_LG z := by
  unfold xiG_LG xiE_LG
  have hΛ := completedRiemannZeta_eq z
  have hz1m : 1 - z ≠ 0 := by
    intro h
    apply hz1
    rw [show 1 - z = -(z - 1) by ring] at h
    rw [neg_eq_zero] at h
    exact sub_eq_zero.mp h
  calc
    (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z
        = (1 / 2 : ℂ) * z * (z - 1) * (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) := by
            rw [hΛ]
    _ = (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z := by
            field_simp [hz0, hz1m]
            ring

lemma differentiable_xiE_LG : Differentiable ℂ xiE_LG := by
  unfold xiE_LG
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hhead : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  have hc : Differentiable ℂ (fun _ : ℂ => (1 / 2 : ℂ)) := (differentiable_const (1 / 2 : ℂ))
  exact hc.add (hhead.mul hΛ)

lemma xiE_LG_zero : xiE_LG 0 = (1 / 2 : ℂ) := by
  unfold xiE_LG
  simp

lemma xiE_LG_one : xiE_LG 1 = (1 / 2 : ℂ) := by
  unfold xiE_LG
  simp

lemma xiE_LG_one_sub (s : ℂ) : xiE_LG (1 - s) = xiE_LG s := by
  unfold xiE_LG
  have hFE := completedRiemannZeta₀_one_sub s
  calc
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * completedRiemannZeta₀ (1 - s)
        = (1 / 2 : ℂ) + (1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * completedRiemannZeta₀ s := by
            rw [hFE]
    _ = (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s := by ring

lemma xiE_LG_ne_zero_aux {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : xiE_LG z = 0) :
    0 ≤ z.re ∧ z.re ≤ 1 := by
  have hΛ0 : completedRiemannZeta z = 0 := by
    have hG : xiG_LG z = 0 := by
      rw [xiG_LG_eq_xiE_LG_of_ne_zero_one hz0 hz1]
      exact hz
    have hhead : (1 / 2 : ℂ) * z * (z - 1) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact hz0
      · exact sub_ne_zero.mpr hz1
    exact (mul_eq_zero.mp hG).resolve_left hhead
  have hzle : z.re ≤ 1 := by
    by_contra h1
    have h1' : (1 : ℝ) < z.re := lt_of_not_ge h1
    have hzζ : riemannZeta z = 0 := by
      rw [riemannZeta_def_of_ne_zero hz0]
      simp [hΛ0]
    exact riemannZeta_ne_zero_of_one_lt_re h1' hzζ
  have hzge : (0 : ℝ) ≤ z.re := by
    by_contra h0
    have hw : 1 - z ≠ 0 := by
      intro h
      apply hz1
      rw [show 1 - z = -(z - 1) by ring] at h
      rw [neg_eq_zero] at h
      exact sub_eq_zero.mp h
    have hΛw : completedRiemannZeta (1 - z) = 0 := by
      rw [completedRiemannZeta_one_sub z]
      exact hΛ0
    have hwζ : riemannZeta (1 - z) = 0 := by
      rw [riemannZeta_def_of_ne_zero hw]
      simp [hΛw]
    have hwre : (1 : ℝ) ≤ (1 - z).re := by
      rw [Complex.sub_re]
      norm_num
      linarith [lt_of_not_ge h0]
    exact riemannZeta_ne_zero_of_one_le_re (s := (1 - z)) hwre hwζ
  exact ⟨hzge, hzle⟩

/-- Zeros of the entire completion lie in the critical strip `0 ≤ ρ.re ≤ 1`. -/
lemma xiE_LG_zeros_strip {ρ : ℂ} (hρ : xiE_LG ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  by_cases hρ0 : ρ = 0
  · subst ρ
    simp [xiE_LG_zero] at hρ
  by_cases hρ1 : ρ = 1
  · subst ρ
    simp [xiE_LG_one] at hρ
  · exact xiE_LG_ne_zero_aux hρ0 hρ1 hρ

lemma xiE_LG_analyticOnNhd (U : Set ℂ) : AnalyticOnNhd ℂ xiE_LG U := by
  intro z _
  exact differentiable_xiE_LG.analyticAt z

lemma divisor_xiE_LG_nonneg (U : Set ℂ) (u : ℂ) :
    0 ≤ (MeromorphicOn.divisor xiE_LG U) u := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (xiE_LG_analyticOnNhd U) u

lemma xiE_LG_zero_of_divisor_ne_zero {R : ℝ} {u : ℂ}
    (hd : MeromorphicOn.divisor xiE_LG (Metric.closedBall 0 R) u ≠ 0) : xiE_LG u = 0 := by
  exact Commons.Analysis.Complex.zero_of_divisor_ne_zero (f := xiE_LG) (a := (0:ℂ)) (ρ := R)
    (xiE_LG_analyticOnNhd (Metric.closedBall 0 R)) hd

lemma one_div_re_normSq_LG (z : ℂ) (hz : z ≠ 0) :
    (1 / z).re = z.re / Complex.normSq z := by
  calc
    (1 / z).re = (z⁻¹).re := by simp [one_div]
    _ = z.re / Complex.normSq z := by
      rw [Complex.inv_def]
      rw [Complex.mul_re]
      simp
      ring

lemma re_sub_inv_nonneg_of_re_le_LG {s u : ℂ} (hs : s ≠ u) (hu : u.re ≤ s.re) :
    0 ≤ (1 / (s - u)).re := by
  have hsu' : s - u ≠ 0 := sub_ne_zero.mpr hs
  rw [one_div_re_normSq_LG (s - u) hsu']
  have hns : 0 < Complex.normSq (s - u) := by
    rw [Complex.normSq_eq_norm_sq]
    positivity
  have hnum : 0 ≤ (s - u).re := by
    rw [Complex.sub_re]
    exact sub_nonneg.mpr hu
  exact div_nonneg hnum (le_of_lt hns)

lemma re_inv_nonneg_of_re_nonneg_LG {u : ℂ} (hu0 : u ≠ 0) (hu : 0 ≤ u.re) : 0 ≤ (1 / u).re := by
  rw [one_div_re_normSq_LG u hu0]
  have hns : 0 < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    positivity
  exact div_nonneg hu (le_of_lt hns)

lemma pf_term_re_nonneg_LG {s u : ℂ} (hs : (1 : ℝ) < s.re)
    (hz : xiE_LG u = 0) (hu_ne_s : s ≠ u) : 0 ≤ ((1 / (s - u) + 1 / u)).re := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    have : xiE_LG 0 = 0 := hz
    rw [xiE_LG_zero] at this
    norm_num at this
  rcases xiE_LG_zeros_strip hz with ⟨huβ0, huβ1⟩
  have hle : u.re ≤ s.re := le_trans huβ1 (le_of_lt hs)
  have h1 : 0 ≤ (1 / (s - u)).re := re_sub_inv_nonneg_of_re_le_LG hu_ne_s hle
  have h2 : 0 ≤ (1 / u).re := re_inv_nonneg_of_re_nonneg_LG hu0 huβ0
  rw [Complex.add_re]
  linarith

private lemma re_finset_sum_LG (A : Finset ℂ) (f : ℂ → ℂ) :
    (∑ u ∈ A, f u).re = ∑ u ∈ A, (f u).re := by
  classical
  refine Finset.induction_on A ?base ?step
  · simp
  · intro a A' ha ih
    rw [Finset.sum_insert ha]
    rw [Complex.add_re]
    rw [Finset.sum_insert ha]
    rw [ih]

lemma xiE_LG_pf_re_nonneg {s : ℂ} (hs : (1 : ℝ) < s.re) (R : ℝ) :
    0 ≤ ((∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor xiE_LG (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))).re := by
  classical
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor xiE_LG (Metric.closedBall 0 R) u
  have hsupp : (Function.support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := xiE_LG)
      (U := Metric.closedBall 0 R) (V := Metric.closedBall 0 R)
      (xiE_LG_analyticOnNhd (Metric.closedBall 0 R)).meromorphicOn (isCompact_closedBall 0 R)
      (by intro z hz; exact hz)
  let S : Finset ℂ := hsupp.toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    simpa [S] using hsupp.mem_toFinset
  have hsub : Function.support (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    exact (hS_mem u).mpr (by
      intro hd0
      apply hu
      simp [d, hd0])
  have hsum_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) =
      ∑ u ∈ S, (((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) := by
    exact finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) hsub
  rw [hsum_eq]
  rw [re_finset_sum_LG]
  apply Finset.sum_nonneg
  intro u huS
  have hdu : d u ≠ 0 := (hS_mem u).mp huS
  have hz : xiE_LG u = 0 := xiE_LG_zero_of_divisor_ne_zero (by simpa [d] using hdu)
  have hd_nonneg_int : 0 ≤ d u := divisor_xiE_LG_nonneg (Metric.closedBall 0 R) u
  have hterm : 0 ≤ (1 / (s - u) + 1 / u).re := pf_term_re_nonneg_LG (s := s) (u := u) hs hz (by
    intro hsu
    rcases xiE_LG_zeros_strip hz with ⟨_, huβ1⟩
    have : u.re ≤ s.re := le_trans huβ1 (le_of_lt hs)
    have hse : s.re = u.re := congrArg Complex.re hsu
    linarith)
  have hdR : 0 ≤ ((d u : ℤ) : ℝ) := by exact_mod_cast hd_nonneg_int
  have htermR : 0 ≤ (((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)).re := by
    rw [Complex.mul_re]
    have hdre : (((d u : ℤ) : ℂ).re) = ((d u : ℤ) : ℝ) := by simp
    have hdim : (((d u : ℤ) : ℂ).im) = 0 := by simp
    rw [hdre, hdim]
    rw [zero_mul]
    rw [sub_zero]
    exact mul_nonneg hdR hterm
  exact htermR

lemma xiE_LG_ne_zero_of_one_lt_re {s : ℂ} (hs : (1 : ℝ) < s.re) : xiE_LG s ≠ 0 := by
  intro h0
  rcases xiE_LG_zeros_strip h0 with ⟨hb0, hb1⟩
  linarith

lemma re_logDeriv_xiE_LG_lower {s : ℂ} (hs : (1 : ℝ) < s.re) :
    (logDeriv xiE_LG 0).re ≤ (logDeriv xiE_LG s).re := by
  have hξs : xiE_LG s ≠ 0 := xiE_LG_ne_zero_of_one_lt_re hs
  have hPF := xiE_partialFraction_eq s (by simpa [xiE_LG] using hξs)
  let G : ℝ → ℝ := fun R =>
      ((∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor xiE_LG (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))).re
  have hGL : Tendsto G atTop (𝓝 ((logDeriv xiE_LG s - logDeriv xiE_LG 0).re)) := by
    dsimp [G]
    have ht := (Complex.continuous_re.tendsto (logDeriv xiE_LG s - logDeriv xiE_LG 0))
    exact Filter.Tendsto.comp ht hPF
  have hGnonneg : ∀ R : ℝ, 0 ≤ G R := by
    intro R
    dsimp [G]
    exact xiE_LG_pf_re_nonneg (s := s) hs R
  have hL0 : 0 ≤ (logDeriv xiE_LG s - logDeriv xiE_LG 0).re := by
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    exact hclosed.mem_of_tendsto hGL (Filter.Eventually.of_forall (fun R => mem_Ici.mpr (hGnonneg R)))
  rw [Complex.sub_re] at hL0
  linarith

lemma xiE_LG_eventuallyEq_xiG_LG_of_one_lt_re (s : ℂ) (hs : (1 : ℝ) < s.re) :
    (fun z : ℂ => xiE_LG z) =ᶠ[𝓝 s] (fun z : ℂ => xiG_LG z) := by
  have hopen : IsOpen {z : ℂ | (1 : ℝ) < z.re} := by
    simpa [Set.preimage, Set.mem_Ioi] using (isOpen_Ioi.preimage Complex.continuous_re)
  refine eventually_of_mem (IsOpen.mem_nhds hopen hs) ?_
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hz
  symm
  exact xiG_LG_eq_xiE_LG_of_ne_zero_one (z := z) hz0 hz1

lemma logDeriv_xiG_LG_eq_logDeriv_xiE_LG_of_one_lt_re (s : ℂ) (hs : (1 : ℝ) < s.re) :
    logDeriv xiG_LG s = logDeriv xiE_LG s := by
  have hE := xiE_LG_eventuallyEq_xiG_LG_of_one_lt_re s hs
  have hlg := logDeriv_congr_nhds hE
  exact (hlg.eq_of_nhds).symm

lemma re_logDeriv_xiG_LG_lower {s : ℂ} (hs : (1 : ℝ) < s.re) :
    (logDeriv xiE_LG 0).re ≤ (logDeriv xiG_LG s).re := by
  rw [logDeriv_xiG_LG_eq_logDeriv_xiE_LG_of_one_lt_re s hs]
  exact re_logDeriv_xiE_LG_lower hs

/--
Deep classical core.  Let `xi(s) := (1/2)*s*(s-1)*completedRiemannZeta s` (Riemann xi function).
Claim: the real part of `logDeriv xi s` is uniformly bounded below on the half-plane `Re s > 1`.
-/
theorem xi_logDeriv_re_lower_general :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re →
      -C ≤ (logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z) s).re := by
  let B : ℂ := logDeriv xiE_LG 0
  let C : ℝ := ‖B‖ + 1
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro s hs
  have hlb := re_logDeriv_xiG_LG_lower (s := s) hs
  have hreB : B.re ≤ (logDeriv xiG_LG s).re := by
    simpa [B] using hlb
  have hn : -‖B‖ ≤ B.re := by
    have h1 := Complex.abs_re_le_norm B
    have hA : -B.re ≤ |B.re| := by simpa using (le_abs_self (-B.re))
    have hAB : -B.re ≤ ‖B‖ := le_trans hA h1
    exact neg_le.mp hAB
  have hCb : -C ≤ B.re := by
    dsimp [C]
    linarith
  have hgoal : -C ≤ (logDeriv xiG_LG s).re := by linarith
  exact hgoal

end Commons.NumberTheory.Zeta
