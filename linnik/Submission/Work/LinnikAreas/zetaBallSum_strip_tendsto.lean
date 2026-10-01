import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.kernelStripInvSqBound
import Submission.Work.LinnikAreas.zetaOrder_eq_xiF
import Submission.Work.LinnikAreas.completedRiemannZeta_orderAt_zero_one
import Submission.Work.LinnikAreas.stripSum_tendsto_of_ballSum_entire
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
import Submission.Commons.NumberTheory.Zeta.xiE_zeroCount

/-!
# From the ball-restricted divisor sum of `Λ = completedRiemannZeta` to the strip zero sum

`zetaBallSum q R` is the sum of the divisor of the completed Riemann zeta function `Λ` over the
ball of radius `R`, against Heath-Brown's tent kernel `tentK (11/2) (3/10) ((1-u) log q)`.

Since `Λ` is meromorphic with *simple poles* at `0` and `1` and no other singularities, its divisor
on a ball of radius `R ≥ 1` is

`div Λ (|u| ≤ R) = Σ_{Λ(u)=0} ord_u(Λ) · δ_u − δ_0 − δ_1`,

so the ball sum differs from the multiplicity-weighted sum over the *zeros* of `Λ` inside the ball
by exactly the two pole terms, which are the values `tentPhi … q 0` and `tentPhi … q 1` of the tent
kernel at the poles.  The zeros of `Λ` (equivalently of the entire completion
`Ξ(s) = 1/2 + (1/2) s (s-1) Λ₀(s)`, which has the same vanishing orders) lie in the *open* critical
strip and are counted by `≪ R log R` in the ball of radius `R`, so the general entire-function
statement `stripSum_tendsto_of_ballSum_entire` (applied to `Ξ`) turns convergence of the ball sums
into convergence of the truncated vertical zero sums.
-/

namespace Work.LinnikAreas

open Complex Filter Metric
open scoped BigOperators Topology

noncomputable section

/-- The tent weight of the ζ-side explicit formula, at `L = 11/2`, `K = 3/10` and scale `q`. -/
private def Phi (q : ℕ) (u : ℂ) : ℂ :=
  Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q u

/-! ## 1. `Λ = completedRiemannZeta` is meromorphic everywhere -/

private lemma meromorphicAt_completedRiemannZeta (x : ℂ) : MeromorphicAt completedRiemannZeta x := by
  set C : ℂ → ℂ := fun s => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ with hC
  have h0 : MeromorphicAt completedRiemannZeta₀ x :=
    (differentiable_completedZeta₀.analyticAt x).meromorphicAt
  have h1 : MeromorphicAt (fun s : ℂ => s⁻¹) x := (MeromorphicAt.id x).inv
  have h2 : MeromorphicAt (fun s : ℂ => (1 - s)⁻¹) x :=
    ((MeromorphicAt.const (1 : ℂ) x).sub (MeromorphicAt.id x)).inv
  have h3 : MeromorphicAt C x := by
    rw [hC]; exact (h0.sub h1).sub h2
  refine h3.congr ?_
  filter_upwards with s
  show completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ = completedRiemannZeta s
  rw [completedRiemannZeta_eq, one_div, one_div]

private lemma meromorphicOn_completedRiemannZeta (U : Set ℂ) : MeromorphicOn completedRiemannZeta U :=
  fun x _ => meromorphicAt_completedRiemannZeta x

/-! ## 2. The vanishing multiplicities of `Λ` and of the entire completion `Ξ = xiC` agree -/

/-- The multiplicity of `u` as a zero of `Λ`, written as the vanishing order of `Ξ`. -/
private lemma mult_xiC_eq (u : ℂ) :
    analyticOrderNatAt xiC u = analyticOrderNatAt completedRiemannZeta u :=
  (show analyticOrderNatAt xiC u
      = analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u from rfl).trans
    (zetaOrder_eq_xiF u).symm

private lemma mult_zeta_zero (u : ℂ) (hu : u = 0 ∨ u = 1) :
    analyticOrderNatAt completedRiemannZeta u = 0 := by
  rcases hu with rfl | rfl
  · rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedZeta_zero]
  · rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedZeta_one]

/-! ## 3. The two pole orders (proved in `completedRiemannZeta_orderAt_zero_one`) -/

private lemma completedRiemannZeta_orderAt_one :
    meromorphicOrderAt completedRiemannZeta (1 : ℂ) = (-1 : ℤ) :=
  completedRiemannZeta_orderAt_zero_one.1

private lemma completedRiemannZeta_orderAt_zero :
    meromorphicOrderAt completedRiemannZeta (0 : ℂ) = (-1 : ℤ) :=
  completedRiemannZeta_orderAt_zero_one.2

/-! ## 4. The divisor of `Λ` on a ball: order off the poles, `-1` at the poles -/

private lemma divisor_completedRiemannZeta_of_ne {R : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) (h0 : u ≠ 0) (h1 : u ≠ 1) :
    MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R) u
      = (analyticOrderNatAt completedRiemannZeta u : ℤ) := by
  rw [MeromorphicOn.divisor_apply (meromorphicOn_completedRiemannZeta _) hu,
    (analyticAt_completedZeta_of_ne u h0 h1).meromorphicOrderAt_eq]
  simp only [analyticOrderNatAt]
  cases h : analyticOrderAt completedRiemannZeta u with
  | top => simp
  | coe n => simp

private lemma divisor_completedRiemannZeta_zero_of_le {R : ℝ} (hR : 1 ≤ R) :
    MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R) (0 : ℂ) = (-1 : ℤ) := by
  have hmem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_zero]
    linarith
  rw [MeromorphicOn.divisor_apply (meromorphicOn_completedRiemannZeta _) hmem,
    completedRiemannZeta_orderAt_zero]
  rfl

private lemma divisor_completedRiemannZeta_one_of_le {R : ℝ} (hR : 1 ≤ R) :
    MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R) (1 : ℂ) = (-1 : ℤ) := by
  have hmem : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_one]
    exact hR
  rw [MeromorphicOn.divisor_apply (meromorphicOn_completedRiemannZeta _) hmem,
    completedRiemannZeta_orderAt_one]
  rfl

/-- The divisor of the entire completion `Ξ` inside a ball is the vanishing order. -/
private lemma divisor_xiC_eq {R : ℝ} {u : ℂ} (hu : u ∈ Metric.closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R) u = (analyticOrderNatAt xiC u : ℤ) :=
  Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (xiC_analyticOn _) hu

/-! ## 5. The zeros of `Ξ` lie in the open critical strip and are counted in balls -/

private lemma xiC_zeros_openStrip {z : ℂ} (hz : xiC z = 0) : 0 < z.re ∧ z.re < 1 := by
  have hz0 : z ≠ 0 := by
    intro h; subst h; exact xiC_zero_ne hz
  have hz1 : z ≠ 1 := by
    intro h; subst h; exact xiC_one_ne hz
  -- `Ξ z = 0` forces `Λ z = 0`
  have hΛ0 : completedRiemannZeta z = 0 := by
    have hG : Commons.NumberTheory.Zeta.xiG_LG z = 0 := by
      rw [Commons.NumberTheory.Zeta.xiG_LG_eq_xiE_LG_of_ne_zero_one hz0 hz1]
      exact hz
    have hhead : (1 / 2 : ℂ) * z * (z - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hz0) (sub_ne_zero.mpr hz1)
    exact (mul_eq_zero.mp hG).resolve_left hhead
  have hlt : z.re < 1 := by
    by_contra h
    have h1 : (1 : ℝ) ≤ z.re := le_of_not_gt h
    have hζ : riemannZeta z = 0 := by
      rw [riemannZeta_def_of_ne_zero hz0]
      simp [hΛ0]
    exact riemannZeta_ne_zero_of_one_le_re h1 hζ
  have hgt : 0 < z.re := by
    by_contra h
    have h1 : z.re ≤ 0 := le_of_not_gt h
    have hw : 1 - z ≠ 0 := by
      intro hh
      apply hz1
      rw [show 1 - z = -(z - 1) by ring] at hh
      rw [neg_eq_zero] at hh
      exact sub_eq_zero.mp hh
    have hΛw : completedRiemannZeta (1 - z) = 0 := by
      rw [completedRiemannZeta_one_sub z]; exact hΛ0
    have hζ : riemannZeta (1 - z) = 0 := by
      rw [riemannZeta_def_of_ne_zero hw]
      simp [hΛw]
    have hre : (1 : ℝ) ≤ (1 - z).re := by
      rw [Complex.sub_re]; norm_num; linarith
    exact riemannZeta_ne_zero_of_one_le_re hre hζ
  exact ⟨hgt, hlt⟩

private lemma xiC_ne_zero : xiC ≠ 0 := fun h => xiC_zero_ne (congrFun h 0)

private lemma xiC_ballCount :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiC (Metric.closedBall 0 R)) u : ℤ) : ℝ))
        ≤ c * R * (Real.log (R + 2) + 2) := by
  obtain ⟨c, hc⟩ := Commons.NumberTheory.Zeta.xiE_zeroCount
  refine ⟨max c 0, le_max_right c 0, fun R hR => ?_⟩
  have h := hc R hR
  have hsame : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiC (Metric.closedBall 0 R)) u : ℤ) : ℝ))
      = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
          (fun z : ℂ => 1 / 2 + 1 / 2 * z * (z - 1) * completedRiemannZeta₀ z)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ)) := rfl
  rw [hsame]
  refine h.trans ?_
  have hR0 : 0 ≤ R := by linarith
  have hX : 0 ≤ Real.log (R + 2) + 2 := by
    have h1 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    linarith
  have hfac : 0 ≤ R * (Real.log (R + 2) + 2) := mul_nonneg hR0 hX
  calc c * R * (Real.log (R + 2) + 2)
      = c * (R * (Real.log (R + 2) + 2)) := by ring
    _ ≤ max c 0 * (R * (Real.log (R + 2) + 2)) :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) hfac
    _ = max c 0 * R * (Real.log (R + 2) + 2) := by ring

/-! ## 6. The `‖u‖⁻²` bound for the tent kernel on the critical strip -/

private lemma tentPhi_bound {q : ℕ} (hq : 2 ≤ q) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ →
      ‖Phi q u‖ ≤ A / ‖u‖ ^ 2 := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  obtain ⟨A, hApos, hA⟩ := kernelStripInvSqBound hlog (11 / 2 : ℝ) (3 / 10 : ℝ)
  refine ⟨A, hApos, fun u hu0 hu1 hu2 => ?_⟩
  have hz : (1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h
      have hu1' : u = 1 := by linear_combination -h
      rw [hu1'] at hu1
      norm_num at hu1
    · exact_mod_cast ne_of_gt hlog
  have hcoe : Phi q u = Work.LinnikContract.Hk (11 / 2) (3 / 10)
      ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)) := by
    rw [Phi, Commons.NumberTheory.Linnik.tentPhi, ← Hk_eq_tentK hz]
  rw [hcoe]
  exact hA u (le_of_lt hu0) (le_of_lt hu1) hu2

/-! ## 7. The pole correction: the ball sum plus the two pole terms is the `Ξ`-ball sum -/

private lemma zetaBallSum_add_poles {q : ℕ} {R : ℝ} (hR : 1 ≤ R) :
    zetaBallSum q R + Phi q 0 + Phi q 1
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u := by
  classical
  have hfinΛ : (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R) u)).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset (f := completedRiemannZeta)
      (meromorphicOn_completedRiemannZeta _) (isCompact_closedBall (0 : ℂ) R) (le_refl _)
  set D : Finset ℂ := hfinΛ.toFinset with hD
  have hDmem : ∀ u : ℂ, u ∈ D ↔ MeromorphicOn.divisor completedRiemannZeta
      (Metric.closedBall (0 : ℂ) R) u ≠ 0 := by
    intro u
    rw [hD, Set.Finite.mem_toFinset, Function.mem_support]
  have hDball : ∀ u ∈ D, u ∈ Metric.closedBall (0 : ℂ) R := by
    intro u hu
    by_contra h
    exact (hDmem u).mp hu (Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem h)
  have hmem0 : (0 : ℂ) ∈ D := by
    rw [hDmem, divisor_completedRiemannZeta_zero_of_le hR]; norm_num
  have hmem1 : (1 : ℂ) ∈ D := by
    rw [hDmem, divisor_completedRiemannZeta_one_of_le hR]; norm_num
  have hpoint : ∀ u ∈ D,
      (((MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u
        = (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * Phi q u
          - (if u = 0 then Phi q 0 else 0) - (if u = 1 then Phi q 1 else 0) := by
    intro u hu
    by_cases h0 : u = 0
    · subst h0
      have hz : MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R) (0 : ℂ)
          = (analyticOrderNatAt xiC 0 : ℤ) := divisor_xiC_eq (by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_zero]; linarith)
      rw [divisor_completedRiemannZeta_zero_of_le hR, hz, mult_xiC_eq 0, mult_zeta_zero 0 (Or.inl rfl)]
      simp
    · by_cases h1 : u = 1
      · subst h1
        have hz : MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R) (1 : ℂ)
            = (analyticOrderNatAt xiC 1 : ℤ) := divisor_xiC_eq (by
              rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_one]; exact hR)
        rw [divisor_completedRiemannZeta_one_of_le hR, hz, mult_xiC_eq 1, mult_zeta_zero 1 (Or.inr rfl)]
        simp
      · rw [divisor_completedRiemannZeta_of_ne (hDball u hu) h0 h1,
          divisor_xiC_eq (hDball u hu), mult_xiC_eq u]
        simp [h0, h1]
  -- the summand with the two indicator terms
  have hif0 : (∑ u ∈ D, (if u = 0 then Phi q 0 else (0 : ℂ))) = Phi q 0 := by
    rw [Finset.sum_ite_eq' D 0 (fun _ => Phi q 0), if_pos hmem0]
  have hif1 : (∑ u ∈ D, (if u = 1 then Phi q 1 else (0 : ℂ))) = Phi q 1 := by
    rw [Finset.sum_ite_eq' D 1 (fun _ => Phi q 1), if_pos hmem1]
  have hsumD : (∑ u ∈ D,
        (((MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u)
      = (∑ u ∈ D, (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u) - Phi q 0 - Phi q 1 := by
    rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hif0, hif1]
  -- the `Λ`-finsum as a sum over `D`
  have hzb : zetaBallSum q R = ∑ u ∈ D,
      (((MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
        * Phi q u := by
    have hsupp : (Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u)) ⊆ ↑D := by
      intro u hu
      rw [Finset.mem_coe, hDmem]
      intro h0
      exact (Function.mem_support.mp hu) (by rw [h0]; simp)
    rw [show zetaBallSum q R = ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u from by
      simp only [zetaBallSum, Phi, Commons.NumberTheory.Linnik.tentPhi]]
    exact finsum_eq_sum_of_support_subset _ hsupp
  -- the `Ξ`-finsum as a sum over `D`
  have hsuppΞ : (Function.support (fun u : ℂ =>
      (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * Phi q u)) ⊆ ↑D := by
    intro u hu
    rw [Finset.mem_coe, hDmem]
    have hdu : MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R) u ≠ 0 := by
      intro h0; exact (Function.mem_support.mp hu) (by rw [h0]; simp)
    have hball : u ∈ Metric.closedBall (0 : ℂ) R := by
      by_contra h
      exact hdu (Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem h)
    have hmult : analyticOrderNatAt xiC u ≠ 0 := by
      intro h0
      exact hdu (by rw [divisor_xiC_eq hball, h0]; simp)
    have hmultΛ : analyticOrderNatAt completedRiemannZeta u ≠ 0 := by
      rwa [← mult_xiC_eq u]
    have hne : u ≠ 0 ∧ u ≠ 1 := by
      constructor <;> intro h
      · exact hmultΛ (mult_zeta_zero u (Or.inl h))
      · exact hmultΛ (mult_zeta_zero u (Or.inr h))
    rw [divisor_completedRiemannZeta_of_ne hball hne.1 hne.2]
    exact_mod_cast hmultΛ
  have hfinsumΞ : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * Phi q u)
      = ∑ u ∈ D, (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ)
          * Phi q u := finsum_eq_sum_of_support_subset _ hsuppΞ
  rw [hzb, hsumD, hfinsumΞ]
  ring

/-! ## 8. The main theorem -/

theorem zetaBallSum_strip_tendsto {q : ℕ} (hq : 2 ≤ q) {Z : ℂ}
    (hZ : Filter.Tendsto (fun ρ : ℝ => Work.LinnikAreas.zetaBallSum q ρ) Filter.atTop (nhds Z)) :
    Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℂ) *
          Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q u else 0)) Filter.atTop
      (nhds (Z + Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q 1
        + Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q 0)) := by
  obtain ⟨A, hApos, hA⟩ := tentPhi_bound (q := q) hq
  obtain ⟨c, hc0, hcount⟩ := xiC_ballCount
  -- Step 1: transfer the hypothesis `hZ` to the ball sums of the entire completion `Ξ`.
  have hZΞ : Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor xiC (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * Phi q u)
      Filter.atTop (nhds (Z + Phi q 0 + Phi q 1)) := by
    have h1 : Filter.Tendsto (fun R : ℝ => (zetaBallSum q R + Phi q 0) + Phi q 1)
        Filter.atTop (nhds ((Z + Phi q 0) + Phi q 1)) :=
      (hZ.add_const (Phi q 0)).add_const (Phi q 1)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact zetaBallSum_add_poles (q := q) hR
  -- Step 2: the general entire-function strip-sum theorem, applied to `Ξ`.
  have key := stripSum_tendsto_of_ballSum_entire (f := xiC) xiC_diff xiC_ne_zero
    (fun u hu => xiC_zeros_openStrip hu) hc0 hcount hApos hA hZΞ
  -- Step 3: rewrite the vanishing multiplicities of `Ξ` as those of `Λ` and reorder the poles.
  have hfun : (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        ((analyticOrderNatAt xiC u : ℕ) : ℂ) * Phi q u else 0))
      = fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℂ) * Phi q u else 0) := by
    funext T
    refine finsum_congr (fun u => ?_)
    by_cases h : |u.im| < T
    · rw [if_pos h, if_pos h, ← mult_xiC_eq u]
    · rw [if_neg h, if_neg h]
  rw [hfun] at key
  rw [show Z + Phi q 0 + Phi q 1 = Z + Phi q 1 + Phi q 0 from by ring] at key
  simpa only [Phi] using key

end

end Work.LinnikAreas
