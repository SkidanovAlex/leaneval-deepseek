import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `Work.RHContract.B.h2Minus_unbounded`

ROUTE_LEAD §3.3, step B6: the function `h₂ − h₂′` of `LandauDefs` has a double pole at
`s = ρ − 1` for every zero `ρ` of the completed zeta function in the critical strip, hence is
unbounded in every punctured neighbourhood of `ρ − 1`.

The proof is a pure "order of a meromorphic function" computation:

* `logDeriv ζ` has a simple pole at `ρ` (`meromorphicOrderAt_logDeriv_eq_neg_one`), so
  `A(s) = −(logDeriv ζ)(s+1)/(s+1)` has order `−1` at `s = ρ − 1`;
* the remainder `B(s) = −2^{−s}/s` of `h2Closed` (see the pointwise identity below) is analytic
  there, hence has nonnegative order, so `h2Closed = A + B` has order `−1`;
* differentiating lowers the order by one, so `deriv h2Closed` has order `−2`, and since the two
  orders differ, `h2Minus = h2Closed − deriv h2Closed` has order `min(−1,−2) = −2 < 0`;
* a meromorphic function of negative order tends to infinity along the punctured neighbourhood
  (`tendsto_cobounded_of_meromorphicOrderAt_neg`), which is exactly the claimed unboundedness.
-/

namespace Work.RHContract.B

open Filter
open scoped Topology

lemma ENat_map_cast_ne_zero {n : ℕ∞} (h : n ≠ 0) :
    ENat.map (Nat.cast : ℕ → ℤ) n ≠ (0 : WithTop ℤ) := by
  intro hh
  apply h
  cases n with
  | top => simp at hh
  | coe n =>
    simp only [ENat.map_natCast] at hh
    exact_mod_cast hh

/-- At a zero `ρ ≠ 1` of `riemannZeta₁`, the logarithmic derivative of `riemannZeta` has a simple
pole: its meromorphic order at `ρ` is `−1`. -/
lemma logDeriv_zeta_order (ρ : ℂ) (hρ : riemannZeta₁ ρ = 0) (_hb1 : (1/2:ℝ) < ρ.re)
    (hb2 : ρ.re < 1) :
    meromorphicOrderAt (logDeriv riemannZeta) ρ = -1 := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hb2; norm_num at hb2
  have hAn : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  have hζρ : riemannZeta ρ = 0 := by rw [riemannZeta_eq_inv_sub_mul hρ1, hρ, mul_zero]
  refine meromorphicOrderAt_logDeriv_eq_neg_one hAn.meromorphicAt ?_ ?_
  · rw [hAn.meromorphicOrderAt_eq]
    exact ENat_map_cast_ne_zero ((AnalyticAt.analyticOrderAt_ne_zero hAn).mpr hζρ)
  · intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hζ1 : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta₁ z = 0 := by
      filter_upwards [htop, nhdsWithin_le_nhds (compl_singleton_mem_nhds hρ1)] with z hz hz1
      rw [riemannZeta_eq_inv_sub_mul hz1] at hz
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (sub_ne_zero.mpr hz1))
    have hfull : ∀ᶠ z in 𝓝 ρ, riemannZeta₁ z = 0 := by
      rw [eventually_nhdsWithin_iff] at hζ1
      filter_upwards [hζ1] with z hz
      by_cases hzρ : z = ρ
      · rw [hzρ]; exact hρ
      · exact hz hzρ
    exact Commons.NumberTheory.Zeta.riemannZeta₁_not_eventually_zero ρ hfull

/-- An analytic function that does not vanish at `x` has meromorphic order `0` there. -/
lemma meromorphicOrderAt_of_analytic_ne_zero {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hx : f x ≠ 0) : meromorphicOrderAt f x = 0 := by
  rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hx)]
  simp

/-- At `ρ − 1`, the closed form `h2Closed` of `h₂` has a simple pole: its meromorphic order is
`−1`.  Concretely, on the punctured neighbourhood of `ρ − 1`
`h2Closed = −(logDeriv ζ)(·+1)/(·+1) − 2^{−(·)}/(·)`, the first summand having order `−1` and the
second being analytic there. -/
lemma h2Closed_order (ρ : ℂ) (hρ : riemannZeta₁ ρ = 0)
    (hb1 : (1/2:ℝ) < ρ.re) (hb2 : ρ.re < 1) :
    meromorphicOrderAt Work.RHContract.Landau.h2Closed (ρ - 1) = -1 := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hb2; norm_num at hb2
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hb1; norm_num at hb1
  have hlog := logDeriv_zeta_order ρ hρ hb1 hb2
  set s₀ := ρ - 1 with hs0def
  have hs0ne : s₀ ≠ -1 := by rw [hs0def]; intro h; exact hρ0 (by linear_combination h)
  have hs0ne0 : s₀ ≠ 0 := by rw [hs0def]; intro h; exact hρ1 (by linear_combination h)
  have hs0add : s₀ + 1 = ρ := by rw [hs0def]; ring
  let N : ℂ → ℂ := fun s => -(logDeriv riemannZeta (s + 1))
  let G : ℂ → ℂ := fun s => s + 1
  let A : ℂ → ℂ := fun s => -(logDeriv riemannZeta (s + 1)) / (s + 1)
  let B : ℂ → ℂ := fun s => -(2:ℂ)^(-s) / s
  have hGan : AnalyticAt ℂ G s₀ := by simp only [G]; fun_prop
  have hGval : G s₀ ≠ 0 := by simp only [G]; rw [hs0add]; exact hρ0
  have hG0 : meromorphicOrderAt G s₀ = 0 := meromorphicOrderAt_of_analytic_ne_zero hGan hGval
  have hNord : meromorphicOrderAt N s₀ = -1 := by
    have hcomp : N = (fun w : ℂ => -(logDeriv riemannZeta w)) ∘ (fun s : ℂ => s + 1) := by
      ext s; simp [N]
    rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    rw [hs0add, ← meromorphicOrderAt_fun_neg (f := logDeriv riemannZeta) (x := ρ), hlog]
  have hAmero : MeromorphicAt N s₀ :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hNord]; norm_num)
  have hAord : meromorphicOrderAt A s₀ = -1 := by
    have hdiv : meromorphicOrderAt (N / G) s₀ = meromorphicOrderAt N s₀ - meromorphicOrderAt G s₀ :=
      meromorphicOrderAt_div hAmero hGan.meromorphicAt
    have hAG : A = N / G := by ext s; simp [A, N, G]
    rw [hAG, hdiv, hNord, hG0, sub_zero]
  have hBan : AnalyticAt ℂ B s₀ := by
    have h2 : (2:ℂ) ∈ Complex.slitPlane := by norm_num [Complex.mem_slitPlane_iff]
    simp only [B]
    exact ((AnalyticAt.cpow analyticAt_const (analyticAt_id.neg) h2).neg).div analyticAt_id hs0ne0
  have hlt : meromorphicOrderAt A s₀ < meromorphicOrderAt B s₀ := by
    rw [hAord]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num : (-1:ℤ) < 0))
      (AnalyticAt.meromorphicOrderAt_nonneg hBan)
  have hABord : meromorphicOrderAt (A + B) s₀ = -1 := by
    rw [meromorphicOrderAt_add_eq_left_of_lt hBan.meromorphicAt hlt, hAord]
  have heq : Work.RHContract.Landau.h2Closed =ᶠ[𝓝[≠] s₀] A + B := by
    have h1 : ∀ᶠ s in 𝓝[≠] s₀, s + 1 ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (compl_singleton_mem_nhds hs0ne)] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
      intro h; exact hs (by linear_combination h)
    have h2 : ∀ᶠ s in 𝓝[≠] s₀, s ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (compl_singleton_mem_nhds hs0ne0)] with s hs
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
    filter_upwards [h1, h2] with s hs1 hs0
    have key : Work.RHContract.Landau.h2Closed s =
        -(logDeriv riemannZeta (s + 1)) / (s + 1) + (-(2:ℂ)^(-s) / s) := by
      simp only [Work.RHContract.Landau.h2Closed, logDeriv, Pi.div_apply]
      field_simp
      ring
    simpa [A, B, Pi.add_apply] using key
  rw [hs0def] at hABord heq
  rw [meromorphicOrderAt_congr heq, hABord]

theorem h2Minus_unbounded (ρ : ℂ) (hρ : riemannZeta₁ ρ = 0)
    (hb1 : (1 / 2 : ℝ) < ρ.re) (hb2 : ρ.re < 1) :
    ∀ M : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ s : ℂ, ‖s - (ρ - 1)‖ < ε ∧ M ≤ ‖Work.RHContract.Landau.h2Minus s‖ := by
  have h2ord : meromorphicOrderAt Work.RHContract.Landau.h2Closed (ρ - 1) = -1 :=
    h2Closed_order ρ hρ hb1 hb2
  have hderiv : meromorphicOrderAt (deriv Work.RHContract.Landau.h2Closed) (ρ - 1) = -2 := by
    have h := meromorphicOrderAt_deriv_eq_sub_one (f := Work.RHContract.Landau.h2Closed)
      (x := ρ - 1) (n := -1) (by norm_num) h2ord
    simpa using h
  have hnegderiv : meromorphicOrderAt
      (fun s => -(deriv Work.RHContract.Landau.h2Closed s)) (ρ - 1) = -2 := by
    rw [← meromorphicOrderAt_fun_neg (f := deriv Work.RHContract.Landau.h2Closed) (x := ρ - 1)]
    exact hderiv
  have hmin : meromorphicOrderAt Work.RHContract.Landau.h2Minus (ρ - 1) = -2 := by
    have hmem1 : MeromorphicAt Work.RHContract.Landau.h2Closed (ρ - 1) :=
      meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [h2ord]; norm_num)
    have hmem2 : MeromorphicAt (fun s => -(deriv Work.RHContract.Landau.h2Closed s)) (ρ - 1) :=
      meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hnegderiv]; norm_num)
    have hne : meromorphicOrderAt Work.RHContract.Landau.h2Closed (ρ - 1) ≠
        meromorphicOrderAt (fun s => -(deriv Work.RHContract.Landau.h2Closed s)) (ρ - 1) := by
      rw [h2ord, hnegderiv]; norm_num
    have hsum : meromorphicOrderAt
        (Work.RHContract.Landau.h2Closed + fun s => -(deriv Work.RHContract.Landau.h2Closed s))
        (ρ - 1) = -2 := by
      rw [meromorphicOrderAt_add_of_ne hmem1 hmem2 hne, h2ord, hnegderiv]
      decide
    have hEq : Work.RHContract.Landau.h2Minus =
        (Work.RHContract.Landau.h2Closed +
          fun s => -(deriv Work.RHContract.Landau.h2Closed s)) := by
      ext s; simp [Work.RHContract.Landau.h2Minus, sub_eq_add_neg]
    rw [hEq, hsum]
  have htend : Tendsto Work.RHContract.Landau.h2Minus (𝓝[≠] (ρ - 1)) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg (by rw [hmin]; decide)
  intro M ε hε
  rw [← tendsto_norm_atTop_iff_cobounded] at htend
  have hev1 : ∀ᶠ s in 𝓝[≠] (ρ - 1), M ≤ ‖Work.RHContract.Landau.h2Minus s‖ :=
    htend.eventually_ge_atTop M
  have hev2 : ∀ᶠ s in 𝓝[≠] (ρ - 1), ‖s - (ρ - 1)‖ < ε := by
    have hball : Metric.ball (ρ - 1) ε ∈ 𝓝 (ρ - 1) := Metric.ball_mem_nhds _ hε
    filter_upwards [nhdsWithin_le_nhds hball] with s hs
    rwa [Metric.mem_ball, dist_eq_norm] at hs
  obtain ⟨s, hs1, hs2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hev2 hev1)
  exact ⟨s, hs1, hs2⟩

end Work.RHContract.B
