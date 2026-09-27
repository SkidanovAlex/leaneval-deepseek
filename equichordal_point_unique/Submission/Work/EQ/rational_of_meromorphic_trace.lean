import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.polynomial_of_analyticOn_compl_finset
import Submission.Work.EQ.entire_of_polyGrowth
import Submission.Work.EQ.meromorphic_order_nonneg_of_bounded
import Submission.Work.EQ.polynomial_eval_growth
import Submission.Work.EQ.exists_finite_pole_killers
import Submission.Work.EQ.eventually_zero_of_analyticOn_ball
import Submission.Work.EQ.toMeromorphicNFOn_far

/-! # Rationality of a meromorphic trace on `ℂ*`

A function `G` that is meromorphic on `ℂ*`, agrees with an analytic `g` on punctured
neighbourhoods of the points of the punctured disc `0 < ‖u‖ < ε`, and is bounded near `∞`, forces
`g` to be a rational germ at `0` with denominator nonzero at `0`.

The proof composes three ingredients:
* the normal form `Ĝ = toMeromorphicNFOn G {0}ᶜ`, which is analytic at every point where the
  meromorphic order is nonnegative (this removes the irrelevant values of `G` at single points);
* a finite set of local factors `(z - i) ^ n i`, `i` in the compact annulus containing all poles
  of `Ĝ`, which makes `D(z) · Ĝ z` analytic on all of `ℂ*`;
* a removable singularity at `0` (using `Ĝ =ᶠ[𝓝[≠] 0] g`) turning that product into an entire
  function of polynomial growth, hence a polynomial `N`.
-/

namespace Work.EQ

open Filter _root_.Topology

/-! ### The main theorem -/

/-- **A function meromorphic on `ℂ*`, analytic-continuable through `0` and bounded at `∞`, is
rational.** `G` is meromorphic at every `u ≠ 0`, agrees with the analytic `g` on punctured
neighbourhoods of the points of the punctured disc `0 < ‖u‖ < ε`, and is bounded near `∞`.
Then `g` is a rational germ at `0` with denominator nonzero at `0`. -/
theorem rational_of_meromorphic_trace {G g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 ε))
    (hmero : ∀ u : ℂ, u ≠ 0 → MeromorphicAt G u)
    (hnear : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → G =ᶠ[𝓝[≠] u] g)
    (hfar : ∃ R B : ℝ, ∀ u : ℂ, R < ‖u‖ → ‖G u‖ ≤ B) :
    ∃ N D : Polynomial ℂ, D.eval 0 ≠ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), g u * D.eval u = N.eval u := by
  obtain ⟨R, B, hfar⟩ := hfar
  set R' : ℝ := max R 1 with hR'def
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := by rw [hB'def]; exact le_max_right _ _
  have hR'1 : (1 : ℝ) ≤ R' := by rw [hR'def]; exact le_max_right _ _
  -- normal form of `G` on `ℂ*`
  set Ĝ : ℂ → ℂ := toMeromorphicNFOn G {0}ᶜ with hĜdef
  have hMerG : MeromorphicOn G {0}ᶜ := fun z hz => hmero z (by simpa using hz)
  have hNF : MeromorphicNFOn Ĝ {0}ᶜ := by
    rw [hĜdef]; exact meromorphicNFOn_toMeromorphicNFOn G {0}ᶜ
  have hĜG : ∀ z : ℂ, z ≠ 0 → Ĝ =ᶠ[𝓝[≠] z] G := by
    intro z hz
    rw [hĜdef]
    exact hMerG.toMeromorphicNFOn_eq_self_on_nhdsNE (by simpa using hz)
  -- `Ĝ` is analytic and equals `g` near the points of the punctured disc
  have hnear_an : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < ε → AnalyticAt ℂ Ĝ x ∧ Ĝ =ᶠ[𝓝 x] g := by
    intro x hx0 hxε
    have hxne : x ≠ 0 := by simpa using hx0.ne'
    have hxmem : x ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hxε
    have hgan : AnalyticAt ℂ g x := hg x hxmem
    have hnfn : MeromorphicNFAt Ĝ x := hNF (by simpa using hxne)
    have hord : 0 ≤ meromorphicOrderAt Ĝ x := by
      rw [meromorphicOrderAt_congr (hĜG x hxne), meromorphicOrderAt_congr (hnear x hxne hxε)]
      exact hgan.meromorphicOrderAt_nonneg
    have hĜan : AnalyticAt ℂ Ĝ x := (hnfn.meromorphicOrderAt_nonneg_iff_analyticAt).mp hord
    have heq : Ĝ =ᶠ[𝓝[≠] x] g := (hĜG x hxne).trans (hnear x hxne hxε)
    have heqfull : Ĝ =ᶠ[𝓝 x] g :=
      (hnfn.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hgan.meromorphicNFAt).mp heq
    exact ⟨hĜan, heqfull⟩
  -- hence `Ĝ = g` on a punctured neighbourhood of `0`
  have hĜ0g : Ĝ =ᶠ[𝓝[≠] (0 : ℂ)] g := by
    have hU : {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < ε} ∈ 𝓝[≠] (0 : ℂ) := by
      have h1 : {0}ᶜ ∈ 𝓝[≠] (0 : ℂ) := self_mem_nhdsWithin
      have h2 : Metric.ball (0 : ℂ) ε ∈ 𝓝[≠] (0 : ℂ) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
      have heq : {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < ε} = {0}ᶜ ∩ Metric.ball (0 : ℂ) ε := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
          Metric.mem_ball, dist_eq_norm, sub_zero, norm_pos_iff]
      rw [heq]; exact inter_mem h1 h2
    filter_upwards [hU] with x hx
    exact (hnear_an x hx.1 hx.2).2.eq_of_nhds
  -- far region
  have hfar_an : ∀ u : ℂ, R' < ‖u‖ → AnalyticAt ℂ Ĝ u ∧ ‖Ĝ u‖ ≤ B' := by
    intro u hu
    have hu' : max R 1 < ‖u‖ := by rw [hR'def] at hu; exact hu
    have h := toMeromorphicNFOn_far hmero hfar u hu'
    simpa only [hĜdef, hB'def] using h
  -- the compact annulus containing every pole
  set K : Set ℂ := Metric.closedBall (0 : ℂ) (R' + 1) \ Metric.ball (0 : ℂ) (ε / 2) with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef]; exact (isCompact_closedBall (0 : ℂ) (R' + 1)).diff Metric.isOpen_ball
  have hK0 : (0 : ℂ) ∉ K := by
    intro h
    rw [hKdef] at h
    exact h.2 (by rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_zero]; linarith [hε])
  have hKmer : ∀ x ∈ K, MeromorphicAt Ĝ x := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hK0 (h ▸ hx)
    exact (hNF (by simpa using hx0)).meromorphicAt
  obtain ⟨t, n, htK, htkill⟩ := exists_finite_pole_killers hKcomp hK0 hKmer
  -- the pole-killing polynomial
  set D : Polynomial ℂ := ∏ i ∈ t, (Polynomial.X - Polynomial.C i) ^ (n i) with hDdef
  have eval_factor : ∀ (s : Finset ℂ) (z : ℂ),
      (∏ j ∈ s, (Polynomial.X - Polynomial.C j) ^ (n j)).eval z
        = ∏ j ∈ s, (z - j) ^ (n j) := by
    intro s z
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hDeval : ∀ z : ℂ, D.eval z = ∏ i ∈ t, (z - i) ^ (n i) := by
    intro z
    rw [hDdef]
    exact eval_factor t z
  have hD0 : D.eval 0 ≠ 0 := by
    rw [hDeval]
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hiK : i ∈ K := htK i hi
    have hi0 : i ≠ 0 := fun h => hK0 (h ▸ hiK)
    exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hi0))
  -- `D * Ĝ` is analytic on `ℂ*`
  have hDĜ_an : AnalyticOnNhd ℂ (fun z => D.eval z * Ĝ z) {0}ᶜ := by
    intro y hy
    have hy0 : y ≠ 0 := by simpa using hy
    by_cases hyK : y ∈ K
    · obtain ⟨i, hit, hikill⟩ := htkill y hyK
      have hpoly0 := (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ)
        (∏ j ∈ t.erase i, (Polynomial.X - Polynomial.C j) ^ (n j))) y (Set.mem_univ y)
      have hpoly : AnalyticAt ℂ (fun z => ∏ j ∈ t.erase i, (z - j) ^ (n j)) y :=
        hpoly0.congr (Filter.EventuallyEq.of_eq (funext (fun z => eval_factor _ z)))
      refine (hpoly.mul hikill).congr (Filter.EventuallyEq.of_eq (funext (fun z => ?_)))
      show (∏ j ∈ t.erase i, (z - j) ^ (n j)) * ((z - i) ^ (n i) * Ĝ z) = D.eval z * Ĝ z
      rw [hDeval z, ← Finset.prod_erase_mul t (fun j => (z - j) ^ (n j)) hit, mul_assoc]
    · by_cases hyfar : R' < ‖y‖
      · exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) D) y (Set.mem_univ y)).mul
          (hfar_an y hyfar).1
      · have hyle : ‖y‖ ≤ R' := not_lt.mp hyfar
        have hycb : y ∈ Metric.closedBall (0 : ℂ) (R' + 1) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith
        have hyball : y ∈ Metric.ball (0 : ℂ) (ε / 2) := by
          by_contra hb
          exact hyK (by rw [hKdef]; exact ⟨hycb, hb⟩)
        have hyε2 : ‖y‖ < ε / 2 := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hyball; exact hyball
        have hyε : ‖y‖ < ε := lt_trans hyε2 (by linarith)
        have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) D) y (Set.mem_univ y)).mul
          (hnear_an y hypos hyε).1
  -- regularise at `0`: an entire function
  set F : ℂ → ℂ := Function.update (fun z => D.eval z * Ĝ z) 0 (D.eval 0 * g 0) with hFdef
  have hFan : AnalyticOnNhd ℂ F Set.univ := by
    intro y _
    by_cases hy0 : y = 0
    · subst hy0
      have hgan : AnalyticAt ℂ g 0 := by
        refine hg 0 ?_
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_zero]; exact hε
      have hprod : AnalyticAt ℂ (fun z => D.eval z * g z) 0 :=
        ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) D) 0 (Set.mem_univ 0)).mul hgan
      refine hprod.congr ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
      by_cases hz0 : z = 0
      · subst hz0
        rw [hFdef, Function.update_self]
      · have hzε : ‖z‖ < ε := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz; exact hz
        have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        rw [hFdef, Function.update_of_ne hz0, (hnear_an z hzpos hzε).2.eq_of_nhds]
    · have hyne : y ∈ ({0} : Set ℂ)ᶜ := by simpa using hy0
      have h0c : {0}ᶜ ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds (by simpa using hy0)
      refine (hDĜ_an y hyne).congr ?_
      filter_upwards [h0c] with z hz
      exact (Function.update_of_ne (by simpa using hz) (D.eval 0 * g 0)
        (fun z => D.eval z * Ĝ z)).symm
  have hFdiff : Differentiable ℂ F := fun y => (hFan y (Set.mem_univ y)).differentiableAt
  -- polynomial growth
  obtain ⟨C, hCpos, hCbound⟩ := polynomial_eval_growth D
  have hgrowth : ∃ (m : ℕ) (C' R'' : ℝ), 0 < C' ∧ ∀ z : ℂ, R'' ≤ ‖z‖ → ‖F z‖ ≤ C' * ‖z‖ ^ m := by
    refine ⟨D.natDegree, C * B' + 1, R' + 1, ?_, ?_⟩
    · nlinarith [hCpos, hB'0]
    · intro z hz
      have hzR : R' < ‖z‖ := by linarith
      have hz1 : (1 : ℝ) ≤ ‖z‖ := by linarith [hR'1]
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hz
        simp only [norm_zero] at hz
        linarith [hR'1]
      rw [hFdef, Function.update_of_ne hz0]
      have hb : ‖Ĝ z‖ ≤ B' := (hfar_an z hzR).2
      have hDz : ‖D.eval z‖ ≤ C * ‖z‖ ^ D.natDegree := hCbound z hz1
      have hpz : (0 : ℝ) ≤ ‖z‖ ^ D.natDegree := by positivity
      calc ‖D.eval z * Ĝ z‖ = ‖D.eval z‖ * ‖Ĝ z‖ := norm_mul _ _
        _ ≤ (C * ‖z‖ ^ D.natDegree) * B' := mul_le_mul hDz hb (norm_nonneg _) (by positivity)
        _ = (C * B') * ‖z‖ ^ D.natDegree := by ring
        _ ≤ (C * B' + 1) * ‖z‖ ^ D.natDegree := by
              exact mul_le_mul_of_nonneg_right (by linarith) hpz
  obtain ⟨N, hN⟩ := entire_of_polyGrowth hFdiff hgrowth
  refine ⟨N, D, hD0, ?_⟩
  -- the identity `D * g = N` near `0`
  have hE_an : AnalyticOnNhd ℂ (fun z => g z * D.eval z - N.eval z) (Metric.ball 0 ε) := by
    intro z hz
    exact ((hg z hz).mul ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) D) z (Set.mem_univ z))).sub
      ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) N) z (Set.mem_univ z))
  have hE_zero : ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε →
      ∀ᶠ z in 𝓝[≠] x, g z * D.eval z - N.eval z = 0 := by
    intro x hx0 hxε
    have h0c : {0}ᶜ ∈ 𝓝[≠] x :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (by simpa using hx0))
    have hgerm : Ĝ =ᶠ[𝓝[≠] x] g := (hĜG x hx0).trans (hnear x hx0 hxε)
    filter_upwards [hgerm, h0c] with z hz hz0
    have hz0' : z ≠ 0 := by simpa using hz0
    have hFz : F z = D.eval z * Ĝ z := by
      rw [hFdef, Function.update_of_ne hz0']
    have hthis := hN z
    rw [hFz, hz] at hthis
    rw [mul_comm (g z) (D.eval z), hthis, sub_self]
  filter_upwards [eventually_zero_of_analyticOn_ball hε hE_an hE_zero] with z hz
  exact sub_eq_zero.mp hz

end Work.EQ
