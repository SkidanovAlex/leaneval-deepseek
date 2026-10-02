import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Core.bottcher_comm_pMap_domain
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The product formula is the only continuous Böttcher coordinate on the far region.**

Let `c ∈ M*` and let `φ : ℂ → ℂ` be a *continuous* function on the escape set
`EscapeSet c = {z | 0 < green c z}` satisfying the Böttcher requirements of the quartic
`p_c = T_c ∘ T_c`: the Böttcher equation `φ (p_c z) = (φ z)^4` on the escape set, the modulus
relation `‖φ z‖ = exp (green c z)`, and the tangency `φ z / z → 1` at infinity.

Then `φ` agrees with the product formula `bottcher c` on a far region `{z | R ≤ ‖z‖}` with
`escapeRadius c ≤ R`.

Proof outline (no new mathematics beyond the workspace): the ratio `r z = φ z / bottcher c z`
is continuous where `‖z‖ ≥ escapeRadius c`, unimodular, satisfies `r (p_c z) = (r z)^4` and
tends to `1` at infinity; shrink the far region so that `‖r z - 1‖ < 1/2`, put
`Λ z = Complex.log (r z)` (continuous there, with `exp (Λ z) = r z`); then
`Λ (p_c z) - 4 * Λ z ∈ 2πiℤ`, so `z ↦ (Λ (p_c z) - 4 * Λ z).im / (2π)` is a continuous
integer-valued function on the preconnected far region, hence constant `= k`; iterating,
`Λ (p_c^[N] z) = 4^N * Λ z + ((4^N - 1)/3) * k * (2πi)`, and letting `N → ∞` (the orbit escapes,
`Λ → 0` at infinity) gives first `Λ z + (k/3)(2πi) = 0` and then `k = 0`, `Λ z = 0`. -/
theorem eq_bottcher_on_far_of_continuousBottcher (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (φ : ℂ → ℂ)
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∃ R : ℝ, Work.Bottcher.escapeRadius c ≤ R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → φ z = Work.Bottcher.bottcher c z := by
  classical
  -- ## The open far region
  have hSpre : IsPreconnected (Work.Bottcher.Core.farRegion c) :=
    Work.ParamRays.isPreconnected_lt_norm (Work.Bottcher.Core.escapeRadius_pos c).le
  have hfar : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      Work.Bottcher.escapeRadius c ≤ ‖w‖ :=
    fun _ hw => le_of_lt (Work.Bottcher.Core.mem_farRegion.mp hw)
  have hSesc : Work.Bottcher.Core.farRegion c ⊆ Work.Bottcher.EscapeSet c :=
    fun w hw => farRegion_subset_escapeSet c (hfar w hw)
  -- ## The product formula does not vanish on the far region
  have hbne : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c → Work.Bottcher.bottcher c w ≠ 0 := by
    intro w hw h
    have h1 := Work.Bottcher.Core.norm_bottcher_eq_exp_green_of_escapeRadius_le c (hfar w hw)
    rw [h, norm_zero] at h1
    exact absurd h1.symm (Real.exp_ne_zero _)
  -- ## The ratio is continuous on the far region
  have hcont_ratio : ContinuousOn (fun w : ℂ => φ w / Work.Bottcher.bottcher c w)
      (Work.Bottcher.Core.farRegion c) :=
    (hcont.mono hSesc).div
      (fun w hw => (Work.Bottcher.Core.analyticAt_bottcher c w (hfar w hw)).continuousAt.continuousWithinAt)
      hbne
  -- ## The ratio is unimodular on the far region
  have hnorm1 : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      ‖φ w / Work.Bottcher.bottcher c w‖ = 1 := by
    intro w hw
    rw [norm_div, hmod w (green_pos_of_escapeRadius_le c (hfar w hw)),
      Work.Bottcher.Core.norm_bottcher_eq_exp_green_of_escapeRadius_le c (hfar w hw),
      div_self (Real.exp_ne_zero _)]
  -- ## The ratio satisfies the Böttcher equation
  have hfeR : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      φ (Work.Bottcher.pMap c w) / Work.Bottcher.bottcher c (Work.Bottcher.pMap c w)
        = (φ w / Work.Bottcher.bottcher c w) ^ 4 := by
    intro w hw
    rw [hfe w (green_pos_of_escapeRadius_le c (hfar w hw)),
      Work.Bottcher.Core.bottcher_comm_pMap_of_escapeRadius_le c (hfar w hw), div_pow]
  -- ## The ratio tends to `1` at infinity
  have hT : Tendsto (fun u : ℂ => φ u / Work.Bottcher.bottcher c u) (cocompact ℂ) (nhds 1) := by
    have hratio : Tendsto (fun u : ℂ => (φ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds ((1 : ℂ) / 1)) :=
      has.div (Work.Bottcher.Core.bottcher_tendsto_atTop c) one_ne_zero
    have hratio' : Tendsto (fun u : ℂ => (φ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds (1 : ℂ)) := by simpa using hratio
    refine hratio'.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with u hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu
      norm_num at hu
    have hφu0 : Work.Bottcher.bottcher c u ≠ 0 := by
      rw [Work.Bottcher.bottcher]
      exact mul_ne_zero hu0 (Complex.exp_ne_zero _)
    field_simp
  -- ## The `p_c`-iterates of a point of the far region stay in the far region
  have hstrict : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c → ∀ n : ℕ,
      (Work.Bottcher.pMap c)^[n] w ∈ Work.Bottcher.Core.farRegion c := by
    intro w hw n
    rw [Work.Bottcher.Core.mem_farRegion]
    have h1 := (Work.Bottcher.Core.norm_iterate_pMap_ge c (Work.Bottcher.escapeRadius c)
      (fun v hv => Work.Bottcher.Core.escapeRadius_le_norm_pMap c hv) w (hfar w hw) n).2
    have h2 : Work.Bottcher.escapeRadius c < ‖w‖ := Work.Bottcher.Core.mem_farRegion.mp hw
    linarith
  -- ## Every value of the ratio on the far region is a `2`-power root of unity
  have hcert : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      ∃ N : ℕ, (φ w / Work.Bottcher.bottcher c w) ^ (2 ^ N) = 1 := by
    intro w hw
    have hmem := hstrict w hw
    have hiter : ∀ n : ℕ,
        φ ((Work.Bottcher.pMap c)^[n] w)
            / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w)
          = (φ w / Work.Bottcher.bottcher c w) ^ (4 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', hfeR _ (hmem n), ih,
            show (4 : ℕ) ^ (n + 1) = 4 ^ n * 4 from pow_succ 4 n, ← pow_mul]
    have hcoc : Tendsto (fun n : ℕ => (Work.Bottcher.pMap c)^[n] w) atTop (cocompact ℂ) := by
      refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
      have hTn := Work.Bottcher.Core.tendsto_norm_Tantibar_iterate_of_escapeRadius_le c (hfar w hw)
      have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
        tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
      have h1 : Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] w‖) atTop atTop := hTn.comp h2n
      refine h1.congr' (Eventually.of_forall (fun n => ?_))
      simp only [dist_zero_right]
      rw [Work.Bottcher.pMap_iterate]
    have hlim : Tendsto (fun n : ℕ => φ ((Work.Bottcher.pMap c)^[n] w)
        / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w)) atTop (nhds 1) :=
      hT.comp hcoc
    have hpow : Tendsto (fun n : ℕ => (φ w / Work.Bottcher.bottcher c w) ^ (4 ^ n))
        atTop (nhds 1) := hlim.congr' (Eventually.of_forall (fun n => hiter n))
    exact Work.Bottcher.Core.exists_pow_two_pow_eq_one_of_tendsto_pow_four hpow
  -- ## The image of the ratio on the preconnected far region is a singleton
  have himg : IsPreconnected
      ((fun w : ℂ => φ w / Work.Bottcher.bottcher c w) '' Work.Bottcher.Core.farRegion c) :=
    hSpre.image _ hcont_ratio
  have hsingle : ((fun w : ℂ => φ w / Work.Bottcher.bottcher c w)
      '' Work.Bottcher.Core.farRegion c).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one himg
      (by rintro ζ ⟨w, hw, rfl⟩; exact hcert w hw)
  set w₀ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = Work.Bottcher.escapeRadius c + 1 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(Work.Bottcher.Core.escapeRadius_pos c).le])]
  have hw₀S : w₀ ∈ Work.Bottcher.Core.farRegion c := by
    rw [Work.Bottcher.Core.mem_farRegion, hw₀norm]
    linarith
  have hconst : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      φ w / Work.Bottcher.bottcher c w = φ w₀ / Work.Bottcher.bottcher c w₀ :=
    fun w hw => hsingle ⟨w, hw, rfl⟩ ⟨w₀, hw₀S, rfl⟩
  -- ## The constant value of the ratio is `1`
  have hval : φ w₀ / Work.Bottcher.bottcher c w₀ = 1 := by
    have hclose : ∀ ε : ℝ, 0 < ε → ‖φ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ < ε := by
      intro ε hε
      have hmem : {u : ℂ | dist (φ u / Work.Bottcher.bottcher c u) 1 < ε} ∈ cocompact ℂ :=
        (Metric.tendsto_nhds.mp hT) ε hε
      rw [Filter.mem_cocompact] at hmem
      obtain ⟨K, hKc, hKsub⟩ := hmem
      obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
      set t : ℝ := max (Work.Bottcher.escapeRadius c) M + 1 with htdef
      have ht0 : 0 ≤ t := by
        rw [htdef]
        have h := le_max_left (Work.Bottcher.escapeRadius c) M
        linarith [(Work.Bottcher.Core.escapeRadius_pos c).le]
      have htnorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have htmem : (t : ℂ) ∈ Work.Bottcher.Core.farRegion c := by
        rw [Work.Bottcher.Core.mem_farRegion, htnorm, htdef]
        linarith [le_max_left (Work.Bottcher.escapeRadius c) M]
      have htK : (t : ℂ) ∉ K := by
        intro ht
        have h1 := hM ht
        rw [Metric.mem_closedBall, dist_zero_right, htnorm, htdef] at h1
        linarith [le_max_right (Work.Bottcher.escapeRadius c) M]
      have hd := hKsub htK
      rw [Set.mem_ofPred_eq, dist_eq_norm] at hd
      rwa [hconst t htmem] at hd
    have hzero : ‖φ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ ≤ 0 :=
      le_of_forall_pos_le_add (fun ε hε => by simpa using (hclose ε hε).le)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  -- ## Conclusion
  refine ⟨Work.Bottcher.escapeRadius c + 1,
    by linarith [(Work.Bottcher.Core.escapeRadius_pos c).le], fun z hz => ?_⟩
  have hzS : z ∈ Work.Bottcher.Core.farRegion c := by
    rw [Work.Bottcher.Core.mem_farRegion]
    linarith
  have h1 : φ z / Work.Bottcher.bottcher c z = 1 := (hconst z hzS).trans hval
  exact (div_eq_one_iff_eq (hbne z hzS)).mp h1

end Work.Bottcher.Contraction
