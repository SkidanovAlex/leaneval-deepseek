import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green
import Submission.Work.Bottcher.Core.norm_iterate_pMap_ge
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one
import Submission.Work.ParamRays.exists_pow_two_pow_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.Bottcher.Core

/--
Generalises `Work.Bottcher.Core.eq_bottcher_of_analytic` from the closed far region
`{escapeRadius c ≤ ‖z‖}` to the exterior `{R < ‖z‖}` of an arbitrary ball of radius
`R ≥ escapeRadius c`, with the analyticity / functional equation / modulus hypotheses required
only on the open exterior.

Under those hypotheses `ψ z = bottcher c z` for every `‖z‖ > R`.

Copy the proof of `eq_bottcher_of_analytic`, run on the open preconnected exterior
`S = {z | R < ‖z‖}` (which is `pMap c`-invariant because `R ≥ escapeRadius c`, so
`escapeRadius_le_norm_pMap` gives `‖pMap c z‖ ≥ ‖z‖ > R`; `bottcher_comm_pMap` and
`norm_bottcher_eq_exp_green` for `φ_c = bottcher c` hold from `R ≥ escapeRadius c` on):
the ratio `u = ψ / φ_c` has modulus `1` on `S`, satisfies `u ∘ p_c = u^4`, takes values in the
`2`-power roots of unity (iterating reaches the region where `u → 1`), and `S` is preconnected, so
`u` is constant (`Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one`), the constant
being `1` because `u → 1` at infinity.  Unlike `eq_bottcher_of_analytic`, no boundary extension
step is needed: the conclusion is only claimed on the open exterior.
-/
theorem eq_bottcher_of_analytic_tail (c : ℂ) (R : ℝ)
    (hR : Work.Bottcher.escapeRadius c ≤ R) (ψ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ ψ {z : ℂ | R < ‖z‖})
    (hfe : ∀ z : ℂ, R < ‖z‖ → ψ (Work.Bottcher.pMap c z) = (ψ z) ^ 4)
    (hmod : ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => ψ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∀ z : ℂ, R < ‖z‖ → ψ z = Work.Bottcher.bottcher c z := by
  classical
  have hRnonneg : (0 : ℝ) ≤ R := (escapeRadius_pos c).le.trans hR
  -- ## Identical modulus and non-vanishing on the open exterior
  have hmodφ : ∀ w : ℂ, R < ‖w‖ → ‖Work.Bottcher.bottcher c w‖ = Real.exp (Work.Bottcher.green c w) :=
    fun w hw => norm_bottcher_eq_exp_green_of_escapeRadius_le c (hR.trans hw.le)
  have hφne : ∀ w : ℂ, R < ‖w‖ → Work.Bottcher.bottcher c w ≠ 0 := by
    intro w hw h
    have h1 := hmodφ w hw
    rw [h, norm_zero] at h1
    exact absurd h1.symm (Real.exp_ne_zero _)
  have hfeφ : ∀ w : ℂ, R < ‖w‖ →
      Work.Bottcher.bottcher c (Work.Bottcher.pMap c w) = (Work.Bottcher.bottcher c w) ^ 4 :=
    fun w hw => bottcher_comm_pMap_of_escapeRadius_le c (hR.trans hw.le)
  have hnormU : ∀ w : ℂ, R < ‖w‖ →
      ‖ψ w / Work.Bottcher.bottcher c w‖ = 1 := by
    intro w hw
    rw [norm_div, hmod w hw, hmodφ w hw, div_self (Real.exp_ne_zero _)]
  have hfeU : ∀ w : ℂ, R < ‖w‖ →
      ψ (Work.Bottcher.pMap c w) / Work.Bottcher.bottcher c (Work.Bottcher.pMap c w)
        = (ψ w / Work.Bottcher.bottcher c w) ^ 4 := by
    intro w hw
    rw [hfe w hw, hfeφ w hw, div_pow]
  -- ## The ratio `u = ψ / φ_c` has limit `1` at infinity
  have hUtendsto : Tendsto (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      (cocompact ℂ) (nhds (1 : ℂ)) := by
    have hratio : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds ((1 : ℂ) / 1)) :=
      has.div (bottcher_tendsto_atTop c) one_ne_zero
    have hratio' : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds (1 : ℂ)) := by
      simpa using hratio
    refine hratio'.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with u hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu
      norm_num at hu
    have hφu0 : Work.Bottcher.bottcher c u ≠ 0 := by
      rw [Work.Bottcher.bottcher]
      exact mul_ne_zero hu0 (Complex.exp_ne_zero _)
    field_simp
  -- ## The open exterior
  have hSpre : IsPreconnected {z : ℂ | R < ‖z‖} :=
    Work.ParamRays.isPreconnected_lt_norm hRnonneg
  have hcontU : ContinuousOn (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      {z : ℂ | R < ‖z‖} := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact han.continuousOn
    · intro w hw
      exact (analyticAt_bottcher c w (hR.trans hw.le)).continuousAt.continuousWithinAt
    · intro w hw
      exact hφne w hw
  have hpre : IsPreconnected
      ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' {z : ℂ | R < ‖z‖}) :=
    hSpre.image _ hcontU
  -- every value of the ratio on the exterior is a `2`-power root of unity
  have hcert : ∀ w : ℂ, R < ‖w‖ → ∃ N : ℕ,
      (ψ w / Work.Bottcher.bottcher c w) ^ (2 ^ N) = 1 := by
    intro w hw
    have hDiter : ∀ n : ℕ, R < ‖(Work.Bottcher.pMap c)^[n] w‖ := by
      intro n
      have h1 := (norm_iterate_pMap_ge c (Work.Bottcher.escapeRadius c)
        (fun _ hu => escapeRadius_le_norm_pMap c hu) w (hR.trans hw.le) n).2
      exact lt_of_lt_of_le hw h1
    have hiterU : ∀ n : ℕ,
        ψ ((Work.Bottcher.pMap c)^[n] w) / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w)
          = (ψ w / Work.Bottcher.bottcher c w) ^ (4 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', hfeU _ (hDiter n), ih, ← pow_mul, pow_succ]
    have hcoc : Tendsto (fun n : ℕ => (Work.Bottcher.pMap c)^[n] w) atTop (cocompact ℂ) := by
      refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
      have hT := tendsto_norm_Tantibar_iterate_of_escapeRadius_le c (hR.trans hw.le)
      have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
        tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
      have h1 : Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] w‖) atTop atTop := hT.comp h2n
      refine h1.congr' (Eventually.of_forall (fun n => ?_))
      simp only [dist_zero_right]
      rw [Work.Bottcher.pMap_iterate]
    have hlim : Tendsto (fun n : ℕ =>
        ψ ((Work.Bottcher.pMap c)^[n] w) / Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[n] w))
        atTop (nhds 1) := hUtendsto.comp hcoc
    have hpow : Tendsto (fun n : ℕ => (ψ w / Work.Bottcher.bottcher c w) ^ (4 ^ n))
        atTop (nhds 1) :=
      hlim.congr' (Eventually.of_forall (fun n => hiterU n))
    exact exists_pow_two_pow_eq_one_of_tendsto_pow_four hpow
  have hsingle : ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' {z : ℂ | R < ‖z‖}).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre
      (by rintro ζ ⟨w, hw, rfl⟩; exact hcert w hw)
  -- ## The constant value is `1`
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = R + 1 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hw₀S : R < ‖w₀‖ := by
    rw [hw₀norm]; linarith
  have hconst : ∀ w : ℂ, R < ‖w‖ →
      ψ w / Work.Bottcher.bottcher c w = ψ w₀ / Work.Bottcher.bottcher c w₀ :=
    fun w hw => hsingle ⟨w, hw, rfl⟩ ⟨w₀, hw₀S, rfl⟩
  have hval : ψ w₀ / Work.Bottcher.bottcher c w₀ = 1 := by
    have hclose : ∀ ε : ℝ, 0 < ε → ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ < ε := by
      intro ε hε
      have hmem : {u : ℂ | dist (ψ u / Work.Bottcher.bottcher c u) 1 < ε} ∈ cocompact ℂ :=
        (Metric.tendsto_nhds.mp hUtendsto) ε hε
      rw [Filter.mem_cocompact] at hmem
      obtain ⟨K, hKc, hKsub⟩ := hmem
      obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
      set t : ℝ := max R M + 1 with htdef
      have ht0 : 0 ≤ t := by
        rw [htdef]
        have h := le_max_left R M
        linarith
      have htnorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have htmem : R < ‖(t : ℂ)‖ := by
        rw [htnorm, htdef]
        linarith [le_max_left R M]
      have htK : (t : ℂ) ∉ K := by
        intro ht
        have h1 := hM ht
        rw [Metric.mem_closedBall, dist_zero_right, htnorm, htdef] at h1
        linarith [le_max_right R M]
      have hd := hKsub htK
      rw [Set.mem_ofPred_eq, dist_eq_norm] at hd
      rw [hconst t htmem] at hd
      exact hd
    have hzero : ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ ≤ 0 :=
      le_of_forall_pos_le_add (fun ε hε => by simpa using (hclose ε hε).le)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  -- ## Equality on the open exterior
  intro z hz
  have h1 : ψ z / Work.Bottcher.bottcher c z = 1 := (hconst z hz).trans hval
  exact (div_eq_one_iff_eq (hφne z hz)).mp h1

end Work.Bottcher.Core
