/-
# Uniqueness of the Böttcher coordinate on the open far region

`Work.Bottcher.bottcher c` is the explicit product formula.  This file proves the
"uniqueness" statement: on the open far region `S = farRegion c = {z | escapeRadius c < ‖z‖}`,
*any* analytic solution `ψ` of the Böttcher problem

* `ψ ∘ p_c = ψ ^ 4` on `S` (`p_c = T_c ∘ T_c` the holomorphic second iterate), and
* `ψ z / z → 1` as `z → ∞`

coincides with `bottcher c`.

No modulus hypothesis (`‖ψ z‖ = exp (G_c z)`) is needed: the classical ratio argument
already pins `ψ` down.  Put `u = ψ / φ_c` on `S`; then `u` is continuous,
`u ∘ p_c = u ^ 4`, and `u → 1` at infinity.  For `w ∈ S` the orbit `p_c^n w` escapes, so
`u w ^ (4 ^ n) = u (p_c^n w) → 1`, whence `u w` is a `2`-power root of unity
(`Core.exists_pow_two_pow_eq_one_of_tendsto_pow_four`).  Thus `u '' S` is a preconnected
subset of the totally disconnected set of `2`-power roots of unity, hence a singleton
(`ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one`); the constant value is `1`
because it is also a limit value of `u` at infinity.  Hence `u ≡ 1` and `ψ = φ_c` on `S`.
-/
import Mathlib
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable
import Submission.Work.ParamRays.exists_pow_two_pow_eq_one
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

namespace Work.Bottcher.Inverse

noncomputable section


/-- One step of the strict far-region invariance of `p_c`: if `escapeRadius c < ‖v‖` then
also `escapeRadius c < ‖p_c v‖`.  (The non-strict version is
`Work.Bottcher.Core.escapeRadius_le_norm_pMap`; here we use moreover that `p_c` at least
squares a large norm, so the escape radius is strictly exceeded.) -/
theorem escapeRadius_lt_norm_pMap (c : ℂ) {v : ℂ}
    (hv : Work.Bottcher.escapeRadius c < ‖v‖) :
    Work.Bottcher.escapeRadius c < ‖Work.Bottcher.pMap c v‖ := by
  have h2 : 2 + ‖c‖ ≤ ‖v‖ :=
    (lt_of_le_of_lt (Work.Bottcher.Core.two_add_norm_le_escapeRadius c) hv).le
  have hstep : ‖v‖ ^ 4 / 2 ≤ ‖Work.Bottcher.pMap c v‖ :=
    (Work.Bottcher.Core.pMap_norm_step c v h2).2.1
  have hv2 : (2 : ℝ) < ‖v‖ :=
    lt_of_le_of_lt (Work.Bottcher.Core.two_le_escapeRadius c) hv
  have h8 : (8 : ℝ) < ‖v‖ ^ 3 := by
    have := pow_lt_pow_left₀ hv2 (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this
    exact this
  have hlt : ‖v‖ < ‖v‖ ^ 4 / 2 := by nlinarith [h8, norm_nonneg v]
  linarith

/-- The strict far region is invariant under the iterated second iterate `p_c`. -/
theorem escapeRadius_lt_norm_pMap_iterate (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c < ‖w‖) (n : ℕ) :
    Work.Bottcher.escapeRadius c < ‖(Work.Bottcher.pMap c)^[n] w‖ := by
  induction n with
  | zero => simpa using hw
  | succ n ih => rw [Function.iterate_succ_apply']; exact escapeRadius_lt_norm_pMap c ih

theorem eq_bottcher_of_analytic_far (c : ℂ) (ψ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ ψ (Work.Bottcher.Core.farRegion c))
    (hfe : ∀ z : ℂ, z ∈ Work.Bottcher.Core.farRegion c →
      ψ (Work.Bottcher.pMap c z) = (ψ z) ^ 4)
    (has : Filter.Tendsto (fun z : ℂ => ψ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)))
    {z : ℂ} (hz : z ∈ Work.Bottcher.Core.farRegion c) :
    ψ z = Work.Bottcher.bottcher c z := by
  classical
  -- ## Non-vanishing and the functional equation for the product formula on `S`
  have hmodφ : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      ‖Work.Bottcher.bottcher c w‖ = Real.exp (Work.Bottcher.green c w) :=
    fun w hw => Work.Bottcher.Core.norm_bottcher_eq_exp_green_of_escapeRadius_le c
      (Work.Bottcher.Core.mem_farRegion.mp hw).le
  have hφne : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      Work.Bottcher.bottcher c w ≠ 0 := by
    intro w hw h
    have h1 := hmodφ w hw
    rw [h, norm_zero] at h1
    exact absurd h1.symm (Real.exp_ne_zero _)
  have hfeφ : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      Work.Bottcher.bottcher c (Work.Bottcher.pMap c w) = (Work.Bottcher.bottcher c w) ^ 4 :=
    fun w hw => Work.Bottcher.Core.bottcher_comm_pMap_of_escapeRadius_le c
      (Work.Bottcher.Core.mem_farRegion.mp hw).le
  have hfeU : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      ψ (Work.Bottcher.pMap c w) / Work.Bottcher.bottcher c (Work.Bottcher.pMap c w)
        = (ψ w / Work.Bottcher.bottcher c w) ^ 4 := by
    intro w hw
    rw [hfe w hw, hfeφ w hw, div_pow]
  -- ## The ratio `u = ψ / φ_c` has limit `1` at infinity
  have hUtendsto : Tendsto (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      (cocompact ℂ) (nhds (1 : ℂ)) := by
    have hratio : Tendsto (fun u : ℂ => (ψ u / u) / (Work.Bottcher.bottcher c u / u))
        (cocompact ℂ) (nhds ((1 : ℂ) / 1)) :=
      has.div (Work.Bottcher.Core.bottcher_tendsto_atTop c) one_ne_zero
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
  -- ## The open far region is preconnected, and the ratio is continuous there
  have hSpre : IsPreconnected (Work.Bottcher.Core.farRegion c) :=
    Work.ParamRays.isPreconnected_lt_norm (Work.Bottcher.Core.escapeRadius_pos c).le
  have hcontU : ContinuousOn (fun u : ℂ => ψ u / Work.Bottcher.bottcher c u)
      (Work.Bottcher.Core.farRegion c) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact han.continuousOn
    · intro w hw
      exact (Work.Bottcher.Core.analyticAt_bottcher c w
        (Work.Bottcher.Core.mem_farRegion.mp hw).le).continuousAt.continuousWithinAt
    · intro w hw
      exact hφne w hw
  have hpre : IsPreconnected
      ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' Work.Bottcher.Core.farRegion c) :=
    hSpre.image _ hcontU
  -- ## Every value of the ratio on `S` is a `2`-power root of unity
  have hcert : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c → ∃ N : ℕ,
      (ψ w / Work.Bottcher.bottcher c w) ^ (2 ^ N) = 1 := by
    intro w hw
    have hwD : Work.Bottcher.escapeRadius c < ‖w‖ :=
      Work.Bottcher.Core.mem_farRegion.mp hw
    have hDiter : ∀ n : ℕ, (Work.Bottcher.pMap c)^[n] w ∈ Work.Bottcher.Core.farRegion c :=
      fun n => Work.Bottcher.Core.mem_farRegion.mpr (escapeRadius_lt_norm_pMap_iterate c hwD n)
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
      have hT := Work.Bottcher.Core.tendsto_norm_Tantibar_iterate_of_escapeRadius_le c hwD.le
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
    exact Work.Bottcher.Core.exists_pow_two_pow_eq_one_of_tendsto_pow_four hpow
  -- ## The image of the ratio is a singleton
  have hsingle :
      ((fun u : ℂ => ψ u / Work.Bottcher.bottcher c u) '' Work.Bottcher.Core.farRegion c).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre
      (by rintro ζ ⟨w, hw, rfl⟩; exact hcert w hw)
  -- ## The constant value is `1`
  set w₀ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = Work.Bottcher.escapeRadius c + 1 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(Work.Bottcher.Core.escapeRadius_pos c).le])]
  have hw₀S : w₀ ∈ Work.Bottcher.Core.farRegion c := by
    rw [Work.Bottcher.Core.mem_farRegion, hw₀norm]
    linarith
  have hconst : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
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
      rw [hconst t htmem] at hd
      exact hd
    have hzero : ‖ψ w₀ / Work.Bottcher.bottcher c w₀ - 1‖ ≤ 0 :=
      le_of_forall_pos_le_add (fun ε hε => by simpa using (hclose ε hε).le)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  -- ## Conclusion
  have hfinal : ψ z / Work.Bottcher.bottcher c z = 1 := (hconst z hz).trans hval
  exact (div_eq_one_iff_eq (hφne z hz)).mp hfinal

end

end Work.Bottcher.Inverse
