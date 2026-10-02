import Mathlib
import Submission.Work.Bottcher.All
import Submission.Work.ParamRays.IsDynBottcher_modulus
import Submission.Work.Bottcher.Contraction.green_eq_greenFun
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Contraction.eq_bottcher_on_far_of_continuousBottcher
import Submission.Work.Bottcher.Contraction.analyticOnNhd_of_continuousBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The product formula is the only continuous Böttcher coordinate on the far region**
(stated without the (unused) hypothesis `c ∈ Mandelbar`).

This is a verbatim copy of
`Work.Bottcher.Contraction.eq_bottcher_on_far_of_continuousBottcher` with `hc : c ∈ Mandelbar`
deleted from the signature; `hc` does not occur in the original proof body. -/
theorem far_eq_bottcher_of_continuousBottcher (c : ℂ) (φ : ℂ → ℂ)
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
    fun w hw => Work.Bottcher.Contraction.farRegion_subset_escapeSet c (hfar w hw)
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
    rw [norm_div, hmod w (Work.Bottcher.Contraction.green_pos_of_escapeRadius_le c (hfar w hw)),
      Work.Bottcher.Core.norm_bottcher_eq_exp_green_of_escapeRadius_le c (hfar w hw),
      div_self (Real.exp_ne_zero _)]
  -- ## The ratio satisfies the Böttcher equation
  have hfeR : ∀ w : ℂ, w ∈ Work.Bottcher.Core.farRegion c →
      φ (Work.Bottcher.pMap c w) / Work.Bottcher.bottcher c (Work.Bottcher.pMap c w)
        = (φ w / Work.Bottcher.bottcher c w) ^ 4 := by
    intro w hw
    rw [hfe w (Work.Bottcher.Contraction.green_pos_of_escapeRadius_le c (hfar w hw)),
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

/-- **A continuous Böttcher coordinate of the tricorn is analytic on the escape set.**

This is `Work.Bottcher.Contraction.analyticOnNhd_of_continuousBottcher` with its hypothesis
`c ∈ Mandelbar` *removed*: that hypothesis is in fact unused, so the proof goes through
verbatim.

Route.  From `h : Work.ParamRays.IsDynBottcher c φ` derive the four hypotheses of
`Work.Bottcher.Contraction.analyticOnNhd_of_continuousBottcher_of_far` (which needs no
`c ∈ Mandelbar`):

* `hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c)` — from `h.1` and
  `Work.Bottcher.Contraction.escapeSet_eq_escapingSet`;
* `hfe : ∀ z, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z)^4` — iterate the
  antiholomorphic equation `h.2.1`;
* `hmod : ∀ z, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z)` — from
  `Work.ParamRays.IsDynBottcher_modulus` and `Work.Bottcher.Contraction.green_eq_greenFun`;
* `has : Tendsto (fun z => φ z / z) cocompact (nhds 1)` — from the tangency `h.2.2`;

and the far-field input `hfar` is supplied by `far_eq_bottcher_of_continuousBottcher`. -/
theorem analyticOnNhd_dynBottcher {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ) :
    AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c) := by
  -- Continuity on the escape set
  have hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c) := by
    rw [Work.Bottcher.Contraction.escapeSet_eq_escapingSet c]
    exact h.1
  -- The Böttcher equation of the quartic `p_c = T_c ∘ T_c`
  have hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4 := by
    intro z hz
    have hzE : Work.ParamRays.Escaping c z := (Work.Bottcher.Green.green_pos_iff c z).mp hz
    have hT : Work.ParamRays.Escaping c (Tantibar c z) := hzE.iterate 1
    have h2 : Work.Bottcher.pMap c z = Tantibar c (Tantibar c z) := by
      rw [Work.Bottcher.pMap_eq_iterate_two]; rfl
    rw [h2, h.2.1 _ hT, h.2.1 _ hzE, Work.ParamRays.conj_sq_sq]
  -- The modulus relation
  have hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z) := by
    intro z hz
    have hzE : Work.ParamRays.Escaping c z := (Work.Bottcher.Green.green_pos_iff c z).mp hz
    rw [Work.ParamRays.IsDynBottcher_modulus h hzE,
      ← Work.Bottcher.Contraction.green_eq_greenFun c z]
  -- The tangency at infinity
  have has : Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ (ε / 2) * ‖z‖ :=
      h.2.2 (ε / 2) (by linarith)
    have hbig : ∀ᶠ z : ℂ in Filter.cocompact ℂ, (1 : ℝ) ≤ ‖z‖ := by
      refine Filter.mem_of_superset
        (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact ?_
      intro z hz'
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz'
      exact le_of_lt (not_le.mp hz')
    filter_upwards [hδ, hbig] with z h1 h2
    have hz0 : z ≠ 0 := by
      intro hh
      rw [hh, norm_zero] at h2
      linarith
    have hzpos : 0 < ‖z‖ := by linarith
    have hsplit : φ z / z - 1 = (φ z - z) / z := by
      field_simp
    rw [dist_eq_norm, hsplit, norm_div]
    rw [div_lt_iff₀ hzpos]
    nlinarith [norm_nonneg z]
  obtain ⟨R, hR, hfar⟩ := far_eq_bottcher_of_continuousBottcher c φ hcont hfe hmod has
  exact Work.Bottcher.Contraction.analyticOnNhd_of_continuousBottcher_of_far c φ R hR hcont hfe
    hmod hfar

end Work.ELRig
