import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic_tail
import Submission.Work.Bottcher.Core.bottcher_comm_Tantibar_far
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

/-- The `T_c`-orbit norms of a point of the critical domain escape to infinity (it is in the
escape set). -/
theorem tendsto_norm_Tantibar_iterate_of_mem_CritDomain (c : ℂ) {z : ℂ}
    (hz : z ∈ Work.Bottcher.CritDomain c) :
    Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop := by
  have hgp : 0 ≤ Work.Bottcher.greenParam c := by
    rw [Work.Bottcher.greenParam_def]
    exact Work.Bottcher.Green.green_nonneg c 0
  exact (Work.Bottcher.Green.green_pos_iff c z).mp
    (lt_of_le_of_lt hgp (Work.Bottcher.mem_CritDomain.mp hz))

/-- Some `p_c`-iterate of a point of the critical domain lies above `critFarRadius c`. -/
theorem exists_pMap_iterate_critFar_of_mem_CritDomain (c : ℂ) {z : ℂ}
    (hz : z ∈ Work.Bottcher.CritDomain c) :
    ∃ m : ℕ, Work.Bottcher.CritBasic.critFarRadius c < ‖(Work.Bottcher.pMap c)^[m] z‖ := by
  have hT := tendsto_norm_Tantibar_iterate_of_mem_CritDomain c hz
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have h2 : Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] z‖) atTop atTop := hT.comp h2n
  have hev : ∀ᶠ n : ℕ in atTop,
      Work.Bottcher.CritBasic.critFarRadius c < ‖(Tantibar c)^[2 * n] z‖ :=
    h2.eventually (eventually_gt_atTop (Work.Bottcher.CritBasic.critFarRadius c))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  exact ⟨N, by rw [Work.Bottcher.pMap_iterate]; exact hN N le_rfl⟩

/--
Generalises `Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic` (there: the escape set
`{G_c > 0}`) to the critical domain `CritDomain c = {G_c > G_c 0}` of an arbitrary parameter.

An analytic `φ` on `CritDomain c` solving the Böttcher problem of the *holomorphic* quartic
`p_c = T_c ∘ T_c` there (`φ (p_c z) = (φ z)^4`, `‖φ z‖ = exp (G_c z)` on `CritDomain c`) and
tangent to the identity at infinity solves the Böttcher problem of the antiholomorphic quadratic
`T_c` itself: `φ (T_c z) = conj (φ z)^2` on `CritDomain c`.

Proof: copy `bottcher_comm_Tantibar_of_analytic`, replacing `EscapeSet c` by `CritDomain c`,
`0 < green c z` by `z ∈ CritDomain c`, and `isPreconnected_escapeSet c` by
`Work.Bottcher.CritBasic.isPreconnected_CritDomain c`.  The ratio
`K z = conj (φ (T_c z)) / (φ z)^2` is continuous with modulus `1` on `CritDomain c` (using
`Green.green_comm` and `CritBasic.Tantibar_mem_CritDomain`), satisfies `K ∘ p_c = K^4`, and takes
values in the `2`-power roots of unity (the `p_c`-orbit of a point of `CritDomain c` stays in
`CritDomain c` by `CritBasic.pMap_iterate_mem_CritDomain` and reaches the far region); the image is
preconnected, hence a singleton (`Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one`),
and equals `1` at a far point.

The only new ingredient is the location of that far point.  Both `φ` and the product formula
`bottcher c` satisfy the hypotheses of
`Work.Bottcher.Core.eq_bottcher_of_analytic_tail c R` for
`R := Work.Bottcher.CritBasic.critFarRadius c` (`Core.bottcher_comm_pMap`,
`Core.norm_bottcher_eq_exp_green`, `Core.bottcher_tendsto_atTop` for the product formula, and
`CritBasic.critFar_subset_CritDomain` to transfer the hypotheses on `φ`), so
`φ w = bottcher c w` for `‖w‖ > critFarRadius c`; taking
`w := ((critFarRadius c + 1 : ℝ) : ℂ)` and `Core.bottcher_comm_Tantibar_far` (valid since
`escapeRadius c ≤ critFarRadius c ≤ ‖w‖`) gives `K w = 1`.
-/
theorem bottcher_comm_Tantibar_on_CritDomain (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.CritDomain c))
    (hfe : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      φ (LeanEval.ComplexAnalysis.Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2 := by
  -- ## Elementary facts
  have hφne : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c → φ z ≠ 0 := by
    intro z hz
    have h : 0 < ‖φ z‖ := by rw [hmod z hz]; exact Real.exp_pos _
    exact norm_pos_iff.mp h
  have hTcont : Continuous (Tantibar c) := by
    show Continuous (fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c)
    exact (continuous_star.pow 2).add continuous_const
  have hTmem : ∀ w : ℂ, w ∈ Work.Bottcher.CritDomain c →
      Tantibar c w ∈ Work.Bottcher.CritDomain c :=
    fun w hw => Work.Bottcher.CritBasic.Tantibar_mem_CritDomain hw
  -- ## `φ` is the product formula on the exterior of the critical far radius
  have hψ : ∀ w : ℂ, Work.Bottcher.CritBasic.critFarRadius c < ‖w‖ →
      φ w = Work.Bottcher.bottcher c w :=
    fun w hw => Work.Bottcher.Core.eq_bottcher_of_analytic_tail c
      (Work.Bottcher.CritBasic.critFarRadius c)
      (Work.Bottcher.CritBasic.escapeRadius_le_critFarRadius c) φ
      (han.mono (Work.Bottcher.CritBasic.critFar_subset_CritDomain c))
      (fun u hu => hfe u (Work.Bottcher.CritBasic.critFar_subset_CritDomain c hu))
      (fun u hu => hmod u (Work.Bottcher.CritBasic.critFar_subset_CritDomain c hu))
      has w hw
  -- ## the ratio `K` on the far region is `1`
  have hfar : ∀ z : ℂ, Work.Bottcher.CritBasic.critFarRadius c < ‖z‖ →
      (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2 = 1 := by
    intro z hz
    have hRpos : 0 < Work.Bottcher.CritBasic.critFarRadius c :=
      Work.Bottcher.CritBasic.critFarRadius_pos c
    have hzle : Work.Bottcher.escapeRadius c ≤ ‖z‖ :=
      le_trans (Work.Bottcher.CritBasic.escapeRadius_le_critFarRadius c) (le_of_lt hz)
    have hTzfar : Work.Bottcher.CritBasic.critFarRadius c < ‖Tantibar c z‖ := by
      have h2 : 2 * ‖z‖ ≤ ‖Tantibar c z‖ := by
        have h := (Work.Bottcher.Core.escapeRadius_le_norm_Tantibar_iterate c hzle 1).2
        simpa using h
      have hR2 : Work.Bottcher.CritBasic.critFarRadius c < 2 * ‖z‖ := by linarith
      exact lt_of_lt_of_le hR2 h2
    have hzne : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    have hbne : Work.Bottcher.bottcher c z ≠ 0 := Work.Bottcher.bottcher_ne_zero c hzne
    rw [hψ z hz, hψ (Tantibar c z) hTzfar,
      Work.Bottcher.Core.bottcher_comm_Tantibar_far c z hzle, map_pow, Complex.conj_conj,
      div_self (pow_ne_zero 2 hbne)]
  -- ## continuity of the ratio on the critical domain
  have hKcont : ContinuousOn
      (fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2)
      (Work.Bottcher.CritDomain c) := by
    have hcomp : ContinuousOn (fun w : ℂ => φ (Tantibar c w)) (Work.Bottcher.CritDomain c) :=
      han.continuousOn.comp hTcont.continuousOn (fun w hw => hTmem w hw)
    have hconj : ContinuousOn (fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)))
        (Work.Bottcher.CritDomain c) :=
      Complex.continuous_conj.comp_continuousOn' hcomp
    exact hconj.div (han.continuousOn.pow 2) (fun w hw => pow_ne_zero 2 (hφne w hw))
  -- ## the ratio satisfies `K (p_c z) = K z ^ 4`
  have hK4 : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      (starRingEnd ℂ) (φ (Tantibar c (Work.Bottcher.pMap c z)))
          / (φ (Work.Bottcher.pMap c z)) ^ 2
        = ((starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2) ^ 4 := by
    intro z hz
    have hTz : Tantibar c z ∈ Work.Bottcher.CritDomain c := hTmem z hz
    have hcomm : Tantibar c (Work.Bottcher.pMap c z) = Work.Bottcher.pMap c (Tantibar c z) := by
      simpa using (Work.Bottcher.pMap_iterate_Tantibar c z 1).symm
    rw [hcomm, hfe (Tantibar c z) hTz, hfe z hz, map_pow, div_pow,
      show ((φ z) ^ 2) ^ 4 = ((φ z) ^ 4) ^ 2 by ring]
  -- ## values of the ratio are roots of unity of `2`-power order
  have hKpow : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      ∃ n : ℕ, ((starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2) ^ (2 ^ n) = 1 := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_pMap_iterate_critFar_of_mem_CritDomain c hz
    have hmem : ∀ k : ℕ, (Work.Bottcher.pMap c)^[k] z ∈ Work.Bottcher.CritDomain c :=
      fun k => Work.Bottcher.CritBasic.pMap_iterate_mem_CritDomain hz k
    have hiter : ∀ k : ℕ,
        (starRingEnd ℂ) (φ (Tantibar c ((Work.Bottcher.pMap c)^[k] z)))
            / (φ ((Work.Bottcher.pMap c)^[k] z)) ^ 2
          = ((starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2) ^ (4 ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Function.iterate_succ_apply', hK4 ((Work.Bottcher.pMap c)^[k] z) (hmem k), ih,
            show (4 : ℕ) ^ (k + 1) = 4 ^ k * 4 from pow_succ 4 k, pow_mul]
    refine ⟨2 * m, ?_⟩
    have h2m : (2 : ℕ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    rw [h2m, ← hiter m]
    exact hfar ((Work.Bottcher.pMap c)^[m] z) hm
  -- ## the critical domain is preconnected, so the image of the ratio is a subsingleton
  have hpre : IsPreconnected (Work.Bottcher.CritDomain c) :=
    Work.Bottcher.CritBasic.isPreconnected_CritDomain c
  have himg : IsPreconnected
      ((fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2)
        '' (Work.Bottcher.CritDomain c)) :=
    hpre.image _ hKcont
  have hsub : ((fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2)
        '' (Work.Bottcher.CritDomain c)) ⊆ {ζ : ℂ | ∃ n : ℕ, ζ ^ (2 ^ n) = 1} := by
    rintro ζ ⟨w, hw, rfl⟩
    exact hKpow w hw
  have hsingle := Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one himg hsub
  -- ## a far point of the critical domain, where the ratio is `1`
  set z₀ : ℂ := ((Work.Bottcher.CritBasic.critFarRadius c + 1 : ℝ) : ℂ) with hz₀
  have hz₀norm : ‖z₀‖ = Work.Bottcher.CritBasic.critFarRadius c + 1 := by
    rw [hz₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith [Work.Bottcher.CritBasic.critFarRadius_pos c]
  have hz₀far : Work.Bottcher.CritBasic.critFarRadius c < ‖z₀‖ := by
    rw [hz₀norm]; linarith [Work.Bottcher.CritBasic.critFarRadius_pos c]
  have hz₀U : z₀ ∈ Work.Bottcher.CritDomain c :=
    Work.Bottcher.CritBasic.critFar_subset_CritDomain c hz₀far
  -- ## conclusion
  intro z hz
  have hratio : (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2 = 1 := by
    have h1 : (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2
        = (starRingEnd ℂ) (φ (Tantibar c z₀)) / (φ z₀) ^ 2 :=
      hsingle ⟨z, hz, rfl⟩ ⟨z₀, hz₀U, rfl⟩
    rw [h1, hfar z₀ hz₀far]
  have hconj : (starRingEnd ℂ) (φ (Tantibar c z)) = (φ z) ^ 2 :=
    (div_eq_one_iff_eq (pow_ne_zero 2 (hφne z hz))).mp hratio
  have hfin : (starRingEnd ℂ) ((starRingEnd ℂ) (φ (Tantibar c z)))
      = (starRingEnd ℂ) ((φ z) ^ 2) := congrArg (starRingEnd ℂ) hconj
  rw [map_pow] at hfin
  rw [Complex.conj_conj] at hfin
  exact hfin

end Work.Bottcher.Contraction
