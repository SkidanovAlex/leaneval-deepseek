import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Core.bottcher_comm_Tantibar_far
import Submission.Work.ParamRays.isDynBottcher_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

/-!
# The Böttcher equation for `T_c` from the analytic Böttcher coordinate of `p_c`

An analytic function `φ` on the escape set `{G_c > 0}` that solves the Böttcher problem of the
*holomorphic* quartic `p_c = T_c ∘ T_c`,

`φ (p_c z) = φ z ^ 4`,   `‖φ z‖ = exp (G_c z)`,   `φ z / z → 1`,

automatically solves the Böttcher problem of the antiholomorphic quadratic `T_c` itself,

`φ (T_c z) = conj (φ z) ^ 2`.

Proof.  The ratio `K z = conj (φ (T_c z)) / φ z ^ 2` is continuous on the escape set, has modulus
`1` there (because `G_c (T_c z) = 2 G_c z`), satisfies `K (p_c z) = K z ^ 4`, and equals `1` on the
far region `{escapeRadius c < ‖z‖}` — where `φ` is the product formula
(`eq_bottcher_of_analytic`) and the product formula satisfies the equation
(`bottcher_comm_Tantibar_far`).  Since the escape set is preconnected and every `K z` is a root of
unity of `2`-power order (its `p_c`-orbit reaches the far region), `K` is identically `1`.
-/

/-! ## Green function and escape set -/

/-- The `T_c`-iterate of the Green function: `G_c (T_c^n z) = 2^n G_c z`. -/
theorem green_Tantibar_iterate (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Tantibar c)^[n] z) = 2 ^ n * Work.Bottcher.green c z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Work.Bottcher.Green.green_comm, ih, pow_succ]
      ring

/-- The `p_c`-iterate of the Green function: `G_c (p_c^n z) = 4^n G_c z`. -/
theorem green_pMap_iterate (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Work.Bottcher.pMap c)^[n] z) = 4 ^ n * Work.Bottcher.green c z := by
  rw [Work.Bottcher.pMap_iterate, green_Tantibar_iterate]
  congr 1
  rw [pow_mul]
  norm_num

/-- On the closed far region `{escapeRadius c ≤ ‖z‖}` the Green function is positive. -/
theorem green_pos_of_escapeRadius_le (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) : 0 < Work.Bottcher.green c z := by
  rw [Work.Bottcher.Green.green_pos_iff]
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (Work.Bottcher.Core.escapeRadius_pos c) hz
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hmul : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * ‖z‖) atTop atTop := hpow.atTop_mul_const hz0
  exact tendsto_atTop_mono
    (fun n => (Work.Bottcher.Core.escapeRadius_le_norm_Tantibar_iterate c hz n).2) hmul

/-- The closed far region is contained in the escape set. -/
theorem farRegion_subset_escapeSet (c : ℂ) :
    {z : ℂ | Work.Bottcher.escapeRadius c ≤ ‖z‖} ⊆ Work.Bottcher.EscapeSet c :=
  fun _ hz => Work.Bottcher.mem_EscapeSet.mpr (green_pos_of_escapeRadius_le c hz)

/-- Some `p_c`-iterate of an escaping point lies in the open far region. -/
theorem exists_pMap_iterate_far_of_mem_escapeSet (c z : ℂ) (hz : z ∈ Work.Bottcher.EscapeSet c) :
    ∃ n : ℕ, Work.Bottcher.escapeRadius c < ‖(Work.Bottcher.pMap c)^[n] z‖ := by
  have hT : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop :=
    (Work.Bottcher.Green.green_pos_iff c z).mp (Work.Bottcher.mem_EscapeSet.mp hz)
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have h2 : Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] z‖) atTop atTop := hT.comp h2n
  have hev : ∀ᶠ n : ℕ in atTop,
      Work.Bottcher.escapeRadius c < ‖(Tantibar c)^[2 * n] z‖ :=
    h2.eventually (eventually_gt_atTop (Work.Bottcher.escapeRadius c))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  exact ⟨N, by rw [Work.Bottcher.pMap_iterate]; exact hN N le_rfl⟩

/-! ## The main theorem -/

theorem bottcher_comm_Tantibar_of_analytic (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (LeanEval.ComplexAnalysis.Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2 := by
  -- ## Elementary facts
  have hφne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ z ≠ 0 := by
    intro z hz
    have h : 0 < ‖φ z‖ := by rw [hmod z hz]; exact Real.exp_pos _
    exact norm_pos_iff.mp h
  have hTcont : Continuous (Tantibar c) := by
    show Continuous (fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c)
    exact (continuous_star.pow 2).add continuous_const
  have hTmem : ∀ w : ℂ, 0 < Work.Bottcher.green c w → 0 < Work.Bottcher.green c (Tantibar c w) := by
    intro w hw
    rw [Work.Bottcher.Green.green_comm]
    exact mul_pos two_pos hw
  -- ## `φ` is the product formula on the far region
  have hψ : ∀ w : ℂ, Work.Bottcher.escapeRadius c ≤ ‖w‖ → φ w = Work.Bottcher.bottcher c w :=
    fun w hw => Work.Bottcher.Core.eq_bottcher_of_analytic c φ
      (han.mono (farRegion_subset_escapeSet c))
      (fun u hu => hfe u (green_pos_of_escapeRadius_le c hu))
      (fun u hu => hmod u (green_pos_of_escapeRadius_le c hu))
      has hw
  -- ## the ratio `K` on the far region is `1`
  have hfar : ∀ z : ℂ, Work.Bottcher.escapeRadius c < ‖z‖ →
      (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2 = 1 := by
    intro z hz
    have hzle : Work.Bottcher.escapeRadius c ≤ ‖z‖ := le_of_lt hz
    have hzTle : Work.Bottcher.escapeRadius c ≤ ‖Tantibar c z‖ :=
      Work.Bottcher.Core.escapeRadius_le_norm_Tantibar c hzle
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (Work.Bottcher.Core.escapeRadius_pos c) hzle
    have hbne : Work.Bottcher.bottcher c z ≠ 0 :=
      Work.Bottcher.bottcher_ne_zero c (norm_pos_iff.mp hzpos)
    rw [hψ z hzle, hψ (Tantibar c z) hzTle,
      Work.Bottcher.Core.bottcher_comm_Tantibar_far c z hzle, map_pow, Complex.conj_conj,
      div_self (pow_ne_zero 2 hbne)]
  -- ## continuity of the ratio on the escape set
  have hKcont : ContinuousOn
      (fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2)
      (Work.Bottcher.EscapeSet c) := by
    have hcomp : ContinuousOn (fun w : ℂ => φ (Tantibar c w)) (Work.Bottcher.EscapeSet c) :=
      han.continuousOn.comp hTcont.continuousOn
        (fun w hw => Work.Bottcher.mem_EscapeSet.mpr
          (hTmem w (Work.Bottcher.mem_EscapeSet.mp hw)))
    have hconj : ContinuousOn (fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)))
        (Work.Bottcher.EscapeSet c) :=
      Complex.continuous_conj.comp_continuousOn' hcomp
    exact hconj.div (han.continuousOn.pow 2)
      (fun w hw => pow_ne_zero 2 (hφne w (Work.Bottcher.mem_EscapeSet.mp hw)))
  -- ## the ratio satisfies `K (p_c z) = K z ^ 4`
  have hK4 : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      (starRingEnd ℂ) (φ (Tantibar c (Work.Bottcher.pMap c z)))
          / (φ (Work.Bottcher.pMap c z)) ^ 2
        = ((starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2) ^ 4 := by
    intro z hz
    have hTz : 0 < Work.Bottcher.green c (Tantibar c z) := hTmem z hz
    have hcomm : Tantibar c (Work.Bottcher.pMap c z) = Work.Bottcher.pMap c (Tantibar c z) := by
      simpa using (Work.Bottcher.pMap_iterate_Tantibar c z 1).symm
    rw [hcomm, hfe (Tantibar c z) hTz, hfe z hz, map_pow, div_pow,
      show ((φ z) ^ 2) ^ 4 = ((φ z) ^ 4) ^ 2 by ring]
  -- ## values of the ratio are roots of unity of `2`-power order
  have hKpow : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ∃ n : ℕ, ((starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2) ^ (2 ^ n) = 1 := by
    intro z hz
    have hzU : z ∈ Work.Bottcher.EscapeSet c := Work.Bottcher.mem_EscapeSet.mpr hz
    obtain ⟨m, hm⟩ := exists_pMap_iterate_far_of_mem_escapeSet c z hzU
    have hmem : ∀ k : ℕ, 0 < Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) := by
      intro k
      rw [green_pMap_iterate]
      exact mul_pos (by positivity) hz
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
  -- ## the escape set is preconnected, so the image of the ratio is a subsingleton
  have hpre : IsPreconnected (Work.Bottcher.EscapeSet c) := isPreconnected_escapeSet c
  have himg : IsPreconnected
      ((fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2)
        '' (Work.Bottcher.EscapeSet c)) :=
    hpre.image _ hKcont
  have hsub : ((fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2)
        '' (Work.Bottcher.EscapeSet c)) ⊆ {ζ : ℂ | ∃ n : ℕ, ζ ^ (2 ^ n) = 1} := by
    rintro ζ ⟨w, hw, rfl⟩
    exact hKpow w (Work.Bottcher.mem_EscapeSet.mp hw)
  have hsingle := Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one himg hsub
  -- ## a far point of the escape set, where the ratio is `1`
  set z₀ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hz₀
  have hz₀norm : ‖z₀‖ = Work.Bottcher.escapeRadius c + 1 := by
    rw [hz₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith [Work.Bottcher.Core.escapeRadius_pos c]
  have hz₀far : Work.Bottcher.escapeRadius c < ‖z₀‖ := by
    rw [hz₀norm]; linarith [Work.Bottcher.Core.escapeRadius_pos c]
  have hz₀U : z₀ ∈ Work.Bottcher.EscapeSet c :=
    Work.Bottcher.mem_EscapeSet.mpr (green_pos_of_escapeRadius_le c (le_of_lt hz₀far))
  -- ## conclusion
  intro z hz
  have hzU : z ∈ Work.Bottcher.EscapeSet c := Work.Bottcher.mem_EscapeSet.mpr hz
  have hratio : (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2 = 1 := by
    have h1 : (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2
        = (starRingEnd ℂ) (φ (Tantibar c z₀)) / (φ z₀) ^ 2 :=
      hsingle ⟨z, hzU, rfl⟩ ⟨z₀, hz₀U, rfl⟩
    rw [h1, hfar z₀ hz₀far]
  have hconj : (starRingEnd ℂ) (φ (Tantibar c z)) = (φ z) ^ 2 :=
    (div_eq_one_iff_eq (pow_ne_zero 2 (hφne z hz))).mp hratio
  have hfin : (starRingEnd ℂ) ((starRingEnd ℂ) (φ (Tantibar c z)))
      = (starRingEnd ℂ) ((φ z) ^ 2) := congrArg (starRingEnd ℂ) hconj
  rw [map_pow] at hfin
  rw [Complex.conj_conj] at hfin
  exact hfin

end Work.Bottcher.Contraction
