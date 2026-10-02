import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.Escape.continuous_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.NAKANE.GreenJoint

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The joint iterates `(c,z) ↦ (Tantibar c)^[n] z`

`Tantibar c z = star z ^ 2 + c`, so the pair `(c,z) ↦ ((Tantibar c)^[n] z)` is a polynomial in
`c`, `z` and `star z`; in particular it is continuous.  This is all that is needed for the
continuity of the partial Green functions. -/

theorem continuous_jointIter (n : ℕ) :
    Continuous fun p : ℂ × ℂ => (Tantibar p.1)^[n] p.2 := by
  induction n with
  | zero => simpa using continuous_snd
  | succ n ih =>
    have hfun : (fun p : ℂ × ℂ => (Tantibar p.1)^[n + 1] p.2)
        = fun p : ℂ × ℂ => (starRingEnd ℂ ((Tantibar p.1)^[n] p.2)) ^ 2 + p.1 := by
      funext p
      simp only [Function.iterate_succ_apply', LeanEval.ComplexAnalysis.Tantibar]
    rw [hfun]
    exact ((continuous_star.comp ih).pow 2).add continuous_fst

/-! ## The partial Green functions of the tricorn family

`(c,z) ↦ greenIter (Tantibar c) 2 z n = 2⁻ⁿ log⁺ ‖(Tantibar c)^[n] z‖` is continuous, being the
composition of the continuous joint iterate with `w ↦ 2⁻ⁿ log⁺ ‖w‖`. -/

theorem continuous_greenIter_joint (n : ℕ) :
    Continuous fun p : ℂ × ℂ => Work.Escape.greenIter (Tantibar p.1) 2 p.2 n := by
  have hfun : (fun p : ℂ × ℂ => Work.Escape.greenIter (Tantibar p.1) 2 p.2 n)
      = fun p : ℂ × ℂ => ((2 : ℝ) ^ n)⁻¹ * Real.log (max 1 ‖(Tantibar p.1)^[n] p.2‖) := by
    funext p
    simp only [Work.Escape.greenIter_def, Work.Escape.logPos_def, Nat.cast_ofNat]
  rw [hfun]
  refine continuous_const.mul ?_
  refine Continuous.log ?_ ?_
  · exact continuous_const.max (continuous_jointIter n).norm
  · intro p
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖(Tantibar p.1)^[n] p.2‖))

/-! ## Uniform convergence on `{‖c‖ ≤ C} × ℂ`

On the block `‖c‖ ≤ C` the escape radii `R_c = max (2 C) 2` are uniformly bounded, and the
uniform tail bound `Work.Escape.abs_green_sub_greenIter_le` applies simultaneously to every
parameter `c` with `‖c‖ ≤ C` and every `z : ℂ`.  Hence the partial Green functions converge
uniformly to `jointGreen` on that block. -/

theorem tendstoUniformlyOn_greenIter_joint (C : ℝ) (hC : 0 ≤ C) :
    TendstoUniformlyOn (fun n p => Work.Escape.greenIter (Tantibar p.1) 2 p.2 n)
      jointGreen atTop {p : ℂ × ℂ | ‖p.1‖ ≤ C} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) := by
    have h1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
    have h2 : (2 : ℝ)⁻¹ < 1 := by norm_num
    simpa [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one h1 h2
  have hmul : Tendsto (fun n : ℕ =>
      (2 * (Work.Escape.logPos (max (2 * C) 2) + Real.log (2 * (max (2 * C) 2) ^ 2)))
        * ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) := by
    simpa using hpow.const_mul
      (2 * (Work.Escape.logPos (max (2 * C) 2) + Real.log (2 * (max (2 * C) 2) ^ 2)))
  filter_upwards [hmul.eventually_lt_const hε] with n hn
  intro p hp
  have hR : max 2 ‖p.1‖ ≤ max (2 * C) 2 := by
    refine max_le (le_max_right _ _) ?_
    calc ‖p.1‖ ≤ C := hp
      _ ≤ 2 * C := by linarith
      _ ≤ max (2 * C) 2 := le_max_left _ _
  have hb := Work.Escape.abs_green_sub_greenIter_le (Tantibar p.1) 2 ‖p.1‖ (max (2 * C) 2)
    (Work.Escape.monicGrowth_Tantibar p.1) le_rfl hR p.2 n
  have hdist : dist (jointGreen p) (Work.Escape.greenIter (Tantibar p.1) 2 p.2 n)
      = |Work.Escape.green (Tantibar p.1) 2 p.2
          - Work.Escape.greenIter (Tantibar p.1) 2 p.2 n| := by
    rw [Real.dist_eq]
    rfl
  rw [hdist]
  exact lt_of_le_of_lt hb hn

/-! ## The main theorem -/

/-- **Joint continuity of the Green function of the tricorn family.**  `(c,z) ↦ G_c z` is
continuous on `ℂ × ℂ`.

Route: `jointGreen (c,z) = Work.Escape.green (Tantibar c) 2 z = limUnder_n (greenIter ...)`, and
`Work.Escape.abs_green_sub_greenIter_le` gives, for every `R ≥ max 2 ‖c‖` and every `z`,
`|green (Tantibar c) 2 z - greenIter (Tantibar c) 2 z n| ≤ 2 (log⁺R + log (2 R^2)) * (2^n)⁻¹`
uniformly in `z` (the bound `greenIter_step_abs_le` underlying it is uniform over `ℂ`).  Hence on
`{‖c‖ ≤ C}` with `R := max (2*C) 2` the partial Green functions converge uniformly in `(c,z)`, and
each partial Green function `(c,z) ↦ 2⁻ⁿ log⁺ ‖(Tantibar c)^[n] z‖` is continuous (composition of
continuous maps), so the limit is continuous on `{‖c‖ ≤ C} × ℂ`; the sets `{‖c‖ ≤ C}` cover `ℂ`, so
continuity is local and holds globally. -/
theorem continuous_jointGreen : Continuous Work.NAKANE.jointGreen := by
  rw [continuous_iff_continuousAt]
  intro p
  have hOn : ContinuousOn Work.NAKANE.jointGreen {q : ℂ × ℂ | ‖q.1‖ ≤ ‖p.1‖ + 1} :=
    (tendstoUniformlyOn_greenIter_joint (‖p.1‖ + 1) (by positivity)).continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
        (continuous_greenIter_joint n).continuousOn))
  refine hOn.continuousAt ?_
  have hopen : IsOpen {q : ℂ × ℂ | ‖q.1‖ < ‖p.1‖ + 1} :=
    isOpen_lt continuous_fst.norm continuous_const
  exact Filter.mem_of_superset (hopen.mem_nhds (by simp))
    fun q hq => by
      simp only [Set.mem_ofPred_eq] at hq ⊢
      exact le_of_lt hq

end Work.NAKANE.GreenJoint
