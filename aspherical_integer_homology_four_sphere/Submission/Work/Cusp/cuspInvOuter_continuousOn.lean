/-
# Continuity of the inverse of the outer cusp chart

The inverse of the outer chart of the filling piece (`Work.Cusp.Basic.cuspInvOuter`) is, for
`q = (x, s) ∈ E4`,

`cuspInvOuter v q = (t • bndOfU (σ-coordinate of x), y(x))`,

where `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`, `β x > 0` is the ceiling height and
`bndOfU` is the boundary parameterisation of the square `[-1,1]²`.

Every ingredient is continuous on the half space `{q | 0 < q 3}`:

* `q ↦ x = (q 0, q 1, q 2)` and `β` (continuous, `Work.Cusp.beta_continuous`),
* `q ↦ log (β x)` (continuous because `β x > 0` everywhere, `Work.Cusp.beta_pos`),
* `q ↦ log s` (continuous on `{s > 0}`),
* the denominator `2 (log β(x) − log s_J)`: since `0 < β x ≤ βMax = 3/2 < s_J`
  (`Work.Cusp.beta_le_max`, `Work.Cusp.betaMax_lt_sJ`), we have `log β(x) < log s_J`, so the
  denominator never vanishes,
* `bndOfU`: it is `cuspF ∘ Int.fract` for the piecewise linear function `cuspF` which is continuous
  on `[0,1]` with `cuspF 0 = cuspF 1`; hence `ContinuousOn.comp_fract''` applies,
* `outerU`, `outerY`, which are linear in `x`.

Consequently `cuspInvOuter v` is continuous on `{q | 0 < q 3}`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.outerU_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace Topology

namespace Work.Cusp

attribute [local fun_prop] outerU_continuous

/-! ### `bndOfU` is continuous

`bndOfU` is the (piecewise linear) parameterisation of the boundary of the square, which visits
`(1,1)`, `(1,-1)`, `(-1,-1)`, `(-1,1)` at the multiples of `1/4`.  We read it as
`cuspF ∘ Int.fract` with `cuspF` the four-branched function below, and prove `cuspF` continuous on
`[0,1]` (the branches match at the breakpoints) and `cuspF 0 = cuspF 1`. -/

/-- The branch on the right edge `u ∈ [0,1/4]`. -/
private def br1 (s : ℝ) : E2 := !₂[(1:ℝ), 1 - 8 * s]
/-- The branch on the bottom edge `u ∈ [1/4,1/2]`. -/
private def br2 (s : ℝ) : E2 := !₂[3 - 8 * s, (-1:ℝ)]
/-- The branch on the left edge `u ∈ [1/2,3/4]`. -/
private def br3 (s : ℝ) : E2 := !₂[(-1:ℝ), 8 * s - 5]
/-- The branch on the top edge `u ∈ [3/4,1]`. -/
private def br4 (s : ℝ) : E2 := !₂[8 * s - 7, (1:ℝ)]

/-- The four-branched function whose composition with `Int.fract` is `bndOfU`. -/
private def cuspF (s : ℝ) : E2 :=
  if s < 1/4 then br1 s
  else if s < 1/2 then br2 s
  else if s < 3/4 then br3 s
  else br4 s

private lemma bndOfU_eq : bndOfU = cuspF ∘ Int.fract := rfl

private lemma br1_continuous : Continuous br1 := by unfold br1; fun_prop
private lemma br2_continuous : Continuous br2 := by unfold br2; fun_prop
private lemma br3_continuous : Continuous br3 := by unfold br3; fun_prop
private lemma br4_continuous : Continuous br4 := by unfold br4; fun_prop

/-- `cuspF` takes the value of its first branch at `1/4` as well. -/
private lemma cuspF_at_quarter : cuspF (1/4) = br1 (1/4) := by
  unfold cuspF br1 br2
  rw [if_neg (by norm_num : ¬ ((1:ℝ)/4 < 1/4)), if_pos (by norm_num : (1:ℝ)/4 < 1/2)]
  norm_num

/-- `cuspF` takes the value of its second branch at `1/2` as well. -/
private lemma cuspF_at_half : cuspF (1/2) = br2 (1/2) := by
  unfold cuspF br2 br3
  rw [if_neg (by norm_num : ¬ ((1:ℝ)/2 < 1/4)), if_neg (by norm_num : ¬ ((1:ℝ)/2 < 1/2)),
    if_pos (by norm_num : (1:ℝ)/2 < 3/4)]
  norm_num

/-- `cuspF` takes the value of its third branch at `3/4` as well. -/
private lemma cuspF_at_threequarter : cuspF (3/4) = br3 (3/4) := by
  unfold cuspF br3 br4
  rw [if_neg (by norm_num : ¬ ((3:ℝ)/4 < 1/4)), if_neg (by norm_num : ¬ ((3:ℝ)/4 < 1/2)),
    if_neg (by norm_num : ¬ ((3:ℝ)/4 < 3/4))]
  norm_num

private lemma cuspF_eqOn_quarter : Set.EqOn cuspF br1 (Set.Icc 0 (1/4)) := by
  intro s hs
  rcases lt_or_eq_of_le hs.2 with h | h
  · rw [cuspF, if_pos h]
  · subst h
    exact cuspF_at_quarter

private lemma cuspF_eqOn_half : Set.EqOn cuspF br2 (Set.Icc (1/4) (1/2)) := by
  intro s hs
  rcases lt_or_eq_of_le hs.2 with h | h
  · rw [cuspF, if_neg (not_lt.mpr hs.1), if_pos h]
  · subst h
    exact cuspF_at_half

private lemma cuspF_eqOn_threequarter : Set.EqOn cuspF br3 (Set.Icc (1/2) (3/4)) := by
  intro s hs
  rcases lt_or_eq_of_le hs.2 with h | h
  · rw [cuspF, if_neg (not_lt.mpr (by linarith [hs.1] : (1:ℝ)/4 ≤ s)),
      if_neg (not_lt.mpr hs.1), if_pos h]
  · subst h
    exact cuspF_at_threequarter

private lemma cuspF_eqOn_one : Set.EqOn cuspF br4 (Set.Icc (3/4) 1) := by
  intro s hs
  rw [cuspF, if_neg (not_lt.mpr (by linarith [hs.1] : (1:ℝ)/4 ≤ s)),
    if_neg (not_lt.mpr (by linarith [hs.1] : (1:ℝ)/2 ≤ s)), if_neg (not_lt.mpr hs.1)]

private lemma cuspF_zero_eq_one : cuspF 0 = cuspF 1 := by
  unfold cuspF br1 br4
  rw [if_pos (by norm_num : (0:ℝ) < 1/4),
    if_neg (by norm_num : ¬ ((1:ℝ) < 1/4)),
    if_neg (by norm_num : ¬ ((1:ℝ) < 1/2)),
    if_neg (by norm_num : ¬ ((1:ℝ) < 3/4))]
  norm_num

private lemma cuspF_continuousOn_Icc : ContinuousOn cuspF (Set.Icc 0 1) := by
  have h1 : ContinuousOn cuspF (Set.Icc 0 (1/4)) :=
    br1_continuous.continuousOn.congr cuspF_eqOn_quarter
  have h2 : ContinuousOn cuspF (Set.Icc (1/4) (1/2)) :=
    br2_continuous.continuousOn.congr cuspF_eqOn_half
  have h3 : ContinuousOn cuspF (Set.Icc (1/2) (3/4)) :=
    br3_continuous.continuousOn.congr cuspF_eqOn_threequarter
  have h4 : ContinuousOn cuspF (Set.Icc (3/4) 1) :=
    br4_continuous.continuousOn.congr cuspF_eqOn_one
  have hc1 : IsClosed (Set.Icc (0:ℝ) (1/4) ∪ Set.Icc (1/4) (1/2)) :=
    isClosed_Icc.union isClosed_Icc
  have hc2 : IsClosed ((Set.Icc (0:ℝ) (1/4) ∪ Set.Icc (1/4) (1/2)) ∪ Set.Icc (1/2) (3/4)) :=
    hc1.union isClosed_Icc
  have h12 : ContinuousOn cuspF (Set.Icc (0:ℝ) (1/4) ∪ Set.Icc (1/4) (1/2)) :=
    h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  have h123 : ContinuousOn cuspF
      ((Set.Icc (0:ℝ) (1/4) ∪ Set.Icc (1/4) (1/2)) ∪ Set.Icc (1/2) (3/4)) :=
    h12.union_of_isClosed h3 hc1 isClosed_Icc
  have h1234 : ContinuousOn cuspF
      (((Set.Icc (0:ℝ) (1/4) ∪ Set.Icc (1/4) (1/2)) ∪ Set.Icc (1/2) (3/4)) ∪ Set.Icc (3/4) 1) :=
    h123.union_of_isClosed h4 hc2 isClosed_Icc
  have hset : ((Set.Icc (0:ℝ) (1/4) ∪ Set.Icc (1/4) (1/2)) ∪ Set.Icc (1/2) (3/4)) ∪ Set.Icc (3/4) 1
      = Set.Icc 0 1 := by
    ext s
    simp only [Set.mem_union, Set.mem_Icc]
    constructor
    · intro h
      rcases h with ((h | h) | h) | h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · intro h
      rcases le_total s (1/4) with h1 | h1
      · exact Or.inl (Or.inl (Or.inl ⟨h.1, h1⟩))
      rcases le_total s (1/2) with h2 | h2
      · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
      rcases le_total s (3/4) with h3 | h3
      · exact Or.inl (Or.inr ⟨h2, h3⟩)
      · exact Or.inr ⟨h3, h.2⟩
  rw [hset] at h1234
  exact h1234

private lemma bndOfU_continuous : Continuous bndOfU := by
  rw [bndOfU_eq]
  exact ContinuousOn.comp_fract'' cuspF_continuousOn_Icc cuspF_zero_eq_one

/-! ### The main theorem -/

theorem cuspInvOuter_continuousOn (v : Fin 5) :
    ContinuousOn (cuspInvOuter v) {q : E4 | 0 < q 3} := by
  have hX : Continuous (fun q : E4 => (!₂[q 0, q 1, q 2] : E3)) := by fun_prop
  have hb : Continuous (fun q : E4 => beta (!₂[q 0, q 1, q 2] : E3)) :=
    beta_continuous.comp hX
  have hlogb : Continuous (fun q : E4 => Real.log (beta (!₂[q 0, q 1, q 2] : E3))) :=
    Real.continuousOn_log.comp_continuous hb (fun q => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (beta_pos _))
  have hden_ne : ∀ q : E4, 2 * (Real.log (beta (!₂[q 0, q 1, q 2] : E3)) - Real.log sJ) ≠ 0 := by
    intro q h
    have hlt : Real.log (beta (!₂[q 0, q 1, q 2] : E3)) < Real.log sJ :=
      Real.log_lt_log (beta_pos _) (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
    linarith
  have hden : Continuous (fun q : E4 =>
      2 * (Real.log (beta (!₂[q 0, q 1, q 2] : E3)) - Real.log sJ)) :=
    continuous_const.mul (hlogb.sub continuous_const)
  have hlog3 : ContinuousOn (fun q : E4 => Real.log (q 3)) {q : E4 | 0 < q 3} :=
    Real.continuousOn_log.comp (by fun_prop : Continuous (fun q : E4 => q 3)).continuousOn
      (fun q hq => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hq)
  have hnum : ContinuousOn (fun q : E4 =>
      Real.log (q 3) - Real.log (beta (!₂[q 0, q 1, q 2] : E3))) {q : E4 | 0 < q 3} :=
    hlog3.sub hlogb.continuousOn
  have hT : ContinuousOn (fun q : E4 =>
      1 + (Real.log (q 3) - Real.log (beta (!₂[q 0, q 1, q 2] : E3))) /
        (2 * (Real.log (beta (!₂[q 0, q 1, q 2] : E3)) - Real.log sJ)))
      {q : E4 | 0 < q 3} :=
    continuousOn_const.add (hnum.div hden.continuousOn (fun q _ => hden_ne q))
  have hbnd : ContinuousOn (fun q : E4 => bndOfU (outerU v (!₂[q 0, q 1, q 2] : E3)))
      {q : E4 | 0 < q 3} :=
    ((bndOfU_continuous.comp (outerU_continuous v)).comp hX).continuousOn
  have hY : ContinuousOn (fun q : E4 => outerY v (!₂[q 0, q 1, q 2] : E3)) {q : E4 | 0 < q 3} := by
    have hc : Continuous (fun x : E3 => outerY v x) := by
      unfold outerY kappaCoord
      fun_prop
    exact (hc.comp hX).continuousOn
  have hfin := (hT.smul hbnd).prodMk hY
  exact hfin

end Work.Cusp
