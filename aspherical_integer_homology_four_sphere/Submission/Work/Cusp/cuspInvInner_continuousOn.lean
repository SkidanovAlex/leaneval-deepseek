/-
# Continuity of the inverse of the inner (polar/core) chart

`cuspInvInner v : E4 → E2 × E2` (`Work.Cusp.Basic`) is the explicit inverse of the inner charts
`ThetaPolar v`/`ThetaCore v` of the `v`-th cusp: from the polar coordinates `q = (r,θ,w₁,w₂)` it
recovers `y = invY v (w)` from `w`, the perimeter parameter

`u = (θ − 2π⟪y,σ_v⟫/‖σ_v‖²)/(2π)`

from the angle, and the layer parameter `t = ‖p‖∞` from `r` — by `t = r/2r_J` in the inner region
`r ≤ r_J` and by inverting the junction height `s = e^{R₀−r} = β^{2t−1} s_J^{2−2t}` in the collar
`r ≥ r_J` — and finally returns `(t • bndOfU u, y)`.

This file proves the requested statement: `cuspInvInner v` is continuous on the polar box
`{q | 1/4 < q 0}`.  In fact it is continuous everywhere, and we prove that.

The two points worth recording are that the maps involved really are continuous:

* `bndOfU : ℝ → ∂Sq` is the parametrisation of the boundary of the square by the perimeter
  parameter.  It is *piecewise affine* with a switch at the quarter multiples of `1` (and `1`-
  periodic); the four branches take the same value at the four corners, so although `Int.fract` is
  discontinuous at the integers, the composite `bndOfU = F ∘ Int.fract` is continuous
  (`ContinuousOn.comp_fract''`).  This is the only place where `fun_prop` alone does not suffice.

* the layer parameter `t` is a two-branch function: `t = r/(2r_J)` for `r ≤ r_J` and
  `t = 1 + (R₀ − r − log β)/(2(log β − log s_J))` for `r ≥ r_J`.  Each branch is continuous, the
  common boundary is the level `r = r_J`, and there the two branches agree *for every value of the
  ceiling* `β ∈ [β_min, β_max]` (because `R₀ − r_J = log s_J`): both are `1/2`.  Hence
  `Continuous.if` glues the two branches, and `t` is continuous.  (Equivalently: writing
  `A = r − r_J` and `D = log s_J − log β > 0`, the branches are `1/2 + A/(2r_J)` and
  `1/2 + A/(2D)`, and since `0 < D < r_J` the selection at `r_J` is exactly where the two graphs
  cross — so no jump occurs.)

The pinching data used: `β x ∈ [√(3/2), 3/2]` (`beta_min_le`, `beta_le_max`), hence
`1 < β x < s_J = e^{1/2}` (`betaMax_lt_sJ`), so `log β − log s_J < 0` never vanishes and all the
divisions above are by nonzero quantities.  Note that the restriction `1/4 < q 0` of the statement
is not needed for the continuity itself; it is the region on which the chart is applied.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Real InnerProductSpace

namespace Work.Cusp

noncomputable section

/-! ### The parametrisation `bndOfU` of `∂Sq` is continuous

`bndOfU u` depends on `u` only through `Int.fract u` and is the `1`-periodic function

`bndOfU u = if fract u < 1/4 then (1, 1 − 8·fract u) else if … else (8·fract u − 7, 1)`.

We name the four affine branches `bndF1 … bndF4` and the nested piecewise functions
`bndG3, bndG2, bndG1` obtained by adding one branch at a time; each is continuous by
`Continuous.if`, whose boundary condition is the agreement of the two adjacent branches at the
corner where they meet. -/

private def bndF1 (s : ℝ) : E2 := !₂[(1 : ℝ), 1 - 8 * s]
private def bndF2 (s : ℝ) : E2 := !₂[3 - 8 * s, (-1 : ℝ)]
private def bndF3 (s : ℝ) : E2 := !₂[(-1 : ℝ), 8 * s - 5]
private def bndF4 (s : ℝ) : E2 := !₂[8 * s - 7, (1 : ℝ)]
private def bndG3 (s : ℝ) : E2 := if s < 3 / 4 then bndF3 s else bndF4 s
private def bndG2 (s : ℝ) : E2 := if s < 1 / 2 then bndF2 s else bndG3 s
private def bndG1 (s : ℝ) : E2 := if s < 1 / 4 then bndF1 s else bndG2 s

/-- The tent function defining `bndOfU` has the same value at the endpoints `0` and `1` of the
period, so `bndG1 ∘ Int.fract` is the `1`-periodic extension of `bndG1`. -/
private lemma bndG1_zero_eq_one : bndG1 0 = bndG1 1 := by
  simp only [bndG1, bndG2, bndG3, bndF1, bndF4]
  norm_num

/-- `bndG1` is the nested piecewise function of the four affine branches of `bndOfU`. -/
private lemma bndG1_cont : Continuous bndG1 := by
  have h3 : Continuous bndG3 := by
    unfold bndG3
    refine Continuous.if ?_ ?_ ?_
    · intro s hs
      have hs' : s ∈ frontier (Set.Iio (3 / 4 : ℝ)) := hs
      rw [frontier_Iio] at hs'
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      simp only [bndF3, bndF4]
      norm_num
    · unfold bndF3; fun_prop
    · unfold bndF4; fun_prop
  have h2 : Continuous bndG2 := by
    unfold bndG2
    refine Continuous.if ?_ ?_ h3
    · intro s hs
      have hs' : s ∈ frontier (Set.Iio (1 / 2 : ℝ)) := hs
      rw [frontier_Iio] at hs'
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      simp only [bndF2]
      rw [show bndG3 (1 / 2) = bndF3 (1 / 2) from by
        simp only [bndG3]
        rw [ite_eq_left (by norm_num : (1 : ℝ) / 2 < 3 / 4)]]
      simp only [bndF3]
      norm_num
    · unfold bndF2; fun_prop
  unfold bndG1
  refine Continuous.if ?_ ?_ h2
  · intro s hs
    have hs' : s ∈ frontier (Set.Iio (1 / 4 : ℝ)) := hs
    rw [frontier_Iio] at hs'
    simp only [Set.mem_singleton_iff] at hs'
    subst hs'
    simp only [bndF1]
    rw [show bndG2 (1 / 4) = bndF2 (1 / 4) from by
      simp only [bndG2]
      rw [ite_eq_left (by norm_num : (1 : ℝ) / 4 < 1 / 2)]]
    simp only [bndF2]
    norm_num
  · unfold bndF1; fun_prop

/-- **`bndOfU` is the `Int.fract`-pullback of the nested piecewise function `bndG1`.** -/
private lemma bndOfU_eq : bndOfU = bndG1 ∘ Int.fract :=
  funext fun _ => rfl

/-- **The parametrisation `bndOfU` of `∂Sq` by the perimeter parameter is continuous.**  It is the
composition of `Int.fract` (discontinuous at the integers) with the nested piecewise function
`bndG1`, whose four affine branches agree at the four corners of the square; the agreement at `0`
and `1` makes the composition continuous (`ContinuousOn.comp_fract''`). -/
private lemma bndOfU_cont : Continuous bndOfU := by
  have h : Continuous (bndG1 ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (f := bndG1) bndG1_cont.continuousOn bndG1_zero_eq_one
  rwa [bndOfU_eq]

/-! ### The components of `cuspInvInner` -/

/-- The `y`-part `invY v (w)` of `cuspInvInner`. -/
private def cY (v : Fin 5) (q : E4) : E2 := invY v !₂[q 2, q 3]

/-- The perimeter parameter `u` recovered from the polar coordinates. -/
private def cUU (v : Fin 5) (q : E4) : ℝ :=
  (q 1 - 2 * π * (⟪cuspY v (cY v q), slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)

/-- The ceiling `β` evaluated at the cusp coordinate of the recovered perimeter parameter. -/
private def cB (v : Fin 5) (q : E4) : ℝ := beta (cuspX v (cUU v q) (cY v q))

/-- The inner branch `t = r/(2r_J)` of the layer parameter (`r ≤ r_J`). -/
private def cT1 (_v : Fin 5) (q : E4) : ℝ := q 0 / (2 * rJ)

/-- The collar branch `t = 1 + (R₀ − r − log β)/(2 (log β − log s_J))` of the layer parameter
(`r ≥ r_J`). -/
private def cT2 (v : Fin 5) (q : E4) : ℝ :=
  1 + (R0 - q 0 - Real.log (cB v q)) / (2 * (Real.log (cB v q) - Real.log sJ))

/-- The layer parameter of the inverse inner chart: `cT1` in the inner region and `cT2` in the
collar, selected by the junction level `r_J`. -/
private def cT (v : Fin 5) (q : E4) : ℝ := if q 0 ≤ rJ then cT1 v q else cT2 v q

private lemma cY_cont (v : Fin 5) : Continuous (cY v) := by unfold cY invY; fun_prop

private lemma cUU_cont (v : Fin 5) : Continuous (cUU v) := by
  unfold cUU cY invY cuspY; fun_prop

private lemma cuspX_cont (v : Fin 5) :
    Continuous (fun q : E4 => cuspX v (cUU v q) (cY v q)) := by
  unfold cuspX cUU cY invY cuspY
  fun_prop

private lemma cB_cont (v : Fin 5) : Continuous (cB v) := by
  unfold cB
  exact beta_continuous.comp (cuspX_cont v)

/-! ### The pinching data: `1 < β x < s_J` -/

private lemma one_lt_betaMin : (1 : ℝ) < betaMin := by
  rw [betaMin, Real.lt_sqrt (by norm_num)]
  norm_num

private lemma one_lt_cB (v : Fin 5) (q : E4) : 1 < cB v q := by
  unfold cB
  exact lt_of_lt_of_le one_lt_betaMin (beta_min_le _)

private lemma cB_lt_sJ (v : Fin 5) (q : E4) : cB v q < sJ := by
  unfold cB
  exact lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ

/-- `log β` never equals `log s_J`, so the denominator of the collar branch never vanishes. -/
private lemma log_cB_ne (v : Fin 5) (q : E4) : Real.log (cB v q) ≠ Real.log sJ :=
  ne_of_lt (Real.log_lt_log (by linarith [one_lt_cB v q]) (cB_lt_sJ v q))

private lemma log_cB_cont (v : Fin 5) : Continuous (fun q : E4 => Real.log (cB v q)) :=
  continuous_iff_continuousAt.mpr fun q =>
    (cB_cont v).continuousAt.log (ne_of_gt (lt_trans zero_lt_one (one_lt_cB v q)))

/-- **The two branches of the layer parameter agree at the junction `r = r_J`**, for every value of
the ceiling: `r_J/(2r_J) = 1 + (R₀ − r_J − log b)/(2(log b − log s_J))` (both sides are `1/2`),
using `R₀ − r_J = log s_J = 1/2`. -/
private lemma branch_eq_at_junction (b : ℝ) (hb : Real.log b ≠ Real.log sJ) :
    rJ / (2 * rJ) = 1 + (R0 - rJ - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
  have hsJ : Real.log sJ = 1 / 2 := by rw [sJ, Real.log_exp]
  have hR0 : R0 - rJ = 1 / 2 := by norm_num [R0, rJ]
  have hlhs : rJ / (2 * rJ) = 1 / 2 := by norm_num [rJ]
  have hb' : Real.log b ≠ 1 / 2 := fun h => hb (by rw [hsJ, h])
  rw [hlhs, hR0, hsJ]
  rw [show (1 : ℝ) / 2 - Real.log b = -(Real.log b - 1 / 2) by ring]
  have hden : 2 * (Real.log b - 1 / 2) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.mpr hb')
  have hX : (Real.log b - 1 / 2) / (2 * (Real.log b - 1 / 2)) = 1 / 2 := by
    rw [div_eq_div_iff hden two_ne_zero]
    ring
  rw [neg_div, hX]
  norm_num

/-! ### Continuity of the layer parameter -/

private lemma cT1_cont (v : Fin 5) : Continuous (cT1 v) := by unfold cT1; fun_prop

private lemma cT2_cont (v : Fin 5) : Continuous (cT2 v) := by
  have hlog := log_cB_cont v
  have hne : ∀ q : E4, 2 * (Real.log (cB v q) - Real.log sJ) ≠ 0 :=
    fun q => mul_ne_zero two_ne_zero (sub_ne_zero.mpr (log_cB_ne v q))
  have hnum : Continuous (fun q : E4 => R0 - q 0 - Real.log (cB v q)) :=
    (continuous_const.sub (by fun_prop : Continuous fun q : E4 => q 0)).sub hlog
  have hden : Continuous (fun q : E4 => 2 * (Real.log (cB v q) - Real.log sJ)) :=
    continuous_const.mul (hlog.sub continuous_const)
  unfold cT2
  exact continuous_const.add (hnum.div hden hne)

/-- **The layer parameter `t` is continuous**: the two branches `cT1`/`cT2` are continuous and they
agree on the frontier `{q | q 0 = r_J}` of the branch condition `q 0 ≤ r_J`
(`frontier_le_subset_eq`), which `Continuous.if` needs. -/
private lemma cT_cont (v : Fin 5) : Continuous (cT v) := by
  unfold cT
  refine Continuous.if (p := fun q : E4 => q 0 ≤ rJ) (f := cT1 v) (g := cT2 v) ?_ ?_ ?_
  · intro q hq
    have h0 : q 0 = rJ :=
      frontier_le_subset_eq (by fun_prop : Continuous fun q : E4 => q 0) continuous_const hq
    unfold cT1 cT2
    rw [h0]
    exact branch_eq_at_junction (cB v q) (log_cB_ne v q)
  · exact cT1_cont v
  · exact cT2_cont v

/-! ### The inverse inner chart -/

/-- **`cuspInvInner v` is the assembling of the components above**, definitionally: the `let`-chain
of `Work.Cusp.cuspInvInner` is exactly `(cT • bndOfU cUU, cY)`. -/
private lemma cuspInvInner_eq (v : Fin 5) :
    cuspInvInner v = fun q : E4 => (cT v q • bndOfU (cUU v q), cY v q) :=
  rfl

/-- **The inverse of the inner chart is continuous on all of `E4`.** -/
theorem continuous_cuspInvInner (v : Fin 5) : Continuous (cuspInvInner v) := by
  have hbnd : Continuous (fun q : E4 => bndOfU (cUU v q)) := bndOfU_cont.comp (cUU_cont v)
  have hprod : Continuous (fun q : E4 => (cT v q • bndOfU (cUU v q), cY v q)) :=
    ((cT_cont v).smul hbnd).prodMk (cY_cont v)
  simpa only [cuspInvInner_eq v] using hprod

/-- **The requested statement.**  The inverse of the inner (polar/core) chart is continuous on the
polar box `{q : E4 | 1/4 < q 0}` (indeed on all of `E4`, see `continuous_cuspInvInner`). -/
theorem cuspInvInner_continuousOn (v : Fin 5) :
    ContinuousOn (cuspInvInner v) {q : E4 | 1/4 < q 0} :=
  (continuous_cuspInvInner v).continuousOn

end

end Work.Cusp
