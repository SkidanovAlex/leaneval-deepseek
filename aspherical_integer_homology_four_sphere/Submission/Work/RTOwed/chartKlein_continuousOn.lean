/-
# Continuity of the cube chart `chartKlein`

`chartKlein a q = kleinOfHyp ((chartMat a) *ᵥ hypOfUHS q)` is the Möbius chart of the cube
`a`; in coordinates (`chartKlein_apply` of `Submission/Work/RTOwed/chartKlein_ceiling.lean`)

  `chartKlein a q i = (MV a q 4)⁻¹ * MV a q (castSucc i)`,

so on the region `S = {q | q 3 ≠ 0 ∧ MV a q 4 ≠ 0}` it is built from the continuous functions
`q ↦ MV a q k`.  Indeed `MV a q k = ∑ j, (chartMat a k j : ℝ) * hypOfUHS q j` and the coordinates
of `hypOfUHS q` are (with `‖q‖² = q 0 ² + q 1 ² + q 2 ² + q 3 ²`)

  `q 0 / q 3`, `q 1 / q 3`, `q 2 / q 3`, `(‖q‖² - 1) / (2 * q 3)`, `(‖q‖² + 1) / (2 * q 3)`,

which are continuous wherever `q 3 ≠ 0`.  Hence `q ↦ MV a q k` is continuous on `{q | q 3 ≠ 0}`,
and on `S` we may divide by `MV a q 4`, again a continuous function.
-/
import Mathlib
import Submission.Work.RTOwed.chartKlein_ceiling

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix
open Set Topology Function

namespace Work.RTOwed

/-- **The UHS parametrisation of the hyperboloid is continuous where the height is nonzero**:
each coordinate of `hypOfUHS q` is a quotient with denominator `q 3` (or `2 * q 3`). -/
private lemma continuousOn_hypOfUHS (j : Fin 5) :
    ContinuousOn (fun q : CuspE4 => Work.HypModel.hypOfUHS q j) {q : CuspE4 | q 3 ≠ 0} := by
  fin_cases j
  · exact ContinuousOn.div (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).continuousOn
      (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3).continuousOn (fun q hq => hq)
  · exact ContinuousOn.div (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 1).continuousOn
      (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3).continuousOn (fun q hq => hq)
  · exact ContinuousOn.div (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 2).continuousOn
      (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3).continuousOn (fun q hq => hq)
  · refine ContinuousOn.div ?_ ?_ (fun q hq => mul_ne_zero two_ne_zero hq)
    · fun_prop
    · fun_prop
  · refine ContinuousOn.div ?_ ?_ (fun q hq => mul_ne_zero two_ne_zero hq)
    · fun_prop
    · fun_prop

/-- **The Klein numerator of the chart is continuous where the height is nonzero**: it is the
finite sum `∑ j, (chartMat a k j : ℝ) * hypOfUHS q j`. -/
private lemma continuousOn_MV (a : Fin 48) (k : Fin 5) :
    ContinuousOn (fun q : CuspE4 => MV a q k) {q : CuspE4 | q 3 ≠ 0} := by
  have h : (fun q : CuspE4 => MV a q k) =
      fun q => ∑ j : Fin 5, ((chartMat a k j : ℤ) : ℝ) * Work.HypModel.hypOfUHS q j := by
    funext q
    simp [MV, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  rw [h]
  exact continuousOn_finsetSum Finset.univ
    (fun j _ => ContinuousOn.const_mul (continuousOn_hypOfUHS j) _)

/-- **The chart of the cube `a` is continuous on `{q | q 3 ≠ 0 ∧ MV a q 4 ≠ 0}`.**  In coordinates
the chart is `q ↦ (MV a q 4)⁻¹ * MV a q (castSucc i)`. -/
theorem chartKlein_continuousOn (a : Fin 48) :
    ContinuousOn (Work.RTOwed.chartKlein a)
      {q : Work.RTOwed.CuspE4 | q 3 ≠ 0 ∧ Work.RTOwed.MV a q 4 ≠ 0} := by
  have hS : {q : CuspE4 | q 3 ≠ 0 ∧ MV a q 4 ≠ 0} ⊆ {q : CuspE4 | q 3 ≠ 0} :=
    fun q hq => hq.1
  have h4 : ContinuousOn (fun q : CuspE4 => (MV a q 4)⁻¹)
      {q : CuspE4 | q 3 ≠ 0 ∧ MV a q 4 ≠ 0} :=
    (continuousOn_MV a 4).mono hS |>.inv₀ (fun q hq => hq.2)
  have hg : ContinuousOn
      (fun q : CuspE4 => WithLp.toLp 2 (fun i : Fin 4 => (MV a q 4)⁻¹ * MV a q (Fin.castSucc i)))
      {q : CuspE4 | q 3 ≠ 0 ∧ MV a q 4 ≠ 0} := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).continuousOn.comp ?_
      (fun q _ => Set.mem_univ _)
    refine continuousOn_pi.mpr (fun i => ?_)
    exact h4.mul ((continuousOn_MV a (Fin.castSucc i)).mono hS)
  refine hg.congr (fun q _ => ?_)
  rw [WithLp.ext_iff]
  funext i
  exact chartKlein_apply a q i

end Work.RTOwed
