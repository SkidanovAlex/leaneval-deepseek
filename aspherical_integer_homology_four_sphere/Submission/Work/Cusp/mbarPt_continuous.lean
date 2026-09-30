/-
# Continuity of the ceiling map `mbarPt : E3 → M̄`

`CuspGlueData.mbarPt` is the ceiling composed with the cusp coordinate,
`mbarPt x = mbarLow (ceilingPt x)` (`CuspGlueData.mbarPt_eq`), where `ceilingPt x = (x, β x)` is the
point of the UHS coordinate space over the ceiling: the point of the truncation torus `T_v` with
cusp coordinate `x`.

`mbarLow` is a chart of `M̄` — hence continuous — only on the parts of the *boxes* `cuspBoxTop v c δ`
that lie below the ceiling (`CuspGlueData.mbarLow_contTop`); it is not a globally continuous function
of the UHS coordinate (its chimney meets the boundary of `M̄` at the truncation torus).  Continuity of
`mbarPt` therefore comes from the fact that the ceiling point `ceilingPt x` lies in the *interior*
of the box `cuspBoxTop v c δ` around `c` as soon as `|x i - c i| < δ` for all `i`: this needs only
the two bounds `s₁ < β x < sTop` on the ceiling, true for every `x` (`Work.Cusp.s1_lt_beta`,
`Work.Cusp.beta_lt_sTop`), and *not* the meridian slab `0 < outerU v x < 1` which the slabbed box
`cuspChartBox` imposes and which the ceiling of a general `x` need not satisfy.

So the proof is local: around every `x₀`, on the open coordinate box `U = {x | ∀ i, |x i - x₀ i| < 1}`
the map `mbarPt` agrees with `mbarLow ∘ ceilingPt`, which is continuous there by
`ContinuousOn.comp` (`ceilingPt` is continuous by `beta_continuous`, and `U` maps into the domain of
continuity of `mbarLow`).
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.s1_lt_betaMin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology

namespace Work.Cusp

/-- The horizontal part of the ceiling point over `x` is `x`: `ceilingPt` does not move the UHS
coordinate `x`, it only pushes it up to the ceiling `s = β x`. -/
private theorem xOf_ceilingPt (x : E3) : xOf (ceilingPt x) = x := by
  ext i
  fin_cases i <;> simp [xOf, ceilingPt]

/-- **The ceiling map `mbarPt : E3 → M̄` is continuous**.  It is `x ↦ mbarLow (x, β x)`: the ceiling
point over `x` lies in the interior of the unslabbed collar box `cuspBoxTop v x 1` around `x`
(because `s₁ < β x < sTop` for every `x`), where `mbarLow` is continuous. -/
theorem mbarPt_continuous (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v) :
    Continuous D.mbarPt := by
  -- the ceiling point depends continuously on `x`
  have hceil : Continuous (ceilingPt : E3 → E4) := by
    have hb : Continuous beta := beta_continuous
    unfold ceilingPt
    fun_prop
  -- the coordinate functionals of `E3` are continuous
  have hproj : ∀ i : Fin 3, Continuous fun x : E3 => x i := by
    intro i
    simpa only [EuclideanSpace.coe_proj] using (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  -- `mbarPt` is the ceiling followed by the chart `mbarLow`
  have hfun : D.mbarPt = fun x : E3 => D.mbarLow (ceilingPt x) := funext D.mbarPt_eq
  rw [hfun, continuous_iff_continuousAt]
  intro x₀
  -- the neighbourhood of `x₀` on which the argument stays inside the collar box
  set U : Set E3 := {x | ∀ i, |x i - x₀ i| < (1 : ℝ)} with hUdef
  have hUopen : IsOpen U := by
    have hEq : U = ⋂ i, ({x : E3 | -(1 : ℝ) < x i - x₀ i} ∩ {x : E3 | x i - x₀ i < 1}) := by
      ext x; simp [U, abs_lt]
    rw [hEq]
    refine isOpen_iInter_of_finite fun i => ?_
    exact (isOpen_lt continuous_const ((hproj i).sub continuous_const)).inter
      (isOpen_lt ((hproj i).sub continuous_const) continuous_const)
  have hx0U : x₀ ∈ U := by intro i; simp
  -- `mbarLow` is continuous on the part of the box below the ceiling
  have hS : ContinuousOn D.mbarLow
      {q : E4 | q ∈ cuspBoxTop v x₀ 1 ∧ q 3 ≤ beta (xOf q)} := D.mbarLow_contTop x₀ 1
  -- the ceiling point of every `x ∈ U` lies in that region
  have hMap : MapsTo ceilingPt U {q : E4 | q ∈ cuspBoxTop v x₀ 1 ∧ q 3 ≤ beta (xOf q)} := by
    intro x hx
    refine ⟨⟨fun i => ?_, ?_, ?_⟩, ?_⟩
    · rw [xOf_ceilingPt]; exact hx i
    · simpa [ceilingPt] using s1_lt_beta x
    · simpa [ceilingPt] using beta_lt_sTop x
    · show (ceilingPt x) 3 ≤ beta (xOf (ceilingPt x))
      rw [xOf_ceilingPt]
      simp [ceilingPt]
  have hcomp : ContinuousOn (D.mbarLow ∘ ceilingPt) U := hS.comp hceil.continuousOn hMap
  have hcontAt : ContinuousAt (D.mbarLow ∘ ceilingPt) x₀ :=
    hcomp.continuousAt (hUopen.mem_nhds hx0U)
  simpa [Function.comp_def] using hcontAt

end Work.Cusp
