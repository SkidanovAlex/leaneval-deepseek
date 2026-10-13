import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

/-- If `g` is differentiable at `0` and `g 0 = 0`, then the odd extension
`θ ↦ if 0 ≤ θ then g θ else -g (-θ)` is differentiable at `0` with the same derivative. -/
theorem hasDerivAt_oddExtension_zero {g : ℝ → ℝ} {d : ℝ} (h0 : g 0 = 0)
    (hg : HasDerivAt g d 0) :
    HasDerivAt (fun θ : ℝ => if 0 ≤ θ then g θ else -g (-θ)) d 0 := by
  -- Write `F` for the odd extension and split `ℝ` into the two closed halves.
  set F : ℝ → ℝ := fun θ => if 0 ≤ θ then g θ else -g (-θ) with hF
  -- On `[0, ∞)` the odd extension agrees with `g`, hence has derivative `d` from the right.
  have hright : HasDerivWithinAt F d (Set.Ici 0) 0 := by
    refine (hg.hasDerivWithinAt).congr ?_ ?_
    · intro y hy
      exact ite_eq_left hy
    · simp [F]
  -- On `(-∞, 0]` it agrees with `θ ↦ -g (-θ)`, which has derivative `d` at `0`
  -- (chain rule with `θ ↦ -θ`, whose derivative is `-1`).
  have hleft : HasDerivWithinAt F d (Set.Iic 0) 0 := by
    have hg' : HasDerivAt g d (-(0 : ℝ)) := by simpa using hg
    have hgn : HasDerivAt (fun θ : ℝ => g (-θ)) (d * (-1)) 0 :=
      hg'.comp 0 (hasDerivAt_neg 0)
    have hG : HasDerivAt (fun θ : ℝ => -(g (-θ))) d 0 := by
      have h1 : HasDerivAt (fun θ : ℝ => -(g (-θ))) (-(d * (-1))) 0 := hgn.neg
      exact h1.congr_deriv (by ring)
    refine hG.hasDerivWithinAt.congr ?_ ?_
    · intro y hy
      have hy' : y ≤ 0 := hy
      rcases lt_or_eq_of_le hy' with hlt | heq
      · simp only [F]
        exact ite_eq_right (not_le.mpr hlt)
      · subst heq
        simp [F, h0]
    · simp [F, h0]
  -- Glue the two one-sided derivatives; they cover `ℝ`.
  have hunion : HasDerivWithinAt F d (Set.Ici (0 : ℝ) ∪ Set.Iic 0) 0 :=
    hright.union hleft
  have hU : Set.Ici (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_univ, iff_true]
    exact le_total 0 x
  rw [hU] at hunion
  exact hasDerivWithinAt_univ.mp hunion

end Work.FTS.BSIdent.Weyl.Levels
