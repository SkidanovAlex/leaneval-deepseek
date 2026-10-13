import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open Filter
open scoped Topology

/-- If `g x = 0` and the derivative of `g` at `x` is nonzero, then `x` is an isolated
zero of `g`: there is a ball around `x` on which `g` does not vanish except at `x`. -/
private lemma exists_ball_ne_zero_of_deriv_ne_zero (g : ℝ → ℝ) {x : ℝ} (hgx : g x = 0)
    (hd : deriv g x ≠ 0) :
    ∃ ε > 0, ∀ y, y ≠ x → |y - x| < ε → g y ≠ 0 := by
  have hdiff : DifferentiableAt ℝ g x := by
    by_contra h
    exact hd (deriv_zero_of_not_differentiableAt h)
  have hderiv : HasDerivAt g (deriv g x) x := hasDerivAt_deriv_iff.mpr hdiff
  have hev_slope : ∀ᶠ y in 𝓝[≠] x, slope g x y ≠ 0 :=
    hderiv.tendsto_slope.eventually (isOpen_ne.mem_nhds hd)
  have hev : ∀ᶠ y in 𝓝[≠] x, g y ≠ 0 := by
    filter_upwards [hev_slope] with y hy hy0
    exact hy (by simp [slope_def_module, hy0, hgx])
  have hev2 : ∀ᶠ y in 𝓝 x, y ≠ x → g y ≠ 0 := (eventually_nhdsWithin_iff).1 hev
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev2
  refine ⟨ε, hεpos, fun y hyne hylt => ?_⟩
  exact hε (by rw [Real.dist_eq]; exact hylt) hyne

/-- The set of points where a function vanishes but has nonzero derivative is countable.
Each such point is an isolated (hence rational) interval away from the others, and there
are only countably many rational intervals. -/
theorem zero_set_deriv_countable (g : ℝ → ℝ) :
    {x : ℝ | g x = 0 ∧ deriv g x ≠ 0}.Countable := by
  have hloc : ∀ x : ℝ, g x = 0 → deriv g x ≠ 0 →
      ∃ ε > 0, ∀ y, y ≠ x → |y - x| < ε → g y ≠ 0 :=
    fun x hgx hd => exists_ball_ne_zero_of_deriv_ne_zero g hgx hd
  have hex : ∀ x : {x : ℝ | g x = 0 ∧ deriv g x ≠ 0},
      ∃ q : ℚ × ℚ, (x : ℝ) ∈ Set.Ioo (q.1 : ℝ) (q.2 : ℝ) ∧
        (Set.Ioo (q.1 : ℝ) (q.2 : ℝ) ∩ {x : ℝ | g x = 0 ∧ deriv g x ≠ 0}) ⊆ {(x.1)} := by
    intro x
    obtain ⟨ε, hεpos, hε⟩ := hloc x.1 x.2.1 x.2.2
    obtain ⟨a, ha, ha'⟩ := exists_rat_btwn (show (x:ℝ) - ε < (x:ℝ) by linarith)
    obtain ⟨b, hb, hb'⟩ := exists_rat_btwn (show (x:ℝ) < (x:ℝ) + ε by linarith)
    refine ⟨(a, b), ⟨ha', hb⟩, ?_⟩
    rintro y ⟨hyI, hyS⟩
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hε y hne
      (by rw [abs_sub_lt_iff]; exact ⟨by linarith [hyI.2, hb'], by linarith [hyI.1, ha]⟩)
      hyS.1
  let f : {x : ℝ | g x = 0 ∧ deriv g x ≠ 0} → ℚ × ℚ := fun x => Classical.choose (hex x)
  have hf : ∀ x : {x : ℝ | g x = 0 ∧ deriv g x ≠ 0},
      (x : ℝ) ∈ Set.Ioo ((f x).1 : ℝ) ((f x).2 : ℝ) ∧
        (Set.Ioo ((f x).1 : ℝ) ((f x).2 : ℝ) ∩ {x : ℝ | g x = 0 ∧ deriv g x ≠ 0})
          ⊆ {(x.1)} :=
    fun x => Classical.choose_spec (hex x)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxI : (x:ℝ) ∈ Set.Ioo ((f y).1 : ℝ) ((f y).2 : ℝ) := by
      have := (hf x).1
      rwa [hxy] at this
    have : (x:ℝ) ∈ ({((y.1))} : Set ℝ) := (hf y).2 ⟨hxI, x.2⟩
    exact Subtype.ext (by simpa using this)
  have : Countable {x : ℝ | g x = 0 ∧ deriv g x ≠ 0} := Function.Injective.countable hinj
  exact Set.to_countable _

end Work.Coercivity
