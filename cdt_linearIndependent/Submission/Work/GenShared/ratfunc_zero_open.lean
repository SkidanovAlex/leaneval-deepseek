import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.riccati_aux

namespace Work.GenShared

open Complex Metric Work.GenShared

/-- A nonempty open subset of `ℂ` is infinite (it contains a ball, which is a nontrivial
preconnected set). -/
theorem infinite_of_isOpen_nonempty {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    U.Infinite := by
  obtain ⟨z0, hz0⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z0 hz0
  refine Set.Infinite.mono hball ?_
  refine IsPreconnected.infinite_of_nontrivial (Convex.isPreconnected (convex_ball z0 ε)) ?_
  refine ⟨z0, Metric.mem_ball_self hε, z0 + (ε / 2 : ℝ), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have h1 : z0 + ((ε / 2 : ℝ) : ℂ) - z0 = ((ε / 2 : ℝ) : ℂ) := by ring
    rw [h1, show ‖(((ε / 2 : ℝ)) : ℂ)‖ = |(ε / 2 : ℝ)| from RCLike.norm_ofReal (ε / 2)]
    rw [abs_of_pos (show (0 : ℝ) < ε / 2 by linarith)]
    linarith
  · intro hc
    have hc' : z0 + 0 = z0 + ((ε / 2 : ℝ) : ℂ) := by rw [add_zero]; exact hc
    have h2 : (((ε / 2 : ℝ)) : ℂ) = 0 := (add_left_cancel hc').symm
    have : (ε / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h2
    linarith

/-- If `Rval f` vanishes at every point `z` of a nonempty open set `U` at which `f` is regular
(`Rreg f z`, i.e. `f.denom.eval z ≠ 0`), then `f = 0` in `ℂ(X)`. -/
theorem ratfunc_zero_open {f : RatFunc ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, Rreg f z → Rval f z = 0) : f = 0 := by
  -- Away from the poles, the numerator of `f` vanishes on `U`.
  have hnum : ∀ z ∈ U, f.denom.eval z ≠ 0 → f.num.eval z = 0 := by
    intro z hz hd
    have hr : f.num.eval z / f.denom.eval z = 0 := h z hz hd
    rcases div_eq_zero_iff.mp hr with h1 | h2
    · exact h1
    · exact absurd h2 hd
  -- The pole set of `f` is finite.
  have hZfin : ({z : ℂ | f.denom.eval z = 0}).Finite := by
    have hsub : {z : ℂ | f.denom.eval z = 0} ⊆ {z : ℂ | f.denom.IsRoot z} := by
      intro z hz
      simpa only [Polynomial.IsRoot.def] using hz
    exact (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero f)).subset hsub
  -- `U` is infinite, hence `U` minus the (finite) pole set is infinite.
  have hZc : (U \ {z : ℂ | f.denom.eval z = 0}).Infinite :=
    (infinite_of_isOpen_nonempty hUo hUne).sdiff hZfin
  -- Thus the numerator has infinitely many roots.
  have hroot : {z : ℂ | f.num.IsRoot z}.Infinite := by
    refine Set.Infinite.mono ?_ hZc
    intro z hz
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq] at hz
    exact hnum z hz.1 hz.2
  have hnum0 : f.num = 0 := Polynomial.eq_zero_of_infinite_isRoot f.num hroot
  by_contra hf
  exact RatFunc.num_ne_zero hf hnum0

end Work.GenShared
