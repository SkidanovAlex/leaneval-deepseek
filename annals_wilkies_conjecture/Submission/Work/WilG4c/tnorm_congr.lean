import Mathlib
import Submission.Work.WilG2.Tnorm

namespace Work.WilG4c

/-- The jet norm `‖f‖_{T,r}` at a point only depends on the germ of `f` at that point: the
iterated derivatives at `x` are determined by the values of `f` near `x`.  (Used to rewrite the
jet norm of a function that satisfies the chain-rule identity only on a neighbourhood of the
point.) -/
theorem tnorm_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) {f g : E → ℝ}
    {x : E} (h : f =ᶠ[nhds x] g) :
    WilkiesDesign.CG.tnorm r f x = WilkiesDesign.CG.tnorm r g x := by
  have hd : ∀ k : ℕ, iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x :=
    fun k => (h.iteratedFDeriv ℝ k).self_of_nhds
  simp only [WilkiesDesign.CG.tnorm_eq_sum_jetCoeff, WilkiesDesign.CG.jetCoeff, hd]

end Work.WilG4c
