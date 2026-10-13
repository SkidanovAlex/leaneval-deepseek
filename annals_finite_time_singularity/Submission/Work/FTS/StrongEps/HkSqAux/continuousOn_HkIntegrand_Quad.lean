import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Continuity of the `ℋ^k`-integrand on the open quadrant.**

If `f` is `C^n` on the open quadrant `Quad = (0,∞) × (0,π/2)` for every `n`, then the
integrand

  `(z,θ) ↦ HkIntegrand α k f z θ`

is continuous on `Quad`.  On `Quad` the two weights `w z = (1+z)²/z²` and `sin(2θ)^{-η/2}`
resp. `Wt α z θ = w z · sin(2θ)^{-γ/2}` are continuous (the denominators `z` and `sin(2θ)`
do not vanish there), and every one of the finitely many derivatives `D_z^i f`,
`D_z^j D_θ^i f` entering `HkIntegrand` is `C^∞` on `Quad` because `D_z`, `D_θ` preserve
smoothness on an open set (`Work.FTS.LocData.contDiffOn_DzIter`,
`Work.FTS.LocData.contDiffOn_mixed`), hence continuous. -/
theorem continuousOn_HkIntegrand_Quad (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := by
  have hOpen : IsOpen Work.FTS.StrongEps.Quad := Work.FTS.StrongEps.isOpen_Quad
  -- `C^n` for every `n` is `C^∞` (the genuine smooth order, not analyticity)
  have hfq : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.StrongEps.Quad := contDiffOn_infty.mpr hf
  -- on the open quadrant `sin(2θ) > 0`, so every power is finite and continuous
  have hsinpos : ∀ p ∈ Work.FTS.StrongEps.Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  -- the radial weight `w z = (1+z)²/z²`
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.StrongEps.Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ∀ c : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.StrongEps.Quad :=
    fun c => ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- the product weight `Wt α z θ = w z · sin(2θ)^{-γ/2}`
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.StrongEps.Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  -- the pure `D_z`-weight `w z / sin(2θ)^{η/2}`
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Work.FTS.StrongEps.Quad :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  -- the derivatives entering the integrand are smooth, hence continuous, on the quadrant
  have hDzC : ∀ i : ℕ,
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
        Work.FTS.StrongEps.Quad :=
    fun i => (Work.FTS.LocData.contDiffOn_DzIter hOpen hfq i).continuousOn
  have hmC : ∀ j i : ℕ,
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
        Work.FTS.StrongEps.Quad :=
    fun j i => (Work.FTS.LocData.contDiffOn_mixed hOpen hfq j i).continuousOn
  -- unfold the integrand and assemble the (finite) sum of continuous summands
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i f p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
    exact ((hDzC i).mul hwdiv).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact ((hmC j i).mul hWt).pow 2
    · exact continuousOn_const

end Work.FTS.StrongEps.HkSqAux
