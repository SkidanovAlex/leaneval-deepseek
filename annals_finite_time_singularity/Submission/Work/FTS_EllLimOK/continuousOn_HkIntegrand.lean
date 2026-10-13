/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted `ℋ^k`-integrand is continuous on the open quadrant

`Work.Spaces.HkIntegrand α k X z θ` is the finite sum of the squared weighted derivatives that
constitute the `ℋ^k`-norm of the paper:

* `(D_z^i X · w(z) / sin(2θ)^{η/2})²` for `0 ≤ i ≤ k`, and
* `(D_z^j D_θ^i X · W(z,θ))²` for `1 ≤ i`, `i + j ≤ k`,

on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  Both weight factors are finite and continuous
there because `0 < θ < π/2` forces `sin(2θ) > 0`.  Consequently the integrand is continuous on
`Q0` as soon as the finitely many iterated derivatives occurring in it are; this is the
*unbundled* form of the statement, in which only the continuity of the operators `D_z^j D_θ^i X`
for the multi-indices `i + j ≤ k` actually occurring in `HkIntegrand` is assumed (note that the
pure radial slots `D_z^i X = mixed i 0 X` are among these).

The proof is a structural unfolding of `HkIntegrand`: `continuousOn_finsetSum` for the two finite
sums, `ContinuousOn.add`, `split_ifs` for the guard of the mixed slots, and
`ContinuousOn.mul`/`.pow` against the two weight lemmas `continuousOn_wdivsin_Q0` (from
`EllipticEst/OpenQDefs`) and `continuousOn_Wt_Q0` below.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The weights are continuous on the open quadrant -/

private lemma sin_two_pos_of_lt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

private lemma continuousOn_sinpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => ?_)
  exact Or.inl (ne_of_gt
    (sin_two_pos_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1
      (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2))

/-- The product weight `Wt α = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α / 2)))

/-! ## The requested statement -/

theorem continuousOn_HkIntegrand {α : ℝ} {k : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ∀ (j i : ℕ), j + i ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i X p.1 p.2)
        Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  -- the pure radial slots `D_z^i X = mixed i 0 X`, for `i ≤ k`
  have hDz : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := fun i hi =>
    by simpa only [Work.Spaces.mixed_zero_right] using h i 0 (by omega)
  -- the mixed slots `D_z^j D_θ^i X`, for `1 ≤ i`, `i + j ≤ k`
  have hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i X p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun i j _ hij => h j i (by omega)
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · -- the sum of the squared weighted radial derivatives
    refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (((hDz i hik).mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  · -- the sum of the squared weighted mixed derivatives
    refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _hj => ?_))
    split_ifs with hcond
    · exact (((hMx i j hcond.1 hcond.2).mul (continuousOn_Wt_Q0 α))).pow 2
    · exact continuousOn_const

end Work.FTS_EllLimOK
