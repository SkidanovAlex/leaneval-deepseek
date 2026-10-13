import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-!
# The zero profile in the `ℋ^k`-bookkeeping

The five facts about the identically vanishing profile `fun _ _ : ℝ => 0` that the
"clamping" step of the Volterra remainder estimate needs: the iterated mixed operators
vanish, the `ℋ^k`-integrand vanishes (as a function), the profile is `C^∞` on the open
quadrant, and it is `ℋ^k`-honest with `ℋ^k`-norm `0`.
-/

theorem DthIter_zero_profile (n : ℕ) :
    Work.Spaces.DthIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

theorem DzIter_zero_profile (n : ℕ) :
    Work.Spaces.DzIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

theorem mixed_zero_profile (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  rw [Work.Spaces.mixed, DthIter_zero_profile i, DzIter_zero_profile j]

theorem HkIntegrand_zero_profile (α : ℝ) (k : ℕ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand]
  have hz : ∀ i : ℕ, (Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i; rw [DzIter_zero_profile i]; ring
  have hm : ∀ i j : ℕ, (if 1 ≤ i ∧ i + j ≤ k then
      (Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 := by
    intro i j
    split_ifs with h
    · rw [mixed_zero_profile j i]; ring
    · rfl
  simp only [hz, hm, Finset.sum_const_zero, add_zero]

theorem smoothOpen_zero_profile :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => (0 : ℝ)) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h : Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) = fun _ : ℝ × ℝ => 0 := rfl
  rw [h]; exact contDiffOn_const

theorem HkMem_zero_profile (α : ℝ) (k : ℕ) :
    Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    rw [HkIntegrand_zero_profile]
    exact integrableOn_zero
  · rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ => 0 from by
      funext z; rw [HkIntegrand_zero_profile]; simp]
    exact integrableOn_zero

theorem HkNorm_zero_profile (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  rw [Work.Spaces.HkNorm]
  rw [show Work.Spaces.HkSq α k (fun _ _ : ℝ => (0 : ℝ)) = 0 from by
    rw [Work.Spaces.HkSq]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ => 0 from by
      funext z; rw [HkIntegrand_zero_profile]; simp]
    simp]
  exact Real.sqrt_zero

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
