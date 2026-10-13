/-
Copyright: work module for the Elgindi finite-time singularity project.

# The tower identity for the iterated radial derivatives of `L₁₂`

For a profile `f` of class `C⁴` on the open quadrant whose pure `D_z`-slots of order `≤ 2` obey
the standing bound `|D_z^k f| ≤ C₀ · z^{3/2}/(1+z)²`, and given the (analytic, proved
separately) fact that the angular moment `Qang f k` is differentiable with
`∂_z (Qang f k) = Qang f (k+1)/z` for `k ≤ 1`, the iterated `z∂_z`-derivatives of `L₁₂(f)` are

  `D_z^j (L₁₂ f)(z) = - Qang f (j-1) z`,      `Qang f k z = ∫_θ K(θ) D_z^k f (z,θ) dθ`,

for `1 ≤ j ≤ 3` and `z > 0`.  This is the identity that turns the convergence of the iterated
derivatives of `L₁₂` into the convergence of the angular moments of the data, i.e. into a
purely angular dominated-convergence statement.

The two ingredients are `Construction_L12_hasDerivAt` (`∂_z L₁₂ f = - L12dens f`, from
`Work.FM.hasDerivAt_L12`) and the slice form
`D_z^{j+1} f = z ∂_z D_z^j f` (`DzIter_slice_hasDerivAt`), the latter being consumed through its
`Qang`-consequence `hQA`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.L12Iter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The tower identity.**  Let `f` be `C⁴` on the open quadrant with
`|D_z^k f| ≤ C₀ Rwt` for `k ≤ 2`, and suppose that `∂_z (Qang f k) = Qang f (k+1)/z` for
`k ≤ 1` (this is the content of `QangHasDerivAt`).  Then for `1 ≤ j ≤ 3` and `z > 0`,

  `D_z^j (L₁₂ f)(z) = - Qang f (j-1) z`. -/
theorem DzdIter_L12_eq_neg_Qang {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    (hQA : ∀ {k : ℕ}, k ≤ 1 → ∀ {w : ℝ}, 0 < w →
      HasDerivAt (fun w => Work.Elliptic.Qang f k w) (Work.Elliptic.Qang f (k + 1) w / w) w)
    {j : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z
      = -(Work.Elliptic.Qang f (j - 1) z) := by
  -- level `1`, pointwise on `(0,∞)`
  have h1 : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z) w
        = -(Work.Elliptic.Qang f 0 w) := by
    intro w hw
    have hder := Construction_L12_hasDerivAt (f := f) hC0 h4 hbd hw
    have hval : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z) w
        = w * (-(Work.Construction.L12dens f w)) := by
      show w * deriv (fun z => Work.Construction.L12 f z) w
        = w * (-(Work.Construction.L12dens f w))
      rw [hder.deriv]
    rw [hval]
    have hdens : Work.Construction.L12dens f w = Work.Elliptic.Qang f 0 w / w :=
      L12dens_eq_Qang_zero f w
    rw [hdens, mul_neg, neg_inj, ← mul_div_assoc]
    exact mul_div_cancel_left₀ (Work.Elliptic.Qang f 0 w) (ne_of_gt hw)
  -- the induction step, using the eventual form of the identity at the previous level
  have hstep : ∀ {j : ℕ}, 1 ≤ j → j ≤ 2 → ∀ {z : ℝ}, 0 < z →
      (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z)
        =ᶠ[𝓝 z] fun u => -(Work.Elliptic.Qang f (j - 1) u)) →
      Work.Elliptic.DzdIter (j + 1) (fun z => Work.Construction.L12 f z) z
        = -(Work.Elliptic.Qang f j z) := by
    intro j hj1 _ z hz' hev
    have hpred : (j - 1) + 1 = j := Nat.succ_pred_eq_of_pos hj1
    have hQA' : HasDerivAt (fun u => Work.Elliptic.Qang f (j - 1) u)
        (Work.Elliptic.Qang f j z / z) z := by
      have h := hQA (k := j - 1) (by omega) hz'
      rwa [hpred] at h
    have hfull : deriv (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z)) z
        = -(Work.Elliptic.Qang f j z / z) := by
      rw [hev.deriv_eq]
      exact hQA'.neg.deriv
    show z * deriv (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z)) z
      = -(Work.Elliptic.Qang f j z)
    rw [hfull, mul_neg, neg_inj, ← mul_div_assoc]
    exact mul_div_cancel_left₀ (Work.Elliptic.Qang f j z) (ne_of_gt hz')
  have h2 : ∀ {z : ℝ}, 0 < z →
      Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z) z
        = -(Work.Elliptic.Qang f 1 z) := by
    intro z hz'
    refine hstep (j := 1) (by omega) (by omega) hz' ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with u hu
    exact h1 u hu
  have h3 : ∀ {z : ℝ}, 0 < z →
      Work.Elliptic.DzdIter 3 (fun z => Work.Construction.L12 f z) z
        = -(Work.Elliptic.Qang f 2 z) := by
    intro z hz'
    refine hstep (j := 2) (by omega) (by omega) hz' ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with u hu
    exact h2 hu
  interval_cases j
  · exact h1 z hz
  · exact h2 hz
  · exact h3 hz

end Work.FTS_RegExport.RXT.L12Iter
