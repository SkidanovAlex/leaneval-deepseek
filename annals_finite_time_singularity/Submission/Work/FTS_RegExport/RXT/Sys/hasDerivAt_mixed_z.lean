/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `z`-derivative of the slice of a mixed jet, at the finite order `C⁴`

The operator `D_z = z ∂_z` is, by definition, the product of `z` with the `z`-derivative of
the slice, so

  `D_z^{j+1} D_θ^i f (z,θ) = z · ∂_z (D_z^j D_θ^i f) (z,θ)`   (`rfl`),

i.e. the `z`-derivative of the slice `z' ↦ D_z^j D_θ^i f (z',θ)` is `D_z^{j+1}D_θ^if(z,θ)/z`
for `z ≠ 0`.  The only mathematical input is that the slice is differentiable, which follows
from the *joint* smoothness of `f`: the jet `D_z^jD_θ^i f` needs `j + i` derivatives of `f`,
so under the hypothesis `f ∈ C⁴` on the open quadrant `Q0` and `j + i ≤ 3` it is at least `C¹`
there.

The finite-order chain rule used here is the one of
`Submission.Work.FTS.StrongEps.HkMem_of_tendsto` (`contDiffOn_uncurry_DthIter_shift`,
`contDiffOn_uncurry_DzIter_shift`): each iterate of `D_θ` resp. `D_z` costs its index in orders
of differentiability.  (The `ℋ^k`-machinery of `Work.FTS.LocData` states the same chain at
`smoothOrder`, which is not available for a merely `C⁴` datum.)

This is the radial companion of `hasDerivAt_mixed_theta`
(`Work.FTS_RegExport.C4.Dth_mixed_eq_C4` is its exact form), both of which are used to write
`∂_τ D_z^jD_θ^i g = D_z^{j+1}D_θ^i (∂_τ g)/z + D_z^jD_θ^{i+1}(∂_τ g)/sin(2θ)` for the
regularity export of the Galerkin schema.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

/-- **The `z`-derivative of the slice of a mixed jet.**  For a datum `f` which is `C⁴` on the
open quadrant `Q0` and a mixed jet `D_z^jD_θ^i f` of total order `j + i ≤ 3`, the slice
`z' ↦ D_z^jD_θ^i f (z',θ)` is differentiable at every `z > 0` (and every interior `θ`), with
derivative `D_z^{j+1}D_θ^i f (z,θ)/z`.

Indeed `D_z^{j+1}D_θ^i f = D_z(D_z^jD_θ^i f)` is definitionally `z · ∂_z(D_z^jD_θ^i f)`, and the
slice is differentiable because `D_z^jD_θ^i f` is `C^{4-j-i}`, in particular `C¹`, on `Q0`. -/
theorem hasDerivAt_mixed_z {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Spaces.mixed j i f z' θ)
      (Work.Spaces.mixed (j + 1) i f z θ / z) z := by
  -- the point lies in the open quadrant
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨hz, hθ, hθ'⟩
  have hθIoo : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ, hθ'⟩
  -- index arithmetic (`j + i ≤ 3`)
  have hi4 : i ≤ 4 := by omega
  have hjle : j ≤ 4 - i := by omega
  have hone : 1 ≤ (4 - i) - j := by omega
  -- `D_θ^i f` is `C^{4-i}` on the open quadrant
  have hDth : ContDiffOn ℝ (4 - i) (Function.uncurry (Work.Spaces.DthIter i f))
      Work.FTS.EllipticEst.Q0 := by
    have hle : (4 - i) + i ≤ 4 := le_of_eq (Nat.sub_add_cancel hi4)
    have h : ContDiffOn ℝ ((4 - i) + i) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
      hf.of_le (Nat.cast_le.mpr hle)
    exact Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift Work.FTS.EllipticEst.isOpen_Q0
      i (4 - i) h
  -- `D_z^j D_θ^i f` is `C^{(4-i)-j}` on the open quadrant
  have hDz : ContDiffOn ℝ ((4 - i) - j)
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)))
      Work.FTS.EllipticEst.Q0 := by
    have hle : ((4 - i) - j) + j ≤ 4 - i := le_of_eq (Nat.sub_add_cancel hjle)
    have h' : ContDiffOn ℝ (((4 - i) - j) + j)
        (Function.uncurry (Work.Spaces.DthIter i f)) Work.FTS.EllipticEst.Q0 :=
      hDth.of_le (Nat.cast_le.mpr hle)
    exact Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0
      j ((4 - i) - j) h'
  -- in particular `D_z^jD_θ^i f` is `C¹`
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i f))
      Work.FTS.EllipticEst.Q0 :=
    hDz.of_le (Nat.cast_le.mpr hone)
  -- hence its slice at the interior angle `θ` is `C¹` and differentiable at `z > 0`
  have hslice : ContDiffOn ℝ 1 (fun z' : ℝ => Work.Spaces.mixed j i f z' θ) (Set.Ioi 0) := by
    have hmap : ContDiffOn ℝ 1 (fun x : ℝ => (x, θ)) (Set.Ioi 0) :=
      (contDiffOn_id : ContDiffOn ℝ 1 (fun z : ℝ => z) (Set.Ioi 0)).prodMk
        (contDiffOn_const (c := θ))
    have h := h1.comp hmap (fun x hx => ⟨hx, hθIoo⟩)
    rw [show (Function.uncurry (Work.Spaces.mixed j i f)) ∘ (fun x : ℝ => (x, θ))
        = fun z' => Work.Spaces.mixed j i f z' θ from rfl] at h
    exact h
  have hdiff : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.mixed j i f z' θ) z :=
    (hslice.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hH : HasDerivAt (fun z' : ℝ => Work.Spaces.mixed j i f z' θ)
      (Work.Spaces.pz (Work.Spaces.mixed j i f) z θ) z := by
    simpa [Work.Spaces.pz] using hdiff.hasDerivAt
  -- `D_z^{j+1}D_θ^i f = D_z(D_z^jD_θ^i f) = z · ∂_z(D_z^jD_θ^i f)` definitionally
  have hval : Work.Spaces.mixed (j + 1) i f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i f) z θ := rfl
  rw [hval, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  exact hH

end Work.FTS_RegExport.RXT.Sys
