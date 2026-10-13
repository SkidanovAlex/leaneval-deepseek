import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-!
# Subtraction rule for `D_z^j D_θ^i` on the open quadrant, six derivatives

`Work.Spaces.mixed j i f = D_z^j D_θ^i f` with `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`, and
`Work.FTS.EllipticEst.Q0 = (0,∞) × (0,π/2)` is the open quadrant.  This is the order-`6`
counterpart of `Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four`: for two functions that are
`C^6` on the open quadrant

  `D_z^j D_θ^i (A - B) = D_z^j D_θ^i A - D_z^j D_θ^i B`   on `Q0`, for `i + j ≤ 6`.

Route (identical to the order-`4` case).  Write `A - B = A + (-B)` and apply the finite-order
*additivity* lemma `Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin` at `m = 6` (it is
stated for arbitrary order `m`), then use that every iterate of `mixed` is *unconditionally*
scalar homogeneous — `Work.FTS.StrongEps.mixed_neg` — to turn `mixed j i (fun z θ => -(B z θ))`
into `- mixed j i B`.

The statement is byte-for-byte the requested one; the file only adds imports and this comment.
-/

theorem mixed_sub_of_contDiffOn_six {j i : ℕ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hji : j + i ≤ 6) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hA : ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0)
    (hB : ContDiffOn ℝ 6 (Function.uncurry B) Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ := by
  -- `-B` is again `C^6` on the open quadrant
  have hBneg : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => -(B z θ)))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun z θ => -(B z θ))
        = fun p : ℝ × ℝ => -(Function.uncurry B p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact hB.neg
  -- the index bound in the shape expected by `mixed_add_fin`
  have hij : i + j ≤ 6 := by rw [Nat.add_comm i j]; exact hji
  -- rewrite `A - B` as `A + (-B)`
  have hfun : (fun z θ => A z θ - B z θ) = fun z θ => A z θ + -(B z θ) := by
    funext z θ; ring
  rw [hfun]
  -- finite-order additivity for `C^6` data on the open quadrant
  rw [Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin (f := A)
        (g := fun z' θ' => -(B z' θ')) hA hBneg j i hij z θ hz hθ.1 hθ.2]
  -- homogeneity at the scalar `-1`
  rw [Work.FTS.StrongEps.mixed_neg]
  ring

end Work.FTS.StrongEps.EpsE4Thr
