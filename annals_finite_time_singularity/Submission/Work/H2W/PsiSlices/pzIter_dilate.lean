import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

/-- **The chain rule for the iterated radial derivative under a `z`-dilation.**  With
`Ψ_lam(z,θ) := Ψ(lam·z,θ)` one has `∂_z^mΨ_lam(z,θ) = lam^m·∂_z^mΨ(lam·z,θ)` for every `m`, every
`z` and every `θ` (no differentiability hypothesis is needed, because Mathlib's `deriv` has the
junk value `0` off differentiability and `lam > 0` excludes the degenerate `lam = 0` case).  The
slice of the dilated datum at the point `1` is therefore `lam^m` times the slice of `Ψ` at `lam`;
this is the arithmetic input of the covariance reduction. -/
theorem pzIter_dilate {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {lam z : ℝ} (hlam : 0 < lam) (m : ℕ) (θ : ℝ) :
    Work.Spaces.pzIter m (fun z θ => Ψ (lam * z) θ) z θ
      = lam ^ m * Work.Spaces.pzIter m Ψ (lam * z) θ := by
  -- `pzIter m f z θ` is by definition the `m`-th iterate `deriv^[m] (fun z' => f z' θ) z` of the
  -- one-variable derivative along the radial slice, so the statement is the chain rule for the
  -- affine change of variable `z' ↦ lam * z'` applied `m` times to the slice `w ↦ Ψ w θ`.
  --
  -- The two ingredients are unconditionally true, which is why neither hypothesis is used:
  -- `deriv_const_mul_field` pulls a constant out of `deriv`, and `deriv_comp_mul_left`
  -- (`deriv (g <| lam * ·) z = lam * deriv g (lam * z)`) is the affine chain rule with the junk
  -- value `0` for `deriv` off differentiability built in (so `lam ≠ 0` is not needed either).
  have _hΨ := hΨ
  have _hlam := hlam
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
    simp only [Work.Spaces.pz]
    -- replace the inner slice by the inductive hypothesis, as a function of `z'`
    rw [show (fun z' => Work.Spaces.pzIter m (fun z θ => Ψ (lam * z) θ) z' θ)
        = fun z' => lam ^ m * Work.Spaces.pzIter m Ψ (lam * z') θ from
      funext fun z' => ih (z := z')]
    rw [deriv_const_mul_field (u := lam ^ m)
      (v := fun z' => Work.Spaces.pzIter m Ψ (lam * z') θ)]
    rw [deriv_comp_mul_left (c := lam) (f := fun w => Work.Spaces.pzIter m Ψ w θ) (x := z),
      smul_eq_mul]
    ring

end Work.H2W.PsiSlices
