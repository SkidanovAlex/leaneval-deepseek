import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.mixed_const_mul
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Subtraction rule for the mixed operator `D_z^j D_θ^i` at finite regularity

`Work.Spaces.mixed j i f = D_z^j D_θ^i f`, where `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`, and
`Work.FTS.EllipticEst.Q0 = (0,∞) × (0,π/2)` is the open quadrant of the elliptic estimates.

The statement proved here is the *subtraction* (linearity) rule

  `D_z^j D_θ^i (A - B) = D_z^j D_θ^i A - D_z^j D_θ^i B`   on `Q0`, for `i + j ≤ 4`,

for two functions `A`, `B` that are only `C^4` on `Q0` (not `C^∞`, and not smooth on a
neighbourhood of the *closed* quadrant): the downstream strong-`ε` estimates work with the
honest finite-order class, so the additivity lemma of the workspace stated for `C^∞` data
(`Work.FTS.EllipticEst.SmoothOpen.mixed_add`) does not apply and the finite-order version is
needed.

Route.  Write `A - B = A + (-B)` and use the finite-order *additivity* lemma

* `Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin` : `mixed_add` for data that are only
  `C^m` on `Q0`, at orders `i + j ≤ m`,

together with the fact, recorded in `Submission/Work/FTS/StrongEps/mixed_const_mul.lean`, that
every iterate of `D_z`, `D_θ` (hence `mixed`) is *unconditionally* scalar homogeneous —
`deriv` satisfies `deriv_const_mul_field`, so homogeneity needs no differentiability
hypothesis at all.  Taking the scalar `-1` gives `mixed j i (fun z θ => -(B z θ)) =
- mixed j i B`, and the result follows.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps

/-- `∂_z` commutes with negation.  Unconditional: `deriv_const_mul_field` at the scalar `-1`
gives the result even where the function is not differentiable (there both sides are `0`). -/
theorem pz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => -(f z θ)) = fun z θ => -(Work.Spaces.pz f z θ) := by
  have h1 : (fun z θ => -(f z θ)) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [h1, pz_const_mul (-1) f]
  funext z θ; ring

/-- Every `D_θ`-iterate commutes with negation (unconditional). -/
theorem DthIter_neg (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => -(f z θ))
      = fun z θ => -(Work.Spaces.DthIter i f z θ) := by
  have h1 : (fun z θ => -(f z θ)) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [h1, DthIter_const_mul (-1) f i]
  funext z θ; ring

/-- Every `D_z`-iterate commutes with negation (unconditional). -/
theorem DzIter_neg (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => -(f z θ))
      = fun z θ => -(Work.Spaces.DzIter j f z θ) := by
  have h1 : (fun z θ => -(f z θ)) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [h1, DzIter_const_mul (-1) f j]
  funext z θ; ring

/-- `mixed` commutes with negation, i.e. scalar homogeneity at the scalar `-1`
(unconditional; no smoothness hypothesis is needed). -/
theorem mixed_neg {j i : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ} :
    Work.Spaces.mixed j i (fun z' θ' => -(f z' θ')) z θ
      = -(Work.Spaces.mixed j i f z θ) := by
  simp only [Work.Spaces.mixed, DthIter_neg f i, DzIter_neg (Work.Spaces.DthIter i f) j]

theorem mixed_sub_of_contDiffOn_four {j i : ℕ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hji : j + i ≤ 4) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hA : ContDiffOn ℝ 4 (Function.uncurry A) Work.FTS.EllipticEst.Q0)
    (hB : ContDiffOn ℝ 4 (Function.uncurry B) Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ := by
  -- `-B` is again `C^4` on the open quadrant
  have hBneg : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => -(B z θ)))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun z θ => -(B z θ))
        = fun p : ℝ × ℝ => -(Function.uncurry B p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact hB.neg
  -- the index bound in the shape expected by `mixed_add_fin`
  have hij : i + j ≤ 4 := by rw [Nat.add_comm i j]; exact hji
  -- rewrite `A - B` as `A + (-B)`
  have hfun : (fun z θ => A z θ - B z θ) = fun z θ => A z θ + -(B z θ) := by
    funext z θ; ring
  rw [hfun]
  -- finite-order additivity for `C^4` data on the open quadrant
  rw [Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin (f := A)
        (g := fun z' θ' => -(B z' θ')) hA hBneg j i hij z θ hz hθ.1 hθ.2]
  -- homogeneity at the scalar `-1`
  rw [mixed_neg]
  ring

end Work.FTS.StrongEps
