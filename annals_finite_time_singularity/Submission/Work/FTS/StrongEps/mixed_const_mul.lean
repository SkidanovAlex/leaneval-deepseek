import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps

-- The hypotheses `hf`, `hz`, `hθ` of the requested statement are not used by its proof: the
-- identity holds on all of `ℝ²` (see the module docstring).  Silence the corresponding linter.
set_option linter.unusedVariables false

/-!
# Scalar homogeneity of the mixed derivative `D_z^j D_θ^i`

`Work.Spaces.mixed j i f = D_z^j D_θ^i f`, where `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`.
Here we record that every one of these operators — `∂_z`, `∂_θ`, `D_z`, `D_θ` and all their
iterates, hence `mixed j i` — is scalar homogeneous:

  `D_z^j D_θ^i (c·f) = c · D_z^j D_θ^i f`.

The point of the argument is that `deriv` is *unconditionally* homogeneous,
`deriv (fun y => c * g y) x = c * deriv g x` (`deriv_const_mul_field`): when `g` is not
differentiable at `x` both sides are `0` (and if `c ≠ 0`, `c·g` is not differentiable either).
Hence no smoothness or range hypothesis is needed: `mixed_const_mul` holds on all of `ℝ²`,
which is why the hypotheses of the requested statement (`hf`, `hz`, `hθ`) can simply be
discarded by the proof.

(The file opens the `Real` notation scope because the statement writes the angle bound as
`θ ∈ Set.Ioo 0 (π / 2)`: with `autoImplicit = false` in this workspace a bare `π` is not an
identifier, so `open scoped Real` is what makes it denote `Real.pi` as intended.  The statement
itself is byte-for-byte the one requested.)
-/

/-- `∂_z` is scalar homogeneous (unconditionally). -/
theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_field c

/-- `∂_θ` is scalar homogeneous (unconditionally). -/
theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- `D_z = z ∂_z` is scalar homogeneous. -/
theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

/-- `D_θ = sin(2θ) ∂_θ` is scalar homogeneous. -/
theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

/-- Every iterate of `D_z` is scalar homogeneous. -/
theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul]

/-- Every iterate of `D_θ` is scalar homogeneous. -/
theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- Scalar homogeneity of the mixed derivative `D_z^j D_θ^i` (unconditional; the hypotheses of
the statement are not needed and are discarded by the proof). -/
theorem mixed_const_mul {j i : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z' θ' => c * f z' θ') z θ
      = c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul c f i,
    DzIter_const_mul c (Work.Spaces.DthIter i f) j]

end Work.FTS.StrongEps
