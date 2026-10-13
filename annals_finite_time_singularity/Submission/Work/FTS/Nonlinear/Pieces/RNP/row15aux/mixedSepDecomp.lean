import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-!
# Separation of variables for the mixed operators `D_z^l D_θ^m`

For a product of a `θ`-only function and a `z`-only function, the mixed operator
`D_z^l D_θ^m` acts on the two factors separately:

`D_z^l D_θ^m (θ ↦ C θ · z ↦ B z) z θ = (dthU^[m] C) θ · (OpZ^[l] B) z`,

where `OpZ B z = z · B'(z)` and `dthU C θ = sin(2θ) · C'(θ)` are the one-dimensional
`D_z`- and `D_θ`-operators.

The angular half is the existing `Work.Spaces.DthIter_decomp`; the radial half is proved
here by induction, from the slice identity `Work.Spaces.sliceZ_DzIter` and the elementary
fact that `OpZ` commutes with multiplication by a constant (`deriv_const_mul_field`, which
needs no differentiability hypothesis).
-/

/-- `OpZ` commutes with multiplication by a constant. -/
private lemma OpZ_const_mul (c : ℝ) (f : ℝ → ℝ) :
    Work.Spaces.OpZ (fun x => c * f x) = fun x => c * Work.Spaces.OpZ f x := by
  funext x
  simp only [Work.Spaces.OpZ, deriv_const_mul_field]
  ring

/-- Iterated version of `OpZ_const_mul`. -/
private lemma OpZ_iterate_const_mul (l : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    (Work.Spaces.OpZ^[l]) (fun x => c * f x) = fun x => c * (Work.Spaces.OpZ^[l] f) x := by
  induction l with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, OpZ_const_mul]
      rw [Function.iterate_succ_apply']

/-- The radial half of the separation of variables: if the `θ`-factor `A θ` is held fixed,
then `D_z^l` acts only on the `z`-factor `B`. -/
private lemma DzIter_theta_factor (l : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter l (fun z θ => A θ * B z) z θ = A θ * (Work.Spaces.OpZ^[l] B) z := by
  have h := congrFun (Work.Spaces.sliceZ_DzIter l (fun z θ => A θ * B z) θ) z
  rw [h]
  exact congrFun (OpZ_iterate_const_mul l (A θ) B) z

theorem mixedSepDecomp (l m : ℕ) (C B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed l m (fun z θ => C θ * B z) z θ
      = (Work.Spaces.dthU^[m] C) θ * (Work.Spaces.OpZ^[l] B) z := by
  unfold Work.Spaces.mixed
  have hDth : Work.Spaces.DthIter m (fun z θ => C θ * B z)
      = fun z θ => (Work.Spaces.dthU^[m] C) θ * B z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp m C B z θ
  rw [hDth]
  exact DzIter_theta_factor l (Work.Spaces.dthU^[m] C) B z θ

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
