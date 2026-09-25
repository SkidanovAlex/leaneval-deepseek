import Mathlib
import Submission.Work.NN.Core.DbarSquare
import Submission.Work.Dbar.sq_zero
import Submission.Work.AlmostComplex.Types.dbarSq_eq_four_proj02

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- The `(0,2)`-form of this file (`Work.NN.Core.dbarSq`, built from the exterior derivative
`delOne` of a `1`-form) is *definitionally* the `(0,2)`-projection `proj02` of the exterior
derivative: both are

  `(1/4)·(dω(v,w) + i·dω(Jv,w) + i·dω(v,Jw) - dω(Jv,Jw))`

with `dω = delOne ω x = dExterior ω x`. -/
lemma dbarSq_eq_proj02 {n : ℕ} (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x v w : E n) :
    dbarSq J u x v w
      = Work.AlmostComplex.Types.proj02 (J x)
          (fun A B => Work.AlmostComplex.Types.dExterior (Submission.dbar J u) x A B) v w := by
  simp only [Work.NN.Core.dbarSq, Work.AlmostComplex.Types.proj02, delOne,
    Work.AlmostComplex.Types.dExterior]

/-- **Integrability: `∂̄_J ∘ ∂̄_J = 0` for an almost complex structure with vanishing Nijenhuis
tensor.**  For `J` smooth with `J y ∘ J y = -1` on the open set `U ∋ x` whose Nijenhuis tensor
vanishes on `U`, the `(0,2)`-form `∂̄_J²u = dbarSq J u` of every smooth `u` vanishes:

  `dbarSq J u x v w = 0`   for all `v, w : ℝ^{2n}`.

The expression `dbarSq` (see `Work.NN.Core.DbarSquare`) is the `(0,2)`-part of `d(∂̄_Ju)`:
`(1/4)·(dω(v,w) + i·dω(Jv,w) + i·dω(v,Jw) - dω(Jv,Jw))` with `ω = dbar J u` and `dω` the
exterior derivative of a `1`-form, `delOne ω x a b = D_a(ω·b)(x) - D_b(ω·a)(x)`.  The hypothesis
`IsOpen U` is needed: the identity uses `J² = -1` on a *neighbourhood* of `x`.

Two routes.  *Concrete*: expand both sides using `dbar_apply`, the `fderiv`-calculus for the
derivatives of `z ↦ J z (v)`, and the symmetry of second derivatives of `u`; the second-order
terms of `u` cancel identically (using `J x (J x v) = -v`), and the remaining first-order terms
assemble into combinations of the Nijenhuis expression `nijenhuis J V W x` for the constant vector
fields `V = v`, `W = w`, which vanishes by hypothesis.  *Conceptual*: `dbarSq J u x v w =
du_x([v^{01}, w^{01}]^{10}(x))`, and the `(0,1)`-distribution is involutive because `N(V,W) = 0`
is *equivalent*, after applying `J` and using `J² = -1`, to `J[V,W] - J[JV,JW] = [JV,W] + [V,JW]`,
which says exactly that `[V^{01},W^{01}] = (1/4)([V,W],[JV,JW])` has zero `(1,0)`-part. -/
theorem dbar_sq_zero {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n}
    (hU : IsOpen U) (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U)
    {u : E n → ℂ} (hu : ContDiff ℝ ∞ u) (v w : E n) {x : E n} (hx : x ∈ U) :
    dbarSq J u x v w = 0 := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.contDiffAt.of_le (by simp)
  have hJ1 : ContDiffAt ℝ 1 J x := (hJ.1.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  -- `Submission.dbarSq` on the constant fields `v`, `w` is four times the projection form
  -- `proj02` of the exterior derivative of `∂̄_J u`.
  have h4 := Work.AlmostComplex.Types.dbarSq_eq_four_proj02 (J := J) (u := u)
    (X := fun _ : E n => v) (Y := fun _ : E n => w) (x := x) hu2 hJ1
    contDiffAt_const contDiffAt_const
  -- The structure equation `∂̄² = 0` for integrable `J`.
  have h0 := Work.Dbar.sq_zero hU hJ hN hx hu2
    (X := fun _ : E n => v) (Y := fun _ : E n => w) contDiffAt_const contDiffAt_const
  have key : (4 : ℂ) * Work.AlmostComplex.Types.proj02 (J x)
      (fun A B => Work.AlmostComplex.Types.dExterior (Submission.dbar J u) x A B) v w = 0 := by
    rw [← h4]
    exact h0
  have hproj : Work.AlmostComplex.Types.proj02 (J x)
      (fun A B => Work.AlmostComplex.Types.dExterior (Submission.dbar J u) x A B) v w = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · exact h
  rw [dbarSq_eq_proj02]
  exact hproj

end Work.NN.Core
