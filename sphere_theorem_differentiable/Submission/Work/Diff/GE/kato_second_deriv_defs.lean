import Mathlib
import Submission.Work.Diff.GE.KatoDefs
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second derivative of a component of `∇Rm`: vocabulary and decomposition

This module collects the vocabulary and the two "unfolding" identities used in the proof of
`Work.Diff.GE.kato_second_deriv_comp`, the statement that the second derivative of a component
`Sof g W α` of `∇Rm` in a geodesic orthonormal frame is the component `D2` of `∇∇∇Rm` plus the
second order frame correction `Left`.

Contents:

* `covRm_zero_fst` … `covRm_zero_fif`, `cov2Rm_zero_fst` … `cov2Rm_zero_sixth`: `covRm` resp.
  `cov2Rm` vanish as soon as one of their arguments is `0` (they are `ℝ`-multilinear in each slot).
* `derCovRmFun g X F`: the covariant derivative of the component of `∇Rm` in the five fields `F`
  along the field `X`, as a function on `M`;
* `corrFun g X F t`: the `t`-th Leibniz correction to that derivative, i.e. the same component of
  `∇Rm` with the field in slot `t` replaced by `∇_X F t`;
* `derCovRmFun_eq`: the defining equation of `cov2RmExt` read as the decomposition
  `derCovRmFun g X F = cov2RmExt g · (X ·) F + ∑ t, corrFun g X F t`;
* `mvfderiv_cov2Rm_eq`: the defining equation of `cov3RmExt`, read as the derivative
  `∂_w (∇²Rm)(U,V,A,B,C,D)` being `cov3RmExt` plus the six Leibniz corrections.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## `covRm` and `cov2Rm` in a vanishing slot -/

/-- `covRm` vanishes when its direction argument is zero. -/
theorem covRm_zero_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) : covRm g x (0 : TangentSpace I x) a b c d = 0 := by
  simpa using covRm_linear_fst (I := I) (M := M) hLC g x 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) a b c d

/-- `covRm` vanishes when its second argument is zero. -/
theorem covRm_zero_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v b c d : TangentSpace I x) : covRm g x v (0 : TangentSpace I x) b c d = 0 := by
  simpa using covRm_linear_snd (I := I) (M := M) hLC g x v 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) b c d

/-- `covRm` vanishes when its third argument is zero. -/
theorem covRm_zero_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a c d : TangentSpace I x) : covRm g x v a (0 : TangentSpace I x) c d = 0 := by
  simpa using covRm_linear_thd (I := I) (M := M) hLC g x v a 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) c d

/-- `covRm` vanishes when its fourth argument is zero. -/
theorem covRm_zero_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b d : TangentSpace I x) : covRm g x v a b (0 : TangentSpace I x) d = 0 := by
  simpa using covRm_linear_fth (I := I) (M := M) hLC g x v a b 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) d

/-- `covRm` vanishes when its fifth argument is zero. -/
theorem covRm_zero_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c : TangentSpace I x) : covRm g x v a b c (0 : TangentSpace I x) = 0 := by
  simpa using covRm_linear_fif (I := I) (M := M) hLC g x v a b c 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x)

/-- `cov2Rm` vanishes when its first argument is zero. -/
theorem cov2Rm_zero_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w a b c d : TangentSpace I x) : cov2Rm g x (0 : TangentSpace I x) w a b c d = 0 := by
  simpa using Kato3.cov2Rm_lin_first (I := I) (M := M) hLC g x 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) w a b c d

/-- `cov2Rm` vanishes when its second argument is zero. -/
theorem cov2Rm_zero_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c d : TangentSpace I x) : cov2Rm g x v (0 : TangentSpace I x) a b c d = 0 := by
  simpa using Kato3.cov2Rm_lin_snd (I := I) (M := M) hLC g x 0 0 v
    (0 : TangentSpace I x) (0 : TangentSpace I x) a b c d

/-- `cov2Rm` vanishes when its third argument is zero. -/
theorem cov2Rm_zero_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v w b c d : TangentSpace I x) : cov2Rm g x v w (0 : TangentSpace I x) b c d = 0 := by
  simpa using Kato3.cov2Rm_lin_thd (I := I) (M := M) hLC g x 0 0 v w
    (0 : TangentSpace I x) (0 : TangentSpace I x) b c d

/-- `cov2Rm` vanishes when its fourth argument is zero. -/
theorem cov2Rm_zero_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v w a c d : TangentSpace I x) : cov2Rm g x v w a (0 : TangentSpace I x) c d = 0 := by
  simpa using Kato3.cov2Rm_lin_fth (I := I) (M := M) hLC g x 0 0 v w a
    (0 : TangentSpace I x) (0 : TangentSpace I x) c d

/-- `cov2Rm` vanishes when its fifth argument is zero. -/
theorem cov2Rm_zero_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v w a b d : TangentSpace I x) : cov2Rm g x v w a b (0 : TangentSpace I x) d = 0 := by
  simpa using Kato3.cov2Rm_lin_fif (I := I) (M := M) hLC g x 0 0 v w a b
    (0 : TangentSpace I x) (0 : TangentSpace I x) d

/-- `cov2Rm` vanishes when its sixth argument is zero. -/
theorem cov2Rm_zero_sixth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v w a b c : TangentSpace I x) : cov2Rm g x v w a b c (0 : TangentSpace I x) = 0 := by
  simpa using Kato3.cov2Rm_lin_sixth (I := I) (M := M) hLC g x 0 0 v w a b c
    (0 : TangentSpace I x)

/-! ## The decomposition of the first covariant derivative -/

/-- The covariant derivative of the component of `∇Rm` in the five fields `F 0, …, F 4`, in the
direction of the field `X`; by definition of `cov2RmExt` this is `cov2RmExt g · (X ·) F …` plus the
five Leibniz corrections (`derCovRmFun_eq`). -/
noncomputable def derCovRmFun (g : SMet I M) (X : Π y : M, TangentSpace I y)
    (F : Fin 5 → Π y : M, TangentSpace I y) : M → ℝ :=
  fun y => mvfderiv I (fun z : M => covRm g z (F 0 z) (F 1 z) (F 2 z) (F 3 z) (F 4 z)) y (X y)

/-- The `t`-th Leibniz correction to `derCovRmFun g X F`: the component of `∇Rm` in the same five
fields, with the field in slot `t` replaced by `∇_X F t`. -/
noncomputable def corrFun (g : SMet I M) (X : Π y : M, TangentSpace I y)
    (F : Fin 5 → Π y : M, TangentSpace I y) (t : Fin 5) : M → ℝ :=
  fun y => covRm g y
    ((Function.update F t (fun z : M => lcOf g (F t) z (X z))) 0 y)
    ((Function.update F t (fun z : M => lcOf g (F t) z (X z))) 1 y)
    ((Function.update F t (fun z : M => lcOf g (F t) z (X z))) 2 y)
    ((Function.update F t (fun z : M => lcOf g (F t) z (X z))) 3 y)
    ((Function.update F t (fun z : M => lcOf g (F t) z (X z))) 4 y)

/-- **The decomposition of the first derivative of a component of `∇Rm`.**  Pointwise, the defining
equation of `cov2RmExt` reads
`∂_X (∇Rm)(F 0,…,F 4) = cov2RmExt g · (X ·) F 0 … F 4 + ∑ t, ∇Rm(…, ∇_X F t, …)`,
the sum running over the five slots.  This is the identity that is differentiated once more in
`Work.Diff.GE.kato_second_deriv_comp`. -/
theorem derCovRmFun_eq (hLC : LCSmooth I M) (g : SMet I M) (X : Π y : M, TangentSpace I y)
    (F : Fin 5 → Π y : M, TangentSpace I y) :
    derCovRmFun g X F
      = fun y : M => cov2RmExt g y (X y) (F 0) (F 1) (F 2) (F 3) (F 4)
          + ∑ t : Fin 5, corrFun g X F t y := by
  funext y
  simp only [derCovRmFun, corrFun, cov2RmExt, Function.update, Fin.sum_univ_five]
  norm_num

/-! ## The unfolding of `cov3RmExt` -/

/-- **The defining equation of `cov3RmExt`.**  The covariant derivative of `∇∇Rm` on six smooth
fields is the sum of `cov3RmExt` and the six Leibniz corrections, one for each of the differentiated
slots. -/
theorem mvfderiv_cov2Rm_eq (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    (U V A B C D : Π y : M, TangentSpace I y) :
    mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x w
      = cov3RmExt g x w U V A B C D
        + cov2Rm g x (lcOf g U x w) (V x) (A x) (B x) (C x) (D x)
        + cov2Rm g x (U x) (lcOf g V x w) (A x) (B x) (C x) (D x)
        + cov2Rm g x (U x) (V x) (lcOf g A x w) (B x) (C x) (D x)
        + cov2Rm g x (U x) (V x) (A x) (lcOf g B x w) (C x) (D x)
        + cov2Rm g x (U x) (V x) (A x) (B x) (lcOf g C x w) (D x)
        + cov2Rm g x (U x) (V x) (A x) (B x) (C x) (lcOf g D x w) := by
  simp only [cov3RmExt]
  ring

end Work.Diff.GE
