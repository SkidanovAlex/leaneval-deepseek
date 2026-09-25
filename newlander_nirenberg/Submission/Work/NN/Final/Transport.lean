/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The transport of the structure to the flat model `ℂⁿ`

This module re-establishes, inside this chapter, the transport setup that the assembly needs:
the structure `J` on `E n = ℝ^{2n}` transported to `ℂⁿ` by the linear isomorphism
`tupleDeriv T : E n ≃L[ℝ] ℂⁿ` (`Work.NN.Core.tupleDeriv`), the perturbation `A = J₁ - Jstd`, and
the transport identity for the `(0,1)`-operator

  `∂̄_J (u ∘ tupleDeriv T) = (∂̄_{J₁} u ∘ tupleDeriv T) ∘ tupleDeriv T`.

(The same objects were previously provided by `Work/NN/Core/local_holomorphic_frame.lean`, which has
since been removed from the workspace; they are reproduced here so that this chapter is
self-contained.)
-/
import Mathlib
import Submission.Work.Core.Std
import Submission.Work.NN.Core.Defs
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.dbar_stdOf_comp_tupleDeriv
import Submission.Work.NN.Core.tupleDeriv_comp
import Submission.Work.NN.Core.Main

noncomputable section

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff Topology

namespace Work.NN.Final

open Work.NN.Core

variable {n : ℕ}

/-- The structure `J` transported to `ℂⁿ` by the linear isomorphism `tupleDeriv T`. -/
noncomputable def Jtr (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) :
    Cn n → Cn n →L[ℝ] Cn n :=
  fun z => (tupleDeriv T).comp ((J (tupleDerivInv T z)).comp (tupleDerivInv T))

@[simp] lemma Jtr_apply (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) (z w : Cn n) :
    Jtr J T z w = tupleDeriv T (J (tupleDerivInv T z) (tupleDerivInv T w)) := rfl

/-- `tupleDerivInv T` is a right inverse of `tupleDeriv T`. -/
lemma tupleDerivInv_tupleDeriv (T : E n ≃L[ℝ] F n) (x : E n) :
    tupleDerivInv T (tupleDeriv T x) = x := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrFun (congrArg (fun L : E n →L[ℝ] E n => ⇑L) (Work.NN.Core.tupleDeriv_comp T).1) x

/-- **The transport identity for the `(0,1)`-operator.** -/
theorem dbar_comp_tupleDeriv (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n)
    (u : Cn n → ℂ) (x : E n) :
    Submission.dbar J (fun y : E n => u (tupleDeriv T y)) x
      = (Work.NN.Core.dbarCn (Jtr J T) u (tupleDeriv T x)).comp (tupleDeriv T) := by
  ext v
  rw [Submission.dbar_apply, ContinuousLinearMap.comp_apply, Work.NN.Core.dbarCn_apply,
    Work.NN.Core.fderiv_comp_tupleDeriv_apply, Work.NN.Core.fderiv_comp_tupleDeriv_apply]
  have h1 : Jtr J T (tupleDeriv T x) (tupleDeriv T v) = tupleDeriv T (J x v) := by
    show tupleDeriv T (J (tupleDerivInv T (tupleDeriv T x)) (tupleDerivInv T (tupleDeriv T v)))
      = tupleDeriv T (J x v)
    rw [tupleDerivInv_tupleDeriv, tupleDerivInv_tupleDeriv]
  rw [h1]

/-- The transported structure squares to `-1` where `J` does. -/
theorem Jtr_sq (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) (z : Cn n)
    (h : ∀ v : E n, J (tupleDerivInv T z) (J (tupleDerivInv T z) v) = -v) (w : Cn n) :
    Jtr J T z (Jtr J T z w) = -w := by
  rw [Jtr_apply, Jtr_apply, tupleDerivInv_tupleDeriv, h (tupleDerivInv T w), map_neg,
    Work.NN.Core.tupleDeriv_tupleDerivInv]

/-- If `J 0` is the transport of `i` by `T`, then the transported structure at `0` is the
standard structure `JstdCn`. -/
lemma Jtr_zero_eq_JstdCn (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v) (w : Cn n) :
    Jtr J T 0 w = Complex.I • w := by
  have hstd : J 0 = stdOf T 0 := (Work.NN.Core.eq_stdOf_iff J T).mp hT
  rw [Jtr_apply, map_zero (tupleDerivInv T), hstd, stdOf_apply]
  show tupleDeriv T (T.symm (Complex.I • T (tupleDerivInv T w))) = Complex.I • w
  rw [show tupleDeriv T (T.symm (Complex.I • T (tupleDerivInv T w)))
        = Complex.I • tupleDeriv T (tupleDerivInv T w) from by
      show ecInvL n (T (T.symm (Complex.I • T (tupleDerivInv T w))))
        = Complex.I • ecInvL n (T (tupleDerivInv T w))
      rw [ContinuousLinearEquiv.apply_symm_apply, ecInvL_smul],
    Work.NN.Core.tupleDeriv_tupleDerivInv]

/-- The perturbation of the transported structure, `A = J₁ - Jstd`. -/
noncomputable def Atr (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) :
    Cn n → Cn n →L[ℝ] Cn n := fun z => Jtr J T z - JstdCn n z

lemma Atr_apply (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n) (z w : Cn n) :
    Atr J T z w = tupleDeriv T (J (tupleDerivInv T z) (tupleDerivInv T w)) - Complex.I • w := by
  show Jtr J T z w - (JstdCn n z) w = _
  rw [JstdCn_apply]
  rfl

lemma Atr_zero (J : E n → E n →L[ℝ] E n) (T : E n ≃L[ℝ] F n)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v) (w : Cn n) : Atr J T 0 w = 0 := by
  show Jtr J T 0 w - (JstdCn n 0) w = 0
  rw [Jtr_zero_eq_JstdCn J T hT w, JstdCn_apply, sub_self]

end Work.NN.Final
