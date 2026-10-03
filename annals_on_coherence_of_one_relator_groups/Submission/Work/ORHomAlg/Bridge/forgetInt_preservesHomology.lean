/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The forgetful functor `ModuleCat S ⥤ ModuleCat ℤ` is exact.
-/
import Mathlib
import Submission.Work.ORHomAlg.Bridge.BridgeDefs

set_option autoImplicit false

open CategoryTheory

namespace Work.ORHomAlg.Bridge

universe u

/-- The forgetful functor `ModuleCat S ⥤ ModuleCat ℤ` (which keeps the underlying additive
group and its canonical `ℤ`-module structure) is exact: it preserves kernels and cokernels.
Both are computed on underlying additive groups in `ModuleCat`, and the functor does not
change these. -/
instance forgetInt_preservesHomology (S : Type u) [Ring S] : (forgetInt S).PreservesHomology := by
  refine (Functor.exact_tfae (forgetInt S)).out 2 3 |>.mp ?_
  intro T hT
  rw [ShortComplex.moduleCat_exact_iff] at hT ⊢
  intro x₂ hx₂
  exact hT x₂ hx₂

end Work.ORHomAlg.Bridge
