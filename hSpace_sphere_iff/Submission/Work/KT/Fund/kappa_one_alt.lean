/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team
-/
import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_one

/-!
# `Work.KT.Fund.kappa_one_alt`

The trivial clutching class: for the unit `1` over `C(X × S¹, ℂ)` the clutched class `κ(1)` is the
class of the trivial rank-`n` bundle over `X × S²`,

  `kappa X n 1 = cls (Mat.one C(X × S², ℂ) n)`.

This is the same statement as `Work.KT.Fund.kappa_one`; it is recorded here under its own name so
that modules which cannot (for reasons of declaration-name clashes elsewhere in the workspace)
import `Fund/kappa_one.lean` still have access to the evaluation of `κ(1)`.
-/

namespace Work.KT.Fund

theorem kappa_one_alt (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ) :
    Work.KT.Fund.kappa X n (1 : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
      = Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) :=
  Work.KT.Fund.kappa_one X n

end Work.KT.Fund
