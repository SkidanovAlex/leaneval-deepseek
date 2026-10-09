/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coinduced module `G → R`

This module re-exports the coinduced module structure on function spaces,
`(g • f) x = f (x * g)`, from `Submission.InducedModules`, together with the basic API of
`Submission/Work/Tate/Basic.lean`, so that the vanishing results for Tate cohomology of
coinduced modules (`Work.Tate.H0_coind_subsingleton`, `Work.Tate.Hm1_coind_subsingleton`)
can be stated in this vocabulary.

The action is registered as a global instance by `Submission.InducedModules`
(`Submission.instSMulCoind`, `Submission.instDistribMulActionCoind`), so importing the present
module is enough to make `G → R` a `G`-module in the coinduced way.
-/
import Submission.Work.Tate.Basic
import Submission.InducedModules
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open scoped BigOperators

/-- The coinduced action on `G → R` is the one from `Submission.InducedModules`; this lemma
records the defining formula for convenience. -/
theorem coind_smul_eq {G : Type*} {R : Type*} [Group G] (g : G) (f : G → R) (x : G) :
    (g • f) x = f (x * g) := rfl

/-- The trivial `SMul` law for the coinduced action, recorded separately from `one_smul` because
the coinduced `SMul` and the pointwise `DistribSMul` on `G → R` are different instances. -/
theorem coind_one_smul {G : Type*} {R : Type*} [Group G] (f : G → R) :
    (1 : G) • f = f := by
  funext x
  rw [coind_smul_eq, mul_one]

theorem coind_mul_smul {G : Type*} {R : Type*} [Group G] (g h : G) (f : G → R) :
    (g * h) • f = g • (h • f) := by
  funext x
  simp only [coind_smul_eq, mul_assoc]

theorem coind_smul_zero {G : Type*} {R : Type*} [Group G] [Zero R] (g : G) :
    g • (0 : G → R) = 0 := by
  funext x
  rw [coind_smul_eq]
  rfl

theorem coind_smul_add {G : Type*} {R : Type*} [Group G] [Add R] (g : G) (f f' : G → R) :
    g • (f + f') = g • f + g • f' := by
  funext x
  simp only [coind_smul_eq, Pi.add_apply]

theorem coind_smul_neg {G : Type*} {R : Type*} [Group G] [Neg R] (g : G) (f : G → R) :
    g • (-f) = -(g • f) := by
  funext x
  simp only [coind_smul_eq, Pi.neg_apply]

theorem coind_smul_sub {G : Type*} {R : Type*} [Group G] [Sub R] (g : G) (f f' : G → R) :
    g • (f - f') = g • f - g • f' := by
  funext x
  simp only [coind_smul_eq, Pi.sub_apply]

end Work.Tate
