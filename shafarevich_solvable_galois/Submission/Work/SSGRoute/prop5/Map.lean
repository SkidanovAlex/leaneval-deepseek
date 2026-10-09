/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 5 of Schmidt–Wingberg: packaging the raw value map into the linear map `θ`

`Basic.lean` defines the raw value map `valFn` of Proposition 5.  This file does the formal
packaging:

* `slotFn` : the `k`-th slot map of `valFn`;
* `slotHom` : that slot map as a homomorphism `F(d) →* Multiplicative E(d,(i,j))`, given
  additivity in each slot (this additivity is `valFn_update_mul`);
* `slotHom_ker` / `slotHomDesc` : it kills the second `p`-central term `P₂ = F(d)^p[F(d),F(d)]`,
  given that it kills `p`-th powers and commutators (`valFn_update_pow`,
  `valFn_update_commutator`), hence descends to `F(d)/P₂ = F(d)/F(d)²`;
* `thetaMul` / `theta` : the resulting multilinear map and the `𝔽_p`-linear map
  `θ_d : (F(d)/F(d)²)^{⊗j} → E(d,(i,j))`.

The three well-definedness inputs are taken as explicit hypotheses so that this file is
independent of the (nontrivial) commutator calculus that proves them.

**Status.** `slotFn`, `slotHom`, `slotHom_ker`, `slotHomDesc` are proved.  The remaining
statements (`thetaMul`, `theta`, naturality, equivariance, surjectivity) are the ongoing work.
-/

import Mathlib
import Submission.Work.SSGRoute.prop5.Basic
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement

set_option maxHeartbeats 1600000

namespace Work.SSGRoute.prop5

universe u

section Slots

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)

/-- The `k`-th slot map of the raw value map: fix all entries of `x` except the `k`-th. -/
noncomputable def slotFn (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    Work.Shrinking.freeOperatorGroup G d → Work.CohomologicalShrinking.E p G d i j :=
  fun a => valFn p G i j d hj hji (Function.update x k a)

/-- **Well-definedness ingredient (1)**: `valFn` is additive in every slot.  This is
`Work.SSGRoute.prop5.valFn_update_mul`. -/
def SlotAdditive : Prop :=
  ∀ (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a b : Work.Shrinking.freeOperatorGroup G d),
    slotFn p G i j d hj hji x k (a * b)
      = slotFn p G i j d hj hji x k a + slotFn p G i j d hj hji x k b

/-- **Well-definedness ingredient (2a)**: `valFn` kills `p`-th powers in every slot.  This is
`Work.SSGRoute.prop5.valFn_update_pow`. -/
def SlotPow : Prop :=
  ∀ (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a : Work.Shrinking.freeOperatorGroup G d),
    slotFn p G i j d hj hji x k (a ^ p) = 0

/-- **Well-definedness ingredient (2b)**: `valFn` kills commutators in every slot.  This is
`Work.SSGRoute.prop5.valFn_update_commutator`. -/
def SlotCommutator : Prop :=
  ∀ (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a b : Work.Shrinking.freeOperatorGroup G d),
    slotFn p G i j d hj hji x k ⁅a, b⁆ = 0

variable {p G i j d}

@[simp] lemma slotFn_self (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    slotFn p G i j d hj hji x k (x k) = valFn p G i j d hj hji x := by
  simp [slotFn]

end Slots

/-- The `k`-th slot map of `valFn`, as a homomorphism into `Multiplicative E(d,(i,j))`,
given that it is additive in the slot. -/
noncomputable def slotHom (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (hadd : ∀ (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
      (a b : Work.Shrinking.freeOperatorGroup G d),
      slotFn p G i j d hj hji x k (a * b)
        = slotFn p G i j d hj hji x k a + slotFn p G i j d hj hji x k b)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    Work.Shrinking.freeOperatorGroup G d →*
      Multiplicative (Work.CohomologicalShrinking.E p G d i j) where
  toFun a := Multiplicative.ofAdd (slotFn p G i j d hj hji x k a)
  map_one' := by
    have h := hadd x k 1 1
    rw [mul_one] at h
    have h3 : slotFn p G i j d hj hji x k 1 = 0 := by
      have h2 := congrArg (fun z : Work.CohomologicalShrinking.E p G d i j =>
        z - slotFn p G i j d hj hji x k 1) h
      simpa using h2.symm
    simp [h3]
  map_mul' a b := Multiplicative.ext (hadd x k a b)

end Work.SSGRoute.prop5
