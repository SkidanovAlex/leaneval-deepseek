/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Descent of almost splitting to splitting

The shape of the final step of the equal characteristic `p` argument (and of the derived
variant): the obstruction is an ideal `I ⊆ A` (in the affine case `I = evalIdeal A B`; in the
derived case the image of `Hom_{D(A)}(RΓ(X,𝒪), A[0]) → A`, `r ↦ r(unit)`).  If, after base
change to a faithfully flat perfect `S`, some nonzero `a ∈ I` acquires all its `p^e`-th roots
*inside* `I·S`, then `I` must be the unit ideal, i.e. the obstruction vanishes.
-/
import Mathlib
import Submission.Work.DSEQP.Basic
import Submission.Work.DSEQP.krull_descent

namespace Work.DSEQP

/-- **Descent of almost splitting.**  Let `A` be a Noetherian local domain, `I ⊆ A` an ideal,
`0 ≠ a ∈ I`, and `S` a faithfully flat `A`-algebra.  If for every `e` the `p^e`-th root of `a`
lies in `I·S`, then `I` is the unit ideal.

Equivalently (contrapositive): an obstruction lying in a *proper* ideal cannot become
"almost split" after a faithfully flat base change. -/
theorem one_mem_of_forall_pthRoot_mem (A S : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S] (p : ℕ)
    [Fact p.Prime] {I : Ideal A} {a : A} (ha : a ∈ I) (ha0 : a ≠ 0)
    (h : ∀ e : ℕ, ∃ t : S, t ∈ I.map (algebraMap A S) ∧ t ^ (p ^ e) = algebraMap A S a) :
    (1 : A) ∈ I := by
  by_contra h1
  exact krull_descent A S p I (IsLocalRing.le_maximalIdeal fun htop => h1 (htop ▸ Submodule.mem_top))
    ha ha0 h

end Work.DSEQP
