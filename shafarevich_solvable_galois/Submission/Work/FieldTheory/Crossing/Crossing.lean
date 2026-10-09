/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closure of Galois realizability over `ℚ` under products with finite abelian groups

This file assembles the `Crossing` area:

* `ZMod.lean` : `realizableOver_prod_zmod`, crossing with a cyclic group `Multiplicative (ZMod n)`
  (built on `exists_disjoint_cyclic` from cyclotomic fields),
* `realizableOver_prod_pi.lean` : iterating the one-step crossing over a finite type-indexed
  product of cyclic groups,
* this file : `realizableOver_prod_commGroup`, using the structure theorem for finite abelian
  groups (`CommGroup.equiv_prod_multiplicative_zmod_of_finite`).

## Main declarations

* `realizableOver_prod_commGroup_of_prod_zmod` : the abstract iteration, with the one-cyclic-factor
  step as a hypothesis
* `realizableOver_prod_commGroup` : `RealizableOver ℚ G → RealizableOver ℚ (G × A)` for finite
  abelian `A`

-/
import Mathlib
import Submission.Combine
import Submission.Work.FieldTheory.Crossing.ZMod
import Submission.Work.FieldTheory.Crossing.realizableOver_prod_pi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Classical

noncomputable section

set_option linter.style.haveILetI false

/-- **Closure of realizability over `ℚ` under products with finite abelian groups**, from the
one-cyclic-factor step (`hstep`, provided by `realizableOver_prod_zmod`).

`A` is decomposed as `A ≃* ∀ i, Multiplicative (ZMod (n i))` with `1 < n i`
(`CommGroup.equiv_prod_multiplicative_zmod_of_finite`), the index type is re-indexed through the
chosen `Fintype` instance, the product is crossed in one go using `realizableOver_prod_pi`, and
the result is transported back along `MulEquiv.prodCongr`. -/
theorem realizableOver_prod_commGroup_of_prod_zmod (G : Type) [Group G] (A : Type) [CommGroup A]
    [Finite A]
    (hstep : ∀ (H : Type) [Group H] (m : ℕ), m ≠ 0 →
      Submission.RealizableOver ℚ H → Submission.RealizableOver ℚ (H × Multiplicative (ZMod m)))
    (h : Submission.RealizableOver ℚ G) :
    Submission.RealizableOver ℚ (G × A) := by
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI : Fintype ι := hι
  have hpi := realizableOver_prod_pi G ι n (fun i => (zero_lt_one.trans (hn i)).ne') hstep h
  exact hpi.of_mulEquiv (MulEquiv.prodCongr (MulEquiv.refl G) e.symm)

/-- **Closure of Galois realizability over `ℚ` under products with finite abelian groups.**  If
`G` is realizable as a Galois group over `ℚ` and `A` is finite abelian, then `G × A` is
realizable over `ℚ`. -/
theorem realizableOver_prod_commGroup (G : Type) [Group G] (A : Type) [CommGroup A] [Finite A]
    (h : Submission.RealizableOver ℚ G) : Submission.RealizableOver ℚ (G × A) :=
  realizableOver_prod_commGroup_of_prod_zmod G A
    (fun H _ m hm => realizableOver_prod_zmod H m hm) h


/-- **Closure under any finite product of finite abelian groups.**  (The product `∀ i, A i` is
again a finite abelian group, so this is `realizableOver_prod_commGroup` with `A := ∀ i, A i`.) -/
theorem realizableOver_prod_pi_commGroup (G : Type) [Group G] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, CommGroup (A i)] [∀ i, Finite (A i)]
    (h : Submission.RealizableOver ℚ G) :
    Submission.RealizableOver ℚ (G × (∀ i, A i)) :=
  realizableOver_prod_commGroup G (∀ i, A i) h

/-- Binary form of `realizableOver_prod_commGroup`, for convenience. -/
theorem realizableOver_prod_commGroup_prod (G : Type) [Group G] (A B : Type)
    [CommGroup A] [CommGroup B] [Finite A] [Finite B]
    (h : Submission.RealizableOver ℚ G) :
    Submission.RealizableOver ℚ (G × (A × B)) :=
  realizableOver_prod_commGroup G (A × B) h

end

end Work.FieldTheory.Crossing
