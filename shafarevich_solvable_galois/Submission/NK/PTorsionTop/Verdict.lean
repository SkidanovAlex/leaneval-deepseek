/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The honest verdict: what can and cannot be said about the abstract predicate

`NK.LocalAnabelian.HasPTorsionAbelianization p G` is `∃ x : Abelianization G, x ≠ 1 ∧ x ^ p = 1`
with `Abelianization G = G ⧸ commutator G` the quotient by the **abstract** commutator subgroup.

This file records the two formal facts which the verdict in `README.md` rests on:

* for a *commutative* group the old and the new predicate coincide
  (`hasPTorsionAbelianization_iff_hasPTorsionAbelianizationTop_of_commutative`, in `Basic.lean`),
  so no discrepancy can be exhibited inside the abelian world;
* **a `ℤ/p`-quotient does not produce `p`-torsion** (`zmodQuotient_without_pTorsion`), the
  elementary reason the intended `⟸` direction of the old `p_torsion_iff` cannot be justified:
  `Multiplicative ℤ` (or `ℤ_p`) has no element of order `p`, yet it has a surjection onto `ℤ/p`.

No claim is made in either direction for `G = Gal(K'/κ)`: see `README.md`.
-/
import Mathlib
import Submission.NK.PTorsionTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.PTorsionTop

universe u

noncomputable section

/-- **A `ℤ/p`-quotient does not force `p`-torsion.**  `Multiplicative ℤ` is torsion-free, yet it
admits a surjection onto `ℤ/p` (`p ≠ 0`).  Consequently the classical style of argument "there is a
cyclic degree-`p` extension, hence `p`-torsion in the abelianised Galois group" is invalid. -/
theorem zmodQuotient_without_pTorsion {p : ℕ} (hp : p ≠ 0) :
    (∃ f : Multiplicative ℤ →* Multiplicative (ZMod p), Function.Surjective f) ∧
      ¬ HasPTorsion p (Multiplicative ℤ) := by
  constructor
  · refine ⟨AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod p)), ?_⟩
    intro y
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective y.toAdd
    refine ⟨Multiplicative.ofAdd n, ?_⟩
    show Multiplicative.ofAdd ((n : ℤ) : ZMod p) = y
    rw [hn]
    exact (ofAdd_toAdd y).symm
  · rintro ⟨x, hx1, hxp⟩
    refine hx1 (Multiplicative.ext ?_)
    have h := congrArg Multiplicative.toAdd hxp
    simp only [toAdd_pow, toAdd_one] at h
    have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    have h' : (p : ℤ) * x.toAdd = 0 := by simpa [nsmul_eq_mul] using h
    exact (mul_eq_zero.mp h').resolve_left hp'

/-- **The discrepancy can only come from non-commutativity**: for a commutative topological group
the old predicate and the corrected one are both plain `p`-torsion. -/
theorem hasPTorsionAbelianization_iff_top_commutative (p : ℕ) (G : Type u) [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G] :
    NK.LocalAnabelian.HasPTorsionAbelianization p G ↔ HasPTorsionAbelianizationTop p G :=
  hasPTorsionAbelianization_iff_hasPTorsionAbelianizationTop_of_commutative p G

end

end NK.PTorsionTop
