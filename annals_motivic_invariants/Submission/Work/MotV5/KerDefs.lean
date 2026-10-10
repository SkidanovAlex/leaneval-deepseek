/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV5

# The fifth powers in the function field of a Weierstrass curve (characteristic 5)

Auxiliary definitions for the lemma `Work.MotV5.ker_deriv_fifthpowers`: for a Weierstrass curve `E`
over an algebraically closed field `N` of characteristic `5`, the set
`fifthPowers E = {s ^ 5 | s : Func E} ⊆ Func E` of fifth powers is a subfield (it contains `N`
because `N` is perfect), and it is contained in the kernel of every `N`-derivation of `Func E`.

The main structural input needed downstream (proved in terms of these definitions in the sibling
files) is that `Func E` is generated over `fifthPowers E` by the coordinate `genX E`, i.e. that
`fifthPowers E⟮genX E⟯ = ⊤`.

## Main definitions

* `Work.MotV5.fifthPowers E` — the subfield `{s ^ 5 | s : Func E}` of the function field.

## Main results

* `Work.MotV5.mem_fifthPowers` — membership characterization;
* `Work.MotV5.deriv_pow_five`, `Work.MotV5.deriv_fifthPowers_eq_zero` — a derivation kills fifth
  powers;
* `Work.MotV5.isPurelyInseparable_fifthPowers` — `Func E` is purely inseparable over `fifthPowers E`.

## Tags

elliptic curve, function field, derivation, inseparable extension
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

/-- `5` is prime: an explicit instance, needed by `add_pow_char` and by the `ExpChar` bookkeeping
of the purely inseparable theory. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {N : Type*} [Field N]

/-- The function field of a Weierstrass curve over a field of characteristic `5` again has
characteristic `5`. -/
instance instCharP_func [CharP N 5] (E : WeierstrassCurve N) : CharP (Work.MotC2.Func E) 5 :=
  charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective N (Work.MotC2.Func E)) 5

/-- The function field of a Weierstrass curve over a field of characteristic `5` again has
characteristic `5` (named form of the instance `instCharP_func`). -/
lemma charP_func [CharP N 5] (E : WeierstrassCurve N) : CharP (Work.MotC2.Func E) 5 :=
  instCharP_func E

variable [IsAlgClosed N] [CharP N 5]

/-- Every element of an algebraically closed field of characteristic `5` is a fifth power. -/
theorem exists_fifth_root (c : N) : ∃ s : N, s ^ 5 = c := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 5 - Polynomial.C c) (by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  rw [Polynomial.IsRoot] at hs
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hs
  exact ⟨s, sub_eq_zero.mp hs⟩

/-- **The subfield of fifth powers** of the function field of a Weierstrass curve: the image of the
Frobenius endomorphism `s ↦ s ^ 5`.  It is a subfield because `N` is perfect (`IsAlgClosed`) and
the characteristic is the prime `5`. -/
noncomputable def fifthPowers (E : WeierstrassCurve N) : IntermediateField N (Work.MotC2.Func E) where
  carrier := {z | ∃ s : Work.MotC2.Func E, s ^ 5 = z}
  mul_mem' := by rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩; exact ⟨s * t, by rw [mul_pow]⟩
  one_mem' := ⟨1, by rw [one_pow]⟩
  add_mem' := by
    rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, by rw [add_pow_char]⟩
  zero_mem' := ⟨0, by rw [zero_pow (by norm_num : (5 : ℕ) ≠ 0)]⟩
  algebraMap_mem' := by
    intro c
    obtain ⟨s, hs⟩ := exists_fifth_root (N := N) c
    exact ⟨algebraMap N (Work.MotC2.Func E) s, by rw [← map_pow, hs]⟩
  inv_mem' := by rintro a ⟨s, rfl⟩; exact ⟨s⁻¹, by rw [inv_pow]⟩

@[simp]
theorem mem_fifthPowers (E : WeierstrassCurve N) {z : Work.MotC2.Func E} :
    z ∈ fifthPowers E ↔ ∃ s : Work.MotC2.Func E, s ^ 5 = z := Iff.rfl

theorem fifthPowers_pow_mem (E : WeierstrassCurve N) (s : Work.MotC2.Func E) :
    s ^ 5 ∈ fifthPowers E := ⟨s, rfl⟩

theorem fifthPowers_exists_pow (E : WeierstrassCurve N) (z : fifthPowers E) :
    ∃ s : Work.MotC2.Func E, s ^ 5 = (z : Work.MotC2.Func E) := z.2

/-- The subfield of fifth powers of `Func E` has characteristic `5`. -/
instance instCharP_fifthPowers (E : WeierstrassCurve N) : CharP (fifthPowers E) 5 :=
  (algebraMap (fifthPowers E) (Work.MotC2.Func E)).charP
    (FaithfulSMul.algebraMap_injective (fifthPowers E) (Work.MotC2.Func E)) 5

/-- The subfield of fifth powers of `Func E` has characteristic `5` (named form). -/
lemma charP_fifthPowers (E : WeierstrassCurve N) : CharP (fifthPowers E) 5 :=
  instCharP_fifthPowers E

/-- **A derivation kills fifth powers**: in characteristic `5`,
`D (z ^ 5) = 5 * z ^ 4 * D z = 0`. -/
theorem deriv_pow_five (E : WeierstrassCurve N)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E)) (z : Work.MotC2.Func E) :
    D (z ^ 5) = 0 := by
  rw [Derivation.leibniz_pow]
  rw [nsmul_eq_mul, CharP.cast_eq_zero (Work.MotC2.Func E) 5, zero_mul]

/-- Every element of the subfield of fifth powers is killed by every derivation. -/
theorem deriv_fifthPowers_eq_zero (E : WeierstrassCurve N)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E)) (c : fifthPowers E) :
    D (c : Work.MotC2.Func E) = 0 := by
  obtain ⟨s, hs⟩ := c.2
  rw [← hs, deriv_pow_five]

/-- Every element of `Func E` is purely inseparable over the subfield of fifth powers. -/
theorem isPurelyInseparable_fifthPowers (E : WeierstrassCurve N) :
    IsPurelyInseparable (fifthPowers E) (Work.MotC2.Func E) := by
  rw [isPurelyInseparable_iff_pow_mem (fifthPowers E) 5]
  intro z
  exact ⟨1, ⟨⟨z ^ 5, fifthPowers_pow_mem E z⟩, rfl⟩⟩

end Work.MotV5
