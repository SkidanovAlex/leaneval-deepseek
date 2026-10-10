import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.Reconstruct.exists_aux_imaginary_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary imaginary quadratic levels over an arbitrary number field

For a number field `K ⊆ Ω` and an *arbitrary* finite level `L/K` (no total reality
assumption), we produce two square roots `i` (`i ^ 2 = -1`) and `y` (`y ^ 2 = -q`, `q > 0`)
inside `Ω` such that the two quadratic extensions `L(i)` and `L(y)` meet exactly in `L`:

`(L ⊔ K⟮i⟯) ⊓ (L ⊔ K⟮y⟯) = L`.

The construction is elementary: choose a prime `q` which is not a square in `L`
(`NK.Reconstruct.exists_prime_not_sq`).  Then:

* if `i ∈ L` (resp. `y ∈ L`) the corresponding extension is trivial and the claim is
  immediate;
* otherwise both `L(i)` and `L(y)` are quadratic extensions of `L`; they coincide only if
  `i ∈ L` or `q` is a square in `L`, neither of which holds, so they are distinct and hence
  linearly disjoint over `L` (`NK.Reconstruct.inf_sup_adjoin_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace NK.Reconstruct

theorem exists_aux_imaginary_level_gen {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K : NK.Reconstruct.NumFieldIn ℚ Ω)
    (L : IntermediateField ↥K.L Ω) [FiniteDimensional ↥K.L L] [NumberField ↥L] :
    ∃ (i y : Ω) (q : ℕ), i ^ 2 = -1 ∧ y ^ 2 = -(q : Ω) ∧ 0 < q ∧
      ((L ⊔ IntermediateField.adjoin ↥K.L {i}) ⊓
        (L ⊔ IntermediateField.adjoin ↥K.L {y}) = L) := by
  haveI hsc : IsSepClosed Ω := IsSepClosure.sep_closed ℚ
  haveI hchar : CharZero Ω := Algebra.charZero_of_charZero ℚ Ω
  haveI hFfin : FiniteDimensional ℚ ↥K.L := K.finite
  -- a prime which is not a square in `L`, viewed as a field over `ℚ`
  let Lq : IntermediateField ℚ Ω := IntermediateField.restrictScalars ℚ L
  haveI hLq : FiniteDimensional ℚ ↥Lq := FiniteDimensional.trans ℚ ↥K.L ↥L
  obtain ⟨q, hqprime, hqnsq⟩ := exists_prime_not_sq Lq
  have hqnsq0 : ¬ ∃ x : ↥L, x ^ 2 = (q : ↥L) := hqnsq
  have hqnsq' : ¬ IsSquare (q : ↥L) := by
    rintro ⟨r, hr⟩
    exact hqnsq0 ⟨r, by rw [hr, pow_two]⟩
  -- square roots of `-1` and of `-q`
  obtain ⟨i, hi⟩ : ∃ i : Ω, i ^ 2 = -1 := by
    obtain ⟨j, hj⟩ := IsSepClosed.exists_eq_mul_self (-1 : Ω)
    exact ⟨j, by rw [pow_two, hj]⟩
  obtain ⟨y, hy⟩ : ∃ y : Ω, y ^ 2 = -(q : Ω) := by
    obtain ⟨j, hj⟩ := IsSepClosed.exists_eq_mul_self (-(q : Ω))
    exact ⟨j, by rw [pow_two, hj]⟩
  refine ⟨i, y, q, hi, hy, hqprime.pos, ?_⟩
  by_cases hiL : i ∈ (L : Set Ω)
  · -- `i ∈ L`, so the first extension is trivial
    have hM : L ⊔ IntermediateField.adjoin ↥K.L ({i} : Set Ω) = L := by
      rw [sup_eq_left]
      rw [IntermediateField.adjoin_le_iff]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hiL
    rw [hM]
    exact inf_eq_left.mpr le_sup_left
  · by_cases hyL : y ∈ (L : Set Ω)
    · -- `y ∈ L`, so the second extension is trivial
      have hN : L ⊔ IntermediateField.adjoin ↥K.L ({y} : Set Ω) = L := by
        rw [sup_eq_left]
        rw [IntermediateField.adjoin_le_iff]
        rintro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hyL
      rw [hN]
      exact inf_eq_right.mpr le_sup_left
    · -- both extensions are quadratic and distinct
      exact inf_sup_adjoin_eq (F := ↥K.L) (Ω := Ω) L hi hy hiL hyL hqnsq'

end NK.Reconstruct
