import Mathlib
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `1`-units of an odd `p`-adic completion are squares

Local arithmetic used by the p. 16 computation of Schmidt–Wingberg's corrected proof
(`SSGRoute/ZDataTwo/TwoRec/claimOfPreTwo_diagonal`, step 3 of the plan): if `P ∤ 2` and `x/y` is a
`1`-unit (i.e. `x/y ≡ 1` modulo the prime), then `x/y` is a **square** in the completion, so the
local Hilbert symbol `(·, b)_P` cannot distinguish `x` from `y`.

Here `F = Q.adicCompletion k` is the completion of a number field at a finite place `Q`, and the
`1`-units of `F` are the elements `1 + t` with `t` in the maximal ideal of the ring of integers
`Q.adicCompletionIntegers k`.  The statement is Hensel's lemma for the polynomial `X² - (1 + t)`
(the residue `1` is a square, and `2` is a unit at an odd place):
`Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow`.
-/

open scoped Classical

noncomputable section

namespace Work.SSGRoute.ZConstruction

/-- **A unit of a Henselian local ring whose residue is an `n`-th power in the residue field is an
`n`-th power** (restatement, for the fraction field, of
`Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow`). -/
theorem exists_unit_pow_eq_of_residue_pow {R F : Type*} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) (u : Rˣ)
    (h : Units.map (IsLocalRing.residue R).toMonoidHom u ∈ (powMonoidHom n).range) :
    ∃ s : Fˣ, ((s : F)) ^ n = algebraMap R F (u : R) := by
  obtain ⟨w, hw⟩ := Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow n hn u h
  have hwn : ((w : R)) ^ n = (u : R) := by
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun v : Rˣ => (v : R)) hw
  refine ⟨Units.map (algebraMap R F) w, ?_⟩
  show ((Units.map (algebraMap R F) w : Fˣ) : F) ^ n = algebraMap R F (u : R)
  rw [show ((Units.map (algebraMap R F) w : Fˣ) : F) = algebraMap R F (w : R) from rfl]
  rw [← map_pow, hwn]

/-- **A `1`-unit of the ring of integers of a `p`-adic completion at an odd place is a square in
the completion**: for `t` in the maximal ideal and `2` a unit of the integers,
`1 + t = s²` for some unit `s` of the completion `F = Q.adicCompletion k`.

This is step 3 of the p. 16 computation: `x/y ≡ 1` modulo `Q` (with `Q ∤ 2`) implies that `x/y` is
a square in the completion, hence the local symbol `(·, b)_Q` cannot distinguish `x` from `y`. -/
theorem exists_unit_sq_one_add {k : Type*} [Field k] [NumberField k]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h2 : IsUnit (2 : Q.adicCompletionIntegers k))
    (t : Q.adicCompletionIntegers k)
    (ht : t ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers k)) :
    ∃ s : (Q.adicCompletion k)ˣ,
      (s : Q.adicCompletion k) * (s : Q.adicCompletion k) =
        algebraMap (Q.adicCompletionIntegers k) (Q.adicCompletion k) (1 + t) := by
  haveI := Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
    (R := NumberField.RingOfIntegers k) (K := k) Q
  have htres : IsLocalRing.residue (Q.adicCompletionIntegers k) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ht
  have hunit : IsUnit (1 + t : Q.adicCompletionIntegers k) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [map_add, map_one, htres, add_zero]
    exact one_ne_zero
  have hres1 : Units.map (IsLocalRing.residue (Q.adicCompletionIntegers k)).toMonoidHom
      (IsUnit.unit hunit) ∈ (powMonoidHom 2).range := by
    have hres_apply : IsLocalRing.residue (Q.adicCompletionIntegers k)
        ((IsUnit.unit hunit : (Q.adicCompletionIntegers k)ˣ) :
          Q.adicCompletionIntegers k) = 1 := by
      rw [IsUnit.unit_spec, map_add, map_one, htres, add_zero]
    refine ⟨1, ?_⟩
    rw [show Units.map (IsLocalRing.residue (Q.adicCompletionIntegers k)).toMonoidHom
        (IsUnit.unit hunit) = 1 from Units.ext hres_apply, map_one]
  obtain ⟨s, hs⟩ := exists_unit_pow_eq_of_residue_pow
    (R := Q.adicCompletionIntegers k) (F := Q.adicCompletion k) 2 h2 (IsUnit.unit hunit) hres1
  refine ⟨s, ?_⟩
  rw [pow_two] at hs
  rw [IsUnit.unit_spec hunit] at hs
  exact hs

end Work.SSGRoute.ZConstruction
