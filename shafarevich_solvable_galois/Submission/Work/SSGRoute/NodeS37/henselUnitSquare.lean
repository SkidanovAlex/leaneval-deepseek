import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Hensel step of the inert/`ρ`-fixed branch of the p. 16 dichotomy

At a `ρ`-fixed place `A` the invariant factor `a` of Schmidt--Wingberg's p. 16 computation has to be
shown to be a **square** in the completion `↥K_A`.  The last step is Hensel's lemma: a unit of
`𝔭.adicCompletionIntegers ↥K` whose **residue** is a square (and `2` a unit there) is a square in
the integers, hence in the completion.

This is the general-unit version of `ZConstruction.LocalSquares.exists_unit_sq_one_add` (which
handles the `1`-unit case, i.e. residue `1`): the residue hypothesis is exactly what
`NodeS37.isSquare_algebraMap_of_finrank_two` supplies at an inert prime, where the residue lies in
the fixed residue field `κ_𝔭` of the quadratic residue extension `κ_A/κ_𝔭`.

The proof is `Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow` at `n = 2`.
-/

namespace Work.SSGRoute.NodeS37

/-- **Hensel: a unit of the integers of an odd completion with square residue is a square.** -/
theorem exists_sq_of_residue_isSquare {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers ↥K))
    (u : (𝔭.adicCompletionIntegers ↥K)ˣ)
    (hsq : IsSquare ((IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K)) u)) :
    ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      (c : 𝔭.adicCompletion ↥K) ^ 2 =
        algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)
          (u : 𝔭.adicCompletionIntegers ↥K) := by
  classical
  haveI := Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
    (R := NumberField.RingOfIntegers ↥K) (K := ↥K) 𝔭
  -- the residue is a square, hence the unit lies in the range of the squaring map
  have hmem : Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K)).toMonoidHom u ∈ (powMonoidHom 2).range := by
    obtain ⟨w, hw⟩ := hsq
    have hne : (IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K)) (u : 𝔭.adicCompletionIntegers ↥K) ≠ 0 :=
      IsUnit.ne_zero (IsUnit.map _ (Units.isUnit u))
    refine ⟨Units.mk0 w (by rintro rfl; exact hne (by simpa using hw)), ?_⟩
    ext
    rw [powMonoidHom_apply, Units.coe_map, Units.val_pow_eq_pow_val, pow_two, Units.val_mk0]
    change w * w = (IsLocalRing.residue (𝔭.adicCompletionIntegers ↥K)) (u : 𝔭.adicCompletionIntegers ↥K)
    rw [hw]
  obtain ⟨b, hb⟩ := Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow (R := 𝔭.adicCompletionIntegers ↥K) 2
    (by simpa using h2) u hmem
  have hb2 : b ^ 2 = u := by
    rw [powMonoidHom_apply] at hb
    exact hb
  refine ⟨Units.map (algebraMap (𝔭.adicCompletionIntegers ↥K) (𝔭.adicCompletion ↥K)).toMonoidHom b, ?_⟩
  have hb2coe : ((b : 𝔭.adicCompletionIntegers ↥K)) ^ 2 = ((u : 𝔭.adicCompletionIntegers ↥K)) := by
    have h := congrArg (fun v : (𝔭.adicCompletionIntegers ↥K)ˣ => (v : 𝔭.adicCompletionIntegers ↥K)) hb2
    simpa [Units.val_pow_eq_pow_val, pow_two] using h
  rw [Units.coe_map, ← map_pow, hb2coe]
  rfl

end Work.SSGRoute.NodeS37
