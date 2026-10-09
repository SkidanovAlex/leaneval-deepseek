import Mathlib
import Submission.Work.SSGRoute.valuation_lt_one_algebraMap_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LevelInertiaProEll

theorem residuePrimeNeZero
    (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) :
    (p : IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) ≠ 0 := by
  -- The comap `R` cuts out the same "strictly less than one" set as `A` on `↥M`.
  have hbridge := Work.SSGRoute.valuation_lt_one_algebraMap_iff A
      (A.comap (algebraMap ↥M Ω)) rfl ((p : ↥M))
  -- `↥M` and `Ω` see `p` the same way.
  have heq : algebraMap ↥M Ω ((p : ↥M)) = ((p : ℚ) : Ω) := by
    rw [map_natCast, Rat.cast_natCast]
  have hnot : ¬ (A.comap (algebraMap ↥M Ω)).valuation ((p : ↥M)) < 1 := by
    rw [← hbridge, heq]
    exact h
  -- Hence `p` is not in the maximal ideal of `R` ...
  have hmem : (p : A.comap (algebraMap ↥M Ω)) ∉
      IsLocalRing.maximalIdeal (A.comap (algebraMap ↥M Ω)) := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hnot
  -- ... so its residue is nonzero, and `residue` commutes with `Nat.cast`.
  have hres : IsLocalRing.residue (A.comap (algebraMap ↥M Ω))
      (p : A.comap (algebraMap ↥M Ω)) ≠ 0 := fun hc =>
    hmem ((IsLocalRing.residue_eq_zero_iff _).mp hc)
  rwa [← map_natCast (IsLocalRing.residue (A.comap (algebraMap ↥M Ω))) p]

end Work.SSGRoute.LevelInertiaProEll
