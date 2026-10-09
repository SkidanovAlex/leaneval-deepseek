import Mathlib
import Submission.Work.SSGRoute.LevelInertiaProEll.Defs
import Submission.Work.SSGRoute.LevelInertiaProEll.numberFieldValuationSubringBasic
import Submission.Work.SSGRoute.LevelInertiaProEll.residuePrimeNeZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.SSGRoute.LevelInertiaProEll

theorem levelRingBasic
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    IsDiscreteValuationRing (A.comap (algebraMap ↥M Ω)) ∧
    IsNoetherianRing (A.comap (algebraMap ↥M Ω)) ∧
    PerfectField (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) ∧
    Finite (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) ∧
    (∃ (ℓ f : ℕ), ℓ.Prime ∧ ℓ ≠ p ∧
      Nat.card (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) = ℓ ^ f) := by
  -- `B := A ∩ M` is a proper valuation subring of the number field `M`.
  obtain ⟨hdvr, hnoeth, hperf, hfin, ℓ, f, hℓprime, hℓchar, hcard⟩ :=
    numberFieldValuationSubringBasic ↥M (A.comap (algebraMap ↥M Ω)) (by
      intro htop
      exact hA (Submission.NeukirchUchida.Local.comap_algebraMap_eq_top_of_comap_eq_top
        (A := A) (L := M) htop))
  -- `p` is a nonzero element of the residue field of `A ∩ M`.
  have hres : (p : IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) ≠ 0 :=
    residuePrimeNeZero p k Ω A h M
  haveI : CharP (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) ℓ := hℓchar
  have hℓne : ℓ ≠ p := by
    intro hlp
    have hzero : (p : IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) = 0 := by
      rw [← hlp]
      exact CharP.cast_eq_zero (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) ℓ
    exact hres hzero
  exact ⟨hdvr, hnoeth, hperf, hfin, ⟨ℓ, f, hℓprime, hℓne, hcard⟩⟩

end Work.SSGRoute.LevelInertiaProEll
