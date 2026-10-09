import Mathlib
import Submission.Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp
import Submission.Work.SSGRoute.E7cOmega.card_stab_eq_of_liesOver
import Submission.Work.SSGRoute.E7cOmega.card_stab_dvd_of_tower
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_p_dvd_stab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A Galois level `L ≥ L₀` whose prescribed finite place has `p`-divisible stabilizer

Given a finite Galois level `L₀ ≥ K` (both finite Galois over `k`) and a finite place `A` of `Ω`,
we need a finite Galois level `L ≥ L₀` such that the canonical prime `P = finQW L A hA` fixed by
`A` has stabilizer in `Gal(L/k)` of order divisible by `p`.

This is the "`≥ L₀`" strengthening of `Work.SSGRoute.PT.G1plusOwn.exists_level_p_dvd_stab`
(`L ≥ K`).  It follows from it by moving up to the compositum `K ⊔ L₀`: the upper level
`K ⊔ L₀` is again finite Galois over `k` (`IntermediateField.finiteDimensional_sup`,
`IsGalois k (K ⊔ L₀)`), contains both `K` and `L₀`, and the sibling theorem produces a further
level `L ≥ K ⊔ L₀` with the required `p`-divisibility; a fortiori `L ≥ L₀`.
-/

namespace Work.SSGRoute.PT.G1plusOwn

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem exists_level_ge_p_dvd_stab
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L₀ : IntermediateField k Ω) [FiniteDimensional k L₀] [IsGalois k L₀] (hK : K ≤ L₀) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (_ : NumberField L),
      L₀ ≤ L ∧
      p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) := by
  -- The compositum `LT = K ⊔ L₀` is finite Galois over `k` and contains both `K` and `L₀`.
  let LT : IntermediateField k Ω := K ⊔ L₀
  haveI : FiniteDimensional k LT := IntermediateField.finiteDimensional_sup K L₀
  haveI : IsGalois k LT := inferInstance
  -- Apply the sibling (`≥ K`) theorem at the level `LT = K ⊔ L₀`.
  obtain ⟨L, hfd, hgal, hnf, hle, hdiv⟩ :=
    exists_level_p_dvd_stab (p := p) (k := k) (Ω := Ω) (K := LT) A hA
  exact ⟨L, hfd, hgal, hnf, le_trans le_sup_right hle, hdiv⟩

end Work.SSGRoute.PT.G1plusOwn
