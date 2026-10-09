import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.defs
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.preTwoExists
import Submission.Work.SSGRoute.P2Core.escapeStepNormalised
import Submission.Work.SSGRoute.H9.swHistKExists_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

/-! ROUTE (read this first).  This is the `p = 2` member of the recursion proved for odd `p` in
`Submission/Work/SSGRoute/H9/swHistKExists_proved.lean` — read its `Pre`, `Pre_congr`, `Pre_step`
and final `Nat.rec` argument, and mirror them.  The `p = 2` step oracle is
`Work.SSGRoute.P2Core.escapeStepNormalised` (PROVED, `Submission/Work/SSGRoute/P2Core/escapeStepNormalised.lean`),
which is the same statement as the odd-`p` `escape_realisation_core_normalised` *plus* the escape
normalisation `∃𝔮, Q.comap = valuationSubringAtPrime 𝔮 ∧ Odd (count 𝔮 b)` — the last conjunct of
`TwoRec.PreTwo`.  Use `TwoRec.TBlock` (place set), `TwoRec.prescDatum` (datum `prescribed − g`) with
the PROVED `TwoRec.prescDatum_add`, `TwoRec.prescDatum_locConst`,
`TwoRec.prescDatum_eq_zero_of_isConjPlace`, `TwoRec.prescDatum_eq_of_escape`, `TwoRec.TBlock_disj`,
`TwoRec.TBlock_covers_S`, `TwoRec.TBlock_covers_Q`.  At stage `n` apply the oracle with
`T := TwoRec.TBlock S s.f n`, `g := y`, `h := TwoRec.prescDatum ζ hζ hζK S y s.f s.hf n`; note
`IsSepClosure ↥K Ω` is available as `IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω`, and
`NumberField ↥K` as `NumberField.of_module_finite k ↥K`.  You will need to add short helper lemmas
above the theorem (e.g. `TBlock` finiteness and raw coverage from `hSram`, `prescDatum` invariance
under `gesKConj` and under conjugation by `τ ∈ K.fixingSubgroup`, and prefix-independence
`PreTwo_congr`); `Submission/Work/SSGRoute/P2Core/placeSetBookkeeping.lean` and
`Submission/Work/SSGRoute/H9/swHistKExists_proved.lean` show how. -/

theorem twoRecExists {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K),
      ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s := by
  -- The escape oracle of the `p = 2` recursion, in the bundled form `TwoRec.Oracle` consumed by
  -- `TwoRec.PreTwo_step` / `TwoRec.preTwoExists`: it is the proved `P2Core.escapeStepNormalised`.
  have hO : Work.SSGRoute.ZDataTwo.TwoRec.Oracle (K := K) Λ ζ hζ hζK := by
    intro T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhinf
    exact Work.SSGRoute.P2Core.escapeStepNormalised k Ω K Λ hKΛ ζ hζ hζK T hTfin hTdisj
      hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhinf
  exact Work.SSGRoute.ZDataTwo.TwoRec.preTwoExists (K := K) hKΛ ζ hζ hζK S hSfin hSram
    y hy hyc hyS hyT hyinf hO

end Work.SSGRoute.NodeS37
