import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux

/-!
# The two inputs of the prime-power case of Hilbert reciprocity

`NK.CFTLib.HilbertReciprocityOnePlace` (Hilbert reciprocity in the "no singleton place of
local-norm failure" form) is reduced to its prime-power-degree case by the *proved*
`NK.NUV2.ARL.HR.hilbertReciprocityOnePlace_of_primePower`.  This module fixes, as two `Prop`s, the
two remaining inputs of the prime-power case, so that the final assembly
(`NK.CFTLib.Existence.hilbertReciprocityOnePlace_of_inputs`) can be stated independently of their
proofs:

* `LocalBaseChangeInput` — the *local* input (Milne, *CFT*, III.3.5/III.3.6, "L6" of the plan): for
  `E = L·M` over `K`, a finite place `Q` of `K` and a place `w | Q` of `M` which is unramified over
  `Q`, if every local degree `[L_r : K_Q]` divides `[M_w : K_Q]`, then every `x ∈ Kˣ` is a local
  norm from `E` over `M_w`.  This is the statement of
  `NK.CFTLib.IdeleHasse.Descent.localBaseChange_of_unramified` (Milne III.3.6, proved via the
  index sandwich `NK.CFTLib.IdeleHasse.normGroup_index_sandwich` and the local norm index
  theorem).

* `TransferInput` — the *descent* (`transfer`) step of the Brauer descent (Milne, *CFT*, VII §8):
  from the one-place statement at the cyclic cyclotomic auxiliary level `M/K` at the single place
  `v₀`, the one-place statement at `L/K` at `v₀` follows.  This is the statement of
  `NK.CFTLib.Existence.descentTransfer_at_v0` (equivalently `Descent.transferStep` /
  `HR.transferAt`, with the hypothesis `hM` restricted to the single place `v₀`, which is all the
  proof uses).

The primed/auxiliary cyclotomic inputs (`HR.isCyclotomic_onePlace_real`,
`HR.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero`, and the triviality at a
complex place) are already proved and are consumed directly by the assembly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- **The local input** (Milne, *CFT*, III.3.5/III.3.6): the base change of the local invariant, in
the form in which the descent consumes it.  Verbatim the statement of
`NK.CFTLib.IdeleHasse.Descent.localBaseChange_of_unramified`. -/
def LocalBaseChangeInput : Prop :=
  ∀ {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
    [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1)
    (hloc : ∀ (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
              (hr : r.asIdeal.LiesOver Q.asIdeal),
      Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M)),
    ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
      (hq : q.asIdeal.LiesOver w.asIdeal),
      ∀ x : Kˣ, Units.map (algebraMap M (w.adicCompletion M)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
        (Place.localNormFinite q w hq).range

/-- **The descent (`transfer`) input** (Milne, *CFT*, VII §8): verbatim the statement of
`NK.CFTLib.Existence.descentTransfer_at_v0`. -/
def TransferInput : Prop :=
  ∀ {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M]
    [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ (y : Kˣ),
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        NK.CFTLib.IdeleHasse.localImageAt v y ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀)
    (x : Kˣ)
    (hx : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : NK.GlobalCFT.Place M, NK.GlobalCFT.Place.LiesOver w v₀ →
      Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w),
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀

end NK.CFTLib.Existence
