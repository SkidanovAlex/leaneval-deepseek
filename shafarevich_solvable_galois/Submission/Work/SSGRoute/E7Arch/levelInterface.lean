import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E7Arch.decomp_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.E7Arch

/-- **The place of the finite level `L` below the place `A` of `Ω`**, i.e. the intersection
`A ∩ L` regarded as a finite place of the number field `L`. -/
noncomputable def levelPlace (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [FiniteDimensional k L] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  Submission.NeukirchUchida.Local.placeOf (Submission.NeukirchUchida.primeOf A hA) A
    (Submission.NeukirchUchida.primeOf_spec A hA) L

/-- **The decomposition group of `A ∩ L` in `Gal(L/k)`.** -/
noncomputable def levelDecomp (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] :
    Subgroup (L ≃ₐ[k] L) :=
  Submission.NeukirchUchida.Local.decompositionSubgroup (K := k) (levelPlace k Ω A hA L)

/-- The order of that decomposition group is the local degree `e · f` of `A` at the level `L`. -/
theorem card_levelDecomp_eq (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] :
    Nat.card ↥(levelDecomp k Ω A hA L) =
      (Submission.NeukirchUchida.primeOf A hA).asIdeal.ramificationIdxIn (𝓞 L) *
        (Submission.NeukirchUchida.primeOf A hA).asIdeal.inertiaDegIn (𝓞 L) :=
  Submission.NeukirchUchida.Local.card_decompositionSubgroup (Submission.NeukirchUchida.primeOf A hA)
    (levelPlace k Ω A hA L)
    (Submission.NeukirchUchida.Local.placeOf_liesOver (Submission.NeukirchUchida.primeOf A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) L)

/-- **`L` realises local degree at least three at `A`**: the decomposition group of `A ∩ L` has at
least three elements, i.e. the local degree of `A` at the level `L` is `e · f ≥ 3`. -/
def LevelHasLocalDegreeGeThree (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) : Prop :=
  ∃ (hfin : FiniteDimensional k L) (hnorm : Normal k L),
    letI : FiniteDimensional k L := hfin
    letI : Normal k L := hnorm
    3 ≤ Nat.card ↥(levelDecomp k Ω A hA L)

/-- **The reduction**: one level with local degree ≥ 3 makes `decomp k A` different from every
`Subgroup.zpowers c` with `c ^ 2 = 1`. -/
theorem decomp_ne_zpowers_of_sq_eq_one_of_levelHasLocalDegree
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (L : IntermediateField k Ω)
    (h : LevelHasLocalDegreeGeThree k Ω A hA L)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    SSGRoute.decomp k A ≠ Subgroup.zpowers c := by
  obtain ⟨hfin, hnorm, h3⟩ := h
  letI : FiniteDimensional k L := hfin
  letI : Normal k L := hnorm
  have h3' : 3 ≤ Nat.card (Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
      (Submission.NeukirchUchida.Local.placeOf (Submission.NeukirchUchida.primeOf A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) L)) := h3
  exact decomp_ne_zpowers_of_sq_eq_one_of_level k Ω A hA _ (Submission.NeukirchUchida.primeOf_spec A hA)
    L h3' c hc

/-- **`LocalGroupDisjoint` follows from the existence of one such level** (for every finite place
`A`; this is the exact remaining arithmetic obligation of `E7Arch/g1Assembly`). -/
theorem decomp_ne_zpowers_of_sq_eq_one_of_levelExists
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ∃ L : IntermediateField k Ω, LevelHasLocalDegreeGeThree k Ω A hA L)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    SSGRoute.decomp k A ≠ Subgroup.zpowers c := by
  obtain ⟨L, hL⟩ := h
  exact decomp_ne_zpowers_of_sq_eq_one_of_levelHasLocalDegree k Ω A hA L hL c hc

end Work.SSGRoute.E7Arch
