import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_hpair
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_perfect_left
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_perfect_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G1⁺`'s clause bundle for the finite half `g1FinHalf` — the interface supply

`PT/canonical_localPairing_reciprocity_converse.lean` (node `G1⁺`) discharges its `hclauses` block
clause by clause; clauses (1)–(3) come from `PT/G1plusOwn/levelFree.lean` and clauses (4)
left/right are the two remaining `sorry`s of that file.  The v4 restatement
(`_lead_design/v4_0215/restates/NOTE.md`) moved those two clauses to *abstract* nodes over a
`pair`/`βl` interface (`Work.SSGRoute.PT.G1plusOwn.g1FinHalf_perfect_left` / `_right`), so that their
types do not mention the dictionary `PT.finZB` (whose source
`E1aClean.localDictionary_natural_family` is still open and would taint them).

This file performs the **instantiation** the lead's note prescribes, in the node lane, so that
`G1⁺`'s `hclauses` block becomes a single `exact`:

* `βl := PT.finZB`, with the four clauses `finZB_add`, `finZB_eq_zero_iff`, `finZB_surjective`,
  `finZB_unramified` (all proved in `PT/finHalfData.lean` from `finZB_spec`);
* `pair := G1pOwn.g1FinHalf χ M`;
* `hpair` from `Work.SSGRoute.PT.G1plusOwn.g1FinHalf_hpair`.

The *type* of the result mentions `g1FinHalf` (and hence, transitively, the still-open
`localDictionary_natural_family`), which is unavoidable: it is the `G1⁺`-side statement itself.  It
certifies as soon as that family lands.
-/

open scoped TensorProduct

namespace Work.SSGRoute.PT.G1plusOwn

/-- **The clause bundle (`H1Pair.PairClauses`) of `G1⁺`'s finite half** at a decomposition group,
assembled from the proved clause lemmas of `levelFree` and the two restated perfectness nodes at the
interface `βl := PT.finZB`, `pair := g1FinHalf`. -/
theorem g1FinHalf_pairClauses
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.H1Pair.PairClauses p K T M
      (fun a b => Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
        (SSGRoute.decomp k A) a b)
      (SSGRoute.decomp k A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- clause (1): additivity in the first variable
    intro a a' b ha ha' hb
    exact Work.SSGRoute.PT.G1pOwn.g1FinHalf_add_left p k Ω K ζ hζ hζK T hT χ hχadd M A hA a a' b
      ha.2 ha'.2 hb.2 (SSGRoute.IsLocConstOn.add ha.2 ha'.2) ha.1 ha'.1
  · -- clause (2): additivity in the second variable
    intro a b b' ha hb hb'
    exact Work.SSGRoute.PT.G1pOwn.g1FinHalf_add_right p k Ω K ζ hζ hζK T hT χ hχcompat hχadd
      M A hA a b b' ha.2 hb.2 hb'.2 (SSGRoute.IsLocConstOn.add hb.2 hb'.2) hb.1 hb'.1
  · -- clause (3): vanishing on a coboundary
    intro a b ha hb hcob
    exact Work.SSGRoute.PT.G1pOwn.g1FinHalf_coboundary p k Ω K ζ hζ hζK T hT χ hχadd M A hA a b
      ha.2 hb.2 ha.1 hb.1 hcob
  · -- clause (4), left: perfectness in the first variable
    intro a ha h
    refine Work.SSGRoute.PT.G1plusOwn.g1FinHalf_perfect_left p k Ω K ζ hζ hζK T hT χ hχadd hχinj
      hχcompat M (fun A hA => Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA) ?_ ?_ ?_ ?_
      (fun H a b => Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b) ?_
      A hA a ha.1 ha.2 h
    · intro A hA b b' hb hlb hb' hlb'
      exact Work.SSGRoute.PT.finZB_add p k Ω K ζ hζ hζK T hT M A hA b b' hb hlb hb' hlb'
    · intro A hA b hb hlb
      exact Work.SSGRoute.PT.finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA b hb hlb
    · intro A hA y
      exact Work.SSGRoute.PT.finZB_surjective p k Ω K ζ hζ hζK T hT M A hA y
    · intro A hA hp hram b hb hlb hiner
      exact Work.SSGRoute.PT.finZB_unramified p k Ω K ζ hζ hζK T hT M A hA hp hram b hb hlb hiner
    · intro A hA a b hla hlb hb L hN hFD hGal hKL hAlg hS1 hS2 b₀ hb₀
      letI : NumberField ↥L := hN
      letI : FiniteDimensional k ↥L := hFD
      letI : IsGalois k ↥L := hGal
      letI : Algebra ↥K ↥L := hAlg
      letI : IsScalarTower k ↥K ↥L := hS1
      letI : IsScalarTower ↥K ↥L Ω := hS2
      exact Work.SSGRoute.PT.G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA
        a b hla hlb hb L hKL b₀ hb₀
  · -- clause (4), right: perfectness in the second variable
    intro b hb h
    refine Work.SSGRoute.PT.G1plusOwn.g1FinHalf_perfect_right p k Ω K ζ hζ hζK T hT χ hχadd hχinj
      hχcompat M (fun A hA => Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA) ?_ ?_ ?_ ?_
      (fun H a b => Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b) ?_
      A hA b hb.1 hb.2 h
    · intro A hA b b' hb hlb hb' hlb'
      exact Work.SSGRoute.PT.finZB_add p k Ω K ζ hζ hζK T hT M A hA b b' hb hlb hb' hlb'
    · intro A hA b hb hlb
      exact Work.SSGRoute.PT.finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA b hb hlb
    · intro A hA y
      exact Work.SSGRoute.PT.finZB_surjective p k Ω K ζ hζ hζK T hT M A hA y
    · intro A hA hp hram b hb hlb hiner
      exact Work.SSGRoute.PT.finZB_unramified p k Ω K ζ hζ hζK T hT M A hA hp hram b hb hlb hiner
    · intro A hA a b hla hlb hb L hN hFD hGal hKL hAlg hS1 hS2 b₀ hb₀
      letI : NumberField ↥L := hN
      letI : FiniteDimensional k ↥L := hFD
      letI : IsGalois k ↥L := hGal
      letI : Algebra ↥K ↥L := hAlg
      letI : IsScalarTower k ↥K ↥L := hS1
      letI : IsScalarTower ↥K ↥L Ω := hS2
      exact Work.SSGRoute.PT.G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA
        a b hla hlb hb L hKL b₀ hb₀

end Work.SSGRoute.PT.G1plusOwn
