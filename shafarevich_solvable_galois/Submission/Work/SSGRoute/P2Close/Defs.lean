import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.reduce
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Closing the `p = 2` §4 core: the vocabulary of the last three pieces

This module (owned by the node lane of `Work.SSGRoute.scholz_succ_of_properStage`) carries the
vocabulary in which the last three pieces of the `p = 2` recursion of Schmidt--Wingberg §4 are
stated:

* `ClaimOracle` — the escape step **with** the paper's Claim (Schmidt--Wingberg p. 16: the escape
  class vanishes on the local groups of the siblings `σQ`, `σ ∉ G_K` with `res σ` an involution of
  `Gal(K|k)`).  This is `Work.SSGRoute.ZDataTwo.escapeStepKfreshNormalisedClaim`, i.e.
  `Work.SSGRoute.P2Core.escapeStepNormalised` plus the Claim; it is taken here as a *hypothesis*
  of the recursion step so that the bookkeeping half can be proved before the Claim lands.
* `ClaimClause` — the Claim for one pair `(b, Q)`.
* `PreTwoC` — the strengthened prefix invariant of the recursion: the lane's
  `Work.SSGRoute.ZDataTwo.TwoRec.PreTwo` (the oracle's local prescriptions, the involution clause,
  the confinement and the odd-count normalisation) **together with** the Claim at every stage.

Everything else (the Ψ-vector `TwoRec.psiVal`, the prescribed datum `TwoRec.prescDatum`, the place
set `TwoRec.TBlock`, the stage oracle `P2Core.escapeStepNormalised`, the datum specification
`P2Core.recDatum_spec`, the shoe box `pigeonhole_three_minimal`, the branch algebra
`P2Core.prescriptionAlgebra` and the six block equations `ZDataTwo.blocks_of_prVal`) is already on
disk and `sorry`-free.
-/

open scoped Pointwise

namespace Work.SSGRoute.P2Close

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The Claim for one pair `(b, Q)`.**  For every `σ ∉ G_K` whose restriction to `K` is an
involution of `Gal(K|k)`, the Kummer cochain of `b` vanishes on the local group of the sibling
`σ • Q`.  (Schmidt--Wingberg p. 16.) -/
def ClaimClause (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (Q : ValuationSubring Ω) (b : (↥K)ˣ) : Prop :=
  ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
    ∀ u ∈ SSGRoute.decomp k (σ • Q) ⊓ K.fixingSubgroup,
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b u = 0

/-- **The escape oracle with the Claim.**  This is
`Work.SSGRoute.ZDataTwo.escapeStepKfreshNormalisedClaim` (equivalently: the proved
`Work.SSGRoute.P2Core.escapeStepNormalised` with the Claim adjoined), with the escape step's
conclusion *and* the Claim inside the existential — **and** with the extra input that the paper's
proof of the Claim actually consumes: the datum `g + h A` is trivial on the whole local group of
every dyadic or `Λ`-ramified block `A ∈ T`, not merely on its inertia.  (See
`P2Close/NOTE_escapeStepClaim_findings.md`: without that clause a nontrivial unramified `2`-adic
class is admissible and the Hilbert-symbol chain of the Claim does not close.) -/
def ClaimOracle (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) : Prop :=
  ∀ (T : Finset (ValuationSubring Ω)), (∀ A ∈ T, SSGRoute.IsFinPlace k A) →
    (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B) →
    -- the coverage the p. 16 chain needs: `T` must meet every `K`-class over the places of `2` and
    -- of `Ram(K|k)`.  The hypothesis above does *not* give this: its second disjunct is
    -- `Λ|K`-ramification (`σ` is required to lie in `K.fixingSubgroup`), whereas the chain needs the
    -- places ramified in `K|k`.  (For `Λ = K` the disjunct is even unsatisfiable.)  In the recursion
    -- it is discharged from `hSram` (`Ram(K|k) ⊆ Ram(Λ|k)` for `K ≤ Λ`) with `TBlock_covers_S`.
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k K B) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B) →
    ∀ (g : (Ω ≃ₐ[k] Ω) → ZMod 2),
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y) →
      SSGRoute.IsLocConstOn K.fixingSubgroup g →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0) →
      ∀ (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2),
        (∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y) →
        (∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
          ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) →
        (∀ A ∈ T,
          (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
            SSGRoute.IsSplitIn k Λ A) →
        (∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) →
        (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0) →
        (∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) →
        -- the paper's local-triviality input at the places over `2` and at the places ramified in
        -- `K|k`: the datum `g + h B` vanishes on the *whole* local group there, not merely on its
        -- inertia.  Without it the Claim is false (a nontrivial unramified `2`-adic class is
        -- admissible, and then the Hilbert-symbol chain of Schmidt--Wingberg p. 16 does not
        -- close); see `P2Close/NOTE_escapeStepClaim_findings.md` and `ACTION_p2_claim_gap.md` §2.
        -- The quantifier ranges over **all** finite places, not only the blocks of `T`: the places
        -- ramified in `K|k` need not lie in a `T`-class (the oracle's coverage hypothesis speaks of
        -- `Λ|K`-ramification).  In the recursion the hypothesis is discharged from the node's `hy0`
        -- (`B` is then `k`-conjugate to an `S`-member by `hSram`, so `prescDatum` vanishes at `B`).
        (hsq : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (B.valuation (2 : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k K B) →
          ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, g σ + h B σ = 0) →
        ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
          SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
          (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
          (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
          (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
            Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = g σ + h A σ) ∧
          (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
            Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
            (¬ Work.SSGRoute.gesKConj K Q B) →
            ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
          (∃ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
            Q.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
            Odd (FractionalIdeal.count ↥K 𝔮
              (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
                (b : ↥K)))) ∧
          (∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
            ∀ u ∈ SSGRoute.decomp k (σ • Q) ⊓ K.fixingSubgroup,
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b u = 0)

/-- **The strengthened prefix invariant of the `p = 2` recursion.**  The lane's `TwoRec.PreTwo`
(the escape classes realise the prescribed datum on the blocks of `T_m`, kill the involutions of
`G_K`, are confined to `T_m` and their own escape prime, and are normalised there) together with the
two clauses that the *conclusion* `ThreeHalvesConcl` needs and that `PreTwo` alone does not carry:

* the paper's Claim at every already constructed stage (`ClaimClause`), and
* **`k`-freshness**: every escape prime is not only not `K`-conjugate but not `k`-conjugate to any
  block of its own place set `T_m`.  `PreTwo`'s clause 4 records only the `K`-conjugacy exclusion,
  and `¬ gesKConj K A Q` does *not* imply `¬ IsConjPlace k A Q` (a `k`-conjugate of `A` that is not
  a `K`-conjugate lies in a *different* `K`-class above the same `k`-prime); clause (c) of
  `ThreeHalvesConcl` is the `k`-conjugacy statement, so it has to be recorded.  Both clauses are
  `k`-level output of the escape step (`ClaimOracle`'s conjuncts `¬ IsConjPlace k A Q` and the
  Claim). -/
def PreTwoC (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2) (n : ℕ)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (k := k) (Ω := Ω) (K := K)) : Prop :=
  Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s ∧
    (∀ m < n, ClaimClause (K := K) ζ hζ hζK (s.f m).1 (s.f m).2) ∧
    (∀ m < n,
      ∀ A ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock (k := k) (Ω := Ω) (K := K) S s.f m,
        ¬ SSGRoute.IsConjPlace k A (s.f m).1)

end Work.SSGRoute.P2Close
