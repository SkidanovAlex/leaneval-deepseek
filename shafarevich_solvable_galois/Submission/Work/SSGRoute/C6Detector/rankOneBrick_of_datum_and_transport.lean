import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.TatePoitouRoute.rankOneBrick_of_levelCocycleDatum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one brick from the canonical-ambient datum and the ambient transport

This file is *wiring*: it shows that the rank-one brick of the unramified detector at the canonical
ambient field `AlgebraicClosure K` follows from the two statements

* `LevelDatumCanonical p k` — the level-cocycle datum for the coinduced permutation module, in the
  ambient field `AlgebraicClosure K'` **canonical for `K'`** (i.e. the statement of
  `Work.SSGRoute.C6Detector.rankOneLevelDatumAlgClosure`, as a `Prop` over the parameters);
* `DetectorAlgClosedExt p k` — the independence of the unramified detector of the ambient
  algebraically closed field (i.e. the statement of
  `Work.SSGRoute.C6Detector.detector_algClosedExt`, as a `Prop` over the parameters).

Everything else used here is proved and sorry-free:
`Work.SSGRoute.TatePoitouRoute.unramifiedDetector_rankOne_of_levelCocycleDatum` (datum ⟹ detector for
the permutation module) and the uniqueness of algebraic closures (`IsAlgClosure.equiv`) which
produces the `K'`-algebra map `AlgebraicClosure K' → AlgebraicClosure K` the transport needs.

The purpose of the file is to make the two delegated statements above separately sufficient for the
brick, so that the brick is available as soon as either of them (together with the transport) lands.
-/

namespace Work.SSGRoute.C6Detector

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-- **The canonical-ambient level datum, as a `Prop`.**

For every finite Galois `K/k`, every finite place `q ∤ p` of `K`, every `N ⊴ Gal(K/k)` containing the
inertia at `q` and fixing a primitive `p`-th root of unity `ζ ∈ K`, and every nonzero
`D_w`-equivariant functional `μ` on the coinduced permutation module `coInd_N^Γ 𝔽_p`, the
level-cocycle datum holds in the **canonical** ambient field `AlgebraicClosure K`. -/
def LevelDatumCanonical (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (μ : Rep.res (decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0),
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K (AlgebraicClosure K) w q hwq
      (Rep.coind N.subtype (Rep.trivial Coeff N (ZMod p))) μ

/-- **The ambient-independence of the unramified detector, as a `Prop`.** -/
def DetectorAlgClosedExt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra k Ω₀] [Algebra k Ω] [Algebra K Ω₀] [Algebra K Ω]
    [IsScalarTower k K Ω₀] [IsScalarTower k K Ω] [IsAlgClosed Ω₀] [IsAlgClosed Ω]
    (φ : Ω₀ →ₐ[k] Ω) (hφ : Function.Injective φ)
    (hφK : ∀ x : K, φ (algebraMap K Ω₀ x) = algebraMap K Ω x)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)),
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω₀ w q hwq M →
      Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M

/-- **The rank-one brick of `C6` at the canonical ambient field.**

For every finite Galois `K'/k` with an embedding into `AlgebraicClosure K`, every place
`w = Place.ofFinite q` with `p ∤ q` and every `N ⊴ Gal(K'/k)` containing the inertia at `q` and
fixing a primitive `p`-th root of unity `ζ ∈ K'`, the unramified detector holds for the permutation
module `Ind_N^{Gal(K'/k)} 𝔽_p`.

The proof builds the detector at the canonical ambient field `AlgebraicClosure K'` of `K'` from the
level datum, and transports it to the given ambient `AlgebraicClosure K` along the `K'`-algebra
isomorphism `AlgebraicClosure K' ≃ₐ[K'] AlgebraicClosure K` supplied by the uniqueness of algebraic
closures. -/
theorem rankOneBrick_of_datum_and_transport (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (hdat : LevelDatumCanonical p k) (htr : DetectorAlgClosedExt p k) :
    Work.SSGRoute.PTdualControl.RankOneBrick p k (AlgebraicClosure K) := by
  intro K' _ _ _ _ _ _ _ w q hwq hpq N _ hNI ζ hζ hNζ
  -- the level datum at the canonical ambient field of `K'` gives the detector there
  have hdet₀ : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K' (AlgebraicClosure K') w q hwq
      (Rep.ind N.subtype (Rep.trivial Coeff N (ZMod p))) :=
    Work.SSGRoute.TatePoitouRoute.unramifiedDetector_rankOne_of_levelCocycleDatum p k K'
      (AlgebraicClosure K') w q hwq N
      (fun μ hμ => hdat K' w q hwq hpq N hNI ζ hζ hNζ μ hμ)
  -- `AlgebraicClosure K` is an algebraic closure of `K'` (it is algebraic over `k` and `K'`
  -- is finite over `k`), so there is a `K'`-algebra isomorphism onto it
  haveI halg : Algebra.IsAlgebraic k (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans k K (AlgebraicClosure K)
  haveI halg' : Algebra.IsAlgebraic K' (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := K') (A := AlgebraicClosure K)
  haveI hclosure : IsAlgClosure K' (AlgebraicClosure K) := ⟨inferInstance, halg'⟩
  let φ₀ : AlgebraicClosure K' ≃ₐ[K'] AlgebraicClosure K :=
    IsAlgClosure.equiv K' (AlgebraicClosure K') (AlgebraicClosure K)
  -- as a `k`-algebra map
  let φ : AlgebraicClosure K' →ₐ[k] AlgebraicClosure K :=
    { φ₀.toRingHom with
      commutes' := fun x => by
        rw [IsScalarTower.algebraMap_apply k K' (AlgebraicClosure K'),
          IsScalarTower.algebraMap_apply k K' (AlgebraicClosure K)]
        exact φ₀.commutes (algebraMap k K' x) }
  exact htr K' (AlgebraicClosure K') (AlgebraicClosure K) φ φ₀.injective
    (fun x => φ₀.commutes x) w q hwq _ hdet₀

/-- **The rank-one brick of `C6` at an arbitrary algebraically closed ambient field.**

Same wiring as `rankOneBrick_of_datum_and_transport`, with the ambient field `Ω` arbitrary (a
`k`-algebra that is algebraically closed, together with a `K`-algebra structure): the `K'`-algebra
map `AlgebraicClosure K' → Ω` exists by `IsAlgClosed.lift` (an algebraic extension embeds into any
algebraically closed extension). -/
theorem rankOneBrick_of_datum_and_transport_general (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (hdat : LevelDatumCanonical p k) (htr : DetectorAlgClosedExt p k)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] :
    Work.SSGRoute.PTdualControl.RankOneBrick p k Ω := by
  intro K' _ _ _ _ _ _ _ w q hwq hpq N _ hNI ζ hζ hNζ
  -- the level datum at the canonical ambient field of `K'` gives the detector there
  have hdet₀ : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K' (AlgebraicClosure K') w q hwq
      (Rep.ind N.subtype (Rep.trivial Coeff N (ZMod p))) :=
    Work.SSGRoute.TatePoitouRoute.unramifiedDetector_rankOne_of_levelCocycleDatum p k K'
      (AlgebraicClosure K') w q hwq N
      (fun μ hμ => hdat K' w q hwq hpq N hNI ζ hζ hNζ μ hμ)
  -- an algebraic extension embeds into the algebraically closed `Ω`
  let ψ : AlgebraicClosure K' →ₐ[K'] Ω := IsAlgClosed.lift
  have hψinj : Function.Injective ψ := fun _ _ h => RingHom.injective (ψ : AlgebraicClosure K' →+* Ω) h
  -- as a `k`-algebra map
  let φ : AlgebraicClosure K' →ₐ[k] Ω :=
    { ψ.toRingHom with
      commutes' := fun x => by
        rw [IsScalarTower.algebraMap_apply k K' (AlgebraicClosure K'),
          IsScalarTower.algebraMap_apply k K' Ω]
        exact ψ.commutes (algebraMap k K' x) }
  exact htr K' (AlgebraicClosure K') Ω φ hψinj (fun x => ψ.commutes x) w q hwq _ hdet₀

end

end Work.SSGRoute.C6Detector
