import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.corestriction_hom_on_fixingSubgroup
import Submission.Work.SSGRoute.corestriction_vanishes_on_inertia
import Submission.Work.SSGRoute.isLocConstOn_corestriction
import Submission.Work.SSGRoute.exists_corestriction
import Submission.Work.SSGRoute.odd_involution_coboundary
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
import Submission.Work.SSGRoute.exists_cyclic_quotient_subgroup_vanishing
import Submission.Work.SSGRoute.exists_cyclic_quotient_subgroup_of_cyclic_image
import Submission.Work.SSGRoute.PT.pairAlgebra
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.NK.Reconstruct.denseChebotarev
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NeukirchUchida.Local.Transitivity
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Work.SSGRoute.exists_levelSub_le_of_isOpen
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.Chebotarev.IsFrobAtStabilizes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Čebotarev new-prime step of Schmidt--Wingberg §4, *below* the node

This module is a **relocation below the node `Work.SSGRoute.shafarevich_z_construction`** of the
Čebotarev "new ramification prime" step of Schmidt--Wingberg §4 and of the place/bookkeeping
lemmas it rests on.

## Why a copy, and not just an import

The step is proved (axiom-clean) as `Work.SSGRoute.frobeniusClass_realisation` and
`Work.SSGRoute.frobeniusClass_realisation_of_res_eq_one` in
`Submission/Work/SSGRoute/shafarevich_theorem13.lean`, and in the `Work.SSGRoute.ZDataTwo`
vocabulary as `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`.  All of those live **above**
this node in the import order: `shafarevich_theorem13` imports `shafarevich_z_construction`.  The
two arithmetic cores of the `μ_p` (`MupGate`) lane — `Work.SSGRoute.sw_z_exists_odd_sketch`
(`z_data_mup_arith.lean`, Piece 2) and `Work.SSGRoute.shafarevich_z_data_two_kummerCore`
(`shafarevich_z_data_two.lean`) — sit **below** the node and therefore cannot import them: the
sibling statements are `sorry` there for exactly this reason.  Hence the step must exist below the
node as well.

The declarations here are verbatim copies (same statements, same proofs) of the block
`shafarevich_theorem13.lean` lines 3044–3628, placed in the namespace
`Work.SSGRoute.FrobBelow` so that no name clashes with the originals; a module importing both this
file and `shafarevich_theorem13` sees two independently named copies.  The copies use only
below-node imports (checked on the transitive import closure), so any module of the `MupGate` lane
may import this one.

## The conditional Čebotarev input

As in the originals, the general-`k` Čebotarev density theorem is carried as the hypothesis
`hc : NK.Reconstruct.ChebotarevDensityInput k Ω` (it is derived in the workspace from
`NK.Chebotarev.ArtinReciprocityInput` at every finite Galois level, i.e. from Artin reciprocity
together with the Hecke `L`-function bounds; it is not available unconditionally).  Every
declaration of this file that needs it names it explicitly, so that discharging `hc` later (or
specialising to a `k` where it is known) is a syntactic substitution.

## Contents

* `exists_isFrobAtPrime_notMem_finite` — Čebotarev with a finite set of primes avoided;
* the prime–place bridge `map_res_decomp_eq_stabilizer_valuationRing`, complete splitting
  (`isSplitIn_iff_primesOver_ncard`), the level/inertia dictionary
  (`isTrivialAtLevel_iff_mem_inertia_general`,
  `levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one`,
  `not_isRamifiedIn_of_levelSub_le_fixingSubgroup`) and the finiteness/avoidance bookkeeping
  (`finite_setOf_primeUnder`, `finite_setOf_primeUnder_ramified`,
  `isFinPlace_of_comap_valuationSubringAtPrime`, `not_isConjPlace_of_notMem_primeUnder`);
* `frobeniusClass_realisation` and its `res k N τ = 1` form
  `frobeniusClass_realisation_of_res_eq_one` — the new-prime step itself.
-/

open _root_.SSGRoute
open scoped Pointwise

namespace Work.SSGRoute.FrobBelow


/-! ## Čebotarev with a finite set of primes avoided (the arithmetic input of §4)

The arithmetic heart of Schmidt–Wingberg §4 is Čebotarev's density theorem: to build the auxiliary
class `z` one repeatedly needs a *new* prime at which a prescribed element of the Galois group of a
finite Galois level is an arithmetic Frobenius element, and that prime must avoid the finitely many
primes already used.  The workspace's Chebotarev for a general number field `k` is available in the
**density** form `NK.Reconstruct.ChebotarevDensityInput k Ω`, which follows from Artin reciprocity
(`NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`) and is the sharpest form proved in this
repository; `NK.Reconstruct.exists_isFrobAtPrime_mem_of_hasFullDensity` turns it into a prime *inside
a prescribed set of full Dirichlet density*.

The lemma below is the form actually needed: a finite set of primes has Dirichlet density `0`, so
its complement has full density, and the prescribed Frobenius element is realised at a prime outside
the given finite set.  No separability or Galois hypothesis on `Ω` is required beyond `[Algebra k Ω]`. -/

/-- **Čebotarev with a finite set of primes avoided.**  For a finite normal level `M` of an
`k`-algebra `Ω`, every `k`-automorphism `g` of `M` is an arithmetic Frobenius element at a prime of
`k` lying outside any prescribed finite set of primes.

This is `NK.Reconstruct.exists_isFrobAtPrime_mem_of_hasFullDensity` applied to the complement of
`Bad`, which has full Dirichlet density because `Bad` is finite. -/
theorem exists_isFrobAtPrime_notMem_finite
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (Bad : Set (NK.Chebotarev.PrimeIdeal k)) (hBad : Bad.Finite)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (g : (↥M) ≃ₐ[k] (↥M)) :
    ∃ p : NK.Chebotarev.PrimeIdeal k, p ∉ Bad ∧
      NK.Chebotarev.IsFrobAtPrime (K := k) (L := ↥M) p g := by
  refine NK.Reconstruct.exists_isFrobAtPrime_mem_of_hasFullDensity
    (K := k) (K' := Ω) (R := Badᶜ) hc ?_ M g
  show NumberField.Set.HasDirichletDensity (Badᶜ : Set (NK.Chebotarev.PrimeIdeal k))ᶜ 0
  simpa using Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hBad

/-! ## The prime–place bridge: decomposition groups versus stabilisers of primes

The step that turns the Čebotarev statement of the previous section (formulated with prime ideals of
`𝓞 M`) into the place-level statement needed by Theorem 13 is the correspondence

  `res k M (decomp k B)  =  stabiliser of the prime of 𝓞 M below B`.

The naive form of this correspondence, "`τ ∈ decomp k B` if and only if `res k M τ` fixes the prime
`P` below `B`", is **false**: over a fixed place of `M` there are in general several places of `Ω`,
conjugate under `Gal(Ω/M)`, and a `τ` preserving the prime need not fix the particular place `B`.
The correct statement is the one below: `res k M` maps `decomp k B` *onto* the stabiliser (which is
legitimate because `Gal(Ω/M) = M.fixingSubgroup ⊆ ker (res k M)`, so the places over a fixed prime
of `𝓞 M` are indistinguishable after applying `res k M`).  The proof is the assembly of two public
results of the Neukirch–Uchida chapter:

* `NK.Reconstruct.comap_smul_eq_restrictNormalHom_smul'` — the trace of `σ • B` on `M` is
  `res k M σ` applied to the trace of `B` (this gives `⊆`);
* `Submission.NeukirchUchida.Local.exists_mem_stabilizer_restrictNormalHom_eq` — restriction of
  decomposition groups of places of `Ω` to a finite normal level is surjective (this gives `⊇`),
  together with `Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup`
  for the passage between the stabiliser of the valuation ring and the decomposition subgroup. -/

/-- **The decomposition group of a place of `Ω` maps onto the stabiliser of the prime below it.**
Let `M|k` be a finite Galois level, `B` a finite place of `Ω` whose trace on `M` is the valuation
ring of the prime `P` of `𝓞 M`.  Then `res k M` maps `decomp k B` onto the stabiliser of `P` in
`Gal(M|k)` (equivalently, of the valuation ring of `P`). -/
theorem map_res_decomp_eq_stabilizer_valuationRing {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M]
    (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M))
    (hP : B.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) :
    (decomp k B).map (res k M) =
      MulAction.stabilizer (↥M ≃ₐ[k] ↥M)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI : NumberField ↥M := inferInstance
  set p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Submission.NeukirchUchida.primeOf B hB with hpdef
  have hp : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p :=
    Submission.NeukirchUchida.primeOf_spec B hB
  have hplaceOf : Submission.NeukirchUchida.Local.placeOf p B hp M = P :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥M) (K := ↥M)
      (by rw [← Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf p B hp M,
        hP])
  refine le_antisymm ?_ ?_
  · -- `⊆`: the trace of `σ • B` on `M` is `res k M σ` applied to the trace of `B`
    intro g hg
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
    have hσB : σ • B = B := hσ
    have hcom :=
      NK.Reconstruct.comap_smul_eq_restrictNormalHom_smul' (F := k) (E := ↥M) (K := Ω) B σ
    rw [hσB, hP] at hcom
    rw [MulAction.mem_stabilizer_iff]
    exact hcom.symm
  · -- `⊇`: restriction of decomposition groups to a finite normal level is surjective
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have hgdec : g ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := k) P :=
      (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
        P g).mp hg
    have hgdec' : g ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
        (Submission.NeukirchUchida.Local.placeOf p B hp M) := by
      rw [hplaceOf]; exact hgdec
    obtain ⟨σ, hσ, hσres⟩ :=
      Submission.NeukirchUchida.Local.exists_mem_stabilizer_restrictNormalHom_eq p B hp M
        ⟨g, hgdec'⟩
    exact Subgroup.mem_map.mpr ⟨σ, hσ, hσres⟩

/-- **Complete splitting: the place language and the prime-ideal language agree.**

`IsSplitIn k N B` (the decomposition group of the place `B` is contained in the fixing subgroup of
`N`) holds exactly when the prime `p` of `k` below `B` has `[N : k]` primes above it in `𝓞 N` — the
prime-ideal form of "`p` splits completely in `N|k`".  This is
`NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely`, restated in the vocabulary of
`Interfaces.lean`; it is the bookkeeping step that turns a trivial Frobenius at `p` (together with
the unramifiedness of `p`) into the clause `IsSplitIn k N B` of Theorem 13. -/
theorem isSplitIn_iff_primesOver_ncard {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N]
    (B : ValuationSubring Ω)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hp : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p) :
    IsSplitIn k N B ↔
      (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank k ↥N := by
  haveI : IsSepClosure k Ω := inferInstance
  haveI : NumberField ↥N := Commons.NumberTheory.NumberField.numberField_of_intermediateField N
  exact NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely p B hp

/-- **The level subgroup inside the fixing subgroup implies unramifiedness.**

By definition (`SSGRoute.IsRamifiedIn`) a place `B` is ramified in `N|k` when some inertia element of
`B` fails to lie in `N.fixingSubgroup`, and the inertia is the intersection of the level subgroups
`levelSub B M` (`Work.SSGRoute.mem_levelSub_iff`).  Hence it is enough that the level subgroup at the
single level `N` be contained in `N.fixingSubgroup`:

  `levelSub B N ≤ N.fixingSubgroup  ⟹  ¬ IsRamifiedIn k N B`.

Note that the hypothesis is *not* `levelSub B N = ⊥` and that the latter is **false** in general:
`levelSub B N` is a subgroup of `G_k = Ω ≃ₐ[k] Ω` and always contains `decomp k B ⊓ Gal(Ω/N)`
(an element fixing `N` pointwise has `δ x - x = 0`, and `B.valuation 0 = 0 < 1`); for `N = k` this is
all of `decomp k B`, which is infinite at a finite place.  What unramifiedness gives is precisely
triviality of the *image* of `levelSub B N` in `Gal(N|k)`, i.e. containment in the kernel
`N.fixingSubgroup` of the restriction — this is the second half of the ramification bookkeeping of
`frobeniusClass_realisation`, recorded as the standalone input in the STATUS comment below. -/
theorem not_isRamifiedIn_of_levelSub_le_fixingSubgroup {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [Normal k N]
    (B : ValuationSubring Ω) (h : levelSub B N ≤ N.fixingSubgroup) :
    ¬ IsRamifiedIn k N B := by
  rintro ⟨σ, hσI, hσnot⟩
  exact hσnot (h ((mem_levelSub_iff B σ).mpr hσI N))

/-- **The `P`-adic valuation of an integer is `< 1` exactly on the prime `P`.**

For a number field `N` and a prime `P` of `𝓞 N`, an integer `y : 𝓞 N` has
`(valuationSubringAtPrime N P).valuation (algebraMap y) < 1` exactly when `y ∈ P.asIdeal`.

This is the first of the two identifications isolated in the STATUS comment as the last gap of
`frobeniusClass_realisation`: it is Mathlib's `HeightOneSpectrum.valuation_lt_one_iff_mem` for the
ambient valuation `P.valuation N`, transported to the valuation *of the valuation subring* through
`valuationSubringAtPrime_eq_valuationSubring` and `ValuationSubring.valuationSubring_valuation`
(which give `Valuation.IsEquiv` of the two valuations, and `Valuation.IsEquiv.lt_one_iff_lt_one`
preserves the condition `< 1`).  It is the step that converts the *ideal* form of "acts trivially on
the residue field" (`galRestrict (res k N δ) x - x ∈ P.asIdeal`, the shape in which
`Ideal.inertia` and `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel` are stated) into the *valuation*
form in which `Work.SSGRoute.levelSub` is defined. -/
theorem valuationSubringAtPrime_valuation_lt_one_iff_mem {N : Type} [Field N] [NumberField N]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers N))
    (y : NumberField.RingOfIntegers N) :
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime N P).valuation
        (algebraMap (NumberField.RingOfIntegers N) N y) < 1 ↔ y ∈ P.asIdeal := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have heq : Valuation.IsEquiv
      ((IsDedekindDomain.HeightOneSpectrum.valuation N P).valuationSubring).valuation
      (IsDedekindDomain.HeightOneSpectrum.valuation N P) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr
      (ValuationSubring.valuationSubring_valuation _)
  exact (Valuation.IsEquiv.lt_one_iff_lt_one heq
    (x := algebraMap (NumberField.RingOfIntegers N) N y)).trans
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := N) P y)

/-- **The level-triviality condition is membership of the restriction in `Ideal.inertia`.**

`IsTrivialAtLevel k Ω B hB L g` (the residue-field condition of `g` on the level `L`) holds exactly
when the restriction `res k L g` lies in `Ideal.inertia` of the prime of `𝓞 L` below `B`.  This is the
general-`k` form of the finite-level statement proved privately in
`Submission/Work/SSGRoute/decomp_mod_inertia_cyclic.lean`, made public here because it is the bridge
between the *ideal* form of "acts trivially on the residue field" (`Ideal.inertia`, in which both
`Ideal.inertia` and `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel` are stated) and the *valuation*
form used by `Work.SSGRoute.levelSub`. -/
theorem isTrivialAtLevel_iff_mem_inertia_general {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {B : ValuationSubring Ω}
    (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (g : Ω ≃ₐ[k] Ω) :
    IsTrivialAtLevel k Ω B hB L g ↔
      AlgEquiv.restrictNormalHom L g ∈
        Ideal.inertia (↥L ≃ₐ[k] ↥L) (levelPrime k Ω B hB L).asIdeal := by
  rw [IsTrivialAtLevel, NK.FrobeniusBridge.IsTrivialOnResidueAtLevel, AddSubgroup.mem_inertia]
  refine forall_congr' fun x => ?_
  have hsmul : (AlgEquiv.restrictNormalHom L g) • x =
      galRestrict (NumberField.RingOfIntegers k) k ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom L g) x := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [algebraMap_galRestrict_apply, algebraMap.smul']
    rfl
  rw [hsmul]
  exact Iff.rfl

/-- **Unramifiedness gives containment of the level subgroup in the fixing subgroup.**

If the prime `p` below the place `B` is unramified in the finite Galois level `N|k` (ramification
index `1` at every prime of `𝓞 N` above `p`), then every element of `levelSub B N` — every element of
`decomp k B` acting trivially modulo the maximal ideal on the level `N` — fixes `N` pointwise:

  `levelSub B N ≤ N.fixingSubgroup`.

This is the classical `#I_w = e(w/v)` in the level language.  The chain is:

* `δ ∈ levelSub B N` acts trivially modulo the maximal ideal at the level, which is `IsTrivialAtLevel`
  after transporting the valuation condition through the two dictionaries
  `NK.Reconstruct.primeOfLevel_spec` (`B.comap (algebraMap ↥N Ω) = valuationSubringAtPrime ↥N P`) and
  `Work.SSGRoute.valuationSubringAtPrime_valuation_lt_one_iff_mem` (valuation `< 1` ⟺ membership of
  the prime ideal);
* `Work.SSGRoute.isTrivialAtLevel_iff_mem_inertia_general` turns that into membership of `res k N δ`
  in `Ideal.inertia (N ≃ₐ[k] N) P`;
* `e = 1` makes that inertia trivial
  (`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`), whence
  `res k N δ = 1`, i.e. `δ ∈ N.fixingSubgroup` (`mem_fixingSubgroup_iff_res_eq_one`).

Together with `Work.SSGRoute.not_isRamifiedIn_of_levelSub_le_fixingSubgroup` (contrapositive of the
definition of `IsRamifiedIn`) this completes the ramification bookkeeping of
`frobeniusClass_realisation`. -/
theorem levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N]
    (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hp : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p)
    (hunr : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥N),
      P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    levelSub B N ≤ N.fixingSubgroup := by
  intro δ hδ
  haveI : NumberField ↥N := inferInstance
  haveI : IsGalois k ↥N := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have htriv : IsTrivialAtLevel k Ω B hB N δ := by
    intro x
    refine (valuationSubringAtPrime_valuation_lt_one_iff_mem (levelPrime k Ω B hB N)
      (galRestrict (NumberField.RingOfIntegers k) k ↥N (NumberField.RingOfIntegers ↥N)
        (AlgEquiv.restrictNormalHom N δ) x - x)).mp ?_
    have hC : algebraMap (NumberField.RingOfIntegers ↥N) ↥N x ∈ B.comap (algebraMap ↥N Ω) := by
      rw [NK.Reconstruct.primeOfLevel_spec B N (NK.Reconstruct.comap_level_ne_top hB N)]
      exact Commons.RingTheory.Valuation.algebraMap_mem_valuationSubringAtPrime
        (levelPrime k Ω B hB N) x
    have hval : B.valuation (δ (algebraMap ↥N Ω
          (algebraMap (NumberField.RingOfIntegers ↥N) ↥N x))
        - algebraMap ↥N Ω (algebraMap (NumberField.RingOfIntegers ↥N) ↥N x)) < 1 :=
      hδ.2 ⟨algebraMap (NumberField.RingOfIntegers ↥N) ↥N x, hC⟩
    rw [← NK.Reconstruct.primeOfLevel_spec B N (NK.Reconstruct.comap_level_ne_top hB N),
      comap_valuation_lt_one_iff, map_sub, algebraMap_galRestrict_apply, map_sub]
    convert hval using 1
    exact congrArg (fun z => B.valuation (z - algebraMap ↥N Ω
        (algebraMap (NumberField.RingOfIntegers ↥N) ↥N x)))
      (AlgEquiv.restrictNormal_commutes δ ↥N
        (algebraMap (NumberField.RingOfIntegers ↥N) ↥N x))
  have hmem : AlgEquiv.restrictNormalHom N δ ∈
      Ideal.inertia (↥N ≃ₐ[k] ↥N) (levelPrime k Ω B hB N).asIdeal :=
    (isTrivialAtLevel_iff_mem_inertia_general hB N δ).mp htriv
  have hlies : (levelPrime k Ω B hB N).asIdeal.LiesOver p.asIdeal := by
    have h1 := NK.ResidueFrob.primeOfLevel_liesOver ⟨B, hB⟩ N
    have h2 : Submission.NeukirchUchida.primeOf B hB = p :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (by rw [← Submission.NeukirchUchida.primeOf_spec B hB, hp])
    rwa [h2] at h1
  have hbot : Ideal.inertia (↥N ≃ₐ[k] ↥N) (levelPrime k Ω B hB N).asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      p (levelPrime k Ω B hB N).asIdeal).mpr (hunr _ hlies)
  rw [hbot] at hmem
  rw [← mem_fixingSubgroup_iff_res_eq_one]
  exact Subgroup.mem_bot.mp hmem

/-- **The primes of `k` below a finite set of places of `Ω` form a finite set.**

This is the finiteness of the "bad" set `Bad` of the assembly of
`Work.SSGRoute.frobeniusClass_realisation`: the primes below the conjugates of the places of `T'`.
Since `p ↦ valuationSubringAtPrime k p` is injective
(`Commons.RingTheory.Valuation.valuationSubringAtPrime_injective`), the set of primes below a finite
set of places is finite. -/
theorem finite_setOf_primeUnder {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (T' : Finset (ValuationSubring Ω)) :
    {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      ∃ A ∈ T', A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun p => IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p) ?_ ?_
  · refine (T'.finite_toSet.image (fun A => A.comap (algebraMap k Ω))).subset ?_
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨A, hA, hAp⟩ := hp
    exact ⟨A, hA, hAp⟩
  · intro p _ q _ hpq
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hpq

/-- **The primes of `k` in which a finite level `M|k` ramifies are finite.**

The second half of the "bad" set `Bad` of the assembly of
`Work.SSGRoute.frobeniusClass_realisation`: the primes of `k` below a prime of `𝓞 M` whose
ramification index over `k` is `≠ 1` (only finitely many primes of `𝓞 M` ramify, so their traces on
`k` form a finite set). -/
theorem finite_setOf_primeUnder_ramified {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M] :
    {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1}.Finite := by
  have hL : {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M) |
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
  refine (hL.image (fun P =>
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers k) P)).subset ?_
  rintro p ⟨P, hP, heP⟩
  exact ⟨P, heP, IsDedekindDomain.HeightOneSpectrum.ext
    (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hP.over])⟩

/-- **Finiteness of a place descends along a finite level.**

If a place `B` of `Ω` induces on the finite level `M|k` the valuation ring of the prime `P` of
`𝓞 M`, then `B` is a finite place of `k`.  Indeed the trace of `B` on `k` is
`(𝒪_{↥M,P}).comap (algebraMap k ↥M)`, and by
`Commons.RingTheory.Valuation.comap_valuationSubringAtPrime` this is `𝒪_{k,q}` for
`q := IsDedekindDomain.HeightOneSpectrum.under (𝓞 k) P`, which is `≠ ⊤`
(`Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top`).

This is the plumbing step of the assembly of `Work.SSGRoute.frobeniusClass_realisation` producing
the clause `IsFinPlace k B` for the place cut out by the Frobenius prime.

*Elaboration notes* (each of these cost a round trip):
* `ValuationSubring.comap_comap` takes its two ring homomorphisms **explicitly** —
  `comap_comap B (algebraMap ↥M Ω) (algebraMap k ↥M)` — and the resulting identification of
  `algebraMap k Ω` with `(algebraMap ↥M Ω).comp (algebraMap k ↥M)` is *definitional* for
  intermediate fields, so it is cleanest to `exact (…comap_comap …).symm` rather than to `rw` the
  composed form (`rw` requires a syntactic match);
* the `≠ ⊤` lemma lives in the `Commons.RingTheory.Valuation` namespace, **not** under
  `IsDedekindDomain.HeightOneSpectrum`;
* `IsDedekindDomain.HeightOneSpectrum.under` is a map on `HeightOneSpectrum`s, and the
  `Ideal.LiesOver` instance it satisfies is best built by hand:
  `Ideal.LiesOver.mk (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal])`;
* `IsFinPlace k B` must be unfolded with `show B.comap (algebraMap k Ω) ≠ ⊤` before rewriting. -/
theorem isFinPlace_of_comap_valuationSubringAtPrime {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (M : IntermediateField k Ω) [FiniteDimensional k M]
    (B : ValuationSubring Ω)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M))
    (hB : B.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) :
    IsFinPlace k B := by
  haveI : NumberField ↥M := Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  have h1 : B.comap (algebraMap k Ω) =
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).comap
        (algebraMap k ↥M) := by
    rw [← hB]
    exact (ValuationSubring.comap_comap B (algebraMap ↥M Ω) (algebraMap k ↥M)).symm
  show B.comap (algebraMap k Ω) ≠ ⊤
  set q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers k) P with hq
  have h2 := Commons.RingTheory.Valuation.comap_valuationSubringAtPrime q P
    (Ideal.LiesOver.mk (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]))
  rw [h1, h2]
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) q

/-- **Avoidance for the assembly of `frobeniusClass_realisation`.**

A place `B` whose trace on `k` is the valuation ring of a prime `q` that lies below no place of
`T'` is not a `G_k`-conjugate of any place of `T'`.  Indeed the trace of a conjugate place is
unchanged (`Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap`), so a conjugate of a
place of `T'` would have the same trace `𝒪_{k,q}` on `k`, putting `q` in the set of primes below
`T'`.

This is the avoidance clause of the assembly: with `q` the prime of `𝓞 k` below the Frobenius prime
`P` of `𝓞 M`, and `q ∉ Bad`, it gives `∀ C ∈ T', ¬ IsConjPlace k C B` for the place `B` over `P`.
Note that neither the finiteness of `T'` nor its "one place per prime" hypothesis is used. -/
theorem not_isConjPlace_of_notMem_primeUnder {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (T' : Finset (ValuationSubring Ω)) (B : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hB : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q)
    (hq : q ∉ {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) |
      ∃ A ∈ T', A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p}) :
    ∀ C ∈ T', ¬ IsConjPlace k C B := by
  intro C hC hconj
  obtain ⟨σ, hσ⟩ := hconj
  have h2 := Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap C σ
  rw [hσ, hB] at h2
  exact hq ⟨C, hC, h2.symm⟩


set_option linter.style.haveILetI false in
/-! ## The Čebotarev step of Schmidt–Wingberg §4 (the new ramification prime)

The construction of the auxiliary class `z` of Schmidt–Wingberg §4 (the paper's pp. 13–20) chooses,
at each step, a *new* prime `P_{n+1} ∈ S∖T_n(K)`, completely decomposed in `Λ|k`, at which a
prescribed Frobenius element is realised, and which avoids the finitely many primes already used.
The lemma below is that step, in the corrected form: the prescribed Frobenius element of `Gal(L|k)`
is realised by an element of the decomposition group of one and the same *place* `B` (not merely up
to conjugacy, which was the defect of the sibling node's `chebotarev_sameFrobeniusClass_split`).

All of its ingredients are the ones proved above in this file:
* `exists_isFrobAtPrime_notMem_finite` — Čebotarev with a finite set of primes avoided;
* the prime–place bridge `map_res_decomp_eq_stabilizer_valuationRing`;
* `isSplitIn_iff_primesOver_ncard` and `Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely`
  for the complete-splitting clause (with `NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one`
  supplying the inertia degree `1`);
* `levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one` +
  `not_isRamifiedIn_of_levelSub_le_fixingSubgroup` for the unramifiedness clause (applied at the
  level `M = L ⊔ N ⊇ L`, so that only the ramification of `M` has to be avoided);
* `not_isConjPlace_of_notMem_primeUnder` for the avoidance clause. -/

/-- **Čebotarev with a prescribed Frobenius element, prescribed splitting and prescribed
unramifiedness (the "new ramification prime" of Schmidt–Wingberg §4).**

Let `L` and `N` be finite Galois levels of a number field `k` inside an algebraic closure `Ω`, let
`T'` be a finite set of pairwise non-conjugate finite places of `Ω`, and let `τ ∈ G_k` be an element
whose restriction to `N` is trivial.  Then there is a finite place `B` of `Ω` such that

* `B` is not a `G_k`-conjugate of any place of `T'`;
* the prime of `k` below `B` is unramified in `L` (hence `¬ IsRamifiedIn k L B`);
* the prime of `k` below `B` splits completely in `N` (that is, `IsSplitIn k N B`);
* some `σ ∈ decomp k B` restricts to `res k L τ` on `L`.

Note that `T'` is used only through its underlying *set*: neither its finiteness nor the
"one place per prime" condition (`hT'disj` in the sibling statements) is needed, so they are not
hypotheses here.

The compatibility hypothesis `hτ` ("`τ` is trivial on `N`, and realises `res k L τ` on `L`") is
what makes the prescribed Frobenius well defined at the compositum `L ⊔ N`: it is the condition
that `(res k L τ, 1)` comes from an element of `Gal(L ⊔ N|k)`.

This is the corrected form of the "Piece 2" of the arithmetic lane of the `z`-node
(`Submission/Work/SSGRoute/z_data_mup_arith.lean`, where the statement without `hτ` is *false*:
see the counterexample recorded in the docstring of the sibling `frobeniusClass_realisation`
discussion in the STATUS comment of this file). -/
theorem frobeniusClass_realisation {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (L N : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k N] [IsGalois k N]
    (T' : Finset (ValuationSubring Ω))
    (τ : Ω ≃ₐ[k] Ω) (hτ : ∃ τ₀ : Ω ≃ₐ[k] Ω, res k N τ₀ = 1 ∧ res k L τ₀ = res k L τ) :
    ∃ B : ValuationSubring Ω, IsFinPlace k B ∧
      (∀ C ∈ T', ¬ IsConjPlace k C B) ∧
      ¬ IsRamifiedIn k L B ∧ IsSplitIn k N B ∧
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ decomp k B ∧ res k L σ = res k L τ := by
  classical
  obtain ⟨τ₀, hτ₀N, hτ₀L⟩ := hτ
  -- ### The compositum `M = L ⊔ N` and its structure
  let M : IntermediateField k Ω := L ⊔ N
  have hLM : L ≤ M := le_sup_left
  have hNM : N ≤ M := le_sup_right
  haveI hMfin : FiniteDimensional k M := IntermediateField.finiteDimensional_sup L N
  haveI hMnor : Normal k M := inferInstance
  haveI hMgal : IsGalois k M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hMnum : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- canonical algebra structures for the two towers `k ⊆ L ⊆ M` and `k ⊆ N ⊆ M`
  letI : Algebra ↥L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  haveI : IsScalarTower k ↥L ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ↥L ↥M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  letI : Algebra ↥N ↥M := (Subsemiring.inclusion hNM).toAlgebra
  haveI : IsScalarTower k ↥N ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ↥N ↥M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  -- ### The bad set of primes of `k`
  set Bad : Set (NK.Chebotarev.PrimeIdeal k) :=
    {p | (∃ A ∈ T', A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p) ∨
      (∃ P : NK.Chebotarev.PrimeIdeal ↥M,
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1) ∨
      (∃ Q : NK.Chebotarev.PrimeIdeal ↥N,
        Q.asIdeal.LiesOver p.asIdeal ∧
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1)} with hBad
  have hBadfin : Bad.Finite := by
    rw [hBad]
    exact (finite_setOf_primeUnder T').union
      ((finite_setOf_primeUnder_ramified M).union (finite_setOf_primeUnder_ramified N))
  -- ### Čebotarev
  obtain ⟨p, hpBad, hfrobp⟩ :=
    exists_isFrobAtPrime_notMem_finite hc Bad hBadfin M (res k M τ₀)
  obtain ⟨P, hPlies, hPfrob⟩ := hfrobp
  -- ### The place `B` over `P`
  obtain ⟨B, hBcomap⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := ↥M) (K' := Ω) P
  have hBk : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p := by
    have h1 : B.comap (algebraMap k Ω) =
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).comap
          (algebraMap k ↥M) := by
      rw [← hBcomap]
      exact (ValuationSubring.comap_comap B (algebraMap ↥M Ω) (algebraMap k ↥M)).symm
    rw [h1]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p P hPlies
  have hBne : B.comap (algebraMap k Ω) ≠ ⊤ := by
    rw [hBk]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) p
  have hBfin : IsFinPlace k B := hBne
  refine ⟨B, hBfin, ?_, ?_, ?_, ?_⟩
  · -- **avoidance**: `B` is not conjugate to any place of `T'`
    refine not_isConjPlace_of_notMem_primeUnder T' B p hBk (fun h => hpBad (Or.inl h))
  · -- **unramifiedness in `L`**: use the level `M ⊇ L`
    have hunrM : ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver p.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
      intro Q hQ
      by_contra hne
      exact hpBad (Or.inr (Or.inl ⟨Q, hQ, hne⟩))
    have hlev := levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one M B hBne p hBk hunrM
    rintro ⟨σ, hσI, hσnot⟩
    refine hσnot (IntermediateField.fixingSubgroup_le hLM ?_)
    exact hlev ((mem_levelSub_iff B σ).mpr hσI M)
  · -- **complete splitting in `N`**
    have hQlies : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.LiesOver p.asIdeal :=
      Ideal.LiesOver.mk (by
        rw [show (P.under (NumberField.RingOfIntegers ↥N)).asIdeal =
            P.asIdeal.under (NumberField.RingOfIntegers ↥N) from rfl, Ideal.under_under]
        exact hPlies.over)
    have heQ : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) = 1 := by
      by_contra hne
      exact hpBad (Or.inr (Or.inr ⟨P.under (NumberField.RingOfIntegers ↥N), hQlies, hne⟩))
    have hfrobN : NK.Chebotarev.IsFrobAt (P.under (NumberField.RingOfIntegers ↥N))
        (1 : (↥N) ≃ₐ[k] (↥N)) := by
      have h := NK.Chebotarev.isFrobAt_restrictNormalHom_le (L := N) (M := M) (hLM := hNM)
        (P := P) (ρ := res k M τ₀) hPfrob
      rwa [← NK.Chebotarev.restrictNormalHom_le_comp N M hNM τ₀, hτ₀N] at h
    have hfQ : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k) = 1 :=
      (NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one hQlies heQ).mp hfrobN
    rw [isSplitIn_iff_primesOver_ncard N B p hBk,
      Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
        (K := k) (L := ↥N) p]
    haveI : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.LiesOver p.asIdeal := hQlies
    constructor
    · rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal
        (P.under (NumberField.RingOfIntegers ↥N)).asIdeal (Gal(↥N/k))]
      exact heQ
    · rw [Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal
        (P.under (NumberField.RingOfIntegers ↥N)).asIdeal (Gal(↥N/k))]
      exact hfQ
  · -- **the prescribed Frobenius is realised in `decomp k B`**
    have hgdec : res k M τ₀ ∈
        Submission.NeukirchUchida.Local.decompositionSubgroup (K := k) P := by
      show Submission.NeukirchUchida.Local.placeSmul (res k M τ₀) P = P
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
      exact NK.Chebotarev.IsFrobAtStabilizes hPfrob
    have hgstab : res k M τ₀ ∈ MulAction.stabilizer (↥M ≃ₐ[k] ↥M)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) :=
      (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
        P (res k M τ₀)).mpr hgdec
    obtain ⟨σ, hσ, hσres⟩ := Subgroup.mem_map.mp (by
      rw [map_res_decomp_eq_stabilizer_valuationRing M B hBne P hBcomap]
      exact hgstab)
    refine ⟨σ, hσ, ?_⟩
    rw [NK.Chebotarev.restrictNormalHom_le_comp L M hLM σ, hσres,
      ← NK.Chebotarev.restrictNormalHom_le_comp L M hLM τ₀, hτ₀L]


/-- **The Čebotarev new-prime step in the form of the sibling nodes.**  When the prescribed element
`τ` has trivial restriction to `N` (the hypothesis in which the step is used by
`Work.SSGRoute.z_data_mup_core`, `Work.SSGRoute.shafarevich_z_data_two` and
`Work.SSGRoute.sw_z_exists_odd_sketch`), `frobeniusClass_realisation` applies with `τ₀ := τ`: the
compatibility hypothesis `∃ τ₀, res k N τ₀ = 1 ∧ res k L τ₀ = res k L τ` is then automatic.  (It is
in fact automatic for *every* `τ` with `res k N τ = 1`, because `res k L τ` and `1` agree on
`L ⊓ N`: both are obtained by restricting `τ` to `L ⊓ N`.) -/
theorem frobeniusClass_realisation_of_res_eq_one {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (L N : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k N] [IsGalois k N]
    (T' : Finset (ValuationSubring Ω))
    (τ : Ω ≃ₐ[k] Ω) (hτ : res k N τ = 1) :
    ∃ B : ValuationSubring Ω, IsFinPlace k B ∧
      (∀ C ∈ T', ¬ IsConjPlace k C B) ∧
      ¬ IsRamifiedIn k L B ∧ IsSplitIn k N B ∧
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ decomp k B ∧ res k L σ = res k L τ :=
  frobeniusClass_realisation hc L N T' τ ⟨τ, hτ, rfl⟩


/-! ## The step in the exact shape of the `MupGate` cores' Piece 2

The two arithmetic cores of the `μ_p` lane state Piece 2 as `chebotarev_frobenius_split_sketch`
(`Submission/Work/SSGRoute/z_data_mup_arith.lean`) and `chebotarev_frobenius_split`
(`Submission/Work/SSGRoute/ZDataTwo/chebotarev_frobenius_split.lean`, above the node).  The
statement below is the first of those verbatim — including its two unused side conditions
`hT'fin`, `hT'disj` — with the conditional Čebotarev input `hc` added, so that the `sorry` of
Piece 2 can be closed by a single `exact` once the core is allowed to carry `hc`:

```
exact Work.SSGRoute.FrobBelow.chebotarev_frobenius_split_below hc L N T' hT'fin hT'disj τ hτ
```

The second is `frobeniusClass_realisation_of_res_eq_one` itself (same statement, no side
conditions). -/

set_option linter.unusedVariables false in
theorem chebotarev_frobenius_split_below (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (L N : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k N] [IsGalois k N]
    (T' : Finset (ValuationSubring Ω)) (hT'fin : ∀ B ∈ T', SSGRoute.IsFinPlace k B)
    (hT'disj : ∀ B ∈ T', ∀ C ∈ T', SSGRoute.IsConjPlace k B C → B = C)
    (τ : Ω ≃ₐ[k] Ω) (hτ : SSGRoute.res k N τ = 1) :
    ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ C ∈ T', ¬ SSGRoute.IsConjPlace k C B) ∧
      ¬ SSGRoute.IsRamifiedIn k L B ∧ SSGRoute.IsSplitIn k N B ∧
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k B ∧
        SSGRoute.res k L σ = SSGRoute.res k L τ :=
  frobeniusClass_realisation_of_res_eq_one hc L N T' τ hτ

end Work.SSGRoute.FrobBelow