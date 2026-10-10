import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.Chebotarev.IsFrobAtStabilizes
import Submission.NK.Reconstruct.denseChebotarev
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.Work.SSGRoute.PT.pairAlgebra
import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.corestriction_hom_on_fixingSubgroup
import Submission.Work.SSGRoute.corestriction_vanishes_on_inertia
import Submission.Work.SSGRoute.exists_cyclic_quotient_subgroup_of_cyclic_image
import Submission.Work.SSGRoute.exists_levelSub_le_of_isOpen
import Submission.Work.SSGRoute.odd_involution_coboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Place, ramification and Čebotarev vocabulary (below the node)

The lemmas of this module are the place-theoretic and prime-ideal vocabulary that the
`z`-construction of Schmidt–Wingberg §4 (and the Čebotarev "new prime" step) uses: the
density form of Čebotarev with a finite set of primes avoided, the prime–place bridge
`res k M (decomp k B) = stabiliser of the prime below B`, the finiteness of the primes below a
finite place set and of the ramified primes, and the elementary transport lemmas.

These declarations were originally inside `shafarevich_theorem13.lean` (the node), which made
them unusable below the node (in particular by the Z-route of `_NOTE_STEP4_DESIGN.md` §3, whose
`ZSplit/FrobeniusValue` layer needs `map_res_decomp_eq_stabilizer_valuationRing`).  They are
moved here, below the node, verbatim.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

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


end Work.SSGRoute
