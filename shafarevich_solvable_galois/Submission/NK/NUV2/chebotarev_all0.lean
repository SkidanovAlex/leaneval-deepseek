import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.ChebotarevGeneral.Main
import Submission.NK.ReconstructEndgame.chebotarevInput_congr
import Submission.NK.HeckeL.Consequences.primeSum_isBigO
import Submission.NK.HeckeL.Consequences.abelianLFunctions
import Submission.NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn
import Submission.NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem
import Submission.NK.NUV2.RouteB.heckeInput_build
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.kernelLe_of_auxField_B
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Assembly
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinConductor_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex
import Submission.NK.Existence.langCyclicRelIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.NUV2.ARL.isOpenNorm
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFTdeep.SecondInequality.PrimeIdeles
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.NK.NUV2.ChebAux.kernelLe_of_auxField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): (unchanged; see the git history / the
workspace's HANDOFF.md for the full text.)

## This lemma: Čebotarev (`ChebotarevInputDerived`)
Proved: non-abelian reduces to abelian (Deuring: `ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian`).
Open: `HeckeL.HeckeLRegularAtOne`, `FrobeniusCompatibility`, and the bridge `WeakNU.ChebotarevFrobeniusInput →
Reconstruct.ChebotarevInput` (locate it or build it first). For the abelian case with hFC: reciprocity identifies
Gal(L/K) with a ray class group quotient; density of primes in a ray class needs L(1,χ) ≠ 0 for ray class
characters (Hecke) — or Chebotarev's cyclotomic trick reducing to Dirichlet over ℚ, which Mathlib has
(`Nat.forall_exists_prime_gt_and_eq_mod`, Dirichlet L-functions nonvanishing at 1). Check which density notion the
target needs (Dirichlet density suffices for Neukirch's use).

UNIVERSES: everything is in `Type 0`, matching the hypotheses. Missing mathematics is NOT a reason to stop: build it
(delegate). Use declare_false only for a statement that is actually false, with a counterexample.

## What this file does

This file assembles the *finite-level* Čebotarev input `NK.NUV2.ChebAll0` of the Neukirch–Uchida wall
from the existence form `NK.WeakNU.ChebotarevFrobeniusInput` of Čebotarev's theorem over `ℚ`
(the bridge, `chebotarev_all0_of_frobeniusInput`), and records the rest of the chain

  `AbelianLFunctions` ⟹ `AbelianChebotarevDensity` ⟹ `ChebotarevFrobeniusInput` ⟹ `ChebAll0`

that reduces the whole problem to the analytic input of `Submission/Work/HeckeL/`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2

open NumberField IsDedekindDomain

/-! ## The bridge: Čebotarev over `ℚ` gives the finite-level input -/

/-- Čebotarev over `ℚ` in existence form gives the plain finite-level Čebotarev input
`NK.Reconstruct.ChebotarevInput ℚ K'`. -/
theorem chebotarevInput_rat_of_frobeniusInput (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (K' : Type) [Field K'] [Algebra ℚ K'] : NK.Reconstruct.ChebotarevInput ℚ K' := by
  intro L _ _ _ τ
  letI : Algebra ℚ ↥L := IntermediateField.algebra' L
  haveI : IsGalois ℚ ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨p, -, -, hram, P, hP, hfrob⟩ := hC ↥L τ ∅
  refine ⟨IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P, P, ?_, ?_, hfrob⟩
  · exact ⟨IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers ℚ) P⟩
  · exact hram P hP

/-- **The bridge**: `NK.WeakNU.ChebotarevFrobeniusInput` (Čebotarev over `ℚ`, existence form)
implies the finite-level Čebotarev input `NK.ReconstructEndgame.ChebotarevInputDerived` at every
number field. -/
theorem chebotarevInputDerived_of_frobeniusInput (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (K₁ K₁' : Type) [Field K₁] [Field K₁'] [NumberField K₁] [Algebra K₁ K₁']
    [IsSepClosure K₁ K₁'] : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁' := by
  letI : Algebra ℚ K₁' := NK.ReconstructEndgame.ratAlgebra K₁ K₁'
  exact (NK.ReconstructEndgame.chebotarevInput_congr K₁ K₁').mpr
    (chebotarevInput_rat_of_frobeniusInput hC K₁')

/-- **Čebotarev's input at `Type 0` from Čebotarev over `ℚ` in existence form.** -/
theorem chebotarev_all0_of_frobeniusInput (hC : NK.WeakNU.ChebotarevFrobeniusInput) :
    NK.NUV2.ChebAll0 :=
  fun K₁ K₁' _ _ _ _ _ => chebotarevInputDerived_of_frobeniusInput hC K₁ K₁'

/-- **Čebotarev's input at `Type 0` from the abelian case of Čebotarev in density form.** -/
theorem chebotarev_all0_of_abelianChebotarevDensity
    (h : NK.ChebotarevGeneral.AbelianChebotarevDensity) : NK.NUV2.ChebAll0 :=
  chebotarev_all0_of_frobeniusInput (NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian h)

/-- **Čebotarev's input at `Type 0` from the analytic input of the Hecke `L`-function chapter**
(the boundedness of the character-twisted prime sums of every non-trivial character of every
abelian extension). -/
theorem chebotarev_all0_of_lfunctions
    (h : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
      [FiniteDimensional K N] [IsGalois K N], (∀ a b : Gal(N/K), a * b = b * a) →
      NK.Chebotarev.AbelianLFunctions K N) : NK.NUV2.ChebAll0 :=
  chebotarev_all0_of_abelianChebotarevDensity
    (NK.ChebotarevGeneral.abelianChebotarevDensity_of_lfunctions h)

open NumberField IsDedekindDomain

/-- **The Hecke analytic input** (Hecke's theorem), as a hypothesis: the `L`-series of every
non-trivial character of an open finite-index modulus subgroup converges at `s = 1`. -/
def HeckeInput : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ (U : Subgroup (NK.GlobalCFT.Idele K)),
    IsOpen (U : Set (NK.GlobalCFT.Idele K)) →
    Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) →
    ∀ (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U), χ ≠ 1 →
    (∃ 𝔭 : NK.HeckeL.PrimeIdeal K,
      χ (NK.HeckeL.classOfIdeal K U 𝔭.asIdeal) ≠ 1) →
    Nonempty (NK.HeckeL.HeckeLRegularAtOne K U S χ)

/-- **The Frobenius-normalised Artin map**, as a hypothesis. -/
def ArtinFrobeniusInput : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)),
    (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S) →
    ∃ (h : NK.GlobalCFT.ArtinReciprocity K L) (U : Subgroup (NK.GlobalCFT.Idele K))
      (_ : IsOpen (U : Set (NK.GlobalCFT.Idele K)))
      (_ : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U))
      (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
        (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L)),
      NK.HeckeL.FrobeniusCompatibility K L U h e S

/-- **The abelian case of Čebotarev from the two named inputs.** -/
theorem abelianLFunctions_of_inputs (hHecke : HeckeInput) (hFrob : ArtinFrobeniusInput)
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    NK.Chebotarev.AbelianLFunctions K L := by
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  -- the finite set of ramified primes
  have hfin : {𝔭 : NK.HeckeL.PrimeIdeal K | ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭}.Finite :=
    NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn
  let S : Finset (NK.HeckeL.PrimeIdeal K) := hfin.toFinset
  have hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S := fun 𝔭 h𝔭 =>
    hfin.mem_toFinset.mpr h𝔭
  -- the reciprocity isomorphism with its Frobenius normalisation
  obtain ⟨h, U, hUopen, hUfin, e, hFrobC⟩ := hFrob K L S hS
  -- Every non-trivial character of the ray class group is non-trivial on the classes of ideals:
  -- the reciprocity isomorphism identifies the ideal classes with the Frobenius elements, and the
  -- latter generate `Gal(L/K)` (`NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`).
  have hfinχ : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 →
      ∃ 𝔭 : NK.HeckeL.PrimeIdeal K, χ (NK.HeckeL.classOfIdeal K U 𝔭.asIdeal) ≠ 1 := by
    intro χ hχ
    by_contra hcon
    push_neg at hcon
    -- transfer to the Galois side
    set ψ : Gal(L/K) →* ℂˣ := NK.HeckeL.rayCharEquivGalois h e χ with hψ
    have hvan : ∀ σ : Gal(L/K), (∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ S ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ) → ψ σ = 1 := by
      rintro σ ⟨p, hpS, hp⟩
      have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
        by_contra hbad
        exact hpS (hS p hbad)
      have hpeq : NK.Chebotarev.frobAtPrime (K := K) (L := L) p = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm p hunr σ).mp hp
      have h2 : ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) = 1 := by
        rw [hψ, NK.HeckeL.rayCharEquivGalois_apply_apply]
        have hsymm : (NK.HeckeL.reciprocityEquiv h e).symm
            (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) =
            NK.HeckeL.primeClass K U p := by
          rw [← hFrobC.iso_primeClass p hpS]
          exact MulEquiv.symm_apply_apply _ _
        rw [hsymm]
        exact hcon p
      rw [← hpeq]
      exact h2
    -- the Frobenius elements generate `Gal(L/K)`, so a character vanishing on them is trivial
    have hker : Subgroup.closure {σ : Gal(L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ S ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ} ≤ ψ.ker :=
      (Subgroup.closure_le ψ.ker).mpr (fun σ hσ => by
        simp only [Set.mem_setOf_eq] at hσ
        exact MonoidHom.mem_ker.mpr (hvan σ hσ))
    rw [NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem (K := K) (L := L) S,
      top_le_iff] at hker
    have hψ1 : ψ = 1 := MonoidHom.ext fun σ => by
      have : σ ∈ ψ.ker := by rw [hker]; trivial
      simpa using this
    exact hχ ((NK.HeckeL.rayCharEquivGalois_eq_one_iff h e).mp (by rw [← hψ]; exact hψ1))
  -- Hecke's theorem for the non-trivial characters of the modulus
  have hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ :=
    fun χ hχ => (hHecke K U hUopen hUfin S χ hχ (hfinχ χ hχ)).some
  -- transport to the Galois side and apply the chapter's consequences
  have hArtin : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ :=
    NK.HeckeL.Consequences.artinLRegular_of_heckeLRegular h e S hFrobC hH
  exact NK.HeckeL.Consequences.abelianLFunctions S hcomm hS hArtin

/-- **The abelian case of Čebotarev in density form, from the two named inputs.** -/
theorem abelianChebotarevDensity_of_inputs (hHecke : HeckeInput)
    (hFrob : ArtinFrobeniusInput) : NK.ChebotarevGeneral.AbelianChebotarevDensity :=
  fun K L _ _ _ _ _ _ _ hcomm σ =>
    NK.Chebotarev.AbelianChebotarevOfLFunctions hcomm
      (abelianLFunctions_of_inputs hHecke hFrob K L hcomm) σ


/-! ## Status of the remaining inputs (as of this writing)

The chain assembled above reduces `NK.NUV2.ChebAll0` (Čebotarev over `ℚ`, finite-level existence
form) to exactly two named inputs:

* `HeckeInput` — Hecke's theorem: the Hecke `L`-series of a character of an open finite-index
  modulus subgroup which is non-trivial on the *classes of ideals* converges at `s = 1`.  This is
  *pure analysis* (no class field theory): "Abel summation plus the lattice-point estimate for
  ideals in a ray class".  The hypothesis `∃ 𝔭, χ (classOfIdeal K U 𝔭) ≠ 1` is *not* implied by
  `χ ≠ 1`: a character non-trivial only at the archimedean places is invisible to `classOfIdeal`,
  so its `L`-series is the Dedekind zeta function (concrete counterexample: `K = ℚ(√3)`,
  `U = ∏_𝔭 ℤ_𝔭^× × (ℝ_{>0})²`, `χ` the product of the two real signs).  In the application the
  hypothesis is *automatic*: the reciprocity isomorphism identifies the ideal classes with the
  Frobenius elements, which generate `Gal(L/K)`
  (`NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`; see the proof of `hfinχ`
  in `abelianLFunctions_of_inputs`).  The statement is the project's `HeckeInput` as fixed by the
  fleet (cf. `Submission/Work/NUV2/RouteB/heckeInput_build.lean`); the analytic core is the
  lattice-point count with a power-saving error, for which
  `Submission/Work/NUV2/RouteB/latticeCosetCount_cone_isBigO.lean` is already on disk.

* `ArtinFrobeniusInput` — the Artin isomorphism `C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)` *together with its
  Frobenius normalisation* at all unramified primes.  This is the classical Artin map; it is NOT a
  consequence of `NK.GlobalCFTdeep.FundamentalClassElement`:

  - the workspace's `NK.GlobalCFT.ArtinReciprocity` produced from `hFC`
    (`NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement`) is the reciprocity
    isomorphism obtained from an *arbitrarily chosen* element of `H²(Gal(L/K), C_L)` of order
    `[L:K]` (see `GlobalCFTdeep/CoCore/Reciprocity.lean`, `let α := Classical.choose h.fundamentalClass`),
    and it carries no information about which element of `Gal(L/K)` is the image of the class of a
    given prime (this is stated in `CFTLib/pClassFieldArtin_of_fc.lean`, "Status of the target");
  - the Frobenius normalisation is therefore an independent arithmetic input, which the library
    currently only has for `K = ℚ` (`NK.Chebotarev.CyclotomicFrobDensity` and
    `NK.Chebotarev.abelianChebotarev_of_kroneckerWeber`, the latter from Kronecker–Weber).

Consequently, as the library stands, `ChebAll0` is reachable by two routes, both incomplete:

* the *abelian* route over `ℚ`: Kronecker–Weber (`NK.Chebotarev.KroneckerWeber`, delegated as
  `NK.Chebotarev.KroneckerWeber_of_rat`) together with Dirichlet's theorem gives Čebotarev for all
  *abelian* `L/ℚ` (`NK.Chebotarev.abelianChebotarev_of_kroneckerWeber`, proved on disk); the
  *non-abelian* case over `ℚ` is then reduced by the (proved) Deuring transfer
  (`NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian`) to the abelian case over an
  arbitrary number-field base, which is what the next route supplies;

* the *Hecke* route over an arbitrary base: `HeckeInput` + `ArtinFrobeniusInput` give the abelian
  case over an arbitrary base (`abelianChebotarevDensity_of_inputs` above).

So the two open leaves are `HeckeInput` and `ArtinFrobeniusInput`; everything else in the chain is
proved, here or in the workspace. -/

/-- **Čebotarev's input at `Type 0` from the two named inputs of the reciprocity/Hecke route.** -/
theorem chebotarev_all0_of_inputs (hHecke : HeckeInput) (hFrob : ArtinFrobeniusInput) :
    NK.NUV2.ChebAll0 :=
  chebotarev_all0_of_abelianChebotarevDensity (abelianChebotarevDensity_of_inputs hHecke hFrob)

/-! ## The Hecke input, discharged -/

/-- **The analytic input `HeckeInput`, discharged** from the (fleet's) proof of Hecke's partial-sum
estimate in `Submission/Work/NUV2/RouteB/` (`NK.NUV2.RouteB.heckeInput_build`), whose analytic core
is the lattice-point count with a power-saving error
(`Submission/Work/NUV2/RouteB/HeckeTheta/`, on the geometry of numbers in the Minkowski embedding). -/
theorem heckeInput_proved : HeckeInput := fun K _ _ U hU hfin S χ hχ hprime =>
  NK.NUV2.RouteB.heckeInput_build K U hU hfin S χ hχ hprime

/-! ## The ideal-theoretic Artin reciprocity law from Artin's lemma and the transfer

The workspaces's route to the ideal-theoretic law is: Artin's lemma (the auxiliary field) plus the
transfer of Lang's Theorem 2.  These two statements are delegated separately
(`NK.NUV2.ChebAux.auxField_exists`, `NK.NUV2.ChebAux.kernelLe_of_auxField`); everything below is
their assembly, carried out for the statements actually needed. -/

/-- A commutativity proof for a cyclic group, as a term. -/
noncomputable def commOfIsCyclic {G : Type*} [Group G] [IsCyclic G] :
    ∀ a b : G, a * b = b * a := by
  intro a b
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm m n]

/-- The transfer step of Lang's Theorem 2, as a named input. -/
def TransferInput : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))]
    [IsMulCommutative (Gal(L/K))] (m : ℕ) (hm : 0 < m),
    NK.CFTLib.ARL.AuxFieldHyp K L m →
    (∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) →
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m

/-- The conductor drop (the conductor of a cyclic extension is supported on the ramified primes),
as a named input. -/
def ConductorDropInput : Prop :=
  ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (M : ℕ) (hM : 0 < M)
    (hramM : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K,
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprincM : NK.CFTLib.artinKillsPrincipal K L M) (b : Kˣ)
    (hcong : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))),
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1

/-- **The kernel containment for an admissible modulus** (Lang, ANT X §2, Theorem 2), from Artin's
lemma and the transfer. -/
theorem kernelLeOfAdmissible_of_aux
    (htr : TransferInput) (haux : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
      [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m), NK.CFTLib.ARL.AuxFieldHyp K L m)
    (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] [IsMulCommutative (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
  htr K L m hm (haux K L m hm) hram

/-- **Lang's Theorem 2** in the form needed below. -/
theorem langCyclicKernelLe_of_aux
    (htr : TransferInput) (haux : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
      [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m), NK.CFTLib.ARL.AuxFieldHyp K L m)
    (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] [IsMulCommutative (Gal(L/K))] :
    ∃ m : ℕ, 0 < m ∧ NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) ∧
      ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
        NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
        NK.CFTLib.Arl.artinSym (K := K) (L := L) IsMulCommutative.is_comm.comm A = 1 →
        A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
  obtain ⟨m, hm, hadm, hram⟩ :=
    NK.CFTLib.ArtinReciprocityIdeal.exists_admissible (K := K) (L := L)
  exact ⟨m, hm, hadm, hram, kernelLeOfAdmissible_of_aux htr haux K L m hm hadm hram⟩

/-- **The product condition of the reciprocity law**, cyclic case. -/
theorem artinSymbolKillsPrincipal_cyclic_of_aux
    (htr : TransferInput) (haux : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
      [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m), NK.CFTLib.ARL.AuxFieldHyp K L m)
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))] :
    ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) ∧
      NK.CFTLib.ArtinReciprocityIdeal.ArtinSymbolKillsPrincipal K L m := by
  haveI : IsMulCommutative (Gal(L/K)) := IsMulCommutative.of_comm (commOfIsCyclic)
  exact NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex K L
    (langCyclicKernelLe_of_aux htr haux K L)
    (fun m hm hram hadm => NK.Existence.langCyclicRelIndex K L m hm hram hadm)

/-- **The product condition of the reciprocity law**, cyclic case, in the `artinKillsPrincipal`
shape. -/
theorem artinKillsPrincipal_cyclic_of_aux
    (htr : TransferInput) (haux : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
      [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m), NK.CFTLib.ARL.AuxFieldHyp K L m)
    (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] :
    ∃ m : ℕ, 0 < m ∧ NK.CFTLib.artinKillsPrincipal K L m := by
  haveI : IsMulCommutative (Gal(L/K)) := IsMulCommutative.of_comm (commOfIsCyclic)
  exact NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic_of_exists (K := K) (L := L)
    (artinSymbolKillsPrincipal_cyclic_of_aux htr haux K L)

/-- **The conductor exists**, cyclic case. -/
theorem artinConductor_cyclic_of_aux
    (htr : TransferInput) (haux : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
      [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m), NK.CFTLib.ARL.AuxFieldHyp K L m)
    (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] : ∃ m : ℕ, NK.CFTLib.artinConductor K L m := by
  obtain ⟨m, hm, h⟩ := artinKillsPrincipal_cyclic_of_aux htr haux K L
  exact ⟨_, NK.CFTLib.ArtinReciprocityIdeal.artinConductor_of_artinKillsPrincipal hm h⟩

/-- **The ideal-theoretic reciprocity law** `NK.CFTLib.ArtinReciprocityIdeal`, from Artin's lemma
and the transfer. -/
theorem artinReciprocityIdeal_of_auxField
    (htr : TransferInput) (haux : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
      [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m), NK.CFTLib.ARL.AuxFieldHyp K L m) :
    NK.CFTLib.ArtinReciprocityIdeal :=
  NK.CFTLib.ArtinReciprocityIdeal_of_cyclicCase
    (fun K L _ _ _ _ _ _ _ _ => artinConductor_cyclic_of_aux htr haux K L)

/-! ## The reciprocity data at a freely chosen set of bad primes

`ArtinFrobeniusInput` insists that the Frobenius normalisation hold at *every* prime outside the
given set `S`.  For the Hecke/Artin comparison it suffices to avoid the primes *dividing the
modulus*, and the modulus is chosen by the construction; the following variant therefore lets the
proof choose `S` (subject to containing the ramified primes).  This avoids the `conductorDrop`
normalisation at the unramified primes dividing the modulus. -/

/-- **The reciprocity data at a freely chosen finite set of bad primes.** -/
def ArtinFrobeniusInputFree : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)],
    ∃ (h : NK.GlobalCFT.ArtinReciprocity K L) (U : Subgroup (NK.GlobalCFT.Idele K))
      (_ : IsOpen (U : Set (NK.GlobalCFT.Idele K)))
      (_ : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U))
      (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
        (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
      (S : Finset (NK.HeckeL.PrimeIdeal K)),
      (∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
        ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S) ∧
      NK.HeckeL.FrobeniusCompatibility K L U h e S

open NK.GlobalCFT (Idele IdeleClassGroup) in
/-- **The free-bad-prime reciprocity data from the ideal-theoretic Artin reciprocity law.**

The bookkeeping of `NK.NUV2.RouteB.artinFrobenius_of_idelicArtin`, with the idèlic Artin map
built directly by `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` at a modulus `M` supplied by the
law and with `S` chosen to contain the primes dividing `(M)`.  The Frobenius normalisation is
therefore needed only at the primes coprime to `(M)`, where it is the `hgood` clause of the
construction; the `conductorDrop` normalisation at an unramified prime dividing the modulus is not
required. -/
theorem artinFrobeniusInputFree_of_artinReciprocityIdeal
    (harl : NK.CFTLib.ArtinReciprocityIdeal) : ArtinFrobeniusInputFree := by
  intro K L _ _ _ _ _ _ _ hcommI
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => hcommI.is_comm.comm a b
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm hcomm
  obtain ⟨M, hM, hramM, hprincM⟩ := harl K L hcomm
  obtain ⟨U₀, hU₀, hadj₀⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K M hM
  obtain ⟨art, hAgree, hprincipal, hgood, _hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcomm M hM hramM hprincM U₀ hU₀ hadj₀
  -- the norm clause
  have hUeq : U₀ = NK.CFTLib.Arl.congruenceSubgroup K M := by
    refine SetLike.ext fun x => (hU₀.1 x).trans ?_
    rfl
  have hadjN : ∀ y : Idele L, ∃ d : Lˣ,
      Idele.normIdeleHom K L (y * Idele.principalIdele L d) ∈ U₀ := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L M hM y
    exact ⟨d, hUeq ▸ hd⟩
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hAgree]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcomm M hM hramM hprincM U₀ hU₀ hadj₀
      hadjN y
  -- the modulus is the kernel of `art`
  let U : Subgroup (Idele K) := art.ker
  have hprin_le : Idele.principalSubgroup K ≤ U := by
    intro x hx
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  have hnorm_le : Idele.normImage K L ≤ U := by
    intro y hy
    obtain ⟨y₀, hy₀⟩ := Idele.mem_normImage.mp hy
    have hyeq : y = Idele.normIdeleHom K L y₀ := by
      ext v
      rw [hy₀ v]
      rfl
    rw [hyeq]
    exact MonoidHom.mem_ker.mpr (hnorm y₀)
  have hsup : Idele.principalSubgroup K ⊔ U = U := sup_eq_right.mpr hprin_le
  haveI hfinU : Finite (Idele K ⧸ art.ker) := by
    haveI : Finite (art.range) := by infer_instance
    exact Finite.of_injective ((QuotientGroup.quotientKerEquivRange art : _) : _ → art.range)
      (QuotientGroup.quotientKerEquivRange art).injective
  haveI hfinRay : Finite (IdeleClassGroup.rayClassGroup K U) := by
    show Finite (Idele K ⧸ (Idele.principalSubgroup K ⊔ U))
    rw [hsup]
    exact hfinU
  have hker_le : Idele.principalSubgroup K ⊔ U ≤ art.ker := by rw [hsup]
  let bar : IdeleClassGroup.rayClassGroup K U →* Gal(L/K) :=
    QuotientGroup.lift (Idele.principalSubgroup K ⊔ U) art hker_le
  have hprimeClass_eq : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      NK.HeckeL.primeClass K U 𝔭 = QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal) := by
    intro 𝔭
    show IdeleClassGroup.rayClassGroupMk K U
      (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal)) =
        QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal)
    simp only [IdeleClassGroup.rayClassGroupMk, IdeleClassGroup.mk, QuotientGroup.map_mk',
      MonoidHom.id_apply]
  have hbar_primeClass : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, (M : 𝓞 K) ∉ 𝔭.asIdeal →
      bar (NK.HeckeL.primeClass K U 𝔭) = NK.Chebotarev.frobAtPrime 𝔭 := by
    intro 𝔭 h𝔭
    have h1 : bar (QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal)) =
        art (NK.HeckeL.ideleOfIdeal K 𝔭.asIdeal) :=
      QuotientGroup.lift_mk (Idele.principalSubgroup K ⊔ U) hker_le _
    rw [hprimeClass_eq 𝔭, h1,
      NK.GlobalCFTdeep.SecondInequality.ideleOfIdeal_prime_eq_ideleOfPrime]
    exact hgood 𝔭 h𝔭
  -- the set of bad primes: the ramified primes together with those dividing `(M)`
  classical
  have hfinram : {𝔭 : NK.HeckeL.PrimeIdeal K |
      ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭}.Finite :=
    NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn
  have hfinM : {𝔭 : NK.HeckeL.PrimeIdeal K | (M : 𝓞 K) ∈ 𝔭.asIdeal}.Finite :=
    NK.CFTLib.ArtinReciprocityIdeal.finite_setOf_mem_span (K := K) M hM
  let S : Finset (NK.HeckeL.PrimeIdeal K) := hfinram.toFinset ∪ hfinM.toFinset
  have hS_ram : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S := fun 𝔭 h𝔭 =>
    Finset.mem_union_left _ (hfinram.mem_toFinset.mpr h𝔭)
  have hS_M : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭 ∉ S → (M : 𝓞 K) ∉ 𝔭.asIdeal :=
    fun 𝔭 h𝔭 hmem => h𝔭 (Finset.mem_union_right _ (hfinM.mem_toFinset.mpr hmem))
  have hbar_surj : Function.Surjective bar := by
    have hgen : Subgroup.closure {σ : Gal(L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ S ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ} = ⊤ :=
      NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem (K := K) (L := L) S
    have hle : Subgroup.closure {σ : Gal(L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ S ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ} ≤ bar.range := by
      rw [Subgroup.closure_le]
      rintro σ ⟨p, hpS, hpσ⟩
      have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
        by_contra hc
        exact hpS (hS_ram p hc)
      have hpeq : NK.Chebotarev.frobAtPrime (K := K) (L := L) p = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm p hunr σ).mp hpσ
      rw [← hpeq]
      exact ⟨NK.HeckeL.primeClass K U p, hbar_primeClass p (hS_M p hpS)⟩
    have htop : (⊤ : Subgroup Gal(L/K)) ≤ bar.range := by rw [← hgen]; exact hle
    intro x
    exact MonoidHom.mem_range.mp (htop (Subgroup.mem_top x))
  -- the cardinality comparison
  have hle1 : Nat.card (Gal(L/K)) ≤ Nat.card (IdeleClassGroup.rayClassGroup K U) :=
    Nat.card_le_card_of_surjective bar hbar_surj
  haveI hfinN : (Idele.normClassSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr
      (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := L))
  haveI hfinQ : Finite (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) := by infer_instance
  have hN_le : Idele.normClassSubgroup K L ≤ (IdeleClassGroup.rayClassGroupMk K U).ker := by
    rw [IdeleClassGroup.ker_rayClassGroupMk]
    exact Subgroup.map_mono hnorm_le
  let E : (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) →*
      IdeleClassGroup.rayClassGroup K U :=
    QuotientGroup.lift (Idele.normClassSubgroup K L) (IdeleClassGroup.rayClassGroupMk K U) hN_le
  have hE_surj : Function.Surjective E := by
    intro y
    obtain ⟨z, hz⟩ := IdeleClassGroup.rayClassGroupMk_surjective (K := K) U y
    exact ⟨QuotientGroup.mk z, (QuotientGroup.lift_mk (Idele.normClassSubgroup K L) hN_le z).trans hz⟩
  have hle2 : Nat.card (IdeleClassGroup.rayClassGroup K U) ≤
      Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    Nat.card_le_card_of_surjective E hE_surj
  have hle3 : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) ≤ Nat.card (Gal(L/K)) := by
    rw [← Subgroup.index_eq_card (Idele.normClassSubgroup K L), IsGalois.card_aut_eq_finrank]
    exact NK.GlobalCFTdeep.index_le_finrank_of_isSolvable (K := K) (L := L)
  have hcardRayGal : Nat.card (IdeleClassGroup.rayClassGroup K U) = Nat.card (Gal(L/K)) :=
    le_antisymm (le_trans hle2 hle3) hle1
  have hcardRayN : Nat.card (IdeleClassGroup.rayClassGroup K U) =
      Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    le_antisymm hle2 (le_trans hle3 hle1)
  haveI hFtRay : Fintype (IdeleClassGroup.rayClassGroup K U) := Fintype.ofFinite _
  haveI hFtGal : Fintype (Gal(L/K)) := Fintype.ofFinite _
  haveI hFtN : Fintype (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) := Fintype.ofFinite _
  have hbarbij : Function.Bijective bar := by
    refine (Fintype.bijective_iff_surjective_and_card bar).mpr ⟨hbar_surj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardRayGal
  have hEbij : Function.Bijective E := by
    refine (Fintype.bijective_iff_surjective_and_card E).mpr ⟨hE_surj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardRayN.symm
  let barB : IdeleClassGroup.rayClassGroup K U ≃* Gal(L/K) := MulEquiv.ofBijective bar hbarbij
  let Ee : (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) ≃*
      IdeleClassGroup.rayClassGroup K U := MulEquiv.ofBijective E hEbij
  refine ⟨⟨Ee.trans barB⟩, U, Subgroup.isOpen_mono hnorm_le (NK.NUV2.ARL.isOpenNorm K L),
    hfinRay, Ee.symm, S, hS_ram, ?_⟩
  refine ⟨fun 𝔭 h𝔭 => ?_⟩
  have hval : ((Ee.symm).trans (Ee.trans barB)) (NK.HeckeL.primeClass K U 𝔭)
      = barB (NK.HeckeL.primeClass K U 𝔭) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [hval, ← hbar_primeClass 𝔭 (hS_M 𝔭 h𝔭)]
  exact MulEquiv.ofBijective_apply bar hbarbij _

/-- **The abelian case of the analytic input from the Hecke input and the free-bad-prime
reciprocity data.** -/
theorem abelianLFunctions_of_freeInputs (hHecke : HeckeInput) (hFrob : ArtinFrobeniusInputFree)
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    NK.Chebotarev.AbelianLFunctions K L := by
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  obtain ⟨h, U, hUopen, hUfin, e, S, hS, hFrobC⟩ := hFrob K L
  have hfinχ : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 →
      ∃ 𝔭 : NK.HeckeL.PrimeIdeal K, χ (NK.HeckeL.classOfIdeal K U 𝔭.asIdeal) ≠ 1 := by
    intro χ hχ
    by_contra hcon
    push_neg at hcon
    set ψ : Gal(L/K) →* ℂˣ := NK.HeckeL.rayCharEquivGalois h e χ with hψ
    have hvan : ∀ σ : Gal(L/K), (∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ S ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ) → ψ σ = 1 := by
      rintro σ ⟨p, hpS, hp⟩
      have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
        by_contra hbad
        exact hpS (hS p hbad)
      have hpeq : NK.Chebotarev.frobAtPrime (K := K) (L := L) p = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm p hunr σ).mp hp
      have h2 : ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) = 1 := by
        rw [hψ, NK.HeckeL.rayCharEquivGalois_apply_apply]
        have hsymm : (NK.HeckeL.reciprocityEquiv h e).symm
            (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) =
            NK.HeckeL.primeClass K U p := by
          rw [← hFrobC.iso_primeClass p hpS]
          exact MulEquiv.symm_apply_apply _ _
        rw [hsymm]
        exact hcon p
      rw [← hpeq]
      exact h2
    have hker : Subgroup.closure {σ : Gal(L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ S ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ} ≤ ψ.ker :=
      (Subgroup.closure_le ψ.ker).mpr (fun σ hσ => by
        simp only [Set.mem_setOf_eq] at hσ
        exact MonoidHom.mem_ker.mpr (hvan σ hσ))
    rw [NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem (K := K) (L := L) S,
      top_le_iff] at hker
    have hψ1 : ψ = 1 := MonoidHom.ext fun σ => by
      have : σ ∈ ψ.ker := by rw [hker]; trivial
      simpa using this
    exact hχ ((NK.HeckeL.rayCharEquivGalois_eq_one_iff h e).mp (by rw [← hψ]; exact hψ1))
  have hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ :=
    fun χ hχ => (hHecke K U hUopen hUfin S χ hχ (hfinχ χ hχ)).some
  have hArtin : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ :=
    NK.HeckeL.Consequences.artinLRegular_of_heckeLRegular h e S hFrobC hH
  exact NK.HeckeL.Consequences.abelianLFunctions S hcomm hS hArtin

/-- **The abelian case of Čebotarev in density form, from the Hecke input and the free-bad-prime
reciprocity data.** -/
theorem abelianChebotarevDensity_of_freeInputs (hHecke : HeckeInput)
    (hFrob : ArtinFrobeniusInputFree) : NK.ChebotarevGeneral.AbelianChebotarevDensity :=
  fun K L _ _ _ _ _ _ _ hcomm σ =>
    NK.Chebotarev.AbelianChebotarevOfLFunctions hcomm
      (abelianLFunctions_of_freeInputs hHecke hFrob K L hcomm) σ

/-- **Čebotarev's input at `Type 0` from the Hecke input and the free-bad-prime reciprocity
data.** -/
theorem chebotarev_all0_of_freeInputs (hHecke : HeckeInput) (hFrob : ArtinFrobeniusInputFree) :
    NK.NUV2.ChebAll0 :=
  chebotarev_all0_of_abelianChebotarevDensity (abelianChebotarevDensity_of_freeInputs hHecke hFrob)

/-! ## The target lemma -/


/-- **Čebotarev** (`ChebotarevInputDerived`, `Type 0`), from the Hecke input and the
ideal-theoretic Artin reciprocity law. -/
theorem chebotarev_all0 (hFC : NK.GlobalCFTdeep.FundamentalClassElement) : NK.NUV2.ChebAll0 :=
  chebotarev_all0_of_freeInputs heckeInput_proved
    (artinFrobeniusInputFree_of_artinReciprocityIdeal
      (artinReciprocityIdeal_of_auxField
        (fun K L _ _ _ _ _ _ _ _ _ m hm =>
          NK.NUV2.ChebAux.kernelLe_of_auxField K L m hm)
        (fun K L _ _ _ _ _ _ _ _ m hm =>
          NK.CFTLib.ARL.auxField_exists_B K L m hm)))

end NK.NUV2
