import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.EscapeCoreLib.algEquiv_extend_compositum
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
import Submission.Work.SSGRoute.EscapeCoreLib.card_residue_eq_of_isFrobAt_one
import Submission.Work.SSGRoute.EscapeCoreLib.exists_finiteDimensional_galois_superset
import Submission.Work.SSGRoute.EscapeCoreLib.isGalois_comap
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff

/-!
# The escape prime with a prescribed Frobenius, at the prime of `↥K` below it

`escapePrimeFrobAtPrime` is the `↥K`-base refinement of
`Work.SSGRoute.EscapeCoreLib.exists_place_frobenius_of_compat`: instead of asking only for a place
`Q` of `Ω` avoiding a finite set of `G_k`-conjugacy classes, completely split in `N/k`, and
carrying `σ ∈ decomp k Q` with `σ|_M = α`, it also produces the prime `𝔮` of `𝓞 ↥K` below `Q` and
proves that `α` is the arithmetic Frobenius of `𝔮` in the extension `↥M / ↥K`.

The proof is the Čebotarev step of `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split` (over the
base `k`), *with the prime of `𝓞 ↥L` below the escape place exposed*: from the Frobenius `τ|_L` at
that prime one recovers, on the one hand, the trivial Frobenius at the prime of `𝓞 ↥K` below it
(because `τ` fixes `K ≤ N` pointwise) and hence residue degree one, and, on the other hand, the
congruence defining the Frobenius for `α` at the prime below in `𝓞 ↥M` — the two coincide because
the residue degree of the `↥K`-prime over the `k`-prime is one, so **no power of `τ` appears**.

The main ingredients (all proved here, on top of the existing library):

* `trivialFrobAt_under_of_isFrobAt_of_fixes` — `τ` fixing `K` makes `1` the Frobenius at the
  `↥K`-prime below `P`;
* `isFrobAt_under_of_isFrobAt_of_fixes` — the passage from the `k`-base Frobenius to the
  `↥K`-base Frobenius at the prime below, using `↥K`-linearity of `α` (not `↥K`-linearity of `τ`,
  so that no normality of `M/k` is needed);
* `galoisLevel_and_tau_of_orthogonality` — the level `L/k` and `τ` produced from the orthogonality;
* `chebotarev_frobenius_split_withPrime` — the Čebotarev step with the prime exposed.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EscapeCoreLib

open _root_.SSGRoute

/-- The trivial Frobenius at the `K`-prime below `P`: `τ` fixes `K` pointwise, so the Frobenius
of the `K`-prime over the `k`-prime below it is `1`. -/
theorem trivialFrobAt_under_of_isFrobAt_of_fixes
    {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (P : NK.Chebotarev.PrimeIdeal L) (τ : Gal(L/k))
    (hL : NK.Chebotarev.IsFrobAt (K := k) (L := L) P τ)
    (hfix : ∀ x : K, τ (algebraMap K L x) = algebraMap K L x) :
    NK.Chebotarev.IsFrobAt (K := k) (L := K)
      (P.under (NumberField.RingOfIntegers K)) (1 : Gal(K/k)) := by
  rw [NK.Chebotarev.isFrobAt_def]
  intro x
  rw [show Nat.card (NumberField.RingOfIntegers k ⧸
      (P.under (NumberField.RingOfIntegers K)).asIdeal.under (NumberField.RingOfIntegers k))
    = Nat.card (NumberField.RingOfIntegers k ⧸ P.asIdeal.under (NumberField.RingOfIntegers k))
    from by
      congr 1
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]]
  rw [show (galRestrict (NumberField.RingOfIntegers k) k K
      (NumberField.RingOfIntegers K) (1 : Gal(K/k))) = 1 from map_one _]
  simp only [AlgEquiv.one_apply]
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have hy := (NK.Chebotarev.isFrobAt_def (K := k) (L := L) P τ).mp hL
    (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) x)
  have hfixy : (galRestrict (NumberField.RingOfIntegers k) k L
      (NumberField.RingOfIntegers L) τ) (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) x)
      = algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) x := by
    refine NumberField.RingOfIntegers.ext ?_
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      algebraMap_galRestrict_apply]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L x]
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L x]
    exact hfix _
  rw [hfixy] at hy
  simpa [map_sub, map_pow] using hy

/-- **The Frobenius at the `↥K`-prime, from the `k`-base Frobenius at `P`.**  Suppose `τ ∈ Gal(L/k)`
is an arithmetic Frobenius at the prime `P` of `𝓞 L`, that `τ` fixes `K ⊆ L` pointwise, and that
`τ` acts on `M ⊆ L` as `α ∈ Gal(M/K)`.  Then `α` is an arithmetic Frobenius at the prime of `𝓞 M`
below `P` in the extension `M/K`.

Indeed `τ|_K = 1` makes the residue degree of the `K`-prime over the `k`-prime below it one
(`trivialFrobAt_under_of_isFrobAt_of_fixes` plus
`card_residue_eq_of_isFrobAt_one`), so the two defining congruences for `α` — the one at the `k`-base
and the one at the `K`-base — have the same exponent; the `k`-base congruence is then transported
to `𝓞 M` through `𝓞 M → 𝓞 L` using the compatibility of `galRestrict` with the algebra maps
(`algebraMap_galRestrict_apply`).  No normality of `M/k` is used. -/
theorem isFrobAt_under_of_isFrobAt_of_fixes
    {k K M L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L]
    [Algebra k K] [Algebra K M] [Algebra k M] [IsScalarTower k K M]
    [Algebra k L] [Algebra K L] [Algebra M L]
    [IsScalarTower k K L] [IsScalarTower k M L] [IsScalarTower K M L]
    [FiniteDimensional k K] [FiniteDimensional k M] [FiniteDimensional k L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (P : NK.Chebotarev.PrimeIdeal L) (α : Gal(M/K)) (τ : Gal(L/k))
    (hL : NK.Chebotarev.IsFrobAt (K := k) (L := L) P τ)
    (hfix : ∀ x : K, τ (algebraMap K L x) = algebraMap K L x)
    (hagr : ∀ x : M, τ (algebraMap M L x) = algebraMap M L (α x)) :
    NK.Chebotarev.IsFrobAt (K := K) (L := M)
      (P.under (NumberField.RingOfIntegers M)) α := by
  classical
  -- ### the trivial Frobenius at the `K`-prime
  have hK1 := trivialFrobAt_under_of_isFrobAt_of_fixes (k := k) (K := K) (L := L) P τ hL hfix
  -- ### the residue fields of the `K`-prime and of the `k`-prime agree
  have hcardK : Nat.card (NumberField.RingOfIntegers K ⧸
      (P.under (NumberField.RingOfIntegers K)).asIdeal)
      = Nat.card (NumberField.RingOfIntegers k ⧸
          (P.under (NumberField.RingOfIntegers K)).asIdeal.under (NumberField.RingOfIntegers k)) :=
    card_residue_eq_of_isFrobAt_one (P.under (NumberField.RingOfIntegers K)) hK1
  rw [NK.Chebotarev.isFrobAt_def]
  intro x
  -- ### the exponent is `#(𝓞 k ⧸ P ∩ 𝓞 k)`
  rw [show (P.under (NumberField.RingOfIntegers M)).asIdeal.under (NumberField.RingOfIntegers K)
      = (P.under (NumberField.RingOfIntegers K)).asIdeal from by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
          IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]]
  rw [hcardK]
  rw [show (P.under (NumberField.RingOfIntegers K)).asIdeal.under (NumberField.RingOfIntegers k)
      = P.asIdeal.under (NumberField.RingOfIntegers k) from by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]]
  -- ### reduce to the `𝓞 L`-congruence
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have hy := (NK.Chebotarev.isFrobAt_def (K := k) (L := L) P τ).mp hL
    (algebraMap (NumberField.RingOfIntegers M) (NumberField.RingOfIntegers L) x)
  -- ### compatibility of the two `galRestrict`s
  have hcompat : (galRestrict (NumberField.RingOfIntegers k) k L
        (NumberField.RingOfIntegers L) τ)
        (algebraMap (NumberField.RingOfIntegers M) (NumberField.RingOfIntegers L) x)
      = algebraMap (NumberField.RingOfIntegers M) (NumberField.RingOfIntegers L)
        ((galRestrict (NumberField.RingOfIntegers K) K M (NumberField.RingOfIntegers M) α) x) := by
    refine NumberField.RingOfIntegers.ext ?_
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      algebraMap_galRestrict_apply]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers M)
      (NumberField.RingOfIntegers L) L x]
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers M) M L x]
    rw [hagr]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers M)
      (NumberField.RingOfIntegers L) L
      ((galRestrict (NumberField.RingOfIntegers K) K M (NumberField.RingOfIntegers M) α) x)]
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers M) M L
      ((galRestrict (NumberField.RingOfIntegers K) K M (NumberField.RingOfIntegers M) α) x)]
    rw [algebraMap_galRestrict_apply]
  rw [hcompat] at hy
  simpa [map_sub, map_pow] using hy

/-- The finite Galois level `L/k` containing `K`, `M`, `N` together with `τ ∈ G_k` fixing `N`
and acting as `α` on `M`.  (Adapted from the corresponding part of the proof of
`exists_place_frobenius_of_compat`.) -/
theorem galoisLevel_and_tau_of_orthogonality
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hαfix : ∀ x : ↥M, ((x : Ω) ∈ N) → ((α x : ↥M) : Ω) = (x : Ω)) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (τ : Ω ≃ₐ[k] Ω),
      K ≤ L ∧ M.restrictScalars k ≤ L ∧ N ≤ L ∧
      SSGRoute.res k N τ = 1 ∧
      (∀ x : ↥M, τ (x : Ω) = ((α x : ↥M) : Ω)) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  -- ### Step 1: a finite Galois extension of `k` containing `K`, `M` and `N`
  let Mk : IntermediateField k Ω := M.restrictScalars k
  have hMk : (Mk : Set Ω) = (M : Set Ω) := IntermediateField.coe_restrictScalars k (E := M)
  haveI : FiniteDimensional k Mk := by
    haveI : FiniteDimensional k ↥M := FiniteDimensional.trans k ↥K ↥M
    exact ‹FiniteDimensional k ↥M›
  obtain ⟨L, hLd, hLg, hKL, hMLk, hNL⟩ := exists_finiteDimensional_galois_superset K Mk N
  haveI : FiniteDimensional k L := hLd
  haveI : IsGalois k L := hLg
  -- ### Step 2: view `M` and `N` as `↥K`-intermediate fields inside `LK`
  let LK : IntermediateField ↥K Ω := baseChange K L hKL
  haveI htow_k_LK_Ω : IsScalarTower k ↥LK Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htow_k_K_LK : IsScalarTower k ↥K ↥LK := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois k ↥LK := IsGalois.of_algEquiv (baseChangeAlgEquiv K L hKL)
  haveI : IsGalois ↥K LK := isGalois_baseChange K L hKL
  haveI : FiniteDimensional k ↥LK := finiteDimensional_baseChange K L hKL
  haveI : FiniteDimensional ↥K ↥LK := Module.Finite.of_restrictScalars_finite k ↥K ↥LK
  let NK : IntermediateField ↥K Ω := baseChange K N hKN
  haveI : IsGalois ↥K NK := isGalois_baseChange K N hKN
  haveI : FiniteDimensional k ↥NK := finiteDimensional_baseChange K N hKN
  haveI : FiniteDimensional ↥K ↥NK := Module.Finite.of_restrictScalars_finite k ↥K ↥NK
  have hMLK : M ≤ LK := fun x hx => (mem_baseChange K L hKL).mpr (hMLk (by
    show x ∈ (Mk : Set Ω); rw [hMk]; exact hx))
  have hNKLK : NK ≤ LK := fun x hx =>
    (mem_baseChange K L hKL).mpr (hNL ((mem_baseChange K N hKN).mp hx))
  let ML : IntermediateField ↥K ↥LK := M.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  let NL : IntermediateField ↥K ↥LK := NK.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  haveI : IsGalois ↥K ML := isGalois_comap_of_le_over K LK M hMLK
  haveI : IsGalois ↥K NL := isGalois_comap_of_le_over K LK NK hNKLK
  haveI : FiniteDimensional ↥K ↥ML :=
    FiniteDimensional.of_injective (comapAlgEquiv K LK M hMLK).symm.toLinearEquiv.toLinearMap
      (comapAlgEquiv K LK M hMLK).symm.injective
  haveI : FiniteDimensional ↥K ↥NL :=
    FiniteDimensional.of_injective (comapAlgEquiv K LK NK hNKLK).symm.toLinearEquiv.toLinearMap
      (comapAlgEquiv K LK NK hNKLK).symm.injective
  -- ### Step 3: extend `α` to a `↥K`-automorphism of `LK` fixing `NL`
  let e := comapAlgEquiv K LK M hMLK
  let α' : ↥ML ≃ₐ[↥K] ↥ML := e.symm.trans (α.trans e)
  have hα'fix : ∀ x : ↥ML, ((x : ↥LK) ∈ NL) → (((α' x : ↥ML) : ↥LK)) = (x : ↥LK) := by
    intro x hx
    refine Subtype.ext ?_
    have hxN : ((x : ↥LK) : Ω) ∈ NK := hx
    exact comapAlgEquiv_transport K LK M NK hMLK α
      (fun y hy => hαfix y ((mem_baseChange K N hKN).mp hy)) x hxN
  obtain ⟨g, hgML, hgNL⟩ :=
    exists_algEquiv_restrict_eq_of_fixing (K := ↥K) (L := ↥LK) ML NL α' hα'fix
  -- ### Step 4: lift the `↥K`-automorphism of `LK` to a `k`-automorphism `τ` of `Ω`
  let gk : ↥LK ≃ₐ[k] ↥LK := g.restrictScalars k
  have hgk_apply : ∀ y : ↥LK, gk y = g y := fun y => rfl
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥LK) (E := Ω) gk
  -- ### Step 5: `τ` fixes `N` pointwise, hence `res k N τ = 1`
  have hτN : SSGRoute.res k N τ = 1 := by
    rw [show SSGRoute.res k N τ = AlgEquiv.restrictNormalHom N τ from rfl,
      ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxL : x ∈ L := hNL hx
    have hxLK : x ∈ LK := (mem_baseChange K L hKL).mpr hxL
    have hxNK : x ∈ NK := (mem_baseChange K N hKN).mpr hx
    have hxNL : (⟨x, hxLK⟩ : ↥LK) ∈ NL := hxNK
    have hτx : τ x = (((gk ⟨x, hxLK⟩ : ↥LK)) : Ω) := by
      have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨x, hxLK⟩ : ↥LK) : Ω) = τ x :=
        AlgEquiv.restrictNormal_commutes τ ↥LK ⟨x, hxLK⟩
      have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨x, hxLK⟩ = gk ⟨x, hxLK⟩ :=
        congrArg (fun f => f ⟨x, hxLK⟩) hτ
      rw [← h1, hy]
    have hgx : (((g ⟨x, hxLK⟩ : ↥LK)) : Ω) = x := by
      have h := congrArg (fun (z : ↥LK) => (z : Ω)) (hgNL _ hxNL)
      simpa using h
    rw [hτx, hgk_apply, hgx]
  refine ⟨L, hLd, hLg, τ, hKL, hMLk, hNL, hτN, ?_⟩
  -- ### Step 6: `τ` acts as `α` on `M`
  intro x
  have hxL : (x : Ω) ∈ L := hMLk (by show (x : Ω) ∈ (Mk : Set Ω); rw [hMk]; exact x.2)
  have hxLK : (x : Ω) ∈ LK := (mem_baseChange K L hKL).mpr hxL
  have hτx : τ (x : Ω) = (((gk ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) := by
    have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨(x : Ω), hxLK⟩ : ↥LK) : Ω) = τ (x : Ω) :=
      AlgEquiv.restrictNormal_commutes τ ↥LK ⟨(x : Ω), hxLK⟩
    have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨(x : Ω), hxLK⟩ = gk ⟨(x : Ω), hxLK⟩ :=
      congrArg (fun f => f ⟨(x : Ω), hxLK⟩) hτ
    rw [← h1, hy]
  rw [hτx, hgk_apply]
  have hzx : (((e x : ↥ML)) : ↥LK) = ⟨(x : Ω), hxLK⟩ := by
    refine Subtype.ext ?_
    rw [comapAlgEquiv_coe]
  have hgval : (((g ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) = ((((α' (e x) : ↥ML)) : ↥LK) : Ω) := by
    have h1 : g ⟨(x : Ω), hxLK⟩ = ((α' (e x) : ↥ML) : ↥LK) := by
      rw [← hzx]
      exact hgML (e x)
    exact congrArg (fun (z : ↥LK) => (z : Ω)) h1
  rw [hgval]
  have hα'x : α' (e x) = e (α x) := by
    simp only [α', AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [hα'x]
  exact comapAlgEquiv_coe K LK M hMLK (α x)

/-- The Čebotarev step of `ZDataTwo.chebotarev_frobenius_split`, with the `L`-prime exposed:
the prime `P` of `𝓞 ↥L` below the escape place `B`, together with the fact that `τ|_L` is a
Frobenius at `P`. -/
theorem chebotarev_frobenius_split_withPrime (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (L N : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k N] [IsGalois k N] (hNL : N ≤ L)
    (T' : Finset (ValuationSubring Ω))
    (τ : Ω ≃ₐ[k] Ω) (hτ : SSGRoute.res k N τ = 1) :
    ∃ (B : ValuationSubring Ω) (P : NK.Chebotarev.PrimeIdeal ↥L),
      SSGRoute.IsFinPlace k B ∧
      (∀ C ∈ T', ¬ SSGRoute.IsConjPlace k C B) ∧
      ¬ SSGRoute.IsRamifiedIn k L B ∧ SSGRoute.IsSplitIn k N B ∧
      B.comap (algebraMap ↥L Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P ∧
      NK.Chebotarev.IsFrobAt (K := k) (L := ↥L) P (SSGRoute.res k L τ) ∧
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k B ∧
        SSGRoute.res k L σ = SSGRoute.res k L τ := by
  classical
  letI : Algebra ↥N ↥L := (Subsemiring.inclusion hNL).toAlgebra
  haveI htowNLk : IsScalarTower k ↥N ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowNLΩ : IsScalarTower ↥N ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI : NumberField ↥N := NumberField.of_module_finite k ↥N
  set Bad : Set (NK.Chebotarev.PrimeIdeal k) :=
    {p | ∃ A ∈ T', A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p}
    ∪ {p | ∃ P : NK.Chebotarev.PrimeIdeal ↥L,
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1}
    ∪ {p | ∃ P : NK.Chebotarev.PrimeIdeal ↥N,
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} with hBaddef
  have hBad : Bad.Finite := by
    rw [hBaddef]
    exact ((finite_setOf_primeUnder (k := k) (Ω := Ω) T').union
      (finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) L)).union
      (finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) N)
  obtain ⟨p, hpBad, hFrob⟩ := exists_isFrobAtPrime_notMem_finite hc Bad hBad L (SSGRoute.res k L τ)
  obtain ⟨P, hPlies, hPfrob⟩ := hFrob
  obtain ⟨B, hBcomap⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := ↥L) (K' := Ω) P
  -- the three components of `p ∉ Bad`
  have hpBad₁ : p ∉ {p | ∃ A ∈ T', A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p} := by
    rw [hBaddef] at hpBad; exact fun h => hpBad (Or.inl (Or.inl h))
  have hpBadL : ∀ P_L : NK.Chebotarev.PrimeIdeal ↥L, P_L.asIdeal.LiesOver p.asIdeal →
      P_L.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro P_L hPL
    by_contra hne
    rw [hBaddef] at hpBad
    exact hpBad (Or.inl (Or.inr ⟨P_L, hPL, hne⟩))
  have hpBadN : ∀ P_N : NK.Chebotarev.PrimeIdeal ↥N, P_N.asIdeal.LiesOver p.asIdeal →
      P_N.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro P_N hPN
    by_contra hne
    rw [hBaddef] at hpBad
    exact hpBad (Or.inr ⟨P_N, hPN, hne⟩)
  -- the prime of `k` below `B` is `p`
  have hBp : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p := by
    have hunderAs : (IsDedekindDomain.HeightOneSpectrum.under
        (NumberField.RingOfIntegers k) P).asIdeal = p.asIdeal := by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact hPlies.over.symm
    have hunder : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers k) P = p :=
      IsDedekindDomain.HeightOneSpectrum.ext hunderAs
    have h1 : B.comap (algebraMap k Ω) =
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P).comap
          (algebraMap k ↥L) := by
      rw [← hBcomap]
      exact (ValuationSubring.comap_comap B (algebraMap ↥L Ω) (algebraMap k ↥L)).symm
    rw [h1, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p P hPlies]
  have hBne : B.comap (algebraMap k Ω) ≠ ⊤ := by
    rw [hBp]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) p
  refine ⟨B, P, hBne, ?_, ?_, ?_, hBcomap, hPfrob, ?_⟩
  · -- avoidance of the conjugates of `T'`
    intro C hC hconj
    exact not_isConjPlace_of_notMem_primeUnder (k := k) (Ω := Ω) T' B p hBp hpBad₁ C hC hconj
  · -- unramifiedness in `L`
    have hlev := levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one (k := k) (Ω := Ω) L B hBne p
      hBp hpBadL
    exact not_isRamifiedIn_of_levelSub_le_fixingSubgroup (k := k) (Ω := Ω) L B hlev
  · -- complete splitting in `N`
    have hBN : B.comap (algebraMap ↥N Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N
          (P.under (NumberField.RingOfIntegers ↥N)) := by
      have hliesN : P.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers ↥N)).asIdeal := by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
        exact ⟨rfl⟩
      have h1 : B.comap (algebraMap ↥N Ω) =
          (B.comap (algebraMap ↥L Ω)).comap (algebraMap ↥N ↥L) :=
        (ValuationSubring.comap_comap B (algebraMap ↥L Ω) (algebraMap ↥N ↥L)).symm
      rw [h1, hBcomap, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (P.under (NumberField.RingOfIntegers ↥N)) P hliesN]
    have hliesN' : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.LiesOver p.asIdeal := by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      refine ⟨?_⟩
      rw [Ideal.under_under]
      exact hPlies.over
    have he_N : (P.under (NumberField.RingOfIntegers ↥N)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) = 1 := hpBadN _ hliesN'
    have hfrobN : NK.Chebotarev.IsFrobAt (K := k) (L := ↥N)
        (P.under (NumberField.RingOfIntegers ↥N))
        (SSGRoute.res k N τ) := by
      have h := NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := k) (E := ↥N) (M := ↥L) P
        (SSGRoute.res k L τ) hPfrob
      have hcompat := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥N ↥L (F := k) (K₃ := Ω) τ
      have hres : AlgEquiv.restrictNormalHom ↥N (SSGRoute.res k L τ) =
          AlgEquiv.restrictNormalHom ↥N τ := hcompat.symm
      rw [show SSGRoute.res k N τ = AlgEquiv.restrictNormalHom ↥N τ from rfl, ← hres]
      exact h
    have hdec : Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
        (P.under (NumberField.RingOfIntegers ↥N)) = ⊥ := by
      rw [NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt (K := k) (N := ↥N)
        (P.under (NumberField.RingOfIntegers ↥N)) (SSGRoute.res k N τ) he_N hfrobN, hτ]
      exact Subgroup.zpowers_one_eq_bot
    have hbridgeN := map_res_decomp_eq_stabilizer_valuationRing (k := k) (Ω := Ω) N B hBne
      (P.under (NumberField.RingOfIntegers ↥N)) hBN
    have hstab : MulAction.stabilizer (↥N ≃ₐ[k] ↥N)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N
          (P.under (NumberField.RingOfIntegers ↥N))) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      rw [Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup,
        hdec] at hx
      exact hx
    rw [SSGRoute.IsSplitIn]
    intro δ hδ
    rw [← IntermediateField.restrictNormalHom_ker N, MonoidHom.mem_ker]
    have hmem : SSGRoute.res k N δ ∈ (SSGRoute.decomp k B).map (SSGRoute.res k N) :=
      Subgroup.mem_map_of_mem _ hδ
    rw [hbridgeN, hstab] at hmem
    simpa using hmem
  · -- the prescribed Frobenius clause
    have hbridge := map_res_decomp_eq_stabilizer_valuationRing (k := k) (Ω := Ω) L B hBne P hBcomap
    have hgstab : SSGRoute.res k L τ ∈ MulAction.stabilizer (↥L ≃ₐ[k] ↥L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P) := by
      rw [Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup]
      rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup_iff_smul]
      exact NK.Chebotarev.IsFrobAtStabilizes hPfrob
    rw [← hbridge] at hgstab
    obtain ⟨σ, hσmem, hσres⟩ := hgstab
    exact ⟨σ, hσmem, hσres⟩

/-- **The escape prime with a prescribed Frobenius, at the prime of `↥K` below it.**  Given the
orthogonality hypothesis `hαfix` (`α` fixes `M ⊓ N` pointwise) and a finite set `Bad` of places of
`Ω`, there is a finite place `Q` of `Ω` avoiding the `G_k`-conjugates of `Bad`, completely split in
`N` over `k`, lying over a prime `𝔮` of `𝓞 ↥K` at which `α` is the arithmetic Frobenius of the
extension `↥M/↥K`, and such that some `σ ∈ decomp k Q` acts as `α` on `M`. -/
theorem escapePrimeFrobAtPrime
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (Bad : Finset (ValuationSubring Ω))
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hαfix : ∀ x : ↥M, ((x : Ω) ∈ N) → ((α x : ↥M) : Ω) = (x : Ω)) :
    ∃ (Q : ValuationSubring Ω) (𝔮 : NK.Chebotarev.PrimeIdeal ↥K),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ C ∈ Bad, ¬ SSGRoute.IsConjPlace k C Q) ∧
      Q.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      (∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k Q ∧
        ∀ x : ↥M, σ (x : Ω) = ((α x : ↥M) : Ω)) ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔮 α := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  -- ### Step 1: a finite Galois level `L/k` and `τ ∈ G_k` with `τ|_N = 1`, `τ|_M = α`
  obtain ⟨L, hLd, hLg, τ, hKL, hMLk, hNL, hτN, hτM⟩ :=
    galoisLevel_and_tau_of_orthogonality K M N hKN α hαfix
  haveI : FiniteDimensional k L := hLd
  haveI : IsGalois k L := hLg
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ### Step 2: Čebotarev over `k` at the level `L`, exposing the `L`-prime `P`
  obtain ⟨Q, P, hQfin, hQavoid, _hQunr, hQsplit, hQP, hPFrob, σ, hσdec, hσres⟩ :=
    chebotarev_frobenius_split_withPrime k Ω hc L N hNL Bad τ hτN
  -- ### Step 3: the tower `k ⊆ ↥K ⊆ ↥M ⊆ ↥L` of algebra structures
  letI : Algebra ↥K ↥L := (Subsemiring.inclusion hKL).toAlgebra
  letI : Algebra ↥M ↥L := (Subsemiring.inclusion hMLk).toAlgebra
  haveI htowKL : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI htowML : IsScalarTower k ↥M ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI htowKML : IsScalarTower ↥K ↥M ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hfdML : FiniteDimensional ↥M ↥L := by
    haveI : Module.Finite ↥M ↥L := Module.Finite.of_restrictScalars_finite k ↥M ↥L
    exact ‹Module.Finite ↥M ↥L›
  haveI hfdKL : FiniteDimensional ↥K ↥L := by
    haveI : Module.Finite ↥K ↥L := Module.Finite.of_restrictScalars_finite k ↥K ↥L
    exact ‹Module.Finite ↥K ↥L›
  haveI hgalKL : IsGalois ↥K ↥L := IsGalois.tower_top_of_isGalois k ↥K ↥L
  -- `τ` fixes `N`, hence `K`
  have hτNfix : ∀ x ∈ (N : Set Ω), τ x = x := by
    intro x hx
    have hmem : τ ∈ N.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker N]
      simpa [SSGRoute.res] using hτN
    exact (IntermediateField.mem_fixingSubgroup_iff N τ).mp hmem x hx
  have hfix : ∀ x : ↥K, (SSGRoute.res k L τ) (algebraMap ↥K ↥L x) = algebraMap ↥K ↥L x := by
    intro x
    refine Subtype.ext ?_
    rw [SSGRoute.res, AlgEquiv.restrictNormalHom_apply]
    exact hτNfix x (hKN x.2)
  have hagr : ∀ x : ↥M, (SSGRoute.res k L τ) (algebraMap ↥M ↥L x) = algebraMap ↥M ↥L (α x) := by
    intro x
    refine Subtype.ext ?_
    rw [SSGRoute.res, AlgEquiv.restrictNormalHom_apply]
    exact hτM x
  -- ### Step 4: the `↥K`-prime `𝔮` below `P`
  have hlies : P.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers ↥K)).asIdeal :=
    Ideal.LiesOver.mk (IsDedekindDomain.HeightOneSpectrum.under_asIdeal
      (NumberField.RingOfIntegers ↥K) P)
  have hQK : Q.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
        (P.under (NumberField.RingOfIntegers ↥K)) := by
    have h1 : (Q.comap (algebraMap ↥L Ω)).comap (algebraMap ↥K ↥L) =
        Q.comap (algebraMap ↥K Ω) := by
      rw [ValuationSubring.comap_comap]
      congr 1
    rw [← h1, hQP]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime (K := ↥K) (L := ↥L)
      (P.under (NumberField.RingOfIntegers ↥K)) P hlies
  refine ⟨Q, P.under (NumberField.RingOfIntegers ↥K), hQfin, hQsplit, hQavoid, hQK, ?_, ?_⟩
  · -- ### the `σ`-clause
    refine ⟨σ, hσdec, fun x => ?_⟩
    have hxM : (x : Ω) ∈ (M.restrictScalars k : Set Ω) := by
      rw [IntermediateField.coe_restrictScalars]; exact x.2
    have hxL : (x : Ω) ∈ L := hMLk hxM
    have h1 : σ (x : Ω) = τ (x : Ω) := by
      have h : ((AlgEquiv.restrictNormalHom ↥L σ) ⟨(x : Ω), hxL⟩ : Ω) =
          ((AlgEquiv.restrictNormalHom ↥L τ) ⟨(x : Ω), hxL⟩ : Ω) :=
        congrArg (fun (f : ↥L ≃ₐ[k] ↥L) => (((f ⟨(x : Ω), hxL⟩) : ↥L) : Ω)) hσres
      rwa [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply] at h
    rw [h1]
    exact hτM x
  · -- ### the Frobenius clause
    refine ⟨P.under (NumberField.RingOfIntegers ↥M), ?_, ?_⟩
    · refine Ideal.LiesOver.mk ?_
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
        IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    · exact isFrobAt_under_of_isFrobAt_of_fixes (k := k) (K := ↥K) (M := ↥M) (L := ↥L)
        P α (SSGRoute.res k L τ) hPFrob hfix hagr

end Work.SSGRoute.EscapeCoreLib
