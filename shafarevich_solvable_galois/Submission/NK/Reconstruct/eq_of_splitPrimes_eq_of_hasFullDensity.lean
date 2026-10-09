import Mathlib
import Submission.NK.Reconstruct.denseChebotarev
import Submission.NK.Reconstruct.eq_of_splitPrimes_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The completely split primes determine a finite normal subextension, on a set of full density

`NK.Reconstruct.eq_of_splitPrimes_eq` shows that two finite normal number-field subextensions
`L, M ⊆ K'` of a Galois extension `K'/K` are equal as soon as the sets of primes of `K` splitting
completely in `L` and in `M` agree *everywhere*.

Here we prove the sharper statement in which the agreement is only required on a set `R` of primes
of full Dirichlet density (`Rᶜ` has density `0`) — the form in which the hypothesis arises from
Chebotarev's density theorem.  The proof is the same density argument, with one extra ingredient:
the Dirichlet density is *subtractive* on a set difference `S \ T` with `T ⊆ S`
(`NK.Reconstruct.hasDirichletDensity_sdiff`), so

* `S_L \ S_{L ⊔ M}` is contained in `Rᶜ` (a prime of `R` splitting completely in `L` also splits
  completely in `M`, hence in `L ⊔ M`), so it has density `0`;
* its density is also `1/[L : K] - 1/[L ⊔ M : K]`, which is positive unless `L = L ⊔ M`.

Hence `M ≤ L`; symmetrically `L ≤ M`, and the two fields coincide.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open Filter IsDedekindDomain Topology Set in
/-- **Subtractivity of the Dirichlet density.**  If `T ⊆ S` are sets of primes of a number field
with Dirichlet densities `ε` and `δ`, then the difference `S \ T` has Dirichlet density `δ - ε`.

The proof is the additivity of the prime ideal zeta sum over the disjoint union
`S = T ∪ (S \ T)`: the ratio functions therefore satisfy
`ζ(S \ T, s)/ζ(s) = ζ(S, s)/ζ(s) - ζ(T, s)/ζ(s)`, and the claim follows by taking the limit
along `𝓝[>] 1`.  (When the underlying series does not converge, both sides are the junk value `0`.) -/
theorem hasDirichletDensity_sdiff {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hTS : T ⊆ S) {δ ε : ℝ} (hS : NumberField.Set.HasDirichletDensity S δ)
    (hT : NumberField.Set.HasDirichletDensity T ε) :
    NumberField.Set.HasDirichletDensity (S \ T) (δ - ε) := by
  have key : ∀ s : ℝ, NumberField.Set.primeIdealZetaSum (S \ T) s /
      NumberField.Set.primeIdealZetaSum (univ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) s =
      NumberField.Set.primeIdealZetaSum S s / NumberField.Set.primeIdealZetaSum
        (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s -
      NumberField.Set.primeIdealZetaSum T s / NumberField.Set.primeIdealZetaSum
        (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s := by
    intro s
    by_cases hU : Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
    · have hTs : Summable (fun 𝔭 : T => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
        hU.subtype (· ∈ T)
      have hDs : Summable (fun 𝔭 : ↥(S \ T) => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
        hU.subtype (· ∈ S \ T)
      have h1 := Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint
        (S := T) (T := S \ T) disjoint_sdiff_self_right s hTs hDs
      have hu : T ∪ (S \ T) = S := by
        rw [Set.union_comm, Set.sdiff_union_of_subset hTS]
      rw [hu] at h1
      rw [h1, add_div]
      ring
    · have hU0 : NumberField.Set.primeIdealZetaSum
          (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s = 0 := by
        rw [NumberField.Set.primeIdealZetaSum_def,
          tsum_subtype (univ : Set (IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K)))
            (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
              (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)),
          Set.indicator_univ]
        exact tsum_eq_zero_of_not_summable hU
      rw [hU0, div_zero, div_zero, div_zero, sub_zero]
  unfold NumberField.Set.HasDirichletDensity at hS hT ⊢
  exact Tendsto.congr' (Eventually.of_forall fun s => (key s).symm) (hS.sub hT)

/-- **The completely split primes on a set of full density determine the subextension.**  Let
`L, M ⊆ K'` be finite normal number-field subextensions of a Galois extension `K'/K` and let `R` be a
set of primes of `K` of full Dirichlet density.  If every prime of `R` splitting completely in `L`
also splits completely in `M`, then `M ≤ L`.

Indeed, if `L ⊊ L ⊔ M` then `S_L \ S_{L ⊔ M}` is contained in the complement of `R` — a prime of `R`
splitting completely in `L` also splits completely in `M`, hence in the compositum — so it has
density `0`; but by subtractivity its density is `1/[L : K] - 1/[L ⊔ M : K] > 0`, a contradiction. -/
theorem le_of_splitPrimesSet_inter_subset {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsGalois K K']
    {L M : IntermediateField K K'} [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    {R : Set (NK.Chebotarev.PrimeIdeal K)} (hR : HasFullDensity K R)
    (h : splitPrimesSet K ↥L ∩ R ⊆ splitPrimesSet K ↥M) :
    M ≤ L := by
  classical
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : NumberField ↥(L ⊔ M) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L ⊔ M)
  haveI hGalN : IsGalois K ↥(L ⊔ M) := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hsub : splitPrimesSet K ↥(L ⊔ M) ⊆ splitPrimesSet K ↥L :=
    splitPrimesSet_sup_le (L := L) (M := M)
  have hdiff : splitPrimesSet K ↥L \ splitPrimesSet K ↥(L ⊔ M) ⊆ Rᶜ := by
    intro p hp
    simp only [Set.mem_compl_iff]
    intro hpR
    exact hp.2 (splitPrimesSet_subset_sup (L := L) (M := M) hp.1 (h ⟨hp.1, hpR⟩))
  have hzero : NumberField.Set.HasDirichletDensity
      (splitPrimesSet K ↥L \ splitPrimesSet K ↥(L ⊔ M)) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset hR hdiff
  have hd := hasDirichletDensity_sdiff hsub
    (hasDirichletDensity_splitPrimesSet K ↥L)
    (hasDirichletDensity_splitPrimesSet K ↥(L ⊔ M))
  have hEq := tendsto_nhds_unique hzero hd
  have hfin : Module.finrank K ↥L = Module.finrank K ↥(L ⊔ M) := by
    have h1 : (1 : ℝ) / (Module.finrank K ↥L : ℝ) = 1 / (Module.finrank K ↥(L ⊔ M) : ℝ) :=
      sub_eq_zero.mp hEq.symm
    rw [one_div, one_div] at h1
    exact_mod_cast (inv_inj.mp h1)
  have hLN : L = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hfin
  rw [hLN]
  exact le_sup_right

theorem eq_of_splitPrimes_eq_of_hasFullDensity {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsGalois K K'] {L M : IntermediateField K K'}
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    {R : Set (NK.Chebotarev.PrimeIdeal K)} (hR : NK.Reconstruct.HasFullDensity K R)
    (h : ∀ p : NK.Chebotarev.PrimeIdeal K, p ∈ R →
      ((∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ↔
        (∃ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver p.asIdeal ∧
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1))) :
    L = M := by
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- on `R` the split prime sets of `L` and `M` agree
  have hset : splitPrimesSet K ↥L ∩ R = splitPrimesSet K ↥M ∩ R := by
    ext p
    constructor
    · rintro ⟨hpL, hpR⟩
      exact ⟨(splitsCompletely_iff_ncard K ↥M p).mp
        ((h p hpR).mp ((splitsCompletely_iff_ncard K ↥L p).mpr hpL)), hpR⟩
    · rintro ⟨hpM, hpR⟩
      exact ⟨(splitsCompletely_iff_ncard K ↥L p).mp
        ((h p hpR).mpr ((splitsCompletely_iff_ncard K ↥M p).mpr hpM)), hpR⟩
  have hMleL : M ≤ L :=
    le_of_splitPrimesSet_inter_subset hR ((le_of_eq hset).trans Set.inter_subset_left)
  have hLleM : L ≤ M :=
    le_of_splitPrimesSet_inter_subset (L := M) (M := L) hR
      ((le_of_eq hset.symm).trans Set.inter_subset_left)
  exact le_antisymm hLleM hMleL

end NK.Reconstruct
