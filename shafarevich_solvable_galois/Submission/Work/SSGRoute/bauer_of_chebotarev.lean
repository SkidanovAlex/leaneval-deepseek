import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.Reconstruct.eq_of_splitPrimes_eq
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Bauer's theorem from Chebotarev (over any number field k ⊆ ℚ̄-like closure)

If almost every prime of k that splits completely in N also splits completely in M (M, N Galois over k),
then M ⊆ N.

**Sketch.** Suppose M ⊄ N. Let L be the Galois closure over ℚ of MN and σ ∈ Gal(L/MN·…) with σ|_N = 1,
σ|_M ≠ 1; this σ lies in Gal(L/k).
- Chebotarev over ℚ: `NK.NUV2.chebotarev_all0 NK.CFTLib.fundamentalClassElement : NK.NUV2.ChebAll0`, which
  unfolds to `NK.Reconstruct.ChebotarevInput ℚ K'` for a separable closure K'. It gives a prime P of L,
  unramified, with Frob_P = σ.
- Then D_P(L/k) = ⟨σ⟩, so P ∩ k splits in N but not in M.
- Avoid the finite exceptional set with `NK.Reconstruct.dense_frobeniusSet_of_chebotarev`, or by
  replacing L with L·(an auxiliary field ramified at the finitely many bad primes) and σ with (σ, τ),
  τ ≠ 1.
- Translate P to a place A of Ω (a valuation subring extending the localisation at P). Then D_A maps onto
  D_P, and `IsSplitIn k N A` ⇔ `D_A ≤ G_N` ⇔ the image of D_A in Gal(N/k) is trivial.

**Imports.** Interfaces, `Submission.NK.NUV2.chebotarev_all0`, `Submission.NK.CFTLib.fundamentalClassElement`,
`Submission.NK.Reconstruct.Basic`.
-/

namespace Work.SSGRoute

open SSGRoute

/-! ## The density argument

The completely split primes of a finite Galois extension `N/K` have Dirichlet density
`1 / [N : K]`; changing a set of primes by a *finite* set does not change its Dirichlet density.
Hence if all but finitely many primes splitting completely in `N` also split completely in `M`,
then the compositum `N ⊔ M` has the same completely split primes as `N` up to a finite set, so the
two densities agree and `[N ⊔ M : K] = [N : K]`, i.e. `M ≤ N`. -/

/-- **Bauer's theorem, density form.**  If every prime of `K` outside a finite set `Bad` that
splits completely in `N` also splits completely in `M`, then `M ≤ N`. -/
theorem le_of_splitPrimesSet_off_finite {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (M N : IntermediateField K Ω) [FiniteDimensional K M] [Normal K M]
    [FiniteDimensional K N] [Normal K N]
    (Bad : Set (NK.Chebotarev.PrimeIdeal K)) (hBad : Bad.Finite)
    (h : ∀ p : NK.Chebotarev.PrimeIdeal K, p ∉ Bad →
      p ∈ NK.Reconstruct.splitPrimesSet K ↥N → p ∈ NK.Reconstruct.splitPrimesSet K ↥M) :
    M ≤ N := by
  haveI : NumberField ↥(N ⊔ M) := inferInstance
  haveI : IsGalois K ↥N := inferInstance
  haveI : IsGalois K ↥(N ⊔ M) := inferInstance
  set SN : Set (NK.Chebotarev.PrimeIdeal K) := NK.Reconstruct.splitPrimesSet K ↥N with hSN
  set SE : Set (NK.Chebotarev.PrimeIdeal K) := NK.Reconstruct.splitPrimesSet K ↥(N ⊔ M) with hSE
  -- every completely split prime of the compositum is already completely split in `N`
  have hSEle : SE ⊆ SN :=
    NK.Reconstruct.splitPrimesSet_sup_le (K := K) (K' := Ω) (L := N) (M := M)
  -- ... and conversely off the finite set `Bad`
  have hdiff : (SN \ SE ∪ SE \ SN).Finite := by
    refine hBad.subset ?_
    rintro p (hp | hp)
    · rw [Set.mem_diff] at hp
      by_contra hpB
      have hpM : p ∈ NK.Reconstruct.splitPrimesSet K ↥M := h p hpB hp.1
      exact hp.2 (NK.Reconstruct.splitPrimesSet_subset_sup (K := K) (K' := Ω) (L := N) (M := M)
        hp.1 hpM)
    · rw [Set.mem_sdiff] at hp
      exact absurd (hSEle hp.1) hp.2
  -- density of the completely split primes of `N` ...
  have hdN : NumberField.Set.HasDirichletDensity SN (1 / (Module.finrank K ↥N : ℝ)) :=
    NK.Reconstruct.hasDirichletDensity_splitPrimesSet K ↥N
  -- ... of the compositum ...
  have hdE : NumberField.Set.HasDirichletDensity SE (1 / (Module.finrank K ↥(N ⊔ M) : ℝ)) :=
    NK.Reconstruct.hasDirichletDensity_splitPrimesSet K ↥(N ⊔ M)
  -- ... and, by insensitivity to finite modifications, of the compositum again at the density of `N`
  have hdE' : NumberField.Set.HasDirichletDensity SE (1 / (Module.finrank K ↥N : ℝ)) :=
    NK.Chebotarev.HasDirichletDensitySensitivity hdiff hdN
  have hlim : (1 : ℝ) / (Module.finrank K ↥(N ⊔ M) : ℝ) = 1 / (Module.finrank K ↥N : ℝ) :=
    tendsto_nhds_unique hdE hdE'
  have hfin : Module.finrank K ↥N = Module.finrank K ↥(N ⊔ M) := by
    have h2 : (Module.finrank K ↥(N ⊔ M) : ℝ) = (Module.finrank K ↥N : ℝ) :=
      inv_inj.mp (by simpa using hlim)
    exact_mod_cast h2.symm
  have hEq : N = N ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hfin
  intro x hx
  rw [hEq]
  exact SetLike.le_def.mp le_sup_right hx

/-! ## The bridge: places of `Ω` over primes of `k`

A finite place `A` of `Ω` lies over a prime `p` of `k`, and `A` splits completely in a Galois
extension `N/k` exactly when `p` does: both are equivalent to the decomposition group being
trivial, i.e. to `#(primes of `𝓞 N` above `p`) = [N : k]`
(`NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely`). -/

/-- Every prime of `k` outside the finite set `S` which splits completely in `N` splits completely
in `M`, as a statement about prime ideals rather than about places of `Ω`. -/
theorem splitPrimesSet_of_placeHypothesis {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (M N : IntermediateField k Ω) [FiniteDimensional k M]
    [Normal k M] [FiniteDimensional k N] [Normal k N] [NumberField ↥M] [NumberField ↥N]
    (S : Finset (ValuationSubring k))
    (h : ∀ A : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) ∉ S → _root_.SSGRoute.IsSplitIn k N A →
        _root_.SSGRoute.IsSplitIn k M A) :
    ∀ p : NK.Chebotarev.PrimeIdeal k,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p ∉ S →
      p ∈ NK.Reconstruct.splitPrimesSet k ↥N →
      p ∈ NK.Reconstruct.splitPrimesSet k ↥M := by
  intro p hpS hpN
  -- a place of `Ω` above `p`
  obtain ⟨A, hA⟩ := Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
    (K := k) (K' := Ω) p
  have hkey := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
    (K := k) (K' := Ω) (N := N) p A hA
  have hsplitN : _root_.SSGRoute.IsSplitIn k N A := hkey.mpr hpN
  have hmemS : A.comap (algebraMap k Ω) ∉ S := by rw [hA]; exact hpS
  have hAne : A.comap (algebraMap k Ω) ≠ ⊤ := by
    rw [hA]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) p
  have hkeyM := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
    (K := k) (K' := Ω) (N := M) p A hA
  have hsplitM : _root_.SSGRoute.IsSplitIn k M A := h A hAne hmemS hsplitN
  exact hkeyM.mp hsplitM

theorem bauer_of_chebotarev (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (M N : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring k))
    (h : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) ∉ S → SSGRoute.IsSplitIn k N A → SSGRoute.IsSplitIn k M A) :
    M ≤ N := by
  haveI : IsSepClosure k Ω := inferInstance
  haveI : NumberField ↥M := inferInstance
  haveI : NumberField ↥N := inferInstance
  -- the finite set of primes of `k` belonging to `S`
  set Bad : Set (NK.Chebotarev.PrimeIdeal k) :=
    {p | IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p ∈ S} with hBad
  have hBadFin : Bad.Finite := by
    refine Set.Finite.of_finite_image
      (f := fun p => IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p) ?_ ?_
    · refine S.finite_toSet.subset ?_
      rintro x ⟨p, hp, rfl⟩
      rw [hBad] at hp
      exact hp
    · intro p _ q _ hpq
      exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hpq
  have hbridge := splitPrimesSet_of_placeHypothesis (k := k) (Ω := Ω) M N S h
  refine le_of_splitPrimesSet_off_finite (K := k) (Ω := Ω) M N Bad hBadFin ?_
  intro p hpBad hpN
  refine hbridge p ?_ hpN
  intro hpS
  exact hpBad (by simpa [hBad] using hpS)

end Work.SSGRoute
