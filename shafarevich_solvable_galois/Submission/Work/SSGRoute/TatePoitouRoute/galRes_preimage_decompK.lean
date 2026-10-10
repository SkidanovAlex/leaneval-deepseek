import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.decompK_restrict_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Preimage of the decomposition group under the restriction map

Let `k ⊆ K ⊆ L` be number fields with `K/k` and `L/K` Galois (note: `L/k` need **not** be
Galois), `w` a place of `K`, `q'` a finite place of `L` lying over `w`, and `N ≤ Gal(K/k)` a
subgroup.  The lemma says: every `x ∈ Gal(L/k)` whose restriction `x|_K` lies in the
decomposition group `D_w ≤ Gal(K/k)` can be written

`x = d * n`,  `d ∈ D_{q'}`,  `n ∈ N.comap galRes`.

In other words `galRes⁻¹(D_w) ⊆ D_{q'} · galRes⁻¹(N)`.

The argument is purely Galois-theoretic.  Set `w' = ofFinite q'`.  If `x|_K ∈ D_w` then
`x • w'` is a place of `L` over `w`, and since `L/K` is Galois, transitivity of the
`Gal(L/K)`-action on the places over `w` produces `ρ ∈ Gal(L/K)` with `ρ • (x • w') = w'`.
Then `d := ρ * x` (viewed in `Gal(L/k)` via `AlgEquiv.restrictScalars`) satisfies `d • w' = w'`,
i.e. `d ∈ D_{q'}`, and `d|_K = x|_K`, so `n := d⁻¹ * x` has trivial restriction, hence lies in
`galRes⁻¹(N)`.
-/

namespace Work.SSGRoute.TatePoitouRoute

theorem galRes_preimage_decompK (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional K L] [IsGalois K L] (N : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K) (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w) (x : L ≃ₐ[k] L) (hx : SSGRoute.PTExt.galRes k K L x ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w) : ∃ d ∈ SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q'), ∃ n ∈ N.comap (SSGRoute.PTExt.galRes k K L), d * n = x := by
  have hxw : SSGRoute.PTExt.galRes k K L x • w = w := MulAction.mem_stabilizer_iff.mp hx
  have hlies : NK.GlobalCFT.Place.LiesOver (x • (NK.GlobalCFT.Place.ofFinite q')) w := by
    have h2 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L) x
      (SSGRoute.PTExt.galRes k K L x) (fun y => AlgEquiv.restrictNormal_commutes x K y) hq'
    rw [hxw] at h2
    exact h2
  obtain ⟨ρ, hρ⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
    (K := K) (L := L) hlies hq'
  have hsmul : ∀ y : NK.GlobalCFT.Place L, (AlgEquiv.restrictScalars k ρ) • y = ρ • y :=
    fun y => rfl
  have hgal1 : SSGRoute.PTExt.galRes k K L (AlgEquiv.restrictScalars k ρ) = 1 := by
    ext y
    simp only [AlgEquiv.one_apply]
    apply (algebraMap K L).injective
    have hχ : SSGRoute.PTExt.galRes k K L (AlgEquiv.restrictScalars k ρ)
        = (AlgEquiv.restrictScalars k ρ).restrictNormal K := rfl
    rw [hχ, AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
    exact ρ.commutes y
  set d : L ≃ₐ[k] L := (AlgEquiv.restrictScalars k ρ) * x with hd
  have hdmem : d ∈ SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q') := by
    rw [MulAction.mem_stabilizer_iff]
    show ((AlgEquiv.restrictScalars k ρ) * x) • (NK.GlobalCFT.Place.ofFinite q') = _
    rw [mul_smul, hsmul (x • (NK.GlobalCFT.Place.ofFinite q')), hρ]
  have hdgal : SSGRoute.PTExt.galRes k K L d = SSGRoute.PTExt.galRes k K L x := by
    rw [hd, map_mul, hgal1, one_mul]
  refine ⟨d, hdmem, d⁻¹ * x, ?_, ?_⟩
  · rw [Subgroup.mem_comap]
    have h2 : SSGRoute.PTExt.galRes k K L (d⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hdgal, inv_mul_cancel]
    rw [h2]
    exact N.one_mem
  · rw [mul_inv_cancel_left]

end Work.SSGRoute.TatePoitouRoute
