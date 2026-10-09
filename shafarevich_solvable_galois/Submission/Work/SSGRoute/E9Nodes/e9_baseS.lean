import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
import Submission.Work.LocalFields.unramifiedAt_iff_inertia_eq_bot
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9Nodes

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1000000

section Bridge

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]

/-- `IsInertiaAt q σ` is exactly membership of `σ` in the ideal-theoretic inertia subgroup of the
finite prime `q` inside `Gal(K/k)`. -/
lemma isInertiaAt_iff_mem_inertia
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : K ≃ₐ[k] K) :
    SSGRoute.PTExt.IsInertiaAt q σ ↔ σ ∈ Ideal.inertia (K ≃ₐ[k] K) q.asIdeal := by
  have h : σ ∈ Ideal.inertia (K ≃ₐ[k] K) q.asIdeal ↔
      ∀ x : NumberField.RingOfIntegers K, σ • x - x ∈ q.asIdeal := by
    change σ ∈ q.asIdeal.toAddSubgroup.inertia (K ≃ₐ[k] K) ↔
      ∀ x : NumberField.RingOfIntegers K, σ • x - x ∈ q.asIdeal
    rw [AddSubgroup.mem_inertia]
    exact forall_congr' fun x => Submodule.mem_toAddSubgroup q.asIdeal
  rw [h]
  unfold SSGRoute.PTExt.IsInertiaAt
  refine forall_congr' fun x => ?_
  have key : ((σ • x - x : NumberField.RingOfIntegers K) : K) = σ (x : K) - (x : K) := by
    have h : algebraMap (NumberField.RingOfIntegers K) K (σ • x - x) =
        algebraMap (NumberField.RingOfIntegers K) K (σ • x) -
          algebraMap (NumberField.RingOfIntegers K) K x := map_sub _ _ _
    rw [show ((σ • x - x : NumberField.RingOfIntegers K) : K) =
        algebraMap (NumberField.RingOfIntegers K) K (σ • x - x) from rfl, h]
    congr 1
  rw [← key]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (v := q) _

end Bridge

/-- **The base place set of E9a.**  There is a finite set `S` of places of `K` containing every
archimedean place, every place above `p` and every place where `M` ramifies (i.e. outside `S`, no
element of the inertia group acts nontrivially on `M`).  Concretely `S` can be taken to consist of
the archimedean places, the primes over `(p)`, and the prime divisors of the discriminant of `K`
(which contain the ramified primes of `K/k`).  Existing ingredients:
`Work.SSGRoute.dvd_discr_of_isRamifiedIn`, `Work.SSGRoute.finite_ramified_primes_extension`,
`Work.SSGRoute.ramifiedPlaces_finite`. -/
theorem e9_baseS (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] :
    ∃ S : Finset (NK.GlobalCFT.Place K),
      (∀ v : NK.GlobalCFT.Place K,
        (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.GlobalCFT.Place.ofFinite q ∉ S →
          (p : NumberField.RingOfIntegers K) ∉ q.asIdeal ∧
          ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) := by
  classical
  -- finiteness of the primes of `K` ramified over `k`
  have hram : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} : Set _).Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := k) (L := K)
  -- finiteness of the primes of `K` above `p`
  have hp0 : (p : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hoverp : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal} : Set _).Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(p : NumberField.RingOfIntegers K)}) ?_).subset ?_
    · intro hs
      exact hp0 (Ideal.span_singleton_eq_bot.mp hs)
    · intro q hq
      change q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)}
      rw [Ideal.dvd_iff_le, Ideal.span_le]
      exact Set.singleton_subset_iff.mpr hq
  refine ⟨Finset.univ.image NK.GlobalCFT.Place.ofInfinite ∪
      (hram.toFinset ∪ hoverp.toFinset).image NK.GlobalCFT.Place.ofFinite, ?_, ?_⟩
  · intro v hv
    cases v with
    | inl w => exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
    | inr q => exact absurd rfl (hv q)
  · intro q hq
    have hqram : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
      by_contra hne
      exact hq (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_union_left _ ((hram.mem_toFinset).mpr hne))))
    have hqp : (p : NumberField.RingOfIntegers K) ∉ q.asIdeal := by
      intro hmem
      exact hq (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_union_right _ ((hoverp.mem_toFinset).mpr hmem))))
    refine ⟨hqp, ?_⟩
    intro σ hσ m
    have hbot : Ideal.inertia (K ≃ₐ[k] K) q.asIdeal = ⊥ :=
      (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
        (q.asIdeal.under (NumberField.RingOfIntegers k)) q.asIdeal).mpr hqram
    have hmem : σ ∈ Ideal.inertia (K ≃ₐ[k] K) q.asIdeal :=
      (isInertiaAt_iff_mem_inertia (k := k) (K := K) q σ).mp hσ
    rw [hbot] at hmem
    have hσ1 : σ = 1 := Subgroup.mem_bot.mp hmem
    rw [hσ1, map_one]
    rfl

end Work.SSGRoute.E9Nodes
