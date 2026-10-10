import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.SSGRoute.ges_escape_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace Work.SSGRoute

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## Auxiliary lemmas for `finiteIndex_integralIdeles_powTIdeles`

The subgroup `powTIdeles K p T ⊓ integralIdeles K` is, inside the integral idèles, the
simultaneous preimage of the local `p`-th power subgroups at the (finitely many) primes of `T`.
The local hypotheses `hloc` say that each of these local subgroups has finite index in the local
units, so the global subgroup has finite index, whence the relative index is non-zero.
-/

/-- The archimedean places are always in `powAtPlaces` (the defining condition is vacuous
there). -/
theorem mem_powAtPlaces_of_not_isFinite {T : Finset (NK.Chebotarev.PrimeIdeal K)}
    {v : NK.GlobalCFT.Place K} (hv : ¬ NK.GlobalCFT.Place.IsFinite v) :
    v ∈ powAtPlaces K T := by
  rcases v with w | q
  · intro 𝔭 h
    exact absurd h (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w 𝔭).symm
  · exact absurd (NK.GlobalCFT.Place.isFinite_ofFinite q) hv

/-- The evaluation of an integral idèle at a fixed finite prime, as a group homomorphism. -/
def evalLocal (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    NK.GlobalCFT.Idele.integralIdeles K →*
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭) where
  toFun x := ⟨x.1 (NK.GlobalCFT.Place.ofFinite 𝔭),
      (NK.GlobalCFT.Idele.mem_integralIdeles.mp x.2) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.GlobalCFT.Place.isFinite_ofFinite 𝔭)⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl

@[simp] theorem evalLocal_apply (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) (x : NK.GlobalCFT.Idele.integralIdeles K) :
    ((evalLocal K 𝔭 x : NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭)) :
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ) =
      x.1 (NK.GlobalCFT.Place.ofFinite 𝔭) := rfl

/-- `evalLocal` is surjective: an integral idèle can be prescribed at a single finite prime
(put `1` everywhere else). -/
theorem evalLocal_surjective (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) : Function.Surjective (evalLocal K 𝔭) := by
  classical
  intro u
  set f : ∀ v : NK.GlobalCFT.Place K, (NK.GlobalCFT.Place.localField K v)ˣ :=
    Function.update (fun _ => 1) (NK.GlobalCFT.Place.ofFinite 𝔭)
      (u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ) with hf
  have hfsupp : {v : NK.GlobalCFT.Place K | f v ∉ NK.GlobalCFT.Place.localUnits K v} ⊆
      {NK.GlobalCFT.Place.ofFinite 𝔭} := by
    intro v hv
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hv (by rw [hf, Function.update_of_ne hne]; exact Subgroup.one_mem _)
  have hfmem : ∀ᶠ v in Filter.cofinite, f v ∈ NK.GlobalCFT.Place.localUnits K v := by
    rw [Filter.eventually_cofinite]
    exact Set.Finite.subset (Set.finite_singleton _) hfsupp
  refine ⟨⟨(⟨f, hfmem⟩ : NK.GlobalCFT.Idele K), ?_⟩, ?_⟩
  · intro v _
    show f v ∈ NK.GlobalCFT.Place.localUnits K v
    rw [hf]
    by_cases hv : v = NK.GlobalCFT.Place.ofFinite 𝔭
    · rw [hv, Function.update_self]
      exact u.2
    · rw [Function.update_of_ne hv]
      exact Subgroup.one_mem _
  · apply Subtype.ext
    show f (NK.GlobalCFT.Place.ofFinite 𝔭) =
      (u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ)
    rw [hf, Function.update_self]

/-- The subgroup of the integral idèles whose `𝔭`-component is a local `p`-th power. -/
def localPowComap (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (𝔭 : NK.Chebotarev.PrimeIdeal K) : Subgroup (NK.GlobalCFT.Idele.integralIdeles K) :=
  ((NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p).subgroupOf
    (NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭))).comap (evalLocal K 𝔭)

theorem mem_localPowComap {p : ℕ} {𝔭 : NK.Chebotarev.PrimeIdeal K}
    {x : NK.GlobalCFT.Idele.integralIdeles K} :
    x ∈ localPowComap K p 𝔭 ↔
      x.1 (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p : Set _) := by
  rw [localPowComap, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact Iff.rfl

/-- The index of `localPowComap K p 𝔭` in the integral idèles equals the local index, because
`evalLocal K 𝔭` is surjective. -/
theorem index_localPowComap (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    (localPowComap K p 𝔭).index =
      ((NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p).subgroupOf
        (NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭))).index := by
  rw [localPowComap]
  exact Subgroup.index_comap_of_surjective _ (evalLocal_surjective K 𝔭)

/-- Finiteness of the local index transfers to `localPowComap`. -/
theorem localPowComap_finiteIndex (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (h : ((NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p).subgroupOf
      (NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭))).FiniteIndex) :
    (localPowComap K p 𝔭).FiniteIndex :=
  Subgroup.finiteIndex_iff.mpr (by
    rw [index_localPowComap]
    exact Subgroup.finiteIndex_iff.mp h)

/-- `powTIdeles` inside the integral idèles is the intersection of the `localPowComap`s. -/
theorem subgroupOf_powTIdeles_eq_iInf (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    (powTIdeles K p T).subgroupOf (NK.GlobalCFT.Idele.integralIdeles K) =
      ⨅ 𝔭 : T, localPowComap K p 𝔭.1 := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_powTIdeles, Subgroup.mem_iInf]
  constructor
  · intro h 𝔭
    rw [mem_localPowComap]
    exact h.1 𝔭.1 𝔭.2
  · intro h
    refine ⟨fun 𝔭 h𝔭 => ?_, fun v hv => ?_⟩
    · have hh := h ⟨𝔭, h𝔭⟩
      rw [mem_localPowComap] at hh
      exact hh
    · by_cases hv' : NK.GlobalCFT.Place.IsFinite v
      · exact (NK.GlobalCFT.Idele.mem_integralIdeles.mp x.2) v hv'
      · exact absurd (mem_powAtPlaces_of_not_isFinite (K := K) (T := T) hv') hv

theorem finiteIndex_integralIdeles_powTIdeles (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : Finset (NK.Chebotarev.PrimeIdeal K))
    (hloc : ∀ 𝔭 : T, ((NK.UchidaKummer.ellPowSubgroup (𝔭.1.adicCompletion K) p).subgroupOf
      (NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭.1))).FiniteIndex) :
    (Work.SSGRoute.powTIdeles K p T ⊓ NK.GlobalCFT.Idele.integralIdeles K).relIndex
      (NK.GlobalCFT.Idele.integralIdeles K) ≠ 0 := by
  haveI : (⨅ 𝔭 : T, localPowComap K p 𝔭.1).FiniteIndex :=
    Subgroup.finiteIndex_iInf fun 𝔭 => localPowComap_finiteIndex K p 𝔭.1 (hloc 𝔭)
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex, subgroupOf_powTIdeles_eq_iInf]
  exact Subgroup.FiniteIndex.index_ne_zero

end

end Work.SSGRoute
