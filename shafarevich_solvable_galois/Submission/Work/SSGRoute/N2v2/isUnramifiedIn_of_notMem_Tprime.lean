import Mathlib
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The abelian class field of `gesUPow` is unramified outside `T'`

The target of this file is the input `hunr`/`hMunr` of the orthogonality lanes: for an abelian
extension `M / ↥K` whose idèlic norm class subgroup is `gesUPow ↥K p T' = gesU ↾K ⊔ (p-th powers)`,
every prime `𝔮 ∉ T'` is unramified in `M / ↥K`.

The mathematical content is the local–global dictionary of class field theory, in three steps.

1. **The one-place unit idèles lie in `powTIdeles`** (`onePlace_ofFinite_mem_powTIdeles`): the idèle
   which is a local unit `u` at `𝔮` and `1` elsewhere has `𝔮`-component `1` at every prime of `T'`
   (a `p`-th power) and is a local unit at every place not above `T'` (because `𝔮 ∉ T'`).

2. **Local units are local norms** (`onePlace_mem_localNormSubgroup_of_mem_normClassSubgroup`):
   from `hM` the class of such an idèle lies in `N_{M/↥K} C_M`, i.e. the idèle lies in
   `N_{M/↥K} 𝕀_M ⊔ ↥Kˣ`; Milne's local faithfulness at one place for abelian extensions
   (`Work.SSGRoute.ZDataMup.localFaithful_abelian`) upgrades this to membership in
   `N_{M/↥K} 𝕀_M`, which by the one-place dictionary
   (`NK.CFTLib.IdeleHasse.onePlace_ofFinite_mem_normImage_iff`) says exactly
   `u ∈ localNormSubgroup (ofFinite 𝔮)`.

3. **The ramification criterion** (`ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup`):
   if *all* local units of `K_𝔮` are local norms from `M`, then `𝔮` is unramified.  This is the
   classical norm-index computation: the valuation formula
   `Commons.NumberTheory.NumberField.Completion.NormIndexUnits.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux`
   writes `#(K_𝔮ˣ ⧸ N) = f · [U : U ∩ N]` with `U` the unit group and `f` the inertia degree; the
   hypothesis gives `[U : U ∩ N] = 1`, so `#(K_𝔮ˣ ⧸ N) = f`, while the local norm index theorem
   (`NK.LocalReciprocity.index_normGroup_eq_finrank`, in the abelian case) and
   `finrank = e · f` compute the same index as `e · f`; hence `e = 1`.

The only arithmetic inputs are Milne's local faithfulness at one place for abelian extensions
(which is the "one place omitted" form of Hilbert reciprocity) and the abelian local norm index
theorem; both are on disk and axiom-clean.
-/

namespace Work.SSGRoute.N2v2

open scoped NumberField
open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## The one-place idèle at a local unit is in `powTIdeles` -/

/-- **The idèle which is a local unit `u` at `𝔮` and `1` elsewhere lies in `powTIdeles`, provided
`𝔮 ∉ T'`.**

Its component at every prime `𝔭 ∈ T'` is `1` (since `𝔮 ≠ 𝔭`, because `𝔮 ∉ T'`), hence a `p`-th
power; and its component at a place `v` not above `T'` is `u` if `v` is the place of `𝔮` (a local
unit by hypothesis) and `1` otherwise. -/
theorem onePlace_ofFinite_mem_powTIdeles {K : Type} [Field K] [NumberField K] (p : ℕ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) (𝔮 : NK.Chebotarev.PrimeIdeal K) (h𝔮 : 𝔮 ∉ T')
    (u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔮))ˣ)
    (hu : u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮)) :
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u ∈
      Work.SSGRoute.powTIdeles K p T' := by
  rw [Work.SSGRoute.mem_powTIdeles]
  refine ⟨?_, ?_⟩
  · intro 𝔭 h𝔭
    have hne : NK.GlobalCFT.Place.ofFinite 𝔭 ≠ NK.GlobalCFT.Place.ofFinite 𝔮 := by
      intro h
      exact h𝔮 (NK.GlobalCFT.Place.ofFinite_inj.mp h ▸ h𝔭)
    rw [NK.HassePrinciple.onePlace_apply_ne hne]
    exact Subgroup.one_mem _
  · intro v hv
    by_cases hveq : v = NK.GlobalCFT.Place.ofFinite 𝔮
    · rw [hveq, NK.HassePrinciple.onePlace_apply_self]
      exact hu
    · rw [NK.HassePrinciple.onePlace_apply_ne hveq]
      exact Subgroup.one_mem _

/-! ## The general ramification criterion -/

/-- **The ramification criterion, in the abelian case, with no degree hypothesis.**

For a finite abelian extension `L / K` of number fields, a finite place `Q` of `K` at which *all*
local units are local norms is unramified in `L / K`.

The proof is the classical norm-index computation (as in
`NK.CFTLib.Existence.ramificationIdx_eq_one_of_localUnits_le_localNorm`, which is the special case
of cyclic prime degree): with `N ≤ K_Qˣ` the norm group and `U ≤ K_Qˣ` the group of local units,
the valuation formula gives `#(K_Qˣ ⧸ N) = f · [U : U ∩ N]`, which the hypothesis turns into
`#(K_Qˣ ⧸ N) = f`; on the other hand the local norm index theorem and `finrank = e · f` give
`#(K_Qˣ ⧸ N) = e · f`.  Hence `e · f = f` and `e = 1`. -/
theorem ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (Q : NK.Chebotarev.PrimeIdeal K)
    (h : NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q)) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
  intro q hq
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  haveI hq' : q.asIdeal.LiesOver Q.asIdeal := hq
  -- the norm group of the completion is the local norm subgroup
  have hN : (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)).range =
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) := by
    rw [← NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup Q q hq]
    rfl
  -- the local units are contained in the norm group
  have hUN : Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q ≤
      (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K)).range := by
    intro x hx
    rw [hN]
    apply h
    rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    exact (Commons.NumberTheory.NumberField.Completion.mem_adicUnitsVal K Q x).mp hx
  have hrel : (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)).range.relIndex
      (Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q) = 1 :=
    Subgroup.relIndex_eq_one.mpr hUN
  -- the valuation formula, `#(K_Qˣ ⧸ N) = f · [U : U ∩ N]`
  have h1 : Nat.card ((Q.adicCompletion K)ˣ ⧸ (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)).range) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) *
      (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K)).range.relIndex
        (Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q) :=
    Commons.NumberTheory.NumberField.Completion.NormIndexUnits.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux
      Q q hq
  have hval' : Nat.card ((Q.adicCompletion K)ˣ ⧸ (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)).range) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [h1, hrel, mul_one]
  -- the local Galois group is commutative (it is the decomposition subgroup, a subgroup of the
  -- commutative `Gal(L/K)`)
  have hcomm : ∀ a b : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      a * b = b * a := by
    intro a b
    let e := Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      (K := K) (L := L) Q q hq
    have hinner : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext (mul_comm' _ _)
    exact e.symm.injective (by rw [map_mul, map_mul]; exact hinner)
  -- the local norm index theorem and `finrank = e · f`
  have hidx : (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)).range.index =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
    rw [← NK.LocalReciprocity.normGroup_eq_range]
    exact NK.LocalReciprocity.index_normGroup_eq_finrank Q q hcomm
  have hcard : Nat.card ((Q.adicCompletion K)ˣ ⧸ (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)).range) =
      (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K)).range.index :=
    (Subgroup.index_eq_card _).symm
  have hef : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq
  have hef2 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [hef, ← hidx, ← hcard]
    exact hval'
  have hf : 0 < q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K)
  exact Nat.mul_right_cancel hf (by rw [hef2, one_mul])

/-! ## Local faithfulness of the abelian class-field correspondence at one place -/

/-- **A one-place idèle whose class lies in the norm class subgroup is a norm idèle.**

For a finite abelian extension `L / K` of number fields, the idèle which is `a` at the finite place
`Q` and `1` elsewhere, if its class in `C_K` lies in `N_{L/K} C_L = im(N_{L/K} 𝕀_L)`, already lies
in `N_{L/K} 𝕀_L`, i.e. `a ∈ localNormSubgroup K L (ofFinite Q)`.

This is the "one place omitted" form of Hilbert reciprocity, in Milne's formulation
(*CFT*, V.5.3(a)): writing `onePlace Q a = n · (x)` with `n` an idèle norm and `x ∈ Kˣ`, every
component of `(x)` away from `Q` is the inverse of a component of `n`, hence a local norm there, so
`x` is a local norm at `Q` as well; then `(x)` is an idèle norm and so is the product.  The
arithmetic input is packaged as `Work.SSGRoute.ZDataMup.localFaithful_abelian`. -/
theorem onePlace_mem_localNormSubgroup_of_mem_normClassSubgroup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (Q : NK.Chebotarev.PrimeIdeal K)
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ)
    (h : (NK.GlobalCFT.IdeleClassGroup.mk K)
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) a) ∈
      NK.GlobalCFT.Idele.normClassSubgroup K L) :
    a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) := by
  have hcomm : ∀ a b : (L ≃ₐ[K] L), a * b = b * a := fun a b => mul_comm' a b
  obtain ⟨n, hn, hmn⟩ := Subgroup.mem_map.mp h
  have h2 : n⁻¹ * NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) a ∈
      NK.GlobalCFT.Idele.principalSubgroup K :=
    (NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff).mp hmn
  have hsup : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K := by
    have hh := Subgroup.mul_mem_sup hn h2
    rwa [mul_inv_cancel_left] at hh
  exact (NK.CFTLib.IdeleHasse.onePlace_ofFinite_mem_normImage_iff (K := K) (L := L) Q a).mp
    (Work.SSGRoute.ZDataMup.localFaithful_abelian (K := K) (L := L) hcomm hsup)

/-- **The abelian class field of `gesUPow` is unramified outside `T'`.**

`gesU ↾K = im(Kˣ · E_{T',unr})` is generated by the principal idèles and by the idèles whose
`T'`-components are `p`-th powers and whose components at every other place are local units
(`Work.SSGRoute.powTIdeles`); `gesUPow ↾K = gesU ↾K ⊔ (p-th powers)`.  Hence an *abelian* extension
`M` whose norm class subgroup is `gesUPow` is unramified at every prime `𝔮 ∉ T'`: the idèle which is
a local unit `u` at `𝔮` and `1` elsewhere lies in `powTIdeles`, so its class lies in the norm class
subgroup `N_{M/↥K} C_M`, whence the Artin map of `M/↥K` kills it; local faithfulness of the
one-place idèles for abelian extensions turns this into `u ∈ localNormSubgroup (ofFinite 𝔮)`, i.e.
the local units at `𝔮` are norms, and the ramification criterion
`ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup` gives `ramificationIdx = 1`, i.e.
`IsUnramifiedIn`.

The abelianness hypothesis is necessary: `hM` alone only determines the maximal abelian
subextension of `M`, so a non-abelian `M` with the same norm group can be ramified outside `T'`
(e.g. `K = ℚ`, `T' = ∅`, `M` an `A₅`-field). -/
theorem isUnramifiedIn_of_notMem_Tprime (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M =
      Work.SSGRoute.SSG8Escape.gesUPow ↥K p T')
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥K) (h𝔮 : 𝔮 ∉ T') :
    NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 := by
  -- all local units at `𝔮` are local norms
  have hloc : NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
        (NK.GlobalCFT.Place.ofFinite 𝔮) := by
    intro u hu
    -- the one-place idèle at the local unit `u` lies in `powTIdeles`
    have hz : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u ∈
        Work.SSGRoute.powTIdeles ↥K p T' :=
      onePlace_ofFinite_mem_powTIdeles p T' 𝔮 h𝔮 u hu
    -- hence its class lies in `gesU ⊆ gesUPow = N_{M/↥K} C_M`
    have hzges : (NK.GlobalCFT.IdeleClassGroup.mk ↥K)
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u) ∈
        Work.SSGRoute.SSG8Escape.gesUPow ↥K p T' :=
      Work.SSGRoute.SSG8Escape.gesU_le_gesUPow ↥K p T'
        (Subgroup.mem_map.mpr ⟨_, Subgroup.mem_sup_right hz, rfl⟩)
    have hznc : (NK.GlobalCFT.IdeleClassGroup.mk ↥K)
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u) ∈
        NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M := by
      rw [hM]
      exact hzges
    -- local faithfulness upgrades this to membership in the local norm subgroup
    exact onePlace_mem_localNormSubgroup_of_mem_normClassSubgroup 𝔮 u hznc
  -- and the ramification criterion concludes
  exact ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup 𝔮 hloc

end Work.SSGRoute.N2v2
