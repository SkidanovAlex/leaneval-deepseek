import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.t0Generation_cyclic
import Submission.Work.SSGRoute.twistLayer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `T⁰`-places splitting completely and generating the graded piece `E(n,τ)`

Let `K/ℚ` be a finite Galois extension, `τ = (i,j)`, and let

* `ψ : G_ℚ →* Γ^{(n,τ+1)}` be a surjective homomorphism with open kernel, lifting
* `φ : G_ℚ →* Γ^{(n,τ)}`   (`SSGRoute.LiftsFlow ψ φ`).

This file produces a finite set `T⁰` of *finite* places of `ℚ̄` (Step 3 of Schmidt–Wingberg's
proof of Theorem 15, `Work.SSGRoute.exists_T0_generating_flowEKer` and
`Work.SSGRoute.t0Generation_cyclic_strong`) such that

* every place of `T⁰` is over a finite prime of `ℚ` (`SSGRoute.IsFinPlace ℚ A`);
* the decomposition groups `D_A` of the places of `T⁰` are killed by `φ`
  (equivalently, by `LiftsFlow`, the images `ψ(D_A)` lie in `flowEKer p (K ≃ₐ[ℚ] K) n i j = ker
  (Γ^{(n,τ+1)} →* Γ^{(n,τ)})`);
* the images `ψ(D_A)`, `A ∈ T⁰`, generate the graded piece
  `flowEKer p (K ≃ₐ[ℚ] K) n i j`;
* each `ψ(D_A)`, `A ∈ T⁰`, is cyclic.

The mathematics is Chebotarev's theorem in its finite form: for each element of the finite Galois
group `Gal(L/ℚ)` of the field `L` cut out by `ker ψ` there is a place of `ℚ̄` over a finite prime of
`ℚ` whose decomposition group maps onto the cyclic subgroup it generates
(`Work.SSGRoute.t0_placeDecompImage`).  The only difference from the existing generation lemmas is
that the *finiteness* of the places is retained (which the local conditions of Theorem 15 require),
so the construction of `Work.SSGRoute.t0Generation_cyclic_strong` is repeated here keeping the
first component of `t0_placeDecompImage`.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open _root_.SSGRoute

open scoped Pointwise

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-! ## Finiteness of the flow groups at the level of a finite group `G` -/

/-- The quotient `F(m)/F(m)^{(i,j)}` is finite when `G` is finite: `F(m)` is the free group on the
finite set `Fin m × G`, and `flowTerm p G m i j ⊇ pCentralSeries p F(m) i`, whose quotient is
finite (`Work.Shrinking.finite_freeGroup_quotient_pCentralSeries`). -/
theorem finite_flowQuotient_SSGRoute (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (flowQuotient p G m i j) := by
  haveI : Fintype (Fin m × G) := inferInstance
  have hmap : Subgroup.map (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G m)).toMonoidHom
      ((flowTerm p G m i j).subgroupOf ⊤) = flowTerm p G m i j := by
    change Subgroup.map (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).subtype
      ((flowTerm p G m i j).subgroupOf ⊤) = flowTerm p G m i j
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  haveI : (flowTerm p G m i j).Normal := inferInstance
  haveI : Finite (Work.Shrinking.freeOperatorGroup G m ⧸ flowTerm p G m i j) := by
    have hle : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) i
        ≤ flowTerm p G m i j := by
      rw [flowTerm, refinedTerm]; exact le_sup_right
    have hfin : Finite (Work.Shrinking.freeOperatorGroup G m ⧸
        Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) i) :=
      Work.Shrinking.finite_freeGroup_quotient_pCentralSeries p (Fin m × G) i
    have hsurj : Function.Surjective (QuotientGroup.map
        (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) i)
        (flowTerm p G m i j) (MonoidHom.id _) (by simpa using hle)) := fun y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (flowTerm p G m i j) y
      exact ⟨QuotientGroup.mk' _ x, by rw [QuotientGroup.map_mk']; rfl⟩
    exact hfin.of_surjective _ hsurj
  exact Finite.of_equiv _
    (QuotientGroup.congr ((flowTerm p G m i j).subgroupOf ⊤) (flowTerm p G m i j)
      (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G m)) hmap).symm.toEquiv

/-- The flow group `F(m)/F(m)^{(i,j)} ⋊ G` is finite when `G` is finite. -/
theorem finite_flowGroup_SSGRoute (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (flowGroup p G m i j) := by
  haveI : Finite (flowQuotient p G m i j) := finite_flowQuotient_SSGRoute p G m i j
  haveI : Finite (flowQuotient p G m i j × G) := inferInstance
  exact Finite.of_equiv _ (SemidirectProduct.equivProd.symm)

/-! ## `T⁰`-generation by *finite* places -/

/-- **The `T⁰`-generation of a subgroup of a finite quotient of `G_ℚ` by finite places, with
cyclic pieces.**

This is `Work.SSGRoute.t0Generation_cyclic_strong` with the additional clause that every place of
`T⁰` is a finite place.  The construction is the same; the only change is that the finiteness
component of `Work.SSGRoute.t0_placeDecompImage` (which `t0Generation_cyclic_strong` discards) is
kept. -/
theorem t0Generation_cyclic_fin_aux (Γ : Type*) [Group Γ] [Finite Γ] (ψ : SSGRoute.GalQ →* Γ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ)
    (H : Subgroup Γ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ T0, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ ≤ H) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = H ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) := by
  classical
  haveI hAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hclosed : IsClosed (ψ.ker : Set SSGRoute.GalQ) := Subgroup.isClosed_of_isOpen ψ.ker hopen
  let L : IntermediateField ℚ SSGRoute.QBar := IntermediateField.fixedField ψ.ker
  have hLfix : L.fixingSubgroup = ψ.ker := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := AlgebraicClosure ℚ)
      (⟨ψ.ker, hclosed⟩ : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    simpa [L] using h
  have hLfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite (k := ℚ) (K := AlgebraicClosure ℚ) L).mp (hLfix ▸ hopen)
  haveI hLfdI : FiniteDimensional ℚ L := hLfd
  haveI hLgal : IsGalois ℚ L :=
    IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := AlgebraicClosure ℚ) ψ.ker
      (hn := MonoidHom.normal_ker ψ)
  haveI hLnf : NumberField ↥L := inferInstance
  have hrker : (AlgEquiv.restrictNormalHom L).ker = ψ.ker := by
    rw [IntermediateField.restrictNormalHom_ker, hLfix]
  obtain ⟨ψbar, hψbar⟩ := t0_restrictLift L ψ hrker.symm
  let HL : Subgroup (↥L ≃ₐ[ℚ] ↥L) := (H.comap ψ).map (AlgEquiv.restrictNormalHom L)
  have hHmap : HL.map ψbar = H := by
    show Subgroup.map ψbar
        (Subgroup.map (AlgEquiv.restrictNormalHom L) (Subgroup.comap ψ H)) = H
    rw [Subgroup.map_map, hψbar, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hsurj, top_inf_eq]
  have hc : NK.Reconstruct.ChebotarevInput ℚ SSGRoute.QBar := by
    haveI : IsSepClosure ℚ SSGRoute.QBar := inferInstance
    exact (NK.ReconstructEndgame.chebotarevInput_congr ℚ SSGRoute.QBar).mpr
      ((NK.NUV2.chebotarev_all0 NK.CFTLib.fundamentalClassElement) ℚ SSGRoute.QBar)
  have key : ∀ σ : ↥HL, ∃ A : ValuationSubring SSGRoute.QBar,
      SSGRoute.IsFinPlace ℚ A ∧
      (SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom L) =
        Subgroup.zpowers (σ : ↥L ≃ₐ[ℚ] ↥L) :=
    fun σ => t0_placeDecompImage hc L (σ : ↥L ≃ₐ[ℚ] ↥L)
  let Afun : ↥HL → ValuationSubring SSGRoute.QBar := fun σ => Classical.choose (key σ)
  have hAfun : ∀ σ : ↥HL, (SSGRoute.decomp ℚ (Afun σ)).map (AlgEquiv.restrictNormalHom L) =
        Subgroup.zpowers (σ : ↥L ≃ₐ[ℚ] ↥L) := fun σ => (Classical.choose_spec (key σ)).2
  have hAne : ∀ σ : ↥HL, SSGRoute.IsFinPlace ℚ (Afun σ) :=
    fun σ => (Classical.choose_spec (key σ)).1
  have hval : ∀ σ : ↥HL, (SSGRoute.decomp ℚ (Afun σ)).map ψ =
      Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L)) := by
    intro σ
    rw [← hψbar, ← Subgroup.map_map, hAfun σ, t0_map_zpowers]
  refine ⟨Finset.univ.image Afun, ?_, ?_, ?_, ?_⟩
  · intro A' hA'
    rw [Finset.mem_image] at hA'
    obtain ⟨σ, -, rfl⟩ := hA'
    exact hAne σ
  · intro A' hA'
    rw [Finset.mem_image] at hA'
    obtain ⟨σ, -, rfl⟩ := hA'
    rw [hval σ]
    exact Subgroup.zpowers_le.mpr (hHmap ▸ Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩)
  · rw [← Finset.sup_eq_iSup, Finset.sup_image]
    show Finset.univ.sup (fun σ : ↥HL => (SSGRoute.decomp ℚ (Afun σ)).map ψ) = H
    have hsup_eq : (Finset.univ.sup (fun σ : ↥HL =>
        Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L)))) = H := by
      apply le_antisymm
      · apply Finset.sup_le
        intro σ _
        exact Subgroup.zpowers_le.mpr (hHmap ▸ Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩)
      · intro h hh
        rw [← hHmap, Subgroup.mem_map] at hh
        obtain ⟨σ, hσ, rfl⟩ := hh
        exact Finset.le_sup (f := fun σ : ↥HL =>
            Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L))) (Finset.mem_univ ⟨σ, hσ⟩)
          (Subgroup.mem_zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L)))
    rw [show (fun σ : ↥HL => (SSGRoute.decomp ℚ (Afun σ)).map ψ) =
        (fun σ : ↥HL => Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L))) from funext hval]
    exact hsup_eq
  · intro A' hA'
    rw [Finset.mem_image] at hA'
    obtain ⟨σ, -, rfl⟩ := hA'
    rw [hval σ]
    infer_instance

/-! ## The level projection on a lift -/

/-- An element of an intermediate group of the flow tower which lifts `x` has level projection `x`:
the converse of `Work.SSGRoute.liftsFlowAt_of_flowGroupProj_eq`, obtained by reading off the two
components of the semidirect product from the definition of `SSGRoute.LiftsFlowAt`. -/
theorem flowGroupProj_eq_of_liftsFlowAt_SSGRoute (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] {n i j : ℕ}
    {y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2}
    {x : flowGroup p (K ≃ₐ[ℚ] K) n i j} (h : SSGRoute.LiftsFlowAt y x) :
    flowGroupProj p (K ≃ₐ[ℚ] K) n i j y = x := by
  obtain ⟨hright, z, hz1, hz2⟩ := h
  have hy : flowGroupProj p (K ≃ₐ[ℚ] K) n i j y =
      SemidirectProduct.mk (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j) y.right := by
    rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupProj_mk, hz1,
      flowQuotientProj_coe]
  have hx : x = SemidirectProduct.mk (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j)
      x.right := by
    rw [show x = SemidirectProduct.mk x.left x.right from rfl, hz2]
  rw [hy, hx, hright]

/-! ## The target -/

theorem exists_T0_split_generating (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hLift : SSGRoute.LiftsFlow ψ φ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hsurj : Function.Surjective ψ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ T0, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ)
        = Work.SSGRoute.flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  haveI : Finite (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) :=
    finite_flowGroup_SSGRoute p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
  obtain ⟨T0, hfin, hle, hsup, hcyc⟩ :=
    t0Generation_cyclic_fin_aux (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
      ψ hopen hsurj (flowEKer p (K ≃ₐ[ℚ] K) n i j)
  refine ⟨T0, hfin, ?_, hsup, hcyc⟩
  intro A hA σ hσ
  have hmem : ψ σ ∈ flowEKer p (K ≃ₐ[ℚ] K) n i j :=
    hle A hA (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)
  have hproj : flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ) = φ σ :=
    flowGroupProj_eq_of_liftsFlowAt_SSGRoute p K (hLift σ)
  rw [← hproj]
  exact MonoidHom.mem_ker.mp hmem

end Work.SSGRoute
