import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.EuclideanStageDefs
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.localClass_union_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# From the `L`-groups to the homology of the complements

For a compact set `K ⊆ ℝ^N` the connecting map of the pair `(ℝ^N, Kᶜ)` relates the "local
homology" `LK N K = H_N(ℝ^N, ℝ^N∖K)` to `H_{N-1}(Kᶜ)`, naturally in `K`.  This file records

* `complMap_eq_inclChainsSub` — the stage map `complMap` is the homology map of the inclusion of
  chain complexes;
* `lkMap_complMap_square` — the naturality square `complMap T S ∘ δ_{T} = δ_{S} ∘ Λ` relating the
  connecting maps to the stage map `lkMap`;
* `stage_split_of_lkMap_ge_two` — the case `N ≥ 2` of the transport of a stage splitting from the
  `L`-groups to the complements.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology
noncomputable section
variable {N : ℕ}

/-- Transport of a homology module along an equality of degrees. -/
noncomputable def homCast {M : ℕ → ModuleCat ℤ} {a b : ℕ} (h : a = b) : ↥(M a) ≃ₗ[ℤ] ↥(M b) := by
  subst h
  exact LinearEquiv.refl ℤ ↥(M a)

/-- The degree-cast commutes with degreewise maps. -/
theorem homCast_natural {M N : ℕ → ModuleCat ℤ} (φ : ∀ n, M n ⟶ N n) {a b : ℕ} (h : a = b) :
    (homCast (M := N) h).toLinearMap.comp (φ a).hom
      = ((φ b).hom).comp (homCast (M := M) h).toLinearMap := by
  cases h
  ext x
  simp [homCast]

/-- `complMap` is the homology map of the inclusion of chain complexes. -/
theorem complMap_eq_inclChainsSub {T S : Set (EuclideanSpace ℝ (Fin N))} (h : S ⊆ T) :
    complMap T S h = (HomologicalComplex.homologyMap
      (inclChainsSub (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (Set.compl S)
        (Set.compl_subset_compl.mpr h)) (N - 1)).hom := by
  unfold complMap
  congr 2

/-- `lkMap` is the homology map of the bundle map `relCokerMap`. -/
theorem lkMap_eq_relCokerMap {K K' : Set (EuclideanSpace ℝ (Fin N))} (h : K ⊆ K') :
    lkMap (N := N) h = (HomologicalComplex.homologyMap (relCokerMap
      (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl K') (Set.compl K)
        (fun y hy hyK => hy (h hyK))) N).hom := rfl

/-- `relCokerMap` only depends on the underlying function of the inclusion. -/
theorem relCokerMap_congr_proofs {X : TopCat} {A B : Set X} (h h' : A ⊆ B) :
    relCokerMap X A B h = relCokerMap X A B h' := by
  have hEq : h = h' := funext fun x => funext fun hx => Subsingleton.elim _ _
  subst hEq
  rfl

/-- **The naturality square**: the connecting maps of the pairs turn the stage map into the map on
complements. -/
theorem lkMap_complMap_square {T S : Set (EuclideanSpace ℝ (Fin N))} (h : S ⊆ T) :
    (complMap T S h).comp (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (N-1)).hom
      = ((hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S) (N-1)).hom).comp
        ((HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
          (Set.compl T) (Set.compl S) (Set.compl_subset_compl.mpr h)) (N-1+1)).hom) := by
  have hnat := hPairδ_naturality (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
    (A := Set.compl T) (A' := Set.compl S) (Set.compl_subset_compl.mpr h) (N-1)
  have hh := congrArg ModuleCat.Hom.hom hnat
  simp only [ModuleCat.hom_comp] at hh
  rw [complMap_eq_inclChainsSub]
  exact hh

/-- The connecting map of the pair `(ℝ^N, Tᶜ)` is an isomorphism for `N ≥ 2`. -/
theorem hPairδ_compl_isIso {T : Set (EuclideanSpace ℝ (Fin N))} (hN : 2 ≤ N) :
    IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (N - 1)) := by
  refine hPairδ_isIso _ _ (N - 1) ?_ ?_
  · rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
    exact homologyContractible N (by omega)
  · exact homologyContractible (N - 1) (by omega)

/-- **Transport of the stage splitting from the `L`-groups to the complements** (case `N ≥ 2`). -/
theorem stage_split_of_lkMap_ge_two {N : ℕ} (hN : 2 ≤ N) {T S : Set (EuclideanSpace ℝ (Fin N))}
    (h : S ⊆ T) (hL : ∃ s : LK N S →ₗ[ℤ] LK N T, s.comp (lkMap (N := N) h) = LinearMap.id) :
    ∃ s : ↥((singularChains ℤ (TopCat.of (Set.compl S))).homology (N - 1)) →ₗ[ℤ]
        ↥((singularChains ℤ (TopCat.of (Set.compl T))).homology (N - 1)),
      s.comp (complMap T S h) = LinearMap.id := by
  classical
  obtain ⟨sL, hsL⟩ := hL
  have iT : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (N-1)) :=
    hPairδ_compl_isIso (T := T) hN
  have iS : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S) (N-1)) :=
    hPairδ_compl_isIso (T := S) hN
  set δT : ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T)).homology (N-1+1)) →ₗ[ℤ]
      ↥((singularChains ℤ (TopCat.of (Set.compl T))).homology (N-1)) :=
    (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (N-1)).hom with hδTdef
  set δS : ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S)).homology (N-1+1)) →ₗ[ℤ]
      ↥((singularChains ℤ (TopCat.of (Set.compl S))).homology (N-1)) :=
    (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S) (N-1)).hom with hδSdef
  set δSi : ↥((singularChains ℤ (TopCat.of (Set.compl S))).homology (N-1)) →ₗ[ℤ]
      ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S)).homology (N-1+1)) :=
    (inv (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S) (N-1))).hom with hδSidef
  set δTi : ↥((singularChains ℤ (TopCat.of (Set.compl T))).homology (N-1)) →ₗ[ℤ]
      ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T)).homology (N-1+1)) :=
    (inv (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (N-1))).hom with hδTidef
  set Λ' : ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T)).homology (N-1+1)) →ₗ[ℤ]
      ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S)).homology (N-1+1)) :=
    (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
      (Set.compl T) (Set.compl S) (Set.compl_subset_compl.mpr h)) (N-1+1)).hom with hΛ'def
  set cT := homCast (M := fun n => (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
      (Set.compl T)).homology n) (by omega : N = N - 1 + 1) with hcTdef
  set cS := homCast (M := fun n => (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
      (Set.compl S)).homology n) (by omega : N = N - 1 + 1) with hcSdef
  have hδSi_δS : ∀ x, δSi (δS x) = x := by
    intro x
    have h1 := IsIso.hom_inv_id (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl S) (N-1))
    have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
      at h2
    rw [hδSdef, hδSidef]
    exact h2
  have hδT_δTi : ∀ x, δT (δTi x) = x := by
    intro x
    have h1 := IsIso.inv_hom_id (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Set.compl T) (N-1))
    have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
      at h2
    rw [hδTdef, hδTidef]
    exact h2
  have hsquare : (complMap T S h).comp δT = δS.comp Λ' := by
    rw [hδTdef, hδSdef, hΛ'def]
    exact lkMap_complMap_square (N := N) h
  have hcompl_apply : ∀ b, complMap T S h b = δS (Λ' (δTi b)) := by
    intro b
    have h1 : complMap T S h (δT (δTi b)) = δS (Λ' (δTi b)) := by
      have h := LinearMap.congr_fun hsquare (δTi b)
      simpa only [LinearMap.comp_apply] using h
    rwa [hδT_δTi] at h1
  have hcast : cS.toLinearMap.comp (lkMap (N := N) h) = Λ'.comp cT.toLinearMap := by
    rw [hcSdef, hcTdef, hΛ'def, lkMap_eq_relCokerMap]
    exact homCast_natural (M := fun n => (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        (Set.compl T)).homology n) (N := fun n => (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        (Set.compl S)).homology n)
      (fun n => HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
        (Set.compl T) (Set.compl S) (Set.compl_subset_compl.mpr h)) n)
      (by omega : N = N - 1 + 1)
  have hcast_apply : ∀ x, cS (lkMap (N := N) h x) = Λ' (cT x) := fun x => LinearMap.congr_fun hcast x
  have hsL_apply : ∀ x, sL (lkMap (N := N) h x) = x := fun x => LinearMap.congr_fun hsL x
  refine ⟨(δT.comp (cT.toLinearMap.comp sL)).comp (cS.symm.toLinearMap.comp δSi), ?_⟩
  apply LinearMap.ext
  intro b
  show δT (cT (sL (cS.symm (δSi (complMap T S h b))))) = b
  rw [hcompl_apply b, hδSi_δS]
  have h3 : cS.symm (Λ' (δTi b)) = lkMap (N := N) h (cT.symm (δTi b)) := by
    have h := hcast_apply (cT.symm (δTi b))
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h, LinearEquiv.symm_apply_apply]
  rw [h3]
  show δT (cT (sL (lkMap (N := N) h (cT.symm (δTi b))))) = b
  rw [hsL_apply, LinearEquiv.apply_symm_apply, hδT_δTi]

end
end Work.Cohomology
