import Mathlib
import Submission.Work.DSM5b.HCF.Complex

universe u

namespace Work.DSM5b.HCF

set_option linter.unusedSectionVars false

set_option allowUnsafeReducibility true in
attribute [local reducible] Work.DSM5b.chartCoeff

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

variable {R : Type u} [CommRing R] {ι ι' : Type u} [DecidableEq ι] [DecidableEq ι']

/-!
## Reindexing the chart coefficient system along an equivalence of the index types

Fix `e : ι ≃ ι'` and `t : ι' → R`, and write `t ∘ e : ι → R` for the reindexed family.  At a finset
`S : Finset ι`, the chart coefficient system `chartCoeff (t ∘ e)` on `ι` has value
`chartRing (t ∘ e) S`, while `chartCoeff t` on `ι'` has value `chartRing t (S.image e)`.  The first
part of this file compares the two, by transporting the ambient localisations (the identification
`tS (t ∘ e) S = tS t (S.image e)`) and matching the generators `t_i / t_j`, `i ↦ e i`; it shows
that the resulting `R`-algebra equivalence is compatible with the restriction maps `rhoH`.  The
second part uses it to reindex the honest tuple complexes.
-/

/-- Reindexing a product over the image of a finset: `tS (t ∘ e) S = tS t (S.image e)`. -/
lemma tS_comp_equiv (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    tS (fun i => t (e i)) S = tS t (S.image e) := by
  simp only [tS]
  exact (Finset.prod_image (f := t) (g := ⇑e) (s := S)
    (fun a _ b _ h => e.injective h)).symm

/-- The range of a reindexed tuple is the image of the range:
`tupRng (e ∘ τ) = (tupRng τ).image e`. -/
lemma tupRng_reindex (e : ι ≃ ι') {m : ℕ} (τ : Fin (m + 1) → ι) :
    (tupRng τ).image e = tupRng (e ∘ τ) := by
  simp only [tupRng]
  rw [Finset.image_image]

/-- The `R`-algebra map between the ambient localisations induced by the identification
`tS (t ∘ e) S = tS t (S.image e)`. -/
noncomputable def reindexLoc (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    Localization.Away (tS (fun i => t (e i)) S) →ₐ[R]
      Localization.Away (tS t (S.image e)) :=
  IsLocalization.Away.liftAlgHom (tS (fun i => t (e i)) S)
    (f := Algebra.ofId R (Localization.Away (tS t (S.image e)))) (by
      rw [tS_comp_equiv e t S]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (tS t (S.image e)))
        (tS t (S.image e)))

/-- The inverse `R`-algebra map between the ambient localisations. -/
noncomputable def reindexLocInv (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    Localization.Away (tS t (S.image e)) →ₐ[R]
      Localization.Away (tS (fun i => t (e i)) S) :=
  IsLocalization.Away.liftAlgHom (tS t (S.image e))
    (f := Algebra.ofId R (Localization.Away (tS (fun i => t (e i)) S))) (by
      rw [← tS_comp_equiv e t S]
      exact IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (tS (fun i => t (e i)) S)) (tS (fun i => t (e i)) S))

/-- Any two `R`-algebra maps out of a localisation agree, so the two ambient maps are mutually
inverse. -/
lemma reindexLocInv_comp_reindexLoc (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    (reindexLocInv e t S).comp (reindexLoc e t S) = AlgHom.id R _ :=
  (IsLocalization.algHom_subsingleton (Submonoid.powers (tS (fun i => t (e i)) S))).elim _ _

/-- Any two `R`-algebra maps out of a localisation agree, so the two ambient maps are mutually
inverse. -/
lemma reindexLoc_comp_reindexLocInv (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    (reindexLoc e t S).comp (reindexLocInv e t S) = AlgHom.id R _ :=
  (IsLocalization.algHom_subsingleton (Submonoid.powers (tS t (S.image e)))).elim _ _

/-- The forward ambient map carries the chart ring into the reindexed chart ring. -/
lemma reindexLoc_map_adjoin_le (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    Subalgebra.map (reindexLoc e t S) (chartRing (fun i => t (e i)) S)
      ≤ chartRing t (S.image e) := by
  rw [chartRing, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, hi, k, hk⟩ := hx
  refine Algebra.subset_adjoin ⟨e i, Finset.mem_image_of_mem e hi, e k, ?_⟩
  rw [← AlgHom.commutes (reindexLoc e t S) (t (e i)), ← map_mul, hk, AlgHom.commutes]

/-- The inverse ambient map carries the reindexed chart ring back into the chart ring. -/
lemma reindexLocInv_map_adjoin_le (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    Subalgebra.map (reindexLocInv e t S) (chartRing t (S.image e))
      ≤ chartRing (fun i => t (e i)) S := by
  rw [chartRing, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i', hi', k', hk'⟩ := hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hi'
  refine Algebra.subset_adjoin ⟨i, hi, e.symm k', ?_⟩
  rw [show (fun i : ι => t (e i)) (e.symm k') = t k' from by simp [Equiv.apply_symm_apply]]
  rw [← AlgHom.commutes (reindexLocInv e t S) (t (e i)), ← map_mul, hk', AlgHom.commutes]

/-- **The chart rings of the reindexed coefficient system.**  For `e : ι ≃ ι'`, `t : ι' → R` and
`S : Finset ι` there is an `R`-algebra equivalence
`chartRing (t ∘ e) S ≃ₐ[R] chartRing t (S.image e)`, induced by the comparison of the ambient
localisations and the matching of the generators `t_i / t_j` (`i ↦ e i`). -/
noncomputable def chartRing_reindex_algEquiv (e : ι ≃ ι') (t : ι' → R) (S : Finset ι) :
    ↥(chartRing (fun i => t (e i)) S) ≃ₐ[R] ↥(chartRing t (S.image e)) :=
  AlgEquiv.mk
    { toFun := fun x => ⟨reindexLoc e t S x.1, reindexLoc_map_adjoin_le e t S ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y =>
        ⟨reindexLocInv e t S y.1, reindexLocInv_map_adjoin_le e t S ⟨y.1, y.2, rfl⟩⟩
      left_inv := fun x =>
        Subtype.ext (DFunLike.congr_fun (reindexLocInv_comp_reindexLoc e t S) x.1)
      right_inv := fun y =>
        Subtype.ext (DFunLike.congr_fun (reindexLoc_comp_reindexLocInv e t S) y.1) }
    (fun x y => Subtype.ext (map_mul (reindexLoc e t S) x.1 y.1))
    (fun x y => Subtype.ext (map_add (reindexLoc e t S) x.1 y.1))
    (fun r => Subtype.ext (by
      show reindexLoc e t S ((algebraMap R ↥(chartRing (fun i => t (e i)) S)) r).1
        = (algebraMap R ↥(chartRing t (S.image e)) r : Localization.Away (tS t (S.image e)))
      rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
      exact AlgHom.commutes (reindexLoc e t S) r))

@[simp] lemma chartRing_reindex_algEquiv_apply (e : ι ≃ ι') (t : ι' → R) (S : Finset ι)
    (x : ↥(chartRing (fun i => t (e i)) S)) :
    ((chartRing_reindex_algEquiv e t S x : ↥(chartRing t (S.image e))) :
        Localization.Away (tS t (S.image e))) = reindexLoc e t S x.1 := rfl

/-- **Naturality of the reindexing of the chart rings for the restriction maps.** -/
theorem chartRing_reindex_rhoH (e : ι ≃ ι') (t : ι' → R) {S T : Finset ι} (h : S ⊆ T)
    (x : ↥(chartRing (fun i => t (e i)) S)) :
    chartRing_reindex_algEquiv e t T (rhoH (fun i => t (e i)) h x)
      = rhoH t (Finset.image_subset_image (f := ⇑e) h) (chartRing_reindex_algEquiv e t S x) := by
  apply Subtype.ext
  have h2 : (reindexLoc e t T).comp (locRes (fun i => t (e i)) h)
      = (locRes t (Finset.image_subset_image (f := ⇑e) h)).comp (reindexLoc e t S) :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers (tS (fun i => t (e i)) S))).elim _ _
  exact congrArg (fun φ => φ x.1) h2

/-- Restriction maps depend on the inclusions only through the source and the target, also when
those are identified by the transport of chart rings. -/
lemma rhoH_le_rhoH (t : ι → R) {S S' T T' : Finset ι} (hS : S = S') (hT : T = T')
    (h : S ⊆ T) (h' : S' ⊆ T') (x : ↥(chartRing t S)) :
    rhoH t (le_of_eq hT) (rhoH t h x) = rhoH t h' (rhoH t (le_of_eq hS) x) :=
  (HCd_rhoH_comp h (le_of_eq hT) x).trans
    ((HCd_rhoH_congr x).trans (HCd_rhoH_comp (le_of_eq hS) h' x).symm)

/-- The restriction map along a self-inclusion is the identity. -/
lemma rhoH_rfl (t : ι → R) (S : Finset ι) (x : ↥(chartRing t S)) :
    rhoH t (le_rfl : S ⊆ S) x = x :=
  Subtype.ext (DFunLike.congr_fun (locRes_eq t (le_rfl : S ⊆ S) (AlgHom.id R _)) x.1).symm

/-- Transport of chart rings along an equality of finsets, realised by the restriction maps (rather
than by `Eq.rec`), so that all computations stay within the proof-irrelevant `rhoH` calculus. -/
noncomputable def chartRingCast (t : ι → R) {S T : Finset ι} (h : S = T) :
    ↥(chartRing t S) ≃ₗ[R] ↥(chartRing t T) where
  toFun x := rhoH t (le_of_eq h) x
  map_add' x y := map_add _ x y
  map_smul' c x := map_smul _ c x
  invFun y := rhoH t (le_of_eq h.symm) y
  left_inv x := by
    show rhoH t (le_of_eq h.symm) (rhoH t (le_of_eq h) x) = x
    rw [HCd_rhoH_comp]
    exact (HCd_rhoH_congr x).trans (rhoH_rfl t S x)
  right_inv y := by
    show rhoH t (le_of_eq h) (rhoH t (le_of_eq h.symm) y) = y
    rw [HCd_rhoH_comp]
    exact (HCd_rhoH_congr y).trans (rhoH_rfl t T y)

@[simp] lemma chartRingCast_apply (t : ι → R) {S T : Finset ι} (h : S = T)
    (x : ↥(chartRing t S)) : chartRingCast t h x = rhoH t (le_of_eq h) x := rfl

@[simp] lemma chartRingCast_symm_apply (t : ι → R) {S T : Finset ι} (h : S = T)
    (x : ↥(chartRing t T)) : (chartRingCast t h).symm x = rhoH t (le_of_eq h.symm) x := rfl

/-!
## The tuple-level reindexing of the honest complex
-/

/-- The equivalence of tuples induced by `e`: `τ ↦ e ∘ τ`. -/
abbrev tupleEquiv (e : ι ≃ ι') (m : ℕ) : (Fin (m + 1) → ι) ≃ (Fin (m + 1) → ι') where
  toFun τ := e ∘ τ
  invFun σ := e.symm ∘ σ
  left_inv τ := funext fun x => by simp [Function.comp_apply]
  right_inv σ := funext fun x => by simp [Function.comp_apply]

@[simp] lemma tupleEquiv_apply (e : ι ≃ ι') (m : ℕ) (τ : Fin (m + 1) → ι) :
    tupleEquiv e m τ = e ∘ τ := rfl

@[simp] lemma tupleEquiv_symm_apply (e : ι ≃ ι') (m : ℕ) (σ : Fin (m + 1) → ι') :
    (tupleEquiv e m).symm σ = e.symm ∘ σ := rfl

/-- The fibrewise reindexing of the chart rings at a tuple `τ`. -/
noncomputable def reindexFibre (e : ι ≃ ι') (t : ι' → R) {m : ℕ} (τ : Fin (m + 1) → ι) :
    ↥(chartRing (fun i => t (e i)) (tupRng τ)) ≃ₗ[R] ↥(chartRing t (tupRng (e ∘ τ))) :=
  (chartRing_reindex_algEquiv e t (tupRng τ)).toLinearEquiv.trans
    (chartRingCast t (tupRng_reindex e τ))

@[simp] lemma reindexFibre_apply (e : ι ≃ ι') (t : ι' → R) {m : ℕ} (τ : Fin (m + 1) → ι)
    (x : ↥(chartRing (fun i => t (e i)) (tupRng τ))) :
    reindexFibre e t τ x
      = chartRingCast t (tupRng_reindex e τ) (chartRing_reindex_algEquiv e t (tupRng τ) x) := by
  rw [reindexFibre, LinearEquiv.trans_apply]
  rfl

lemma reindexFibre_symm_apply (e : ι ≃ ι') (t : ι' → R) {m : ℕ} (τ : Fin (m + 1) → ι)
    (y : ↥(chartRing t (tupRng (e ∘ τ)))) :
    (reindexFibre e t τ).symm y
      = (chartRing_reindex_algEquiv e t (tupRng τ)).symm
          (rhoH t (le_of_eq (tupRng_reindex e τ).symm) y) := by
  rw [reindexFibre, LinearEquiv.symm_trans_apply, chartRingCast_symm_apply]
  rfl

/-- **The fibrewise reindexing is a morphism of coefficient systems** in the sense that it
intertwines the restriction maps of `chartCoeff (t ∘ e)` and `chartCoeff t` with the transports of
the ranges of tuples. -/
lemma reindexFibre_symm_rhoH (e : ι ≃ ι') (t : ι' → R) {m : ℕ} (τ : Fin (m + 2) → ι)
    (i : Fin (m + 2)) (y : ↥(chartRing t (tupRng (e ∘ tupDel i τ)))) :
    rhoH (fun i => t (e i)) (tupRng_del_subset i τ) ((reindexFibre e t (tupDel i τ)).symm y)
      = (reindexFibre e t τ).symm (rhoH t (tupRng_del_subset i (e ∘ τ)) y) := by
  apply (chartRing_reindex_algEquiv e t (tupRng τ)).injective
  rw [reindexFibre_symm_apply, chartRing_reindex_rhoH, AlgEquiv.apply_symm_apply]
  rw [reindexFibre_symm_apply, AlgEquiv.apply_symm_apply]
  exact (rhoH_le_rhoH t (tupRng_reindex e (tupDel i τ)).symm (tupRng_reindex e τ).symm
    (tupRng_del_subset i (e ∘ τ))
    (Finset.image_subset_image (f := ⇑e) (tupRng_del_subset i τ)) y).symm

/-- **The reindexing of the terms of the honest tuple complex**: the product over the tuples in `ι`
is identified with the product over the tuples in `ι'` by `τ ↦ e ∘ τ`, and the values by the
fibrewise reindexing `reindexFibre`. -/
noncomputable def reindexTerm (e : ι ≃ ι') (t : ι' → R) (m : ℕ) :
    (∀ σ : Fin (m + 1) → ι', ↥(chartRing t (tupRng σ))) ≃ₗ[R]
      (∀ τ : Fin (m + 1) → ι, ↥(chartRing (fun i => t (e i)) (tupRng τ))) :=
  (LinearEquiv.piCongrLeft R (fun σ : Fin (m + 1) → ι' => ↥(chartRing t (tupRng σ)))
      (tupleEquiv e m)).symm.trans
    (LinearEquiv.piCongrRight (fun τ : Fin (m + 1) → ι => (reindexFibre e t τ).symm))

lemma reindexTerm_apply (e : ι ≃ ι') (t : ι' → R) (m : ℕ)
    (w : ∀ σ : Fin (m + 1) → ι', ↥(chartRing t (tupRng σ))) (τ : Fin (m + 1) → ι) :
    reindexTerm e t m w τ = (reindexFibre e t τ).symm (w (e ∘ τ)) := by
  have h1 : (LinearEquiv.piCongrLeft R (fun σ : Fin (m + 1) → ι' => ↥(chartRing t (tupRng σ)))
      (tupleEquiv e m)).symm w τ = w (e ∘ τ) := by
    show (LinearEquiv.piCongrLeft' R (fun σ : Fin (m + 1) → ι' => ↥(chartRing t (tupRng σ)))
      (tupleEquiv e m).symm) w τ = w (e ∘ τ)
    rw [LinearEquiv.piCongrLeft'_apply]
    simp only [Equiv.symm_symm]
    rfl
  rw [reindexTerm, LinearEquiv.trans_apply]
  trans (reindexFibre e t τ).symm
      ((LinearEquiv.piCongrLeft R (fun σ : Fin (m + 1) → ι' => ↥(chartRing t (tupRng σ)))
        (tupleEquiv e m)).symm w τ)
  · exact LinearEquiv.piCongrRight_apply _ _ τ
  · rw [h1]

/-- **The reindexing of the terms commutes with the honest differentials.** -/
theorem reindexTerm_htcD (e : ι ≃ ι') (t : ι' → R) (m : ℕ) :
    ((chartCoeff (fun i => t (e i))).htcD m).comp (reindexTerm e t m).toLinearMap
      = (reindexTerm e t (m + 1)).toLinearMap.comp ((chartCoeff t).htcD m) := by
  apply LinearMap.ext; intro w
  funext τ
  show (chartCoeff (fun i => t (e i))).htcD m ((reindexTerm e t m) w) τ
      = (reindexTerm e t (m + 1)) ((chartCoeff t).htcD m w) τ
  rw [reindexTerm_apply, CoeffSys.htcD_apply, CoeffSys.htcD_apply]
  show (∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) • rhoH (fun i => t (e i)) (tupRng_del_subset i τ)
        ((reindexFibre e t (tupDel i τ)).symm (w (e ∘ tupDel i τ))))
      = (reindexFibre e t τ).symm (∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) •
          rhoH t (tupRng_del_subset i (e ∘ τ)) (w (tupDel i (e ∘ τ))))
  have hsum : (reindexFibre e t τ).symm
        (∑ i : Fin (m + 2),
          (-1 : R) ^ (i : ℕ) • rhoH t (tupRng_del_subset i (e ∘ τ)) (w (tupDel i (e ∘ τ))))
      = ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) •
          (reindexFibre e t τ).symm
            (rhoH t (tupRng_del_subset i (e ∘ τ)) (w (tupDel i (e ∘ τ)))) := by
    change ((reindexFibre e t τ).symm.toLinearMap)
        (∑ i : Fin (m + 2),
          (-1 : R) ^ (i : ℕ) • rhoH t (tupRng_del_subset i (e ∘ τ)) (w (tupDel i (e ∘ τ))))
      = ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) •
          (reindexFibre e t τ).symm
            (rhoH t (tupRng_del_subset i (e ∘ τ)) (w (tupDel i (e ∘ τ))))
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearEquiv.map_smul (reindexFibre e t τ).symm _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z => (-1 : R) ^ (i : ℕ) • z)
    (reindexFibre_symm_rhoH e t τ i (w (e ∘ tupDel i τ)))

/-- **Reindexing the honest chart Čech complex along an equivalence of the index types.**  For an
equivalence `e : ι ≃ ι'` and a family `t : ι' → R`, the honest tuple complexes of the systems
`Work.DSM5b.chartCoeff (fun i => t (e i))` (on `ι`) and `Work.DSM5b.chartCoeff t` (on `ι'`) are
isomorphic, by reindexing every tuple `τ : Fin (m+1) → ι` to `e ∘ τ`.  Route: `e` induces a linear
equivalence `chartRing (fun i => t (e i)) S ≃ₗ[R] chartRing t (S.image e)` on the coefficients
(`tS (fun i => t (e i)) S = tS t (S.image e)`, and `chartGens`/`locRes` match under `i ↦ e i`),
these fit into an isomorphism of coefficient systems, and induce a linear isomorphism
`Htc (chartCoeff (fun i => t (e i))) m ≃ₗ[R] Htc (chartCoeff t) m` commuting with the differentials
(`tupRng (e ∘ τ) = (tupRng τ).image e`), i.e. an isomorphism of the complexes.  Note that
`Work.DSM5b.CoeffSys.Hom`/`htcHom` are indexed by a *fixed* `ι`, so the isomorphism has to be built
directly. -/
theorem htcComplex_reindex {ι ι' : Type u} [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι')
    (R : Type u) [CommRing R] (t : ι' → R) :
    Nonempty ((Work.DSM5b.htcComplex (Work.DSM5b.chartCoeff (fun i => t (e i)))) ≅
      (Work.DSM5b.htcComplex (Work.DSM5b.chartCoeff t))) := by
  classical
  refine ⟨(HomologicalComplex.Hom.isoOfComponents (fun m => ?_) ?_).symm⟩
  · exact LinearEquiv.toModuleIso (reindexTerm e t m)
  · intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    rw [LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_hom]
    rw [htcComplex_d, htcComplex_d]
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    rw [reindexTerm_htcD]

end Work.DSM5b.HCF
