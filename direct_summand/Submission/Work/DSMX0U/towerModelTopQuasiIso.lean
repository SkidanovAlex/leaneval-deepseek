import Mathlib
import Submission.Work.DSMX0U.towerModelTopSetup

/-!
# DSMX0U - the model map at the top degree: the quasi-isomorphism

This file completes the verification of `Work.DSMX0U.quasiIso_towerModelMap2` in the *top degree*
`M = levelDeg M 0 - 1`: the induced map on homology of `psiTop` is an isomorphism
(`phiHTop_surjective`, `phiHTop_injective`), hence `psiTop` is a quasi-isomorphism, and the arrow
of short complexes induced by `phi` is isomorphic to `psiTop`, which gives
`quasiIsoAt_towerModelMap_top`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

namespace TowerModelMapTop

/-! ## The induced map on homology is an isomorphism -/

/-- The map on homology is surjective: every class of `H^M(C)` is represented by a cycle, and
`Cell.hσ` of the base cell provides a generator of `G_0` whose image is that cycle up to a
boundary. -/
theorem phiHTop_surjective (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    Function.Surjective (phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0).hom := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (scCtop (C := C) M).moduleCatToCycles) q
  have hz : (C.d (levelDeg M 0 - 1) (M + 1)).hom z.1 = 0 := LinearMap.mem_ker.mp z.2
  obtain ⟨g, hg⟩ := (tower hstep M s₀ 0).hσ z.1 hz
  let w : ↥((tower hstep M s₀ 0).G A) :=
    ((g, 0) : ↥(tower hstep M s₀ 0).gen × ↥(tower hstep M s₀ 0).rel)
  have hw : w ∈ LinearMap.ker (scTtop hstep M s₀).g.hom := by
    rw [show (scTtop hstep M s₀).g.hom = 0 from rfl, LinearMap.ker_zero]
    exact Submodule.mem_top
  have hphi : (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 ⟨w, hw⟩).1 =
      (C.iCycles (levelDeg M 0 - 1)).hom ((tower hstep M s₀ 0).σ.hom g) := by
    rw [phiKTop_apply, psiTop_τ₂_apply]
    exact TowerMapQI.cell_φHom_pair_zero (A := A) (s := tower hstep M s₀ 0) g
  refine ⟨(hTtop (C := C) (c₀ := c₀) hstep M s₀).π ⟨w, hw⟩, ?_⟩
  rw [phiHTop_pi_apply, TowerMapQI.pi_eq_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  refine (TowerMapQI.mem_range_moduleCatToCycles_iff (scCtop (C := C) M) _).mpr ?_
  rw [Submodule.coe_sub, hphi]
  exact hg

/-- The map on homology is injective: if the image of a cycle of `G_0` is a boundary of `C`, then
that cycle lies in the excess kernel `Cell.K` of the base cell, which — because the differential of
the base cell is zero (`hd0`) — is exactly the range of `towerD 0`. -/
theorem phiHTop_injective (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    Function.Injective (phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0).hom := by
  intro a b hab
  obtain ⟨k₁, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (scTtop hstep M s₀).moduleCatToCycles) a
  obtain ⟨k₂, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (scTtop hstep M s₀).moduleCatToCycles) b
  rw [phiHTop_mk_apply, phiHTop_mk_apply] at hab
  have hmem : (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 k₁ -
      phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 k₂) ∈
      LinearMap.range (scCtop (C := C) M).moduleCatToCycles := by
    have h := hab
    rw [TowerMapQI.pi_eq_mk, TowerMapQI.pi_eq_mk] at h
    exact (Submodule.Quotient.eq _).mp h
  have h1 : (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 k₁ -
      phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 k₂).1 ∈
      LinearMap.range (C.d (levelDeg M 1 - 1) (levelDeg M 0 - 1)).hom :=
    (TowerMapQI.mem_range_moduleCatToCycles_iff (scCtop (C := C) M) _).mp hmem
  have hval : (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 k₁ -
      phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 k₂).1 =
      (tower hstep M s₀ 0).φHom A (k₁.1 - k₂.1) :=
    phiKTop_sub_apply (C := C) (c₀ := c₀) hstep M s₀ hd0 k₁ k₂
  have hK : (k₁ - k₂).1 ∈ (tower hstep M s₀ 0).K A := by
    rw [cell_K_eq (tower hstep M s₀ 0)]
    refine ⟨?_, ?_⟩
    · rw [tower_zero_dHom_eq_zero (C := C) hd0, LinearMap.zero_apply]
    · rw [hval] at h1
      exact h1
  have h3 : (k₁ - k₂).1 ∈ LinearMap.range (scTtop hstep M s₀).f.hom := by
    have h := hK
    rw [← tower_range_d hstep M s₀ 0] at h
    rw [show (scTtop hstep M s₀).f.hom = (tower hstep M s₀ 1).dHom A from rfl]
    exact h
  refine (Submodule.Quotient.eq _).mpr ?_
  exact (TowerMapQI.mem_range_moduleCatToCycles_iff (scTtop hstep M s₀) _).mpr h3

/-- The left homology map data of `psiTop`. -/
noncomputable def gammaTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    ShortComplex.LeftHomologyMapData (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0)
      (hTtop (C := C) (c₀ := c₀) hstep M s₀) (hCtop (C := C) M) where
  φK := phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0
  φH := phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0
  commi := phiKTop_commi (C := C) (c₀ := c₀) hstep M s₀ hd0
  commf' := phiKTop_commf' (C := C) (c₀ := c₀) hstep M s₀ hd0
  commπ := pi_phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0

/-- **`psiTop` is a quasi-isomorphism of short complexes.** -/
theorem quasiIso_psiTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    ShortComplex.QuasiIso (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0) := by
  refine (ShortComplex.LeftHomologyMapData.quasiIso_iff
    (gammaTop (C := C) (c₀ := c₀) hstep M s₀ hd0)).mpr ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨phiHTop_injective (C := C) (c₀ := c₀) hstep M s₀ hd0,
    phiHTop_surjective (C := C) (c₀ := c₀) hstep M s₀ hd0⟩

/-! ## The comparison of the short complexes -/

/-- The short complex of `C` is literally the short complex produced by
`shortComplexFunctor'`. -/
theorem scCtop_eq (M : ℤ) :
    scCtop (C := C) M = (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A)
      (ComplexShape.up ℤ) (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).obj C := rfl

/-- The short complex of the model at the top degree, expressed in terms of the tower: its two
first components `(towerModelXIso 1)`, `(towerModelXIso 0)` identify it with `scTtop`. -/
noncomputable abbrev e1Top (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
      (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).obj (towerModel hstep M s₀) ≅
      scTtop hstep M s₀ :=
  ShortComplex.isoMk (towerModelXIso hstep M s₀ 1) (towerModelXIso hstep M s₀ 0) (Iso.refl _)
    (by
      show (towerModelXIso hstep M s₀ 1).hom ≫ towerD (hstep := hstep) (M := M) (s₀ := s₀) 0 =
        (towerModel hstep M s₀).d (levelDeg M (0 + 1) - 1) (levelDeg M 0 - 1) ≫
          (towerModelXIso hstep M s₀ 0).hom
      rw [towerModel_d hstep M s₀ 0]
      simp [Category.assoc])
    (by
      show (towerModelXIso hstep M s₀ 0).hom ≫ (0 : (tower hstep M s₀ 0).G A ⟶
          (towerModel hstep M s₀).X (M + 1)) =
        (towerModel hstep M s₀).d (levelDeg M 0 - 1) (M + 1) ≫ 𝟙 _
      rw [comp_zero, Category.comp_id]
      exact (IsZero.eq_of_tgt
        (towerModel_isZero_of_gt hstep M s₀ (by omega : M < M + 1)) _ 0).symm)

/-- The square relating the map induced by `φ` on the short complexes to `psiTop`. -/
theorem sqTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (φ : towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (levelDeg M k - 1) = (towerModelXIso hstep M s₀ k).hom ≫
      Cell.φ A (tower hstep M s₀ k)) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
        (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).map φ ≫
        (Iso.refl (scCtop (C := C) M)).hom =
      (e1Top hstep M s₀).hom ≫ psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0 := by
  apply ShortComplex.hom_ext
  · simp only [ShortComplex.comp_τ₁]
    show φ.f (levelDeg M 1 - 1) ≫ 𝟙 _ = (towerModelXIso hstep M s₀ 1).hom ≫
      (tower hstep M s₀ 1).φ A
    rw [Category.comp_id]
    exact hφ 1
  · simp only [ShortComplex.comp_τ₂]
    show φ.f (levelDeg M 0 - 1) ≫ 𝟙 _ = (towerModelXIso hstep M s₀ 0).hom ≫
      (tower hstep M s₀ 0).φ A
    rw [Category.comp_id]
    exact hφ 0
  · simp only [ShortComplex.comp_τ₃]
    show φ.f (M + 1) ≫ 𝟙 _ = 𝟙 _ ≫ (0 : (towerModel hstep M s₀).X (M + 1) ⟶ C.X (M + 1))
    rw [Category.comp_id, Category.id_comp]
    exact IsZero.eq_of_src
      (towerModel_isZero_of_gt hstep M s₀ (by omega : M < M + 1)) _ 0

/-- The square of `sqTop`, in the orientation required by `Arrow.isoMk`. -/
theorem sqTop' (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (φ : towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (levelDeg M k - 1) = (towerModelXIso hstep M s₀ k).hom ≫
      Cell.φ A (tower hstep M s₀ k)) :
    (e1Top hstep M s₀).hom ≫ psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0 =
      (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
        (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).map φ ≫
        (Iso.refl (scCtop (C := C) M)).hom :=
  (sqTop (C := C) (c₀ := c₀) hstep M s₀ hd0 φ hφ).symm


end TowerModelMapTop

namespace TowerModelMapTop

/-- **The top degree case**: `φ` is a quasi-isomorphism in the degree `M = levelDeg M 0 - 1` of
the base cell of the tower. -/
theorem quasiIsoAt_towerModelMap_top {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1))
    (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (φ : towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (levelDeg M k - 1) = (towerModelXIso hstep M s₀ k).hom ≫
      Cell.φ A (tower hstep M s₀ k)) :
    QuasiIsoAt φ (levelDeg M 0 - 1) := by
  rw [quasiIsoAt_iff' (f := φ) (i := levelDeg M 1 - 1) (j := levelDeg M 0 - 1) (k := M + 1)
    (ComplexShape.prev_eq' (c := ComplexShape.up ℤ)
      (ComplexShape.up_mk (levelDeg M 1 - 1) (levelDeg M 0 - 1)
        (by simp only [levelDeg_succ]; ring)))
    (ComplexShape.next_eq' (c := ComplexShape.up ℤ)
      (ComplexShape.up_mk (levelDeg M 0 - 1) (M + 1) (by rw [levelDeg_zero]; ring)))]
  exact ShortComplex.quasiIso_of_arrow_mk_iso (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0)
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
      (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).map φ)
    (Arrow.isoMk
      (f := Arrow.mk ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
        (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).map φ))
      (g := Arrow.mk (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0))
      (e1Top hstep M s₀) (Iso.refl _) (sqTop' (C := C) (c₀ := c₀) hstep M s₀ hd0 φ hφ)).symm
    (hφ := quasiIso_psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0)

end TowerModelMapTop

end Work.DSMX0U
