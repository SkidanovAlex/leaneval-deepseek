import Mathlib
import Submission.Work.DSMX0U.ModelF
import Submission.Work.DSMX0U.Tower
import Submission.Work.DSMX0U.Cells
import Submission.Work.DSMX0U.Cell
import Submission.Work.DSMX0U.towerMap_quasiIsoAt_succ

/-!
# `Work.DSMX0U.quasiIsoAt_towerModelMap_mid`

The model complex `P = towerModel hstep M s₀` (`Submission.Work.DSMX0U/ModelF.lean`) is the tower
of cells extended along the embedding `embeddingUpIntLE M`; the level `k` of the tower sits in
cohomological degree `levelDeg M k - 1 = M - k` and `P` vanishes above `M`.

This file proves that a chain map `φ : P ⟶ C` whose components in the degrees of the levels are the
maps `(tower k).φ` of the cells (transported along the canonical isomorphism `towerModelXIso`) is a
quasi-isomorphism in every *non-top* degree `levelDeg M (k + 1) - 1 = M - k - 1`.

The argument is the exact analogue of `quasiIsoAt_towerModelMap_top`
(`Submission.Work.DSMX0U/quasiIso_towerModelMap2.lean`): in the degree
`levelDeg M (k+1) - 1` the short complex of the model is, through the canonical isomorphisms
`towerModelXIso`, the short complex `G_{k+2} ⟶ G_{k+1} ⟶ G_k` of the tower, and the short complex
of `C` is the concrete short complex `scC` of
`Submission.Work.DSMX0U/towerMap_quasiIsoAt_succ.lean`; the induced map of short complexes is `psi`
of that file, whose quasi-isomorphism is proved there (`quasiIso_psi`).
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

namespace TowerModelMapMid

/-- The short complex of the model in the degree `levelDeg M (k+1) - 1` of the level `k+1`,
identified with the short complex `scT` of the tower through the canonical isomorphisms
`towerModelXIso` of the three levels `k+2`, `k+1`, `k`. -/
noncomputable def e1mid (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
        (levelDeg M (k + 2) - 1) (levelDeg M (k + 1) - 1) (levelDeg M k - 1)).obj
        (towerModel hstep M s₀) ≅
      TowerMapQI.scT (C := C) (c₀ := c₀) hstep M s₀ k :=
  ShortComplex.isoMk (towerModelXIso hstep M s₀ (k + 2)) (towerModelXIso hstep M s₀ (k + 1))
    (towerModelXIso hstep M s₀ k)
    (by
      show (towerModelXIso hstep M s₀ (k + 2)).hom ≫
          towerD (hstep := hstep) (M := M) (s₀ := s₀) (k + 1) =
        (towerModel hstep M s₀).d (levelDeg M (k + 2) - 1) (levelDeg M (k + 1) - 1) ≫
          (towerModelXIso hstep M s₀ (k + 1)).hom
      simp only [towerModel_d hstep M s₀ (k + 1), Category.assoc, Iso.inv_hom_id,
        Category.comp_id])
    (by
      show (towerModelXIso hstep M s₀ (k + 1)).hom ≫
          towerD (hstep := hstep) (M := M) (s₀ := s₀) k =
        (towerModel hstep M s₀).d (levelDeg M (k + 1) - 1) (levelDeg M k - 1) ≫
          (towerModelXIso hstep M s₀ k).hom
      simp only [towerModel_d hstep M s₀ k, Category.assoc, Iso.inv_hom_id,
        Category.comp_id])

/-- The square relating the map induced by `φ` on the short complexes to `psi`: its three
components are the defining property `hφ` of `φ` at the levels `k+2`, `k+1`, `k`. -/
theorem sqMid (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1))
    (φ : towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (levelDeg M k - 1) = (towerModelXIso hstep M s₀ k).hom ≫
      Cell.φ A (tower hstep M s₀ k)) (k : ℕ) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
        (levelDeg M (k + 2) - 1) (levelDeg M (k + 1) - 1) (levelDeg M k - 1)).map φ ≫
        (Iso.refl (TowerMapQI.scC (C := C) M k)).hom =
      (e1mid (C := C) (c₀ := c₀) hstep M s₀ k).hom ≫
        TowerMapQI.psi (C := C) (c₀ := c₀) hstep M s₀ k := by
  apply ShortComplex.hom_ext
  · simp only [ShortComplex.comp_τ₁]
    show φ.f (levelDeg M (k + 2) - 1) ≫ 𝟙 _ =
      (towerModelXIso hstep M s₀ (k + 2)).hom ≫ (tower hstep M s₀ (k + 2)).φ A
    rw [Category.comp_id]
    exact hφ (k + 2)
  · simp only [ShortComplex.comp_τ₂]
    show φ.f (levelDeg M (k + 1) - 1) ≫ 𝟙 _ =
      (towerModelXIso hstep M s₀ (k + 1)).hom ≫ (tower hstep M s₀ (k + 1)).φ A
    rw [Category.comp_id]
    exact hφ (k + 1)
  · simp only [ShortComplex.comp_τ₃]
    show φ.f (levelDeg M k - 1) ≫ 𝟙 _ =
      (towerModelXIso hstep M s₀ k).hom ≫ (tower hstep M s₀ k).φ A
    rw [Category.comp_id]
    exact hφ k

end TowerModelMapMid

open TowerModelMapMid

theorem quasiIsoAt_towerModelMap_mid {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1))
    (φ : Work.DSMX0U.towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (Work.DSMX0U.levelDeg M k - 1) = CategoryTheory.CategoryStruct.comp
        (Work.DSMX0U.towerModelXIso hstep M s₀ k).hom (Work.DSMX0U.Cell.φ A (Work.DSMX0U.tower hstep M s₀ k)))
    (k : ℕ) :
    QuasiIsoAt φ (Work.DSMX0U.levelDeg M (k + 1) - 1) := by
  rw [quasiIsoAt_iff' (f := φ) (i := levelDeg M (k + 2) - 1) (j := levelDeg M (k + 1) - 1)
    (k := levelDeg M k - 1)
    (ComplexShape.prev_eq' (c := ComplexShape.up ℤ)
      (ComplexShape.up_mk (levelDeg M (k + 2) - 1) (levelDeg M (k + 1) - 1)
        (by rw [show levelDeg M (k + 2) = levelDeg M (k + 1) - 1 from rfl]; ring)))
    (ComplexShape.next_eq' (c := ComplexShape.up ℤ)
      (ComplexShape.up_mk (levelDeg M (k + 1) - 1) (levelDeg M k - 1)
        (by rw [show levelDeg M (k + 1) = levelDeg M k - 1 from rfl]; ring)))]
  exact ShortComplex.quasiIso_of_arrow_mk_iso
    (TowerMapQI.psi (C := C) (c₀ := c₀) hstep M s₀ k)
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
      (levelDeg M (k + 2) - 1) (levelDeg M (k + 1) - 1) (levelDeg M k - 1)).map φ)
    (Arrow.isoMk (f := Arrow.mk ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A)
        (ComplexShape.up ℤ) (levelDeg M (k + 2) - 1) (levelDeg M (k + 1) - 1)
        (levelDeg M k - 1)).map φ))
      (g := Arrow.mk (TowerMapQI.psi (C := C) (c₀ := c₀) hstep M s₀ k))
      (e1mid (C := C) (c₀ := c₀) hstep M s₀ k) (Iso.refl _)
      (sqMid (C := C) (c₀ := c₀) hstep M s₀ φ hφ k).symm).symm
    (hφ := TowerMapQI.quasiIso_psi (C := C) (c₀ := c₀) hstep M s₀ k)

end Work.DSMX0U
