import Mathlib
import Submission.Work.DSMX0U.ModelF
import Submission.Work.DSMX0U.Tower
import Submission.Work.DSMX0U.towerMap_quasiIsoAt_succ
import Submission.Work.DSMX0U.cell_d_comm
import Submission.Work.DSMX0U.tower_range_d
import Submission.Work.DSMX0U.cell_K_eq

/-!
# DSMX0U - the model map at the top degree: the setup

This file contains the setup of the verification of `Work.DSMX0U.quasiIso_towerModelMap2` in the
*top degree* `M = levelDeg M 0 - 1` of the tower: the short complex `G_1 -towerD 0-> G_0 -> 0` of
the tower, the short complex `C^(M-1) -> C^M -> C^(M+1)` of `C`, the map `psiTop` between them,
and the resulting maps `phiKTop`, `phiHTop` on cycles and on homology.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

namespace TowerModelMapTop

/-! ## The short complexes at the top degree `M` -/

/-- The short complex of the tower in the top degree `levelDeg M 0 - 1 = M`:
`G_1 --towerD 0--> G_0 ⟶ 0`.  Its third term is the term of the model in degree `M + 1`, which is
a zero object. -/
noncomputable abbrev scTtop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : ShortComplex (ModuleCat.{a} A) :=
  ShortComplex.mk (towerD (hstep := hstep) (M := M) (s₀ := s₀) 0)
    (0 : (tower hstep M s₀ 0).G A ⟶ (towerModel hstep M s₀).X (M + 1)) (by rw [comp_zero])

/-- The short complex of `C` in the top degree `levelDeg M 0 - 1 = M`:
`C^{M-1} ⟶ C^M ⟶ C^{M+1}`.  It is defined as the object of the functor `shortComplexFunctor'`
at the relevant degrees, so that it is syntactically the source of the arrow obtained by applying
that functor to a map. -/
noncomputable abbrev scCtop (M : ℤ) : ShortComplex (ModuleCat.{a} A) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.up ℤ)
    (levelDeg M 1 - 1) (levelDeg M 0 - 1) (M + 1)).obj C

/-- The differential of the base cell gives a cycle condition for its map into `C`: from
`Cell.d_comm` at the base cell and the hypothesis `hd0` (the differential of the base cell is
zero) we get `(tower 0).φ ≫ C.d M (M+1) = 0`. -/
theorem tower_zero_comp_d {hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s} {M : ℤ}
    {s₀ : Cell A C c₀ (M + 1)} (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    (tower hstep M s₀ 0).φ A ≫ C.d (levelDeg M 0 - 1) (M + 1) = 0 := by
  have h := cell_d_comm (s := tower hstep M s₀ 0)
  rw [show (tower hstep M s₀ 0).d A = 0 from hd0, zero_comp] at h
  exact h.symm

/-- The underlying linear map of the differential of the base cell is zero. -/
theorem tower_zero_dHom_eq_zero {hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s} {M : ℤ}
    {s₀ : Cell A C c₀ (M + 1)} (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    (tower hstep M s₀ 0).dHom A = 0 := by
  have h : (Cell.d A (tower hstep M s₀ 0)).hom = 0 := by
    rw [hd0, ModuleCat.hom_zero]
  simpa only [Cell.d, ModuleCat.hom_ofHom] using h

/-- The map of short complexes at the top degree: its components are `(tower 1).φ`, `(tower 0).φ`
and `0`.  The first square is `Cell.d_comm` at the cell of level `1`, the second one is the cycle
condition `tower_zero_comp_d`. -/
noncomputable abbrev psiTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    scTtop hstep M s₀ ⟶ scCtop (C := C) M where
  τ₁ := (tower hstep M s₀ 1).φ A
  τ₂ := (tower hstep M s₀ 0).φ A
  τ₃ := 0
  comm₁₂ := (cell_d_comm (s := tower hstep M s₀ 1)).symm
  comm₂₃ := by
    have h1 : (tower hstep M s₀ 0).φ A ≫ (scCtop (C := C) M).g = 0 := by
      show (tower hstep M s₀ 0).φ A ≫ C.d (levelDeg M 0 - 1) (M + 1) = 0
      exact tower_zero_comp_d (C := C) hd0
    rw [h1, zero_comp]

/-- The second component of `psiTop` is `(tower 0).φ`, i.e. `(tower 0).φHom` on elements. -/
theorem psiTop_τ₂_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (u : ↥(scTtop hstep M s₀).X₂) :
    (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂ u = (tower hstep M s₀ 0).φHom A u := rfl

/-! ## The homology data and the induced map on homology -/

/-- The concrete left homology data of the tower's top short complex: its cycles are all of
`G_0` (the top differential is zero) and the homology is `G_0 / range (towerD 0)`. -/
noncomputable abbrev hTtop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : (scTtop (C := C) (c₀ := c₀) hstep M s₀).LeftHomologyData :=
  (scTtop (C := C) (c₀ := c₀) hstep M s₀).moduleCatLeftHomologyData

/-- The concrete left homology data of the short complex of `C` at the top degree. -/
noncomputable abbrev hCtop (M : ℤ) : (scCtop (C := C) M).LeftHomologyData :=
  (scCtop (C := C) M).moduleCatLeftHomologyData

/-- The map on cycles induced by `psiTop`: it is `(tower 0).φ` restricted to the cycles of the
tower, which is a cycle map by `tower_zero_comp_d`. -/
noncomputable abbrev phiKTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    (hTtop (C := C) (c₀ := c₀) hstep M s₀).K ⟶ (hCtop (C := C) M).K :=
  (hCtop (C := C) M).liftK
    ((hTtop (C := C) (c₀ := c₀) hstep M s₀).i ≫
      (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂) (by
    rw [Category.assoc, (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).comm₂₃, ← Category.assoc,
      (hTtop (C := C) (c₀ := c₀) hstep M s₀).wi, zero_comp])

/-- `phiKTop` intertwines the kernel inclusions. -/
theorem phiKTop_commi (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 ≫ (hCtop (C := C) M).i =
      (hTtop (C := C) (c₀ := c₀) hstep M s₀).i ≫
        (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂ :=
  (hCtop (C := C) M).liftK_i _ _

/-- `phiKTop` intertwines the maps from the first terms. -/
theorem phiKTop_commf' (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    (hTtop (C := C) (c₀ := c₀) hstep M s₀).f' ≫ phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 =
      (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₁ ≫ (hCtop (C := C) M).f' := by
  refine (cancel_mono (hCtop (C := C) M).i).mp ?_
  calc (((hTtop (C := C) (c₀ := c₀) hstep M s₀).f' ≫
          phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0) ≫ (hCtop (C := C) M).i)
      = (hTtop (C := C) (c₀ := c₀) hstep M s₀).f' ≫
          (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 ≫ (hCtop (C := C) M).i) :=
        Category.assoc _ _ _
    _ = (hTtop (C := C) (c₀ := c₀) hstep M s₀).f' ≫
          ((hTtop (C := C) (c₀ := c₀) hstep M s₀).i ≫
            (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂) := by
        rw [phiKTop_commi]
    _ = ((hTtop (C := C) (c₀ := c₀) hstep M s₀).f' ≫
          (hTtop (C := C) (c₀ := c₀) hstep M s₀).i) ≫
            (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂ := (Category.assoc _ _ _).symm
    _ = (scTtop (C := C) (c₀ := c₀) hstep M s₀).f ≫
          (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂ := by
        rw [(hTtop (C := C) (c₀ := c₀) hstep M s₀).f'_i]
    _ = (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₁ ≫
          (scCtop (C := C) M).f :=
        ((psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).comm₁₂).symm
    _ = (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₁ ≫
          ((hCtop (C := C) M).f' ≫ (hCtop (C := C) M).i) := by
        rw [(hCtop (C := C) M).f'_i]
    _ = ((psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₁ ≫ (hCtop (C := C) M).f') ≫
          (hCtop (C := C) M).i := (Category.assoc _ _ _).symm

/-- The map on homology induced by `psiTop`. -/
noncomputable def phiHTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    (hTtop (C := C) (c₀ := c₀) hstep M s₀).H ⟶ (hCtop (C := C) M).H :=
  (hTtop (C := C) (c₀ := c₀) hstep M s₀).descH
    (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 ≫ (hCtop (C := C) M).π) (by
      rw [← Category.assoc, phiKTop_commf' (C := C) (c₀ := c₀) hstep M s₀ hd0, Category.assoc,
        (hCtop (C := C) M).f'_π, comp_zero])

/-- The defining property of `phiHTop`. -/
theorem pi_phiHTop (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0) :
    (hTtop (C := C) (c₀ := c₀) hstep M s₀).π ≫ phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0 =
      phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 ≫ (hCtop (C := C) M).π :=
  (hTtop (C := C) (c₀ := c₀) hstep M s₀).π_descH _ _

/-- The value of `phiHTop` on a class. -/
theorem phiHTop_pi_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (x : ↥(hTtop (C := C) (c₀ := c₀) hstep M s₀).K) :
    (phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0) ((hTtop (C := C) (c₀ := c₀) hstep M s₀).π x) =
      (hCtop (C := C) M).π (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x) := by
  have h := congrArg (fun (g : (hTtop (C := C) (c₀ := c₀) hstep M s₀).K ⟶
      (hCtop (C := C) M).H) => g x) (pi_phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h

/-- The value of `phiHTop` on the class of a cycle of `G_0`. -/
theorem phiHTop_mk_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (x : ↥(hTtop (C := C) (c₀ := c₀) hstep M s₀).K) :
    (phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0) (Submodule.Quotient.mk x) =
      (hCtop (C := C) M).π (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x) :=
  calc (phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0) (Submodule.Quotient.mk x)
      = (phiHTop (C := C) (c₀ := c₀) hstep M s₀ hd0)
          ((hTtop (C := C) (c₀ := c₀) hstep M s₀).π x) := by
        rw [TowerMapQI.pi_eq_mk (scTtop (C := C) (c₀ := c₀) hstep M s₀) x]
    _ = (hCtop (C := C) M).π (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x) :=
        phiHTop_pi_apply (C := C) (c₀ := c₀) hstep M s₀ hd0 x

/-- The value of `phiKTop` on an element: it is `(tower 0).φ` applied to the underlying element. -/
theorem phiKTop_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (x : ↥(hTtop (C := C) (c₀ := c₀) hstep M s₀).K) :
    (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x).1 =
      (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂ x.1 := by
  have h1 : ((hCtop (C := C) M).i (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x) :
      ↥(scCtop (C := C) M).X₂) =
      (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x).1 := TowerMapQI.i_eq_subtype _ _
  have h3 : (hCtop (C := C) M).i (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x) =
      (psiTop (C := C) (c₀ := c₀) hstep M s₀ hd0).τ₂
        ((hTtop (C := C) (c₀ := c₀) hstep M s₀).i x) := by
    have h := congrArg
      (fun (g : (hTtop (C := C) (c₀ := c₀) hstep M s₀).K ⟶ (scCtop (C := C) M).X₂) => g x)
      (phiKTop_commi (C := C) (c₀ := c₀) hstep M s₀ hd0)
    rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  have h4 : ((hTtop (C := C) (c₀ := c₀) hstep M s₀).i x :
      ↥(scTtop (C := C) (c₀ := c₀) hstep M s₀).X₂) = x.1 := TowerMapQI.i_eq_subtype _ _
  rw [← h1, h3, h4]

/-- The difference formula for `phiKTop`. -/
theorem phiKTop_sub_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (hd0 : Cell.d A (tower hstep M s₀ 0) = 0)
    (x y : ↥(hTtop (C := C) (c₀ := c₀) hstep M s₀).K) :
    (phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 x -
        phiKTop (C := C) (c₀ := c₀) hstep M s₀ hd0 y).1 =
      (tower hstep M s₀ 0).φHom A (x.1 - y.1) := by
  rw [Submodule.coe_sub, phiKTop_apply, phiKTop_apply, ← map_sub]
  rfl


end TowerModelMapTop

end Work.DSMX0U
