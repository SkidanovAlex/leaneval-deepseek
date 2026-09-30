import Mathlib
import Submission.Work.MbarHomology.CellAtlas.Core
import Submission.Work.MbarHomology.CellAtlas.levelMap_zero
import Submission.Work.MbarHomology.CellAtlas.quasiIso_levelMap_univ_iff
import Submission.Work.MbarHomology.CellAtlas.quasiIso_levelMap_insert

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-! ## The top level of the refinement is everything -/

theorem CMod_maxDim_eq_top (A : CellAtlas K P C) (k : ℕ) :
    CMod C P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1)))) k = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  rw [mem_CMod]
  intro b hb
  have hk : k ≤ P.maxDim := by
    rw [← A.dim_root k b]
    exact P.dim_le_maxDim _
  exact absurd (inD_of_le (C := C) b hk) hb

theorem KMod_maxDim_eq_top (A : CellAtlas K P C) (k : ℕ) :
    KMod A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1)))) k = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [mem_KMod, mem_kSup]
  intro σ hσ
  refine Or.inl ?_
  rw [← A.dim_root (A.car σ).1 (A.car σ).2]
  exact P.dim_le_maxDim _

theorem isIso_incl_of_sub_eq_top {D : ChainComplex (ModuleCat ℤ) ℕ}
    (S : Work.Subdivision.SubData D) (hs : ∀ k, S.sub k = ⊤) : IsIso S.incl := by
  haveI : ∀ k, IsIso (S.incl.f k) := fun k => by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro x y hxy
      exact Subtype.ext hxy
    · intro y
      exact ⟨⟨y, by rw [hs k]; trivial⟩, rfl⟩
  exact HomologicalComplex.Hom.isIso_of_components S.incl

/-! ## The top level is the whole atlas map -/

theorem zMap_quasiIso_of_levelMap_maxDim (A : CellAtlas K P C) (h : A.BoundaryCompat)
    (hq : QuasiIso (levelMap A h P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1)))))) :
    QuasiIso (A.zMap h) := by
  have hC : ∀ k, (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).sub k = ⊤ := by
    intro k
    rw [CSD_sub]
    exact CMod_maxDim_eq_top A k
  have hK : ∀ k, (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).sub k = ⊤ := by
    intro k
    rw [KSD_sub]
    exact KMod_maxDim_eq_top A k
  haveI hCi : IsIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl :=
    isIso_incl_of_sub_eq_top _ hC
  haveI hKi : IsIso (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl :=
    isIso_incl_of_sub_eq_top _ hK
  have hsq : (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl ≫ (A.zMap h)
      = (levelMap A h P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))) ≫
        (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl := by
    apply HomologicalComplex.hom_ext
    intro k
    show (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl.f k ≫ (A.zMap h).f k
        = (levelMap A h P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).f k ≫
          (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl.f k
    rw [levelMap_f, Work.Subdivision.SubData.incl_f_eq, Work.Subdivision.SubData.incl_f_eq]
    exact Work.Subdivision.incl_restrictCptMap _ _ _ _ k
  have hsq' : (asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom ≫
        (A.zMap h)
      = (levelMap A h P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))) ≫
        (asIso (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom := by
    rw [show (asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom
        = (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl from rfl,
      show (asIso (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom
        = (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl from rfl]
    exact hsq
  have hz : (asIso (CSD (C := C) P.maxDim
        (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).inv ≫
        ((levelMap A h P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))) ≫
          (asIso (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom)
      = A.zMap h := by
    calc (asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).inv ≫
          ((levelMap A h P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))) ≫
            (asIso (KSD A P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom)
        = (asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).inv ≫
          ((asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom ≫
            A.zMap h) := by rw [← hsq']
      _ = ((asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).inv ≫
          (asIso (CSD (C := C) P.maxDim (∅ : Finset (Fin (C.dim (P.maxDim + 1))))).incl).hom) ≫
          A.zMap h := (Category.assoc _ _ _).symm
      _ = A.zMap h := by rw [Iso.inv_hom_id, Category.id_comp]
  rw [← hz]
  haveI := hq
  infer_instance

/-! ## The assembly of the cell-by-cell induction -/

theorem zMap_quasiIso {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (hdd : P.HasDdZero) (haug : P.HasAugZero) (hsp : P.LocallySpherical hdd haug) (h : A.BoundaryCompat) : QuasiIso (A.zMap h) := by
  have hzero : QuasiIso (levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))) := levelMap_zero A h
  have hinsert : ∀ (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))),
      f₀ ∉ E → QuasiIso (levelMap A h n E) → QuasiIso (levelMap A h n (insert f₀ E)) :=
    fun n E f₀ hf ih => quasiIso_levelMap_insert A hdd haug hsp h n E f₀ hf ih
  have huniv : ∀ n : ℕ, QuasiIso (levelMap A h n (Finset.univ : Finset (Fin (C.dim (n + 1)))))
      ↔ QuasiIso (levelMap A h (n + 1) (∅ : Finset (Fin (C.dim (n + 2))))) :=
    fun n => quasiIso_levelMap_univ_iff A h n
  have hlevel : ∀ (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))),
      QuasiIso (levelMap A h n ∅) → QuasiIso (levelMap A h n E) := by
    intro n E
    refine Finset.induction_on E ?_ ?_
    · intro h0; exact h0
    · intro f₀ E hf ih h0
      exact hinsert n E f₀ hf (ih h0)
  have houter : ∀ n : ℕ, QuasiIso (levelMap A h n (∅ : Finset (Fin (C.dim (n + 1))))) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih => exact (huniv n).mp (hlevel n Finset.univ ih)
  exact zMap_quasiIso_of_levelMap_maxDim A h (houter P.maxDim)

end CellAtlas

end

end Work.MbarHomology
