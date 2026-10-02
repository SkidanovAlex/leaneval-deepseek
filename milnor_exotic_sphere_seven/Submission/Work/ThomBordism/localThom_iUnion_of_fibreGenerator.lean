import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.psiClassHyp
import Submission.Work.ThomBordism.iUnion.extra
import Submission.Work.ThomBordism.iUnion.zeroInjSubfamily
import Submission.Work.ThomBordism.iUnion.coneCyclicZeroIUnion
import Submission.Work.ThomBordism.iUnion.coneCyclicPosIUnion
import Submission.Work.ThomBordism.localThomMap_bijective_of_coneData
import Submission.Work.ThomBordism.localThom_iUnion_of_fibreGenerator_zero
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_finrank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

theorem localThom_iUnion_of_fibreGenerator {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (σ : Work.Thom.OpenThom Z n)
    (hn : n = Module.finrank ℝ F) (hσ : Work.ThomBordism.IsFibreGenerator Z n σ)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W)
    (hchain : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' ∨ W' ⊆ W)
    (h : ∀ W (hW : W ∈ C), ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' W) (Set.preimage_mono (Set.subset_sUnion_of_mem hW)) n).hom ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ)) k)) :
    ∀ k, Function.Bijective (Work.Thom.localThomMap Z n (⋃₀ C)
        ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) k) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- the fibre dimension is `0`
    subst hn0
    exact localThom_iUnion_of_fibreGenerator_zero Z σ hn.symm C hC hchain h
  · -- positive fibre dimension
    have hlow : ∀ S : Set B, Subsingleton (Work.Thom.PieceCoh Z S (n - 1)) :=
      fun S => Work.Thom.subsingleton_PieceCoh_of_lt_finrank Z S (by rw [← hn]; omega)
    have h0inj : ∀ (D : Set (Set B)) (hD : D ⊆ C),
        Function.Injective (Work.Thom.localThomMap Z n (⋃₀ D)
          ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' (⋃₀ D))
            (Set.preimage_mono (Set.sUnion_mono hD)) n).hom
              ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ)) 0) :=
      fun D hD => iUnion.zeroInjSubfamily Z (⋃₀ C) ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) C hC
        (fun W hW => Set.subset_sUnion_of_mem hW) h D hD (Set.sUnion_mono hD)
    have h0injC : Function.Injective (Work.Thom.localThomMap Z n (⋃₀ C)
        ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) 0) := by
      have hh := h0inj C (fun W hW => hW)
      rw [pdCohMap_preim_self Z n (⋃₀ C) ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ)] at hh
      exact hh
    have hzero : ∀ (D : Set (Set B)) (hD : D ⊆ C),
        ConeCyclicZero Z n (⋃₀ C) ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) (⋃₀ D)
          (Set.sUnion_mono hD) :=
      fun D hD => iUnion.coneCyclicZeroIUnion Z n hnpos C hC hchain
        ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) h h0inj hlow D hD
    have hpos := iUnion.coneCyclicPosIUnion Z n hnpos C hC hchain
      ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) h hzero C (fun W hW => hW)
    exact localThomMap_bijective_of_coneData Z n (⋃₀ C)
      ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ)
      (psiClassHyp Z n (⋃₀ C) ((Work.Thom.PieceRes Z (⋃₀ C) n).hom σ) (⋃₀ C)
        (fun x hx => hx))
      hpos (hzero C (fun W hW => hW)) h0injC

end Work.ThomBordism
