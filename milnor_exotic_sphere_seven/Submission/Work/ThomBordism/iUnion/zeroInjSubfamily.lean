import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.Thom.localThomMap_pdCohMap
import Submission.Work.Thom.Coh_zero_cover_injective_gen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Injectivity in degree `0` of the local Thom map over a union of pieces

If a piece class `τ` of the Thom pair of a real bundle `Z → B` over `U` is a *local Thom class*
over every member `W` of a family `C` of open sets (`W ⊆ U`), then its restriction to the union
`⋃₀ D` of any subfamily `D ⊆ C` has *injective* local Thom map in degree `0`.

The point is that `H⁰` is detected on an open cover: a class of `H⁰(⋃₀ D)` which restricts to `0`
on every `W ∈ D` is `0` (`Work.Thom.Coh_zero_cover_injective_gen`).  So it suffices to show that
`z` with `localThomMap_{⋃₀ D} z = 0` restricts to `0` over each `W ∈ D`; but that is the
restriction naturality of the local Thom map
(`Work.Thom.localThomMap_pdCohMap`, pointwise form `localThomMap_restrict_apply` below) together
with the injectivity hypothesis over `W` and the functoriality of the restriction of the piece
class (`Work.Thom.pdCohMap_comp_apply`).
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism.iUnion

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Restriction naturality of the local Thom map, pointwise form.**  For `W ⊆ U`, a class
`τ : PieceCoh Z U n` and `x ∈ H^k(U)`, the local Thom map over `W` of the restricted class
`τ|_W` evaluated at `x|_W` is the restriction of the local Thom map over `U` of `τ` evaluated at
`x`.  This is `Work.Thom.localThomMap_pdCohMap` in element form. -/
theorem localThomMap_restrict_apply (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    {U W : Set B} (hWU : W ⊆ U) (τ : Work.Thom.PieceCoh Z U n) (k : ℕ)
    (x : Work.Thom.Coh ℤ k ↥U) :
    Work.Thom.localThomMap Z n W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) n).hom τ) k
        ((Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B)
          U W hWU)) ℤ k).hom x)
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) (k + n)).hom
          (Work.Thom.localThomMap Z n U τ k x) := by
  have h3 := congrArg ModuleCat.Hom.hom (Work.Thom.localThomMap_pdCohMap Z n hWU τ k)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom] at h3
  exact LinearMap.congr_fun h3 x

theorem zeroInjSubfamily {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W) (hWU : ∀ W ∈ C, W ⊆ U)
    (h : ∀ W (hW : W ∈ C), ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono (hWU W hW)) n).hom τ) k))
    (D : Set (Set B)) (hD : D ⊆ C) (hDU : ⋃₀ D ⊆ U) :
    Function.Injective (Work.Thom.localThomMap Z n (⋃₀ D)
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' (⋃₀ D)) (Set.preimage_mono hDU) n).hom τ) 0) := by
  classical
  -- The class over the union, as a local name.
  set τU : Work.Thom.PieceCoh Z (⋃₀ D) n :=
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' (⋃₀ D)) (Set.preimage_mono hDU) n).hom τ with hτU
  -- It suffices to prove that a class killed by the local Thom map over the union is zero.
  have hmain : ∀ z : Work.Thom.Coh ℤ 0 ↥(⋃₀ D),
      Work.Thom.localThomMap Z n (⋃₀ D) τU 0 z = 0 → z = 0 := by
    intro z hz
    -- Step 1: the restriction of `z` to each piece `W ∈ D` (in the base) vanishes, by
    -- naturality of the local Thom map and the injectivity hypothesis over `W`.
    have hstep1 : ∀ W (hW : W ∈ D),
        (Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B)
          (⋃₀ D) W (Set.subset_sUnion_of_mem hW))) ℤ 0).hom z = 0 := by
      intro W hW
      have hWC : W ∈ C := hD hW
      have hWU0 : W ⊆ ⋃₀ D := Set.subset_sUnion_of_mem hW
      -- the piece class over `W` in the naturality statement is the one from the hypothesis
      have hclass :
          (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (⋃₀ D)) (Z.proj ⁻¹' W) (Set.preimage_mono hWU0) n).hom τU
          = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono (hWU W hWC)) n).hom τ := by
        rw [hτU, Work.Thom.pdCohMap_comp_apply Z hWU0 hDU τ]
      have h4 := localThomMap_restrict_apply Z n hWU0 τU 0 z
      rw [hz, map_zero] at h4
      rw [hclass] at h4
      exact (h W hWC 0).1 (by rw [h4, map_zero])
    -- Step 2: the cover of `↥(⋃₀ D)` by the pieces of `D`, and the degree-`0` separation.
    have hcov : ∀ p : ↥(⋃₀ D),
        ∃ W : ↥D, p ∈ ((Subtype.val : ↥(⋃₀ D) → B) ⁻¹' (W : Set B)) := by
      intro p
      obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.mp p.2
      exact ⟨⟨W, hW⟩, hpW⟩
    have hVopen : ∀ W : ↥D, IsOpen ((Subtype.val : ↥(⋃₀ D) → B) ⁻¹' (W : Set B)) :=
      fun W => (hC W.1 (hD W.2)).preimage continuous_subtype_val
    have hper : ∀ W : ↥D,
        (Work.Thom.CohMap (Work.Thom.subtypeMap ((Subtype.val : ↥(⋃₀ D) → B) ⁻¹' (W : Set B)))
          ℤ 0).hom z = 0 := by
      intro W
      -- the inclusion of the piece `W` into the union, as a map out of the subtype-of-subtype
      have hsub : Work.Thom.subtypeMap ((Subtype.val : ↥(⋃₀ D) → B) ⁻¹' (W : Set B))
          = (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) (⋃₀ D) (W : Set B)
                (Set.subset_sUnion_of_mem W.2))).comp
              ((Work.Cohomology.luSubHomeo (X := B) (Set.subset_sUnion_of_mem W.2)).symm
                : C(↥((Subtype.val : ↥(⋃₀ D) → B) ⁻¹' (W : Set B)), ↥(W : Set B))) := by
        apply ContinuousMap.ext
        intro y
        apply Subtype.ext
        rfl
      rw [hsub, Work.Thom.CohMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
        hstep1 (W : Set B) W.2, map_zero]
    exact Work.Thom.Coh_zero_cover_injective_gen
      (fun W : ↥D => (Subtype.val : ↥(⋃₀ D) → B) ⁻¹' (W : Set B)) hVopen hcov z hper
  intro x y hxy
  refine sub_eq_zero.mp (hmain (x - y) ?_)
  rw [map_sub, hxy, sub_self]

end

end Work.ThomBordism.iUnion
