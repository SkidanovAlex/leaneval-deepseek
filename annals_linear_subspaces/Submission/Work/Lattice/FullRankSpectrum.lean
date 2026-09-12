import Mathlib
import Submission.Work.Lattice.SpectrumDiscreteness
import Submission.Work.Lattice.Submodularity
import Submission.Work.Polygon.GraysonEndpoints

/-!
# Project-vocabulary full-rank covolume-spectrum discreteness

The `Submission.SpectrumDiscreteness` core is stated on the lattice point group
(`AddSubgroup ↥Λ`).  This module transports it to the §3 project vocabulary: for a
full-rank lattice `Λ ≤ ℝᵈ` (`ℝᵈ = EuclideanSpace ℝ (Fin d)`, `Λ : Submodule ℤ (E d)`
with `[DiscreteTopology Λ] [IsZLattice ℝ Λ]`), the **top-rank covolume spectrum is
discrete**:

    `finite_fullRank_covol_le` :  Finite {W : Submodule ℤ (E d) //
        W ≤ Λ ∧ subDim W = d ∧ latticeCovol W ≤ C}

i.e. only finitely many full-rank (`subDim = d`) discrete subgroups of `Λ` have
intrinsic covolume below `C` — the statement used by the §3 polygon/HN layer
(`rankData`, Grayson polygon, Prop 4/5); this is the rank-`r = d` case of ROADMAP item
(ii) in the project's own vocabulary.

Reduction to the core:
- a full-rank `W ≤ Λ` is a finite-index subgroup of `Λ`: `subDim W = d` gives
  `realSpan W = ⊤` (`Submodularity.realSpan_eq_top_of_subDim`), hence
  `[DiscreteTopology W]` (`discreteTopology_of_le`) and `[IsZLattice ℝ W]`
  (`isZLattice_of_subDim`), and the ambient-covolume index identity
  `covol X = covol Λ · relIndex (X, Λ)`
  (`Submodularity.covol_eq_covol_lattice_mul_relIndex`, from Mathlib
  `ZLattice.covolume_div_covolume_eq_relIndex'`);
- the intrinsic covolume equals the ambient covolume at full rank
  (`GraysonEndpoints.latticeCovol_eq_covolume_of_span_top`);
- the subgroup of the lattice point group `↥Λ` represented by `W ≤ Λ` is the preimage
  `AddSubgroup.comap (Λ.subtype) W.toAddSubgroup`, whose index in `↥Λ` is exactly
  `W.toAddSubgroup.relIndex Λ.toAddSubgroup` (`AddSubgroup.index_comap`); this map is
  injective on the submodules of `Λ` (`AddSubgroup.map_comap_eq_self` +
  `Submodule.toAddSubgroup_injective`), so the finiteness of
  `SpectrumDiscreteness.finite_fullRank_sublattices_covol_le` transfers.

All declarations are Mathlib + Submission (SpectrumDiscreteness/Submodularity/
GraysonEndpoints).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.FullRankSpectrum

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.GraysonEndpoints
open Submission.Submodularity
open Submission.SpectrumDiscreteness

/-- The additive-group homomorphism from a submodule to the ambient space. -/
abbrev subtypeAddHom {d : ℕ} (Λ : Submodule ℤ (E d)) : ↥Λ →+ E d :=
  (Λ.subtype : ↥Λ →ₗ[ℤ] E d).toAddMonoidHom

/-- Applying the inclusion is the subtype coercion. -/
@[simp] lemma subtypeAddHom_apply {d : ℕ} (Λ : Submodule ℤ (E d)) (v : ↥Λ) :
    subtypeAddHom Λ v = (v : E d) := rfl

/-- The range of the inclusion `Λ ↪ E d` is `Λ.toAddSubgroup`. -/
lemma subtypeAddHom_range {d : ℕ} (Λ : Submodule ℤ (E d)) :
    (subtypeAddHom Λ).range = Λ.toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    exact (Submodule.mem_toAddSubgroup Λ).mpr v.2
  · intro hx
    refine ⟨⟨x, (Submodule.mem_toAddSubgroup Λ).mp hx⟩, rfl⟩

/-- `toAddSubgroup` is monotone. -/
lemma toAddSubgroup_le_of_le {d : ℕ} {A B : Submodule ℤ (E d)} (h : A ≤ B) :
    A.toAddSubgroup ≤ B.toAddSubgroup := by
  intro x hx
  exact (Submodule.mem_toAddSubgroup B).mpr (h ((Submodule.mem_toAddSubgroup A).mp hx))

/-- The subgroup of the lattice point group `↥Λ` represented by a submodule `X ≤ Λ`:
`{v : ↥Λ | (v : E d) ∈ X}`.  Its index in `↥Λ` is the relative index of `X` in `Λ`. -/
def subgroupOfLattice {d : ℕ} (Λ X : Submodule ℤ (E d)) (_hXΛ : X ≤ Λ) : AddSubgroup ↥Λ :=
  AddSubgroup.comap (subtypeAddHom Λ) X.toAddSubgroup

/-- **Index identity**: the index of the preimage subgroup in `↥Λ` is the relative index
`X.toAddSubgroup.relIndex Λ.toAddSubgroup` of `X` inside `Λ`. -/
lemma subgroupOfLattice_index {d : ℕ} (Λ X : Submodule ℤ (E d)) (hXΛ : X ≤ Λ) :
    (subgroupOfLattice Λ X hXΛ).index = X.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  classical
  dsimp [subgroupOfLattice]
  rw [AddSubgroup.index_comap]
  congr 1
  exact subtypeAddHom_range Λ

/-- `subgroupOfLattice` is injective on the submodules of `Λ` (a submodule is determined
by its preimage in the lattice point group). -/
lemma subgroupOfLattice_injective {d : ℕ} (Λ : Submodule ℤ (E d)) :
    Function.Injective (fun X : {X : Submodule ℤ (E d) // X ≤ Λ} =>
      subgroupOfLattice Λ X.1 X.2) := by
  classical
  intro X Y h
  apply Subtype.ext
  have hleX : X.1.toAddSubgroup ≤ (subtypeAddHom Λ).range := by
    rw [subtypeAddHom_range Λ]
    exact toAddSubgroup_le_of_le X.2
  have hleY : Y.1.toAddSubgroup ≤ (subtypeAddHom Λ).range := by
    rw [subtypeAddHom_range Λ]
    exact toAddSubgroup_le_of_le Y.2
  have hmX : X.1.toAddSubgroup =
      AddSubgroup.map (subtypeAddHom Λ) (subgroupOfLattice Λ X.1 X.2) := by
    dsimp [subgroupOfLattice]
    exact (AddSubgroup.map_comap_eq_self (f := subtypeAddHom Λ) (H := X.1.toAddSubgroup)
      hleX).symm
  have hmY : Y.1.toAddSubgroup =
      AddSubgroup.map (subtypeAddHom Λ) (subgroupOfLattice Λ Y.1 Y.2) := by
    dsimp [subgroupOfLattice]
    exact (AddSubgroup.map_comap_eq_self (f := subtypeAddHom Λ) (H := Y.1.toAddSubgroup)
      hleY).symm
  have hm : AddSubgroup.map (subtypeAddHom Λ) (subgroupOfLattice Λ X.1 X.2) =
      AddSubgroup.map (subtypeAddHom Λ) (subgroupOfLattice Λ Y.1 Y.2) := by
    simpa using congrArg (AddSubgroup.map (subtypeAddHom Λ)) h
  have hto : X.1.toAddSubgroup = Y.1.toAddSubgroup := by
    calc
      X.1.toAddSubgroup = AddSubgroup.map (subtypeAddHom Λ) (subgroupOfLattice Λ X.1 X.2) := hmX
      _ = AddSubgroup.map (subtypeAddHom Λ) (subgroupOfLattice Λ Y.1 Y.2) := hm
      _ = Y.1.toAddSubgroup := hmY.symm
  exact Submodule.toAddSubgroup_injective hto

/-- **Full-rank intrinsic covolume = ambient covolume × relative index**: for `X ≤ Λ`
with `subDim X = d`, `latticeCovol X = covol Λ · relIndex(X, Λ)`. -/
lemma latticeCovol_eq_covol_mul_relIndex {d : ℕ} (Λ X : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hXΛ : X ≤ Λ) (hXdim : subDim X = d) :
    latticeCovol X = ZLattice.covolume (E := E d) Λ *
      (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
  classical
  haveI : DiscreteTopology X := discreteTopology_of_le Λ X hXΛ
  haveI : IsZLattice ℝ X := isZLattice_of_subDim X hXdim
  have hspan : realSpan X = ⊤ := realSpan_eq_top_of_subDim X hXdim
  rw [latticeCovol_eq_covolume_of_span_top X hspan,
    covol_eq_covol_lattice_mul_relIndex Λ X hXΛ]

/-- **Project-vocabulary full-rank covolume-spectrum discreteness**: for a full-rank
lattice `Λ ≤ ℝᵈ` and a bound `C`, only finitely many full-rank (`subDim = d`) discrete
subgroups `W ≤ Λ` have intrinsic covolume `latticeCovol W ≤ C`. -/
theorem finite_fullRank_covol_le {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (C : ℝ) :
    Finite {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = d ∧ latticeCovol W ≤ C} := by
  classical
  haveI : Module.Free ℤ ↥Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ ↥Λ := ZLattice.module_finite ℝ Λ
  let A : Type := {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = d ∧ latticeCovol W ≤ C}
  let T : Type := {H : AddSubgroup ↥Λ // H.index ≠ 0 ∧
    (H.index : ℝ) * ZLattice.covolume (E := E d) Λ ≤ C}
  have hT : Finite T := finite_fullRank_sublattices_covol_le (Λ := Λ) C
  have hfin : ∀ W : A, (subgroupOfLattice Λ W.1 W.2.1).index ≠ 0 := by
    intro W
    haveI : DiscreteTopology W.1 := discreteTopology_of_le Λ W.1 W.2.1
    haveI : IsZLattice ℝ W.1 := isZLattice_of_subDim W.1 W.2.2.1
    rw [subgroupOfLattice_index Λ W.1 W.2.1]
    exact relIndex_ne_zero_of_fullRank Λ W.1 W.2.1
  have hcov : ∀ W : A,
      (subgroupOfLattice Λ W.1 W.2.1).index *
          ZLattice.covolume (E := E d) Λ ≤ C := by
    intro W
    have hEq : latticeCovol W.1 = ZLattice.covolume (E := E d) Λ *
        (W.1.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) :=
      latticeCovol_eq_covol_mul_relIndex Λ W.1 W.2.1 W.2.2.1
    calc
      (subgroupOfLattice Λ W.1 W.2.1).index *
          ZLattice.covolume (E := E d) Λ
          = ZLattice.covolume (E := E d) Λ *
              (W.1.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
            rw [subgroupOfLattice_index Λ W.1 W.2.1]
            ring
      _ = latticeCovol W.1 := hEq.symm
      _ ≤ C := W.2.2.2
  let ψ : A → T := fun W =>
    ⟨subgroupOfLattice Λ W.1 W.2.1, hfin W, hcov W⟩
  have hψinj : Function.Injective ψ := by
    intro U V h
    exact Subtype.ext (by
      have hpair : (⟨U.1, U.2.1⟩ : {X : Submodule ℤ (E d) // X ≤ Λ}) =
          (⟨V.1, V.2.1⟩ : {X : Submodule ℤ (E d) // X ≤ Λ}) :=
        subgroupOfLattice_injective Λ
          (by simpa [ψ] using congrArg (fun t : T => t.1) h)
      simpa using congrArg Subtype.val hpair)
  exact Finite.of_injective ψ hψinj

end Submission.FullRankSpectrum
