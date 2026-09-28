import Submission.Work.Serre.Engine
import Submission.Work.StemsB.FieldDualUCT

/-!
# The `ℚ`-duality between rational homology and rational cohomology

`Work.StemsB.ratDualUCT` (the field universal coefficient theorem) identifies
`H^n(X;ℚ) ≅ (H_n(X;ℚ))^*`.  The *forward* consequence (vanishing of homology gives vanishing of
cohomology) is `Work.Serre.isZero_ratCoh_of_isZero_ratH`; this file provides the **converse**, which
is what a Gysin/periodicity argument in cohomology needs in order to conclude about homology, and
the transport of these statements along homotopy equivalences.

The converse is the elementary fact that the double dual of a `ℚ`-vector space contains it
(`Module.Dual.eval_apply_eq_zero_iff`): the dual has no nonzero elements only for the zero space.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

noncomputable section

/-- **A `ℚ`-module with vanishing dual is zero.**  Over a field a nonzero vector has a nonzero
linear functional (`Module.Projective.exists_dual_ne_zero`), so `V^* = 0` forces `V = 0`. -/
theorem subsingleton_of_dual_subsingleton {M : Type*} [AddCommGroup M] [Module ℚ M]
    (h : Subsingleton (M →ₗ[ℚ] ℚ)) : Subsingleton M := by
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  obtain ⟨f, hf⟩ :=
    Module.Projective.exists_dual_ne_zero (V := M) ℚ (x := x - y) (sub_ne_zero.mpr hxy)
  refine hf ?_
  have hf0 : f = 0 := h.elim f 0
  rw [hf0, LinearMap.zero_apply]

/-- **Vanishing of rational cohomology implies vanishing of rational homology** (the converse of
`Work.Serre.isZero_ratCoh_of_isZero_ratH`). -/
theorem isZero_ratH_of_isZero_ratCoh {X : TopCat} {k : ℕ} (h : IsZero (Work.Serre.ratCoh X k)) :
    IsZero (Work.Serre.ratH X k) := by
  have hd : IsZero (ModuleCat.of ℚ (↥(Work.Serre.ratH X k) →ₗ[ℚ] ℚ)) :=
    h.of_iso (Classical.choice (Work.StemsB.ratDualUCT (Work.Serre.ratChains X) k)).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (subsingleton_of_dual_subsingleton (M := ↥(Work.Serre.ratH X k))
      (ModuleCat.isZero_iff_subsingleton.mp hd))

/-- **Vanishing of rational homology transports backwards along a homotopy equivalence.** -/
theorem isZero_ratH_of_homotopyEquiv {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : ContinuousMap.HomotopyEquiv A B) (j : ℕ) (h : IsZero (Work.Serre.ratH (TopCat.of B) j)) :
    IsZero (Work.Serre.ratH (TopCat.of A) j) := by
  haveI : IsIso (Work.Serre.ratHomologyMap e.toFun j) :=
    Work.Serre.IsRatHomologyIso.of_homotopyEquiv e j
  exact IsZero.of_iso h (asIso (Work.Serre.ratHomologyMap e.toFun j))

/-- **`H_j ≅ ℚ` transports backwards along a homotopy equivalence.** -/
theorem isoRat_of_homotopyEquiv {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : ContinuousMap.HomotopyEquiv A B) (j : ℕ)
    (h : Nonempty (Work.Serre.ratH (TopCat.of B) j ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Serre.ratH (TopCat.of A) j ≅ ModuleCat.of ℚ ℚ) := by
  haveI : IsIso (Work.Serre.ratHomologyMap e.toFun j) :=
    Work.Serre.IsRatHomologyIso.of_homotopyEquiv e j
  obtain ⟨h'⟩ := h
  exact ⟨asIso (Work.Serre.ratHomologyMap e.toFun j) ≪≫ h'⟩

end

end Work.Stems
