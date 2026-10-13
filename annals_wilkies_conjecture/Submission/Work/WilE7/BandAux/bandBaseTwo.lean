/-
  WilE7 (`Work.WilE7.BandAux.bandBaseTwo`): the base projection of the connected component
  of the two-strata band presentation `bandS3two`.

  The argument is the one of `Work.WilE7.BandAux.bandComp_base`, but stated for an arbitrary
  subset `T` of the ambient space whose points have their first block in `Z.set` — which is
  exactly the form in which both `bandS3` and `bandS3two` use it.
-/
import Mathlib
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.bandComponent
import Submission.Work.WilE7.imageSubsetConnectedComponentIn

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

/-- If every point of `T` has its first block in `Z.set`, then the base projection of the
component of `bandPt u₀ v v' t₀` in `T` lies in
`C = π_p (connectedComponentIn Z.set u₀)`. -/
theorem bandBaseTwo_mem_C {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    {T : Set (Fin (bandDim p m) → ℝ)} (hT : ∀ y ∈ T, bandZ1 y ∈ Z.set)
    (v v' : Fin (m + 1) → ℝ) (t₀ : ℝ) (hp₀ : bandPt u₀ v v' t₀ ∈ T) :
    ∀ w ∈ connectedComponentIn T (bandPt u₀ v v' t₀), bandBase w ∈ C := by
  intro w hw
  have hZ : ∀ y ∈ connectedComponentIn T (bandPt u₀ v v' t₀), bandZ1 y ∈ Z.set :=
    fun y hy => hT y (connectedComponentIn_subset T _ hy)
  have hmem := imageSubsetConnectedComponentIn
    (s := connectedComponentIn T (bandPt u₀ v v' t₀))
    isPreconnected_connectedComponentIn continuous_bandZ1.continuousOn
    (mem_connectedComponentIn hp₀) hZ w hw
  rw [bandZ1_bandPt u₀ v v' t₀] at hmem
  show projFirst p (m + 1) (bandZ1 w) ∈ C
  rw [hC]
  exact ⟨bandZ1 w, hmem, rfl⟩

/-- The base projection of every point of the component of `bandPt u₀ v v' t₀` in
`bandS3two Z S₁ S₂` lies in `C`. -/
theorem bandCompTwo_base {p m : ℕ} (S₁ S₂ : Stratum p (m + 1)) (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (v v' : Fin (m + 1) → ℝ) (t₀ : ℝ)
    (hp₀ : bandPt u₀ v v' t₀ ∈ (bandS3two Z S₁ S₂).set) :
    ∀ w ∈ connectedComponentIn (bandS3two Z S₁ S₂).set (bandPt u₀ v v' t₀), bandBase w ∈ C :=
  bandBaseTwo_mem_C (T := (bandS3two Z S₁ S₂).set) Z u₀ C hC
    (fun y hy => ((bandS3two_mem_iff Z S₁ S₂ y).mp hy).1) v v' t₀ hp₀

end Work.WilE7.BandAux
