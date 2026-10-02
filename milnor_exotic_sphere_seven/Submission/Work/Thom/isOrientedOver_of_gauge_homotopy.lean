import Mathlib
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.Glue
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.ATools
import Submission.Work.Thom.localThom_line
import Submission.Work.Thom.localThom_genFibre
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.ChartOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Thom

theorem isOrientedOver_of_gauge_homotopy (n : ℕ) (hn : 1 ≤ n)
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hF : Module.finrank ℝ F = n) {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι)
    {U V : Set B} {i j : ι} (hUi : U ⊆ Z.baseSet i) (hVj : V ⊆ Z.baseSet j)
    (H : C(unitInterval × ↥(U ∩ V), F →L[ℝ] F))
    (H0 : ∀ x : ↥(U ∩ V), H (0, x) = Z.coordChange i j (x : B))
    (H1 : ∀ x : ↥(U ∩ V), H (1, x) = 1)
    (Hinv : ∀ t x, Function.Bijective (H (t, x))) :
    Work.Thom.IsOrientedOver Z n U V := by
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]; exact hF
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F)
      (F := EuclideanSpace ℝ (Fin n)) hfr
  have hWi : U ∩ V ⊆ Z.baseSet i := fun x hx => hUi hx.1
  have hWj : U ∩ V ⊆ Z.baseSet j := fun x hx => hVj hx.2
  refine ⟨localThomOfChart Z n e i U hUi, localThomOfChart Z n e j V hVj,
    localThomOfChart Z n e i (U ∩ V) hWi, ?_, ?_⟩
  · exact localThomOfChart_restrict Z n e i (U ∩ V) U hWi hUi (fun x hx => hx.1)
  · exact (localThomOfChart_restrict Z n e j (U ∩ V) V hWj hVj (fun x hx => hx.2)).trans
      (localThomOfChart_eq_of_gauge Z n e i j (U ∩ V) hWi hWj
        (fun x hx => ⟨hUi hx.1, hVj hx.2⟩) H H0 H1 Hinv)

end Work.Thom
