import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatHull

open FirstOrder Language
open scoped FirstOrder
noncomputable section
open Classical

namespace Work.WilC5

/-- The generating sets of the level hulls are increasing in the level: the values of the constants
of level `y` are among the values of the constants of level `z` whenever `y ≤ z`. -/
theorem SatHullLevGen_mono {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (N : Type)
    [instN : (SatLang L (SatCTotal L M κ)).Structure N]
    {y z : SatIdx κ} (h : y ≤ z) :
    Set.range (fun c : SatC L M κ y =>
        @SatConVal L (SatCt L M κ) N instN (SatIncTotal L M κ y c)) ⊆
      Set.range (fun c : SatC L M κ z =>
        @SatConVal L (SatCt L M κ) N instN (SatIncTotal L M κ z c)) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨SatInc L M κ h c, by
    cases c with
    | inl m => rfl
    | inr cu => obtain ⟨⟨u, hu⟩, a⟩ := cu; rfl⟩

theorem SatHullLevMono {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (N : Type)
    [instN : (SatLang L (SatCTotal L M κ)).Structure N]
    {y z : SatIdx κ} (h : y ≤ z) :
    (SatHullLev L M κ N y : Set N) ⊆ (SatHullLev L M κ N z : Set N) := by
  letI : L.Structure N := SatReduct L M κ N
  intro a ha
  simp only [SatHullLev] at ha ⊢
  exact FirstOrder.Language.Substructure.closure_mono (SatHullLevGen_mono N h) ha

end Work.WilC5
