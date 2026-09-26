import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.Split
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.Drive.Final.dentOut_sweep_subset
import Submission.Work.Drive.Final.finrank_union_le_one_of_two_gates_nonconn
import Submission.Work.Drive.Final.dentOut_resolved
import Submission.Work.Drive.EpsFormSphere.dichotomy_of_trace_inessential

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

theorem windingSpan_dentOutRegion_eq_bot
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    {E : Set R3}
    (hEc : E ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hEo : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) E)
    (hEbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) E = ⊥)
    (hcover : Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D ⊆
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre) ∪ E)
    (hXbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre)) = ⊥)
    (hgate : ∃ a b : R3,
      IsPathConnected ((Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) ∩ E) ∩
          connectedComponentIn (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) ∩ E) a) ∧
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
            s c σ u v h ℓ (ℓ D.centre) ∩ E) ⊆
        connectedComponentIn (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) ∩ E) a ∪
        connectedComponentIn (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) ∩ E) b)
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hfront : ∀ x ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier,
      x ∉ Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D →
      (∀ (i : Fin n) (t : ℝ), (cs i).γ t ≠ x) →
      x ∉ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D))
    (hon : ∀ (i : Fin n) (t : ℝ),
      (cs i).γ t ∈ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) ∧
      (cs i).γ t ∉ Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) :
    Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) = ⊥ := by
  -- Pardon's dichotomy at `Ω₁`: its frontier is the inessential trace `cs`
  rcases Work.Drive.EpsFormSphere.windingSpan_bot_or_top_of_trace_inessential
    (P := Work.Drive.EpsSphere.torusOf ψ)
    (X := Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) (γ := cs)
    (Work.Drive.Final.dentOutRegion_subset_carrier D) hsimple hess hdisj
    (Work.Drive.Final.isOpenInCarrier_dentOutRegion D) hfront hon with hbot | htop
  · exact hbot
  · -- the `⊤` branch is impossible: `Ω₁` lies in the union of the two inessential regions
    exfalso
    have hWAE : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
            (ℓ D.centre) ∪ E) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← htop]
      exact Work.SurgeryInvariance.WindingSpan_mono _ hcover
    have hfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
        (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
            (ℓ D.centre) ∪ E)) ≤ 1 :=
      Work.Drive.Final.finrank_union_le_one_of_two_gates_nonconn
        (P := Work.Drive.EpsSphere.torusOf ψ)
        (A := Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
          s c σ u v h ℓ (ℓ D.centre)) (E := E)
        (fun x hx => hx.1) hEc
        Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion hEo hXbot hEbot hgate
    rw [hWAE] at hfin
    have h2 : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
      rw [finrank_top, Module.finrank_prod, Module.finrank_self]
    omega


end Work.Drive.Final
