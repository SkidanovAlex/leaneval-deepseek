import Mathlib
import Submission.Work.Topology.Classical.Defs

namespace Work.Topology.Classical

theorem jordanSchoenflies_single (h : Work.Topology.Classical.JordanSchoenfliesSphere)
    {c : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (hc : Work.Topology.Classical.IsJordanCurveRound c) :
    ∃ e e' : C(Work.InnermostDisk.Disc, LeanEval.KnotTheory.PardonDistortion.R3),
      Function.Injective e ∧ Function.Injective e' ∧
      (∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c θ) ∧
      (∀ θ : ℝ, e' (Work.CoreTopology.circlePoint θ) = c θ) ∧
      (∀ z : Work.InnermostDisk.Disc, e z ∈ Work.Topology.Classical.RoundSphere) ∧
      (∀ z : Work.InnermostDisk.Disc, e' z ∈ Work.Topology.Classical.RoundSphere) ∧
      IsOpen {x : Work.Topology.Classical.RoundSphere |
        ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
          e z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} ∧
      IsOpen {x : Work.Topology.Classical.RoundSphere |
        ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
          e' z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} ∧
      Set.range e ∪ Set.range e' = Work.Topology.Classical.RoundSphere ∧
      Set.range e ∩ Set.range e' = Set.range c := by
  obtain ⟨e, e', _rank, h_inj, h_inj', h_bd, h_bd', h_mem, h_mem',
    h_open, h_open', h_cover, h_meet, _h_rank⟩ :=
    h PUnit (fun _ : PUnit => c) (fun _ => hc)
      (fun i j hij => absurd (Subsingleton.elim i j) hij)
  exact ⟨e PUnit.unit, e' PUnit.unit, h_inj _, h_inj' _, fun θ => h_bd _ θ,
    fun θ => h_bd' _ θ, fun z => h_mem _ z, fun z => h_mem' _ z, h_open _, h_open' _,
    h_cover _, h_meet _⟩

end Work.Topology.Classical
