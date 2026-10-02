import Mathlib
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceGraphData
import Submission.Work.PTGeometric.WeakRegion.rootParamContinuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

open Set Filter Topology

/-- **Existence and uniqueness of the graph function.** On a box `B`, the equation `F (u,s) = 0` has
a unique solution `h u ∈ [0,δ]` for every `u ∈ ball (hsMk S.p) ρ`; `h` is continuous, the sign of
`F (u,s)` is read off from the position of `s` relative to `h u`, and `h (hsMk S.p) = 0`. -/
theorem exists_root {n : ℕ} [NeZero n] (S : Work.PTGeometric.WeakRegion.HalfSpaceGraphSetup n)
    {ρ δ M : ℝ} (B : S.Box ρ δ M) :
    ∃ h : Work.PTGeometric.WeakRegion.hsTang n → ℝ, S.Root B h := by
  classical
  obtain ⟨h, hroot, hcont, hchar, huniq⟩ :=
    rootParamContinuous (α := hsTang n) (B := Metric.ball (hsMk S.p) ρ) Metric.isOpen_ball
      B.hδ (F := fun u s => S.F (u, s))
      (by
        have hmap : MapsTo (fun x : hsTang n × ℝ => x)
            (Metric.ball (hsMk S.p) ρ ×ˢ Set.Icc 0 δ) S.dom :=
          fun x hx => B.hmem x.1 hx.1 x.2 hx.2
        have hc : ContinuousOn (fun x : hsTang n × ℝ => S.F x)
            (Metric.ball (hsMk S.p) ρ ×ˢ Set.Icc 0 δ) :=
          S.contDiffOn_F.continuousOn.comp continuousOn_id hmap
        exact hc)
      (by
        intro u hu
        exact S.slice_strictAntiOn B hu)
      (by
        intro u hu
        exact (B.hsign u hu).1)
      (by
        intro u hu
        exact (B.hsign u hu).2)
  refine ⟨h, fun u hu => hroot u hu, hcont, fun u hu s hs => hchar u hu s hs, ?_⟩
  have hpt_ball : hsMk S.p ∈ Metric.ball (hsMk S.p) ρ := by
    rw [Metric.mem_ball, dist_self]; exact B.hρ
  have hF0 : S.F (hsMk S.p, (0 : ℝ)) = 0 := S.F_pt
  have h0m : (0 : ℝ) ∈ Set.Icc 0 δ := ⟨le_refl 0, le_of_lt B.hδ⟩
  exact ((huniq (hsMk S.p) hpt_ball 0 h0m).mp hF0).symm

end Work.PTGeometric.WeakRegion
