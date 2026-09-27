import Mathlib
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.sideGermDefs

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology
attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-!
# Openness of the good configurations of a pair of *independent* base charts

`Work.Drive.goodPair_pertChart_isOpen` proves that `{p | GoodAt Ξ Q c w p}` is open, i.e. that the
configuration set of the *two-slot* perturbation of a *single* base chart `Q` (the loop slot uses
`Ξ p.1 ∘ Q`, the chain slot uses `rotCapping w ∘ Ξ p.2 ∘ Q`) is open.

The present file is the two-chart generalisation: the loop slot is built on a base chart `Q₁` and the
chain slot on a *different* base chart `Q₂`.  Nothing in the analytic engine
(`Work.Drive.eventually_good_meetBox`) refers to a common base chart — it only sees the two families
`L u = coreLoop (chart of the loop slot)` and `D u = clampedSweep c (1 - ·) (diskPlane (chart of the
chain slot))` — so the same argument applies: the loop family feeds `Q₁`
(`Work.Drive.parityLoopFam`, smoothness `Work.Drive.gpLoop_contMDiff`) and the chain family feeds
`Q₂` (`Work.Drive.parityChainFam`, smoothness `Work.Drive.gpChain_contMDiff`).

Main result: `Work.Drive.goodPairTwoCharts_isOpen`.
-/

set_option maxHeartbeats 1000000

noncomputable section

/-- The chain-slot chart of the two-slot perturbation: the rotated chart perturbation. -/
def rotPertChart {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (w : UnitAddCircle) (t : EuclideanSpace ℝ (Fin m)) : ℂ → CappingSpace :=
  fun z => rotCapping w (pertChart Ξ Q t z)

/-- **The two-chart meet box**: the engine's `meetBox` for the loop family fed by `Q₁` and the chain
family fed by `Q₂` is the design's `coreMeet` at the configuration `A + u` (definitional, the
two-chart analogue of `Work.Drive.meetBox_parityFam`). -/
theorem meetBox_parityFamTwo {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q₁ Q₂ : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (A u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    meetBox (parityLoopFam Ξ Q₁ A u) (parityChainFam Ξ Q₂ c w A u)
      = coreMeet (pertChart Ξ Q₁ (A + u).1) c (diskPlane (rotPertChart Ξ Q₂ w (A + u).2)) := rfl

/-- **Openness of the good configurations of two independently perturbed smooth charts.**  The
two-chart generalisation of `Work.Drive.goodPair_pertChart_isOpen`: the loop slot is perturbed over
the chart `Q₁`, the chain slot over the chart `Q₂`, and both perturbations are independent. -/
theorem isOpen_goodPairTwoCharts_gen {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q₁ Q₂ : ℂ → CappingSpace)
    (hΞ : ChartPert Q₁ m Ξ) (hQ₁ : IsSmoothChart Q₁) (hQ₂ : IsSmoothChart Q₂)
    (c : ℝ) (w : UnitAddCircle) :
    IsOpen {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) |
      GoodPair (pertChart Ξ Q₁ p.1) (rotPertChart Ξ Q₂ w p.2) c} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  obtain ⟨-, -, hfin, hint, htrans⟩ := hA
  -- the three meet-set clauses at the base configuration, in `meetBox` form (the engine's shape)
  have hfin0 : (meetBox (parityLoopFam Ξ Q₁ A 0) (parityChainFam Ξ Q₂ c w A 0)).Finite := by
    rw [meetBox_parityFamTwo (A := A) (u := 0), add_zero]; exact hfin
  have hint0 : ∀ p ∈ meetBox (parityLoopFam Ξ Q₁ A 0) (parityChainFam Ξ Q₂ c w A 0),
      p.1 ∈ Set.Ioo (0:ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0:ℝ) 1 := by
    intro p hp
    rw [meetBox_parityFamTwo (A := A) (u := 0), add_zero] at hp
    exact hint p hp
  have htrans0 : ∀ p ∈ meetBox (parityLoopFam Ξ Q₁ A 0) (parityChainFam Ξ Q₂ c w A 0),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (parityLoopFam Ξ Q₁ A 0) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (parityChainFam Ξ Q₂ c w A 0) p.2).toLinearMap = ⊤ := by
    intro p hp
    rw [meetBox_parityFamTwo (A := A) (u := 0), add_zero] at hp
    rw [parityLoopFam_zero, parityChainFam_zero]
    exact htrans p hp
  -- the analytic engine: smoothness of the two families (loop over `Q₁`, chain over `Q₂`)
  have hL := gpLoop_contMDiff Ξ Q₁ hΞ hQ₁ A
  have hD := gpChain_contMDiff Ξ Q₂ c w hΞ hQ₂ A
  have hEv := eventually_good_meetBox (parityLoopFam Ξ Q₁ A) (parityChainFam Ξ Q₂ c w A)
    hL hD hfin0 hint0 htrans0
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hEv
  refine Filter.mem_of_superset (Metric.ball_mem_nhds A hρ) ?_
  intro A' hA'ball
  have hu : ‖A' - A‖ < ρ := by
    rw [Metric.mem_ball, dist_eq_norm] at hA'ball; exact hA'ball
  set u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) := A' - A with hudef
  have hAsum : A + u = A' := by rw [hudef]; abel
  have hsum1 : A.1 + u.1 = A'.1 := congrArg Prod.fst hAsum
  have hsum2 : A.2 + u.2 = A'.2 := congrArg Prod.snd hAsum
  -- the two families at the translate `u` are the charts of the configuration `A'`
  have hloopfun : parityLoopFam Ξ Q₁ A u = coreLoop (pertChart Ξ Q₁ A'.1) := by
    funext t
    simp only [parityLoopFam_apply]
    rw [hsum1]
  have hchainfun : parityChainFam Ξ Q₂ c w A u
      = clampedSweep c (fun t => 1 - t) (rotPresentation (pertChart Ξ Q₂ A'.2) w) := by
    funext x
    simp only [parityChainFam_apply]
    rw [hsum2]
  have hgood := hρsub (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)
  simp only [Set.mem_ofPred_eq] at hgood
  rw [meetBox_parityFamTwo (A := A) (u := u)] at hgood
  rw [hAsum] at hgood
  rw [hloopfun, hchainfun] at hgood
  exact ⟨contMDiff_pertChart Ξ Q₁ hΞ hQ₁ A'.1, contMDiff_rot_pertChart Ξ Q₂ w hΞ hQ₂ A'.2,
    hgood.1, hgood.2.1, hgood.2.2⟩

/-- Openness of the good configurations of a pair of *independent* base charts: the two-slot
generalisation of `Work.Drive.goodPair_pertChart_isOpen` (which has the same base chart `Q` in both
slots, with a rotation `w` on the second).  Proof: a near-verbatim copy of that proof with `Q₁` in the
loop family (`parityLoopFam` / `gpLoop_contMDiff`) and `Q₂` in the chain family. -/
theorem goodPairTwoCharts_isOpen {Q₁ Q₂ : ℂ → Work.Drive.CappingSpace}
    (hQ₁ : Work.Drive.IsSmoothChart Q₁) (hQ₂ : Work.Drive.IsSmoothChart Q₂)
    (c : ℝ) (w : UnitAddCircle) :
    IsOpen {p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
      Work.Drive.GoodPair (fun z : ℂ => Work.Drive.chartPert p.1 (Q₁ z))
        (fun z : ℂ => Work.Drive.rotCapping w (Work.Drive.chartPert p.2 (Q₂ z))) c} := by
  have hΞ : ChartPert Q₁ 4 (fun s p => chartPert s p) :=
    ⟨fun p => chartPert_zero p, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  exact isOpen_goodPairTwoCharts_gen (fun s p => chartPert s p) Q₁ Q₂ hΞ hQ₁ hQ₂ c w

end

end Work.Drive
