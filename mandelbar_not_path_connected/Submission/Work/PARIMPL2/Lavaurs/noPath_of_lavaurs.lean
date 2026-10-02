import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.noPath_of_trans
import Submission.Work.PARIMPL2.escape_of_exitTrackedWindow
import Submission.Work.PARIMPL2.exitTrackedWindow_of_lockstep
import Submission.Work.PARIMPL.leak_shift_int
import Submission.Work.PARIMPL2.Data
import Submission.Work.PARIMPL.robust_of_greenOpen
import Submission.Work.NAKANE.GreenEscapeOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open LeanEval.ComplexAnalysis (Mandelbar)

/-- The Écalle height of the critical orbit does not depend on the tap time, in the form needed
here: the entry point `Work.PARIMPL.entryPt P nEnter c₀ ∈ fl.Pa` and the later tap point at time
`nIn ≥ nEnter` have the same height.  This is
`Work.FatouCoordFix.ParabolicFlowerFix.ecalleHeight_iterate` after writing `nIn = nEnter + k`. -/
private theorem im_φa_iterate {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    {n m : ℕ} (hnm : n ≤ m) (hmem : (Work.PARIMPL.Ft c₀)^[n] c₀ ∈ fl.Pa) :
    (fl.φa ((Work.PARIMPL.Ft c₀)^[m] c₀)).im
      = (fl.φa ((Work.PARIMPL.Ft c₀)^[n] c₀)).im := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hiter : (Work.PARIMPL.Ft c₀)^[n + k] c₀
      = (Work.PARIMPL.Ft c₀)^[k] ((Work.PARIMPL.Ft c₀)^[n] c₀) := by
    rw [Nat.add_comm, Function.iterate_add_apply]
  rw [hiter]
  exact Work.FatouCoordFix.ParabolicFlowerFix.ecalleHeight_iterate fl hmem k

theorem noPath_of_lavaurs {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (nIn : ℕ)
    (hnIn : Work.PARIMPL.nEnter d fl.toParabolicFlower ≤ nIn)
    (hUT : Work.PARIMPL2.LavaursPhase d P fl.Pa fl.φa fl.Ψ nIn)
    (hleak : ∃ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀)
    (hcrit : (fl.φa (Work.PARIMPL.entryPt P (Work.PARIMPL.nEnter d fl.toParabolicFlower) c₀)).im = 0) :
    ∀ γ : C(Set.Icc (0:ℝ) 1, ℂ), (∀ t, γ t ∈ LeanEval.ComplexAnalysis.Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ P.Nm) := by
  classical
  -- the phase constant of the Lavaurs transit coordinate
  set x₀ : ℝ := (fl.φa (Work.PARIMPL.entryPt P nIn c₀)).re with hx₀
  obtain ⟨θ, hLock⟩ := hUT
  -- the equator leak point, shifted an integer amount into the escaping region
  obtain ⟨xstar, hxstar⟩ := hleak
  obtain ⟨n, hn⟩ : ∃ n : ℤ, xstar + (n : ℝ) < -2 := by
    obtain ⟨n, hn⟩ := exists_int_lt (-2 - xstar)
    exact ⟨n, by linarith⟩
  set xL : ℝ := xstar + (n : ℝ) with hxL
  have hxLleak : fl.Ψ ((xL : ℝ) : ℂ) ∉ Work.EL.K c₀ := by
    rw [hxL]
    exact Work.PARIMPL.leak_shift_int (fun w => fl.Ψ_shift w) hxstar n
  -- the deep leak disc and its family robustness
  obtain ⟨rD, hrD, hdeepD⟩ := Work.PARIMPL2.exists_deepDisc fl.Ψ_diff.continuous hxLleak
  set r : ℝ := min rD 1 with hrdef
  have hr : 0 < r := lt_min hrD one_pos
  have hrD' : r ≤ rD := by rw [hrdef]; exact min_le_left rD 1
  have hdeep : ∀ z ∈ closedBall (((xL - ((0 : ℤ) : ℝ)) : ℝ) : ℂ) r,
      0 < Work.Bottcher.green c₀ (fl.Ψ z) := by
    intro z hz
    have hlt : dist z ((xL : ℝ) : ℂ) ≤ r := by
      have h := hz
      rw [Metric.mem_closedBall] at h
      simpa using h
    exact hdeepD z (by rw [Metric.mem_closedBall]; linarith)
  have hrob' : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall ((xL : ℝ) : ℂ) r, dist y (fl.Ψ z) ≤ ρ) →
        y ∉ Work.EL.K c := by
    obtain ⟨ρ, hρ, h⟩ := Work.PARIMPL.robust_of_greenOpen (xstar := xL) (j₀ := 0) (r₀ := r)
      fl.Ψ_diff.continuous Work.NAKANE.greenEscapeOpen hr hdeep
    refine ⟨ρ, hρ, fun c hc y hy => h c hc y ?_⟩
    obtain ⟨z, hz, hzy⟩ := hy
    have hz2 : dist z ((xL : ℝ) : ℂ) ≤ r := by
      have h := hz
      rw [Metric.mem_closedBall] at h
      simpa using h
    exact ⟨z, by rw [Metric.mem_closedBall]; simpa using hz2, hzy⟩
  -- the entry data at the tap time `nIn`
  have hentry0 : (Work.PARIMPL.Ft c₀)^[Work.PARIMPL.nEnter d fl.toParabolicFlower] c₀ ∈ fl.Pa :=
    Work.PARIMPL.nEnter_spec d fl.toParabolicFlower
  have hentry : (Work.PARIMPL.Ft c₀)^[nIn] c₀ ∈ fl.Pa := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnIn
    have hiter : (Work.PARIMPL.Ft c₀)^[nIn] c₀
        = (Work.PARIMPL.Ft c₀)^[k]
            ((Work.PARIMPL.Ft c₀)^[Work.PARIMPL.nEnter d fl.toParabolicFlower] c₀) := by
      rw [hk, Nat.add_comm, Function.iterate_add_apply]
    rw [hiter]
    exact Work.FatouCoord.mapsTo_iterate_of_mapsTo fl.mapsTo_Pa k hentry0
  have hcrit' : (fl.φa ((Work.PARIMPL.Ft c₀)^[nIn] c₀)).im = 0 := by
    rw [im_φa_iterate fl hnIn hentry0]
    simpa [Work.PARIMPL.entryPt] using hcrit
  -- the bounded-window exit tracking of the lock-step transit
  have hEW : Work.PARIMPL2.ExitTrackedWindow c₀ P.Nm (Work.PARIMPL2.transPh P x₀ θ)
      (fun c z => Work.PARIMPL.Ft c z) fl.Ψ :=
    Work.PARIMPL2.exitTrackedWindow_of_lockstep hLock fl.mapsTo_Pa fl.φa_shift hentry hcrit'
      rfl (fun R => Work.PARIMPL2.transPh_blow P x₀ θ R)
      (fun N => (Work.PARIMPL.continuous_orbit_diag N).continuousAt)
  -- the escort level sits deep enough for the window `[-Xo, -1)`
  have hx : xL + r / 2 < -1 := by
    have h1 : xL < -2 := by rw [hxL]; exact hn
    have h2 : r ≤ 1 := by rw [hrdef]; exact min_le_right rD 1
    linarith
  -- the escape of the leak level
  have hesc : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ ((Work.PARIMPL2.transPh P x₀ θ) c) ((xL : ℝ) : ℂ) < r / 2 →
        c ∉ LeanEval.ComplexAnalysis.Mandelbar :=
    Work.PARIMPL2.escape_of_exitTrackedWindow (Nm := P.Nm)
      (trans := Work.PARIMPL2.transPh P x₀ θ) (Ft := fun c z => Work.PARIMPL.Ft c z)
      (Ψ := fl.Ψ) (x := xL) (r := r)
      hEW hr fl.Ψ_diff.continuous (fun c => rfl) hx hrob'
  -- the path endgame for the explicit transit coordinate
  refine Work.PARIMPL2.Lavaurs.noPath_of_trans d P hr ?_ ?_ ?_ hesc
  · exact Work.PARIMPL2.continuousOn_transPh P x₀ θ
  · intro a ha hab
    exact Work.PARIMPL2.tendsto_transPh P x₀ θ a ha hab
  · refine ⟨P.ρ₀, P.hρ₀, fun c _hc => ?_⟩
    rw [Work.PARIMPL2.transPh_im]
    have : (0 : ℝ) ≤ r / 4 := by linarith
    simpa using this

end Work.PARIMPL2.Lavaurs

end
