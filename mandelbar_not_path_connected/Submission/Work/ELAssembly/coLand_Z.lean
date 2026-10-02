import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.Arm_coLand
import Submission.Work.ELAssembly.rayPt_eq_of_eqOn_compl

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- The point of the ray of angle `θ` at level `t` is periodic in the angle with period `1`
(the ray point only depends on the angle modulo `1`). -/
theorem rayPt_add_one {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ t : ℝ) :
    hN.rayPt (θ + 1) t = hN.rayPt θ t := by
  by_cases h : 1 < t
  · refine hN.injOn_Phi (hN.rayPt_notMem h) (hN.rayPt_notMem h) ?_
    rw [hN.Phi_rayPt h, hN.Phi_rayPt h]
    simpa using Work.ELPull.rayPoint_periodic θ t (1 : ℤ)
  · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt, dite_eq_right h, dite_eq_right h]

/-- Landing of the ray of angle `θ` is periodic in `θ` with period `1`. -/
theorem landsN_add_one {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) (y : ℂ) :
    Work.EL.LandsN hN (θ + 1) y ↔ Work.EL.LandsN hN θ y := by
  simp only [Work.EL.LandsN]
  rw [show (fun t : ℝ => Work.EL.rayPt hN (θ + 1) t) = (fun t => Work.EL.rayPt hN θ t) from
    funext fun t => rayPt_add_one hN θ t]


theorem coLand_Z {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (d : Work.EL.RootParabolic c) (hNcan : Work.ELPull.DynB c) (hφcan : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (hψ : ∀ z : ℂ, z ∉ Work.EL.K c → d.φ z = Work.ParamRays.dynPhiOf c z) (htop : Work.ELPull.PB1Top hNcan) (hbaseA : ∃ y : ℂ, Work.ELPull.LandsN hNcan (Work.ELNest.armA1 0) y ∧ Work.ELPull.LandsN hNcan (Work.ELNest.armA2 0) y) (hbaseB : ∃ y : ℂ, Work.ELPull.LandsN hNcan (Work.ELNest.armB1 0) y ∧ Work.ELPull.LandsN hNcan (Work.ELNest.armB2 0) y) (hbaseC : ∃ y : ℂ, Work.ELPull.LandsN hNcan (Work.ELNest.armC1 0) y ∧ Work.ELPull.LandsN hNcan (Work.ELNest.armC2 0) y) (hndA : ∀ n : ℕ, Work.EL.arcLen (Work.ELNest.armA1 n) (Work.ELNest.armA2 n) ≠ 0) (hndB : ∀ n : ℕ, Work.EL.arcLen (Work.ELNest.armB1 n) (Work.ELNest.armB2 n) ≠ 0) (hndC : ∀ n : ℕ, Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n) ≠ 0) (hcvA : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hNcan), t < 6 → Q.a = (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t).1 → Q.b = (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t).2 → c ∈ Work.ELPull.arcSide hNcan Q (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t)).2 (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (Work.ELNest.armA1 n, Work.ELNest.armA2 n) t)).1) (hcvB : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hNcan), t < 6 → Q.a = (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t).1 → Q.b = (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t).2 → c ∈ Work.ELPull.arcSide hNcan Q (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t)).2 (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (Work.ELNest.armB1 n, Work.ELNest.armB2 n) t)).1) (hcvC : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hNcan), t < 6 → Q.a = (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t).1 → Q.b = (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t).2 → c ∈ Work.ELPull.arcSide hNcan Q (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t)).2 (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t)).1) : (∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armA1 n) y ∧ Work.EL.LandsN d.hN (Work.ELNest.armA2 n) y) ∧ (∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armB1 n) y ∧ Work.EL.LandsN d.hN (Work.ELNest.armB2 n) y) ∧ (∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armC1 n) y ∧ Work.EL.LandsN d.hN (Work.ELNest.armC2 n + 1) y) := by
  -- the two Bottcher coordinates agree off `K c`
  have hagree : ∀ z : ℂ, z ∉ Work.EL.K c →
      Work.ParamRays.dynPhi c z = Work.EL.dynPhi c d.φ z := by
    intro z hz
    rw [Work.ParamRays.dynPhi_of_not_mem hz, Work.EL.dynPhi_of_notMem hz, ← hψ z hz]
  -- transport the rays of the canonical data to the rays of `d.hN`
  have hray := rayPt_eq_of_eqOn_compl hNcan d.hN hagree
  -- the co-landing of the arm pairs in the canonical data
  have key := Work.ELNest.armPair_coLands hc hNcan hφcan htop hbaseA hbaseB hbaseC
    hndA hndB hndC hcvA hcvB hcvC
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · obtain ⟨⟨y, h1, h2⟩, -, -⟩ := key n
    exact ⟨y, (hray.2 (Work.ELNest.armA1 n) y).mp h1,
      (hray.2 (Work.ELNest.armA2 n) y).mp h2⟩
  · obtain ⟨-, ⟨y, h1, h2⟩, -⟩ := key n
    exact ⟨y, (hray.2 (Work.ELNest.armB1 n) y).mp h1,
      (hray.2 (Work.ELNest.armB2 n) y).mp h2⟩
  · obtain ⟨-, -, ⟨y, h1, h2⟩⟩ := key n
    exact ⟨y, (hray.2 (Work.ELNest.armC1 n) y).mp h1,
      (landsN_add_one d.hN (Work.ELNest.armC2 n) y).mpr
        ((hray.2 (Work.ELNest.armC2 n) y).mp h2)⟩

end Work.ELAssembly
