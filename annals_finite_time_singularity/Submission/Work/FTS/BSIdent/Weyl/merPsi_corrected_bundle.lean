import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev17
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev9
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_aux2
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_profiles
import Submission.Work.FTS.BSIdent.Weyl.Levels.psiFieldCorr_cocompact
import Submission.Work.FTS.BSIdent.Weyl.weylPairPrinciple
import Submission.Work.FTS.BSIdent.hid_of_pointwise
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl

open Filter Set MeasureTheory
open scoped Topology

/-- **The corrected stream-function bundle.**  For the meridian stream function `merPsi α A B Φ C · · t`
of the reconstruction there is a continuous axis level `L` such that the corrected field
`psiFieldCorr (merPsi …) L` is continuous and decays at infinity. -/
theorem merPsi_corrected_bundle {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∃ L : ℝ → ℝ, Continuous L ∧
      Continuous (Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t) L) ∧
      Filter.Tendsto (Work.FTS.BSIdent.psiFieldCorr
          (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t) L)
        (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
  change ∃ L : ℝ → ℝ, Continuous L ∧
      Continuous (Work.FTS.BSIdent.psiFieldCorr (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) L) ∧
      Filter.Tendsto (Work.FTS.BSIdent.psiFieldCorr
          (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) L)
        (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0)
  set L : ℝ → ℝ := fun z =>
    Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t) z with hL
  have hLcont : Continuous L := by
    rw [hL]
    exact Work.FTS.BSIdent.Weyl.Levels.continuous_axisLevel (α := α) (A := A) (B := B) (Φ := Φ)
      (C := C) (t := t) hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate
  refine ⟨L, hLcont, ?_, ?_⟩
  · -- continuity of the corrected field
    refine Work.FTS.BSIdent.Weyl.continuous_psiFieldCorr ?_ hLcont ?_
    · -- continuity off the axis
      intro x hx
      exact (Work.FTS.BSIdent.Weyl.Dev17.continuousAt_psiField_offaxis
        (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        (τ := Physical.clockInv C t) rfl hsm hzeroPlane hB hx).continuousWithinAt
    · -- the axis limits
      intro z₀
      by_cases hz : z₀ = 0
      · subst hz
        have hLz : L 0 = 0 := by
          rw [hL]
          simp [Work.FTS.BSIdent.Weyl.Dev12.axisLevel]
        obtain ⟨ho1, ho2, ho3⟩ :=
          Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_profiles (α := α) (A := A) (B := B)
            (Φ := Φ) (C := C) (t := t) hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate
        have ho1' : Filter.Tendsto (fun p : ℝ × ℝ =>
            Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
            (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0))
            (𝓝 (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t) 0)) := by
          simpa [Work.FTS.BSIdent.Weyl.Dev12.axisLevel] using ho1
        have ho2' : Filter.Tendsto (fun p : ℝ × ℝ =>
            Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
            (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0))
            (𝓝 (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t) 0)) := by
          simpa [Work.FTS.BSIdent.Weyl.Dev12.axisLevel] using ho2
        have hmain := Work.FTS.BSIdent.Weyl.Levels.tendsto_psiField_axis (α := α) (A := A)
          (B := B) (Φ := Φ) (C := C) (t := t) (τ := Physical.clockInv C t) (z₀ := 0) ho1' ho2' ho3
        rw [hLz]
        simpa [Work.FTS.BSIdent.Weyl.Dev12.axisLevel] using hmain
      · have h1 := Work.FTS.BSIdent.Weyl.Dev9.tendsto_div_fst_axis (α := α) (A := A) (B := B)
          (Φ := Φ) (C := C) (t := t) (τ := Physical.clockInv C t) rfl hz hsm hzeroAxis hB
        have h2 := Work.FTS.BSIdent.Weyl.Dev13.tendsto_pdR_axis (α := α) (A := A) (B := B)
          (Φ := Φ) (C := C) (t := t) (τ := Physical.clockInv C t) hz rfl hsm hzeroPlane hzeroAxis hB
        have h3 := Work.FTS.BSIdent.Weyl.Dev13.tendsto_pdZ_axis (α := α) (A := A) (B := B)
          (Φ := Φ) (C := C) (t := t) (τ := Physical.clockInv C t) hz rfl hsm hzeroPlane hzeroAxis hB
        have hmain := Work.FTS.BSIdent.Weyl.Levels.tendsto_psiField_axis (α := α) (A := A)
          (B := B) (Φ := Φ) (C := C) (t := t) (τ := Physical.clockInv C t) (z₀ := z₀) h1 h2 h3
        simpa [hL] using hmain
  · -- decay at infinity
    exact Work.FTS.BSIdent.Weyl.Levels.psiFieldCorr_cocompact (α := α) (A := A) (B := B) (Φ := Φ)
      (C := C) (t := t) hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate

end Work.FTS.BSIdent.Weyl
