/-
# `Work.FTS.StrongPersist.H6Aux.RStep` — one step of the commutator induction

The recursion step of the `Lhat`-induction, isolated from the base case (which lives in
`H6Aux.base_R`) so that the two can be developed independently.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongPersist.H6Aux.IPChains
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)
open Work.FTS.IPGen (IPnG IPnG_zero IPnG_succ)
open Work.FTS.CoercivityFix.Transfer (CommSm CSQ AddOKSm)

set_option autoImplicit false

/-- **One step of the commutator induction.** -/
theorem R_step (n : ℕ) (hn : n + 1 ≤ 5)
    (IH : ∃ r : ℝ, 0 < r ∧ ∀ α ∈ Set.Ioc 0 1, ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (n + 2) h →
      -r * IPnG 1 1 α n h h ≤ IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat h) h) :
    ∃ r : ℝ, 0 < r ∧ ∀ α ∈ Set.Ioc 0 1, ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (n + 3) h →
      -r * IPnG 1 1 α (n + 1) h h
        ≤ IPnG 1 1 α (n + 1) (Work.FTS.CoercivityFix.Lhat h) h := by
  obtain ⟨r, hr, IHr⟩ := IH
  obtain ⟨CC, hCC, hCSQunif⟩ := CSQ_IPnG_unif n
  obtain ⟨C₂, hC₂, hE2unif⟩ := HkSq_E2hat_le (m := n + 1) (by omega)
  refine ⟨r + CC * Real.sqrt C₂, by positivity, fun α hα h hs hm3 => ?_⟩
  have hα0 : 0 < α := hα.1
  have hCSQ := hCSQunif α hα
  have hE2 := hE2unif α (by linarith)
  -- ## the elementary facts
  obtain ⟨hm2', hm2dth, hm2dz⟩ := Work.FTS.IPGen.HkMem_descent (by linarith : -(1 / 10 : ℝ) ≤ α) hs hm3
  have hm2 : Work.Spaces.HkMem α (n + 2) h := hm2'
  have hm1dth : Work.Spaces.HkMem α (n + 1) (Work.Spaces.Dth h) :=
    Work.FTS.IPGen.HkMem_mono_le hs.Dth (n + 1) (by omega) hm2dth
  have hm1dz : Work.Spaces.HkMem α (n + 1) (Work.Spaces.Dz h) :=
    Work.FTS.IPGen.HkMem_mono_le hs.Dz (n + 1) (by omega) hm2dz
  have hm1E2 : Work.Spaces.HkMem α (n + 1) (Work.FTS.CoercivityFix.E2hat h) :=
    HkMem_E2hat α (by linarith) hα0 (m := n + 1) (by omega) hs hm2
  -- the smoothness facts
  have hsDth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) := hs.Dth
  have hsDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) := hs.Dz
  have hsE2 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat h) :=
    smoothOpen_E2hat hs
  -- the commutator identities
  obtain ⟨hcommθ, hcommz⟩ := LhatCommOpen hs
  have hcm : CommSm α (n + 1) (IPnG 1 1 α n) := commSm_IPnG α hα0 n
  -- ## the recursion
  have hcongr1 : IPnG 1 1 α n (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h))
        (Work.Spaces.Dth h)
      = IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h))
        (Work.Spaces.Dth h) :=
    hcm.congr _ _ _ hcommθ
  have hcongr2 : IPnG 1 1 α n (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h))
        (Work.Spaces.Dz h)
      = IPnG 1 1 α n (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
          + Work.FTS.CoercivityFix.E2hat h z θ) (Work.Spaces.Dz h) :=
    hcm.congr _ _ _ hcommz
  have hadd : IPnG 1 1 α n (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
        + Work.FTS.CoercivityFix.E2hat h z θ) (Work.Spaces.Dz h)
      = IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h)) (Work.Spaces.Dz h)
        + IPnG 1 1 α n (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h) :=
    hcm.add _ _ _ ⟨q0Sm_Lhat hsDz (n + 1), q0Sm_of_smoothOpen hsE2 (n + 1),
      q0Sm_of_smoothOpen hsDz (n + 1), Lhat_mem α hα0 (n + 1) hsDz hm2dz, hm1E2, hm1dz⟩
  -- ## the induction hypotheses
  have hIH1 := IHr α hα h hs hm2
  have hIH2 := IHr α hα (Work.Spaces.Dth h) hsDth hm2dth
  have hIH3 := IHr α hα (Work.Spaces.Dz h) hsDz hm2dz
  -- ## the correction
  have hcorr : -CC * Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h
      ≤ IPnG 1 1 α n (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h) := by
    have hcs := hCSQ (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h)
      (q0Sm_of_smoothOpen hsE2 (n + 1)) (q0Sm_of_smoothOpen hsDz (n + 1)) hm1E2 hm1dz
    have hE2b := hE2 h hs hm2
    have hDzb : Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz h)
        ≤ Work.Spaces.HkSq α (n + 2) h := HkSq_Dz_le_succ' α (n + 1) hs hm2
    have hcover := lo_IPnG α hα0 (n + 1) h hs hm2
    -- the two norms are bounded by `√(C₂ · HkSq α (n+2) h)` and `√(HkSq α (n+2) h)`
    have hn1 : Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
        ≤ Real.sqrt C₂ * Real.sqrt (Work.Spaces.HkSq α (n + 2) h) := by
      rw [Work.Spaces.HkNorm, ← Real.sqrt_mul hC₂.le]
      exact Real.sqrt_le_sqrt hE2b
    have hn2 : Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)
        ≤ Real.sqrt (Work.Spaces.HkSq α (n + 2) h) := by
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt hDzb
    have hprod := mul_le_mul hn1 hn2 (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C₂) (Real.sqrt_nonneg _))
    have hkey : Real.sqrt C₂ * Real.sqrt (Work.Spaces.HkSq α (n + 2) h)
        * Real.sqrt (Work.Spaces.HkSq α (n + 2) h)
        = Real.sqrt C₂ * Work.Spaces.HkSq α (n + 2) h := by
      rw [mul_assoc, Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α (n + 2) h)]
    rw [hkey] at hprod
    have hfinal : CC * Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
          * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)
        ≤ CC * Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h := by
      calc CC * Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
            * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)
          = CC * (Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
              * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)) := by ring
        _ ≤ CC * (Real.sqrt C₂ * Work.Spaces.HkSq α (n + 2) h) :=
            mul_le_mul_of_nonneg_left hprod hCC.le
        _ ≤ CC * (Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcover (Real.sqrt_nonneg C₂))
              hCC.le
        _ = CC * Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h := by ring
    have hcs' := abs_le.mp hcs
    linarith [hcs'.1, hfinal]
  -- ## the recursion rewritten and the final arithmetic
  have hrec : IPnG 1 1 α (n + 1) (Work.FTS.CoercivityFix.Lhat h) h
      = IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat h) h
        + IPnG 1 1 α n (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dth h)
        + IPnG 1 1 α n (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dz h) := by
    simp only [IPnG_succ, Work.Coercivity.HkIPStep, one_mul]
  have hdiag : IPnG 1 1 α (n + 1) h h
      = IPnG 1 1 α n h h + IPnG 1 1 α n (Work.Spaces.Dth h) (Work.Spaces.Dth h)
        + IPnG 1 1 α n (Work.Spaces.Dz h) (Work.Spaces.Dz h) := by
    simp only [IPnG_succ, Work.Coercivity.HkIPStep, one_mul]
  rw [hrec, hcongr1, hcongr2, hadd, hdiag]
  rw [hdiag] at hcorr
  nlinarith [hIH1, hIH2, hIH3, hcorr]

end Work.FTS.StrongPersist.H6Aux
