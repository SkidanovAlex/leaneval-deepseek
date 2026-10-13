import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksWlInf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksTorWlInf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksMixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

theorem ksDat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInfMem α 6 (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 6 (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α ∧
    Work.Spaces.WlInfMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α ∧
    (∀ (A : Work.FTS.Galerkin.Fn),
        (A = (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ∨
         A = (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z)) →
        ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ C * α * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := ksWlInf
  obtain ⟨C2, hC2pos, hC2⟩ := ksTorWlInf
  obtain ⟨C3, hC3pos, hC3⟩ := ksMixed
  refine ⟨max (max C1 C2) C3, ?_, ?_⟩
  · exact lt_of_lt_of_le hC1pos (le_trans (le_max_left C1 C2) (le_max_left (max C1 C2) C3))
  · intro α hαI
    obtain ⟨hα, hα1⟩ := hαI
    -- identify `FK (Fstar α)` with its explicit value `α·2z/(1+z)²`
    have hKF : (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z)
        = (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) := by
      funext z θ
      exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1
    have hKFt : (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z)
        = (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2))) := by
      funext z θ
      rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    rw [hKF, hKFt]
    obtain ⟨hA1mem, hA1le⟩ := hC1 α ⟨hα, hα1⟩
    obtain ⟨hA2mem, hA2le⟩ := hC2 α ⟨hα, hα1⟩
    have hA3 := hC3 α ⟨hα, hα1⟩
    have hαnn : 0 ≤ α := le_of_lt hα
    have hC1max : C1 ≤ max (max C1 C2) C3 :=
      le_trans (le_max_left C1 C2) (le_max_left (max C1 C2) C3)
    have hC2max : C2 ≤ max (max C1 C2) C3 :=
      le_trans (le_max_right C1 C2) (le_max_left (max C1 C2) C3)
    have hC3max : C3 ≤ max (max C1 C2) C3 := le_max_right (max C1 C2) C3
    refine ⟨?_, ?_, hA1mem, ?_, hA2mem, ?_, ?_⟩
    · exact SmoothOpen_KsFun α
    · exact SmoothOpen_KsTor α
    · calc Work.Spaces.WlInf α 6 (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2))
          ≤ C1 * α := hA1le
        _ ≤ max (max C1 C2) C3 * α := mul_le_mul_of_nonneg_right hC1max hαnn
    · calc Work.Spaces.WlInf α 6
            (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))
          ≤ C2 * α := hA2le
        _ ≤ max (max C1 C2) C3 * α := mul_le_mul_of_nonneg_right hC2max hαnn
    · intro A hA j i hji z θ hz hθ1 hθ2
      have hbound := hA3 A hA j i hji z θ hz hθ1 hθ2
      have hΦnn : 0 ≤ (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
          else 1) := by
        by_cases hi : 1 ≤ i
        · rw [if_pos hi]
          have hs : 0 ≤ Real.sin (2 * θ) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ1]) (by linarith [hθ2, Real.pi_pos])
          exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)
        · rw [if_neg hi]
          norm_num
      have hznn : 0 ≤ z / (1 + z) := div_nonneg (le_of_lt hz) (by linarith)
      have hfacnn : 0 ≤ α * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) :=
        mul_nonneg (mul_nonneg hαnn hznn) hΦnn
      calc |Work.Spaces.mixed j i A z θ|
          ≤ C3 * α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) :=
            hbound
        _ = C3 * (α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) := by
            ring
        _ ≤ max (max C1 C2) C3 * (α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) :=
            mul_le_mul_of_nonneg_right hC3max hfacnn
        _ = max (max C1 C2) C3 * α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
            ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
