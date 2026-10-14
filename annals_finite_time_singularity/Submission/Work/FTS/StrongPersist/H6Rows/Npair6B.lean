import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumBounds
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans_exists
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS_EllLimOK.ThetaJets.Theta_jets_le
import Submission.Work.H2.T1Q.IbpCutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows

theorem Npair6B : ∀ Ce : ℝ, 0 < Ce → ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      Work.Spaces.HkMem α 6
          (Work.Construction.N α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ)) ∧
      |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ))
          (Work.FTS.Galerkin.slice g τ)|
        ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
            * (1 + Work.FTS.StrongPersist.Sq6 α (Work.FTS.Galerkin.slice g τ)) := by
  intro Ce _hCe
  obtain ⟨CB, hCBpos, hBnd⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumBounds Ce
  obtain ⟨CIP, hCIPpos, hIP6u⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.pairing_le_of_slotBoundB (Ce := Ce)
  refine ⟨CIP * CB + 1, 1, ?_, one_pos, le_rfl, ?_⟩
  · nlinarith [hCIPpos, hCBpos]
  · intro α hαIoc g Φ τ M Cs E Φs hτ hctx
    have hα0 : 0 < α := hαIoc.1
    have hα1 : α ≤ 1 := hαIoc.2
    obtain ⟨hmemNsum, hsmNsum⟩ :=
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData Ce α hαIoc g Φ τ M Cs E Φs hτ hctx
    have hslot := hBnd α hαIoc g Φ τ M Cs E Φs
    have hsplit := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6 hα0 hα1
      (f := Work.FTS.Galerkin.slice g τ) (Ef := E (Work.FTS.Galerkin.slice g τ)) (Φs := Φs)
      hctx.hreg hctx.hell.hell.smooth hctx.hell.hstar.smooth
    refine ⟨?_, ?_⟩
    · -- first conjunct: `HkMem` transfers across the (pointwise) splitting identity.
      refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 hmemNsum ?_
      intro z hz θ hθ
      have h1 := hsplit.1 z θ ⟨hz, hθ.1, hθ.2⟩
      rw [hctx.hell.hsum]
      exact h1.symm
    · -- second conjunct: the per-slot bound on `nsum` fed into the pairing reduction.
      have hP4 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
      have hQ4 : 0 ≤ (1 + M) ^ 4 := by positivity
      have hpow : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
      have hT : 0 ≤ 1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ) := by
        have hh := Work.Spaces.HkSq_nonneg α 6 (Work.FTS.Galerkin.slice g τ)
        linarith
      have hB0 : 0 ≤ CB * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCBpos.le hpow) hP4) hQ4) hT
      have hIP := hIP6u α hαIoc g Φ τ M Cs E Φs
        (CB * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)))
        hτ hctx hsmNsum hB0 (fun a b ρ hab hleaf => hslot a b ρ hτ hctx hab hleaf)
      have hstep : CIP * (CB * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)))
          ≤ (CIP * CB + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) := by
        calc CIP * (CB * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)))
            = (CIP * CB) * (α ^ (-(10 : ℝ)) * ((1 + |Ce| + |Cs|) ^ 4
              * ((1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))))) := by
              ring
          _ ≤ (CIP * CB + 1) * (α ^ (-(10 : ℝ)) * ((1 + |Ce| + |Cs|) ^ 4
              * ((1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))))) :=
              mul_le_mul_of_nonneg_right (by linarith)
                (mul_nonneg hpow (mul_nonneg hP4 (mul_nonneg hQ4 hT)))
          _ = (CIP * CB + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) := by
              ring
      exact hIP.trans hstep

end Work.FTS.StrongPersist.H6Rows
