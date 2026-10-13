/-
# `Work.FTS.StrongPersist.H6Aux.Assembly` — the one-sided level-six linear bound

This is the capstone: the level-six one-sided bound `H6Lin` for the concrete pairing
`IP6 1 1 … 1`, i.e. the existence of `α₂, CL > 0` with

  `IP6 1 … 1 α (linPart α f) f ≤ CL · |f|²_{ℋ⁶}`

for every `α ∈ (0,α₂]` and every `f` of the class `H6Adm α` with order-seven honesty
`HkMem α 7 f`.

The proof splits the operator `𝓛_Γ^T = Lhat + Corr` (`LGammaT_eq_Lhat_add_Corr`):

* the clean part is priced by the commutator induction `R_ind`
  (`IP6 (Lhat f) f ≥ -r·IP6 f f`), and the diagonal `IP6 f f` by Cauchy–Schwarz at level six
  (`IP6 f f ≤ CC·|f|²_{ℋ⁶}`);
* the nonlocal part `Corr α f` is priced by Cauchy–Schwarz with the norm bound `Corr_HkSq6`
  (`|Corr α f|_{ℋ⁶} ≤ √Cc·|f|_{ℋ⁶}`).
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongPersist.H6Aux.Induction
import Submission.Work.FTS.StrongPersist.H6Aux.Corr_HkSq6
import Submission.Work.FTS.StrongPersist.H6Aux.q0Sm_Corr
import Submission.Work.FTS.StrongPersist.IP6Clauses

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

/-- **The one-sided level-six linear bound for `IP6 1 1 … 1`.** -/
theorem H6Lin_IP6 : ∃ α₂ CL : ℝ, 0 < α₂ ∧ 0 < CL ∧
    Work.FTS.StrongPersist.H6Lin
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α₂ CL := by
  obtain ⟨r, hr, hR⟩ := R_ind 5 le_rfl
  obtain ⟨CC, hCC, hCSQ⟩ := CSQ_IPnG_unif 5
  obtain ⟨Cc, α₂c, hCc, hα₂c, hCorr⟩ := Corr_HkSq6
  obtain ⟨α₂q, hα₂q, hq0⟩ := q0Sm_Corr
  refine ⟨min 1 (min α₂c α₂q), r * CC + CC * Real.sqrt Cc + 1, ?_, by positivity, ?_⟩
  · exact lt_min one_pos (lt_min hα₂c hα₂q)
  · intro α hα f hf hm7
    change Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
        (Work.FTS.StrongPersist.linPart α f) f
      ≤ (r * CC + CC * Real.sqrt Cc + 1) * Work.Spaces.HkSq α 6 f
    obtain ⟨hα0, hαle⟩ := hα
    have hα1 : α ≤ 1 := le_trans hαle (min_le_left _ _)
    have hαc : α ≤ α₂c := le_trans (le_trans hαle (min_le_right _ _)) (min_le_left _ _)
    have hαq : α ≤ α₂q := le_trans (le_trans hαle (min_le_right _ _)) (min_le_right _ _)
    have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
    obtain ⟨hs, hm6⟩ := hf.reg
    obtain ⟨hc_mem, hc_bd⟩ := hCorr α ⟨hα0, hαc⟩ f hf hm7
    have hq : Work.FTS.CoercivityFix.Transfer.Q0Sm 6 (Work.FTS.CoercivityFix.Corr α f) :=
      hq0 α ⟨hα0, hαq⟩ f hf hm7
    have hLmem : Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Lhat f) :=
      Lhat_mem α hα0 6 hs hm7
    have hs6 : Work.FTS.CoercivityFix.Transfer.Q0Sm 6 f :=
      Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs 6
    have hLq6 : Work.FTS.CoercivityFix.Transfer.Q0Sm 6 (Work.FTS.CoercivityFix.Lhat f) :=
      q0Sm_Lhat hs 6
    -- ## the clean part and the diagonal
    have hRf : -r * Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f
        ≤ Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.CoercivityFix.Lhat f) f :=
      hR α hαI f hs hm7
    have hdiag : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f
        ≤ CC * Work.Spaces.HkSq α 6 f := by
      have h := hCSQ α hαI f f hs6 hs6 hm6 hm6
      calc Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f
          ≤ CC * Work.Spaces.HkNorm α (5 + 1) f * Work.Spaces.HkNorm α (5 + 1) f :=
            (abs_le.mp h).2
        _ = CC * Work.Spaces.HkSq α (5 + 1) f := by
            rw [Work.Spaces.HkNorm, mul_assoc,
              Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α (5 + 1) f)]
        _ = CC * Work.Spaces.HkSq α 6 f := rfl
    -- ## the nonlocal part
    have hcorr_pt : -CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f
        ≤ Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.CoercivityFix.Corr α f) f := by
      have h := hCSQ α hαI (Work.FTS.CoercivityFix.Corr α f) f hq hs6 hc_mem hm6
      rw [abs_le] at h
      have hnc : Work.Spaces.HkNorm α 6 (Work.FTS.CoercivityFix.Corr α f)
          ≤ Real.sqrt Cc * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
        rw [Work.Spaces.HkNorm]
        have hs := Real.sqrt_le_sqrt hc_bd
        rwa [Real.sqrt_mul hCc.le] at hs
      have hprod : CC * Work.Spaces.HkNorm α (5 + 1) (Work.FTS.CoercivityFix.Corr α f)
            * Work.Spaces.HkNorm α (5 + 1) f
          ≤ CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f := by
        have hnf : Work.Spaces.HkNorm α (5 + 1) f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
        rw [hnf]
        calc CC * Work.Spaces.HkNorm α (5 + 1) (Work.FTS.CoercivityFix.Corr α f)
              * Real.sqrt (Work.Spaces.HkSq α 6 f)
            ≤ CC * (Real.sqrt Cc * Real.sqrt (Work.Spaces.HkSq α 6 f))
              * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnc hCC.le)
                (Real.sqrt_nonneg _)
          _ = CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f := by
              rw [mul_assoc, mul_assoc, mul_assoc,
                Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
      have hch := le_trans (neg_le_neg hprod) h.1
      have hgoal : -CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f
          = -(CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f) := by ring
      rwa [hgoal]
    -- ## the split
    have hsplit : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Coercivity.LGammaT α f) f
        = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.CoercivityFix.Lhat f) f
          + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
              (Work.FTS.CoercivityFix.Corr α f) f := by
      have h1 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.Coercivity.LGammaT α f) f
          = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
              (fun z θ => Work.FTS.CoercivityFix.Lhat f z θ
                + Work.FTS.CoercivityFix.Corr α f z θ) f :=
        (commSm_IPnG α hα0 5).congr _ _ _ (fun z θ _ => by
          have h := congrFun (Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α f) z
          exact congrFun h θ)
      rw [h1]
      exact (commSm_IPnG α hα0 5).add _ _ _
        ⟨hLq6, hq, hs6, hLmem, hc_mem, hm6⟩
    have hneg : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.FTS.StrongPersist.linPart α f) f
        = - Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.Coercivity.LGammaT α f) f := by
      have h : Work.FTS.StrongPersist.linPart α f
          = fun z θ => -(Work.Coercivity.LGammaT α f z θ) := rfl
      rw [h]
      exact Work.FTS.StrongPersist.IP6_neg 1 1 1 1 1 1 1 1 1 1 α
        (Work.Coercivity.LGammaT α f) f
    rw [hneg, hsplit]
    have hsqrt : 0 ≤ Real.sqrt Cc := Real.sqrt_nonneg Cc
    have hmain : -r * Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f
          - CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f
        ≤ Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.CoercivityFix.Lhat f) f
          + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
              (Work.FTS.CoercivityFix.Corr α f) f := by
      linarith [hRf, hcorr_pt]
    have hbound : -(r * CC + CC * Real.sqrt Cc + 1) * Work.Spaces.HkSq α 6 f
        ≤ -r * Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f
          - CC * Real.sqrt Cc * Work.Spaces.HkSq α 6 f := by
      nlinarith [hdiag, hr, hCC, hsqrt, Work.Spaces.HkSq_nonneg α 6 f]
    linarith [hmain, hbound]

end Work.FTS.StrongPersist.H6Aux
