/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/LedgerO.lean` — the arithmetic ledger of the level-one
coercivity, on the **open** class

`CoercivityFix/Coer1T/SlotsDzGam.lean` contains `ledger`: the pure-arithmetic assembly of the four
slot estimates (`D_z`, `η`, `W`, `γ`) into the level-one coercivity
`HkSq α 1 f ≤ H1IP α (𝓛_Γ^T f) f`.  Its only class-dependent input is the identity
`HkSq α 1 f = EDz f + EfEta f + EDth α f`, which the frozen chapter takes from `Coer1.HkSq_one_eq`
(needing `SmoothQuad f`).

This file is the open-class transcription: the same ledger with the identity from
`StrongPersist.HkSq_one_eq_SO` (which needs only `SmoothOpen f` and `HkMem α 1 f`).  The four
slot estimates stay as hypotheses, so the lemma is *independent* of the order in which the slot
ports land; it is the assembly point of the open-class `coer1_LGammaT`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The ledger**: the four slot estimates, rescaled by the coefficients of `H1IP`, dominate
the `ℋ¹`-energy. -/
theorem ledger_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm1 : Work.Spaces.HkMem α 1 f)
    (hED : Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f)
    (hEL : Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f)
    (hP : (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f))
    (hQ : (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f + Work.Coercivity.Ef f)
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f)
    (hR : (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f)
    (hS : (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f
        - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hHk' := Work.FTS.StrongPersist.HkSq_one_eq_SO α hso hm1
  have hHk : Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EDz f + Work.Coercivity.EfEta f + Work.Coercivity.EDth α f := by
    rw [hHk']; ring
  rw [hHk, Work.Coercivity.H1IP]
  -- the four slot bounds, rescaled by the coefficients of `H1IP`
  have h1 : (2 : ℝ) * Work.Coercivity.EDz f - 1000 * Work.Coercivity.EfEta f
        - 1000 * Work.Coercivity.EDth α f - 10 ^ 13 * Work.Coercivity.Ef f
      ≤ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
    have := mul_le_mul_of_nonneg_left hP (show (0 : ℝ) ≤ 10 by norm_num)
    linarith [this]
  have h2 : 2 * 10 ^ 9 * Work.Coercivity.EfEta f
        - 17 * 10 ^ 15 * Work.Coercivity.Ef f - 10 ^ 15 * Work.Coercivity.EDth α f
      ≤ (10 : ℝ) ^ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f := by
    have hb := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ (10 : ℝ) ^ 10 by norm_num)
    have hEL' : (10 : ℝ) ^ 15 * Work.Coercivity.EL12z f
        ≤ 16 * 10 ^ 15 * Work.Coercivity.Ef f := by
      have := mul_le_mul_of_nonneg_left hEL (show (0 : ℝ) ≤ (10 : ℝ) ^ 15 by norm_num)
      linarith [this]
    have hED' : (10 : ℝ) ^ 15 * Work.Coercivity.EDthW f
        ≤ (10 : ℝ) ^ 15 * Work.Coercivity.EDth α f :=
      mul_le_mul_of_nonneg_left hED (by norm_num)
    have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
      rw [Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]; exact Work.FTS.CoercivityFix.Coer1.EnOne_nonneg f
    linarith [hb, hEL', hED', hEfnn]
  have h3 : 2 * 10 ^ 16 * Work.Coercivity.Ef f - 10 ^ 20 * Work.Coercivity.EDth α f
      ≤ (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f := by
    have hb := mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ (10 : ℝ) ^ 17 by norm_num)
    have hED' : (10 : ℝ) ^ 20 * Work.Coercivity.EDthW f
        ≤ (10 : ℝ) ^ 20 * Work.Coercivity.EDth α f :=
      mul_le_mul_of_nonneg_left hED (by norm_num)
    linarith [hb, hED']
  have h4 : ((17 / 40 - 1 / 100) * 10 ^ 21) * Work.Coercivity.EDth α f
        - 10 ^ 15 * Work.Coercivity.Ef f
      ≤ (10 : ℝ) ^ 21 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f) := by
    have hb := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    linarith [hb]
  have e1 : 0 ≤ Work.Coercivity.EDz f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDz_eq_En]; exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e2 : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Work.FTS.CoercivityFix.Coer1.EfEta_eq_En]; exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e3 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]; exact Work.FTS.CoercivityFix.Coer1.EnOne_nonneg f
  have e4 : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]; exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  linarith [h1, h2, h3, h4, e1, e2, e3, e4]

end Work.FTS.StrongEps.EpsE4Thr
