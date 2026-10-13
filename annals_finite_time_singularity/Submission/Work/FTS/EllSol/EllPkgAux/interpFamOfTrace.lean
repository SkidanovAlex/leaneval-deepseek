/-
# `Work.FTS.EllSol.EllPkgAux.interpFamOfTrace`

The family (`i = 0`) form of the mixed-derivative interpolation, in the trace-class formulation
`Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt` (instead of the general open-class
`Work.EllipticEst.Core.i0Aux.InterpOpen`, which is blocked by the jump phenomenon).

The proof is the proof of `Work.EllipticEst.LHSDecomp.i0Family_le_of_interpOpen` verbatim,
with the two extra trace hypotheses supplied for `G = D_z^r V` from the family's trace
hypothesis (`j = r` for `G`, `j = r + 1` for `D_zG`, both `≤ k + 1`).

The conclusion is `Work.FTS.EllSol.PkgK5.InterpFam k`, so that the *proved*
`Work.FTS.EllSol.PkgK5.wall_of_interp` (`InterpFam k → WallK5 k`) applies to it.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.EllipticEst.LHSDecomp.i0Family_le_of_interpOpen
import Submission.Work.FTS.EllSol.PkgK5.WallDefs
import Submission.Work.FTS.EllSol.EllPkgAux.TraceStmt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- **The family interpolation in the trace class.**  From the single-function trace-class
estimate `InterpOpenTraceStmt` one gets the `i = 0` family bound of `InterpFam k`: exactly
`i0Family_le_of_interpOpen` with the general `InterpOpen` replaced by the trace-class version and
the (unused) extra trace hypothesis carried along. -/
theorem interpFamOfTrace {C : ℝ} (hC : 0 < C)
    (hopen : InterpOpenTraceStmt C) (k : ℕ) : Work.FTS.EllSol.PkgK5.InterpFam k := by
  refine ⟨((k : ℝ) + 1) * C, by positivity, ?_⟩
  intro α V hα hα14 hsm h0 hpi htrace hdd htt hd
  set R : ℝ := α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
      + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    have h1 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V)
    have h2 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have h3 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V)
    have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
    have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    nlinarith [mul_nonneg hα4 h1, mul_nonneg hα2 h3]
  have key : ∀ r ∈ Finset.range (k + 1),
      α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) ≤ C * R := by
    intro r hr
    have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    by_cases hhon : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        Work.Spaces.Iz
    · have hc := hopen α (Work.Spaces.DzIter r V) hα hα14 (hsm.DzIter r)
        (Work.EllipticEst.Core.i0Aux.DzIter_zero_theta h0 r)
        (Work.EllipticEst.Core.i0Aux.DzIter_pi_theta hpi r)
        (fun z hz => (htrace r (by omega) z hz).1)
        (fun z hz => (htrace r (by omega) z hz).2)
        (fun z hz => (htrace (r + 1) (by omega) z hz).1)
        (fun z hz => (htrace (r + 1) (by omega) z hz).2)
        (Work.EllipticEst.Core.i0Aux.sliceHonestOpen_dzIter hsm hdd htt hd hrk) hhon
        (Work.EllipticEst.Core.i0Aux.ddIntS_integrableOn hsm hdd hrk)
        (Work.EllipticEst.Core.i0Aux.ttIntS_integrableOn hsm htt hrk)
        (Work.EllipticEst.Core.i0Aux.dIntS_integrableOn hsm hd hrk)
      refine le_trans hc (mul_le_mul_of_nonneg_left ?_ hC.le)
      have h1 := Work.EllipticEst.Core.i0Aux.ddIntS_integral_le_HkSq (V := V) hdd hrk
      have h2 := Work.EllipticEst.Core.i0Aux.ttIntS_integral_le_HkSq (V := V) hsm htt hrk
      have h3 := Work.EllipticEst.Core.i0Aux.dIntS_integral_le_HkSq (V := V) hd hrk
      rw [hR]
      have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
      have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hα4, h2, mul_le_mul_of_nonneg_left h3 hα2]
    · rw [MeasureTheory.integral_undef hhon, mul_zero]
      exact mul_nonneg hC.le hRnn
  have hsum : (∑ r ∈ Finset.range (k + 1),
        α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      ≤ ((k : ℝ) + 1) * (C * R) := by
    calc (∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
        ≤ ∑ _r ∈ Finset.range (k + 1), C * R := Finset.sum_le_sum key
      _ = ((k : ℝ) + 1) * (C * R) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc α ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      = ∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) := by
        rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) + 1) * (C * R) := hsum
    _ = ((k : ℝ) + 1) * C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
        rw [hR]
        ring

/-- **`InterpFam k` from the existential trace-class estimate.** -/
theorem interpFamOfTrace_exists
    (h : ∃ C : ℝ, 0 < C ∧ InterpOpenTraceStmt C) (k : ℕ) :
    Work.FTS.EllSol.PkgK5.InterpFam k := by
  obtain ⟨C, hC, hstmt⟩ := h
  exact interpFamOfTrace hC hstmt k

end Work.FTS.EllSol.EllPkgAux
