import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_local
import Submission.Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_N
import Submission.Work.FTS.EllipticEst.remov.AeI1CSPiece
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen
import Submission.Work.FTS.EllipticEst.H2W.SlotA.weightedNLePp
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Clairaut identity for the mixed slot -/

/-- `V u = ∂_θ(U u)` on the open quadrant (Clairaut). -/
theorem V_eq_deriv {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Iθo) :
    V u z θ = deriv (fun θ' => U u z θ') θ := by
  have hqd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt (hqd.mem_nhds ⟨hz, hθ⟩)
  have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
  have h2 : deriv (fun θ' => U u z θ') θ = z * Work.Spaces.pz (Work.Spaces.pth u) z θ := by
    have hfun : (fun θ' => U u z θ') = (fun θ' => z * Work.Spaces.pz u z θ') := rfl
    rw [hfun, deriv_const_mul_field]
    rw [hcl]
    show z * deriv (fun y => Work.Spaces.pz u z y) θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ
    rfl
  rw [h2]
  rfl

/-- The two ways of writing the transfer pairing agree. -/
theorem cw_swap (u : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u)
      = Work.FTS.EllipticEst.AngSecond.IP (U u)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * BB u z θ) := by
  rw [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.IP]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

theorem I1Paper_mixed : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ) →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  refine ⟨2, by norm_num, ?_⟩
  intro α u G hAe hU hV
  have hB : Work.Spaces.HkMem α 0 (BB u) := hAe.memAng2
  have hAA : Work.Spaces.HkMem α 0 (AA u) := hAe.memRad2
  have hId := identity_local hAe hU hV hAA hB
  have hPk := HkSq_pth_grad α u hAe.smooth
  have hha := hardy_N hAe hU hV
  have hcs := Work.FTS.EllipticEst.remov.AeI1CSPiece α u G hAe hU
  have hsw : Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.Spaces.pthIter 2 u z θ) := cw_swap u
  set PP : ℝ := ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
      * ∫ θ in Set.Ioo 0 (Real.pi / 2), (V u z θ) ^ 2 * sigE θ with hPPdef
  set NN : ℝ := ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
      * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ with hNNdef
  set Aa : ℝ := Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
      (Work.FTS.EllipticEst.H2W.Ae.grad u) with hAadef
  set Bb : ℝ := Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
      (Work.Spaces.pthIter 2 u) with hBbdef
  set DD : ℝ := Work.FTS.EllipticEst.AngSecond.IP (AA u) (BB u) with hDDdef
  set CC : ℝ := Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u) with hCCdef
  have hID : DD = PP - 2 * Work.Spaces.eta * Aa
      - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * NN - CC := hId
  have hNle : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * NN
      ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * PP := hha
  have hCCle : CC ≤ 2 * Real.sqrt Aa * Real.sqrt Bb := by
    have h1 : CC = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.Spaces.pthIter 2 u z θ) := hsw
    rw [h1, hAadef, hBbdef]
    have hcs' : - (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.Spaces.pthIter 2 u z θ))
        ≥ - 2 * (Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u))) := hcs
    linarith [hcs']
  have hAa0 : 0 ≤ Aa := by
    rw [hAadef]; exact Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _
  have hBb0 : 0 ≤ Bb := by
    rw [hBbdef]; exact Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _
  have hsa : 0 ≤ Real.sqrt Aa := Real.sqrt_nonneg _
  have hsb : 0 ≤ Real.sqrt Bb := Real.sqrt_nonneg _
  have hmain : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * PP
      - 2 * (Aa + Real.sqrt Aa * Real.sqrt Bb) ≤ DD := by
    have hkey : (1 : ℝ) - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)
        = (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
      rw [Work.Spaces.eta]; norm_num
    have h2η : 2 * Work.Spaces.eta * Aa ≤ 2 * Aa := by
      nlinarith [hAa0, Work.Spaces.eta_lt_one, Work.Spaces.eta_nonneg]
    have hss : 0 ≤ Real.sqrt Aa * Real.sqrt Bb := mul_nonneg hsa hsb
    have step1 : (1 - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * PP
        - 2 * Work.Spaces.eta * Aa - 2 * (Real.sqrt Aa * Real.sqrt Bb) ≤ DD := by
      linarith [hID, hNle, hCCle]
    have step2 : (1 - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * PP
        = ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * PP := by rw [hkey]
    linarith [step1, step2, h2η]
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hfin2 : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (α ^ 2 * PP)
      - 2 * α ^ 2 * (Aa + Real.sqrt Aa * Real.sqrt Bb) ≤ α ^ 2 * DD := by
    have hmul := mul_le_mul_of_nonneg_left hmain hα2
    linarith [hmul]
  rw [hPk]
  rw [show (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) = AA u from rfl,
    show Work.Spaces.pthIter 2 u = BB u from rfl]
  rw [← hDDdef]
  exact hfin2

end
end Work.FTS.EllipticEst.AeI1Fts
