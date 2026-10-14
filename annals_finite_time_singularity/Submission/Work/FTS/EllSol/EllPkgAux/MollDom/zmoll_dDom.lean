import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDDomDomIntegrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzComm
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.pz_mixed_mul_le_4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

local notation "Iθ" => Work.Spaces.Iθ

/-- **Pointwise domination of the `D_z`-slot of the log-mollified datum** (the same statement as
`zmoll_ddDom` with one `D_z` instead of two):

  `|D_zΦ(z,θ)| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |D_zG (e^t) s| ds) dt`

for a.e. `z > 0` and all `θ ∈ Iθ`, `Φ = zmoll G δ ε`, `G` in the trace class with honest
functionals, `δ, ε ∈ (0,1/2]`.  Same route as `zmoll_ddDom` with `j = 1`:  the fold
`D_z(thMoll G ε) w θ = ∫_{Iθ} km ε θ s D_zG w s ds` (`km ε θ s = sKer ε (θ-s) - sKer ε (θ+s) - sKer ε (θ+s-π)`,
a.e. in `w`, from the AC/Fubini argument) and the log-mollification commutation
`D_z(zmoll G δ ε) z θ = ∫_t sKer δ (log z - t) D_z(thMoll G ε) (e^t) θ dt` (a.e. in `z`), then
`|km| ≤ KJ`.  The box integrability `∫_{[a,b]}∫_{Iθ}|D_zG| < ∞` (`0 < a ≤ b`) follows from
`SliceHonestOpen G`. -/
theorem zmoll_dDom (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z θ|
          ≤ ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
              (∫ s in Work.Spaces.Iθ,
                Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G (Real.exp t) s|) := by
  -- `hP` is consumed by the `obtain` below but is needed again in the `rw`; keep a copy.
  have hP' := hP
  -- the `L¹`-bounds for the two angular slice norms (the dominating function `F`)
  obtain ⟨C, hC0, hCint1, hC1, hCint2, hC2⟩ :=
    Work.FTS.EllSol.EllPkgAux.MollDom.sliceL1_bound hT hF
  -- continuity of the slices on the *closed* angular interval
  have hcont : ∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => G w s) Iθ :=
    fun w hw => Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn G hT hw
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  obtain ⟨hS, h0, hπ, -, -, -, -, hhon⟩ := hT
  -- nonnegativity of the two summands of `F`
  have hdnn : ∀ w : ℝ, 0 ≤ Work.EllipticEst.Core.dIntS G w := fun w => by
    rw [Work.EllipticEst.Core.dIntS]
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc ?_)
    intro s hs
    refine mul_nonneg (sq_nonneg _) ?_
    refine Real.rpow_nonneg ?_ _
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1])
      (by linarith [hs.2, Real.pi_pos])
  have hMGnn : ∀ w : ℝ, 0 ≤ Work.FTS.EllSol.EllPkgAux.MGf G w := fun w => by
    simp only [Work.FTS.EllSol.EllPkgAux.MGf]
    have h1 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := Real.sqrt_nonneg _
    linarith
  let F : ℝ → ℝ := fun w => C * Work.FTS.EllSol.EllPkgAux.MGf G w
    + C * (1 + Work.EllipticEst.Core.dIntS G w)
  have hFint : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F (Set.Icc a b) :=
    fun a b ha hab => (hCint1 a b ha hab).add (hCint2 a b ha hab)
  have hFb : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |G w s| ≤ F w :=
    fun w hw => le_trans (hC1 w hw)
      (le_add_of_nonneg_right (mul_nonneg hC0.le (by linarith [hdnn w])))
  have hFb' : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Work.Spaces.Dz G w s| ≤ F w :=
    fun w hw => le_trans (hC2 w hw) (le_add_of_nonneg_left (mul_nonneg hC0.le (hMGnn w)))
  have hIntg' : ∀ w : ℝ, 0 < w → IntegrableOn (fun s : ℝ => Work.Spaces.Dz G w s) Iθ :=
    fun w hw => Work.FTS.EllSol.EllPkgAux.MollDom.dzSliceHonest G hS hhon w hw
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
  intro θ hθ
  -- the `z`-derivative of the log-mollified datum, in folded (kernel) form
  rw [Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_dz_comm (u := G) hP' h0 hπ hcont hS.continuousOn
    (fun w hw s hs => hS.hasDerivAt_slice hs hw) hS.pz.continuousOn hFint hFb hFb' hIntg'
    z hz θ hθ]
  -- the dominating function of the target is honest
  have hInt : Integrable (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
      * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
          * |Work.Spaces.Dz G (Real.exp t) s|)) :=
    Work.FTS.EllSol.EllPkgAux.MollDom.zmollDDomDomIntegrable G hS hhon hF δ ε hδ0 hε0 hε1
      z θ hz hθ
  -- the folded kernel is dominated by `KJ`
  have hpt : ∀ t : ℝ,
      |∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * Work.Spaces.Dz G (Real.exp t) s|
        ≤ ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
            * |Work.Spaces.Dz G (Real.exp t) s| :=
    fun t => Work.FTS.EllSol.EllPkgAux.abs_kernSlot_le_kjSlot hε0
      (fun s => Work.Spaces.Dz G (Real.exp t) s) (hIntg' (Real.exp t) (Real.exp_pos t))
  calc |∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
        * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
            * Work.Spaces.Dz G (Real.exp t) s)|
      ≤ ∫ t : ℝ, |Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
              * Work.Spaces.Dz G (Real.exp t) s)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
          * |∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
              * Work.Spaces.Dz G (Real.exp t) s| := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ0 _)]
    _ ≤ ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
              * |Work.Spaces.Dz G (Real.exp t) s|) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ hInt ?_
        · exact Filter.Eventually.of_forall fun t =>
            mul_nonneg (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ0 _) (abs_nonneg _)
        · exact Filter.Eventually.of_forall fun t =>
            mul_le_mul_of_nonneg_left (hpt t) (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ0 _)

end

end Work.FTS.EllSol.EllPkgAux.MollDom
