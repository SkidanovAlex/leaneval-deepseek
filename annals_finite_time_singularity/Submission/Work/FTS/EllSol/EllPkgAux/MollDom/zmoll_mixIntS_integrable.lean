import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.StripAdm
import Submission.Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.indicatorLog_integrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mixIntS_zmoll_le_indicator

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The `∂_θ²`-slice functional `ttIntS` is pointwise nonnegative. -/
theorem ttIntS_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Work.EllipticEst.Core.ttIntS u z := by
  rw [Work.EllipticEst.Core.ttIntS]
  refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae ?_)
  exact MeasureTheory.ae_restrict_of_forall_mem
    (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))

/-- `mixIntS Φ 0 = 0` because the radial weight vanishes at `z = 0`. -/
theorem mixIntS_zero (u : ℝ → ℝ → ℝ) : Work.EllipticEst.Core.mixIntS u 0 = 0 := by
  rw [Work.EllipticEst.Core.mixIntS, Work.Spaces.w]
  norm_num

/-- **Integrability of the mixed functional of the log-mollified datum** (this is conjunct 4 of
`Work.FTS.EllSol.EllPkgAux.mollDom_fts`).

For `G` in the trace class with honest functionals and `δ, ε ∈ (0,1/2]`,

  `IntegrableOn (fun z => ∫_θ (D_z ∂_θ (zmoll G δ ε)(z,θ))² σ_η(θ) · w(z)²) Iz`.

Here the constant may depend on `δ, ε` (only finiteness/integrability is claimed).

Intended route: `D_z ∂_θ Φ = ∂_θ (D_z Φ)` (Clairaut, `Φ = zmoll G δ ε` is `C^∞` on the strip by
`mollAdm`), then the log-mollification commutation and the `θ`-fold
`D_z Φ(z,θ) = ∫_t sKer δ (log z - t) (∫_{Iθ} km ε θ s D_zG (e^t) s ds) dt`
(`km` the signed three-image kernel), whose `θ`-derivative is
`∂_θ (D_z Φ)(z,θ) = ∫_t sKer δ (log z - t)(∫_{Iθ} ∂_θ km ε θ s · D_zG (e^t) s ds)dt`
(derivative on the kernel, so that only `∫_{Iθ}|D_zG w s| ds < ∞` — available from
`SliceHonestOpen G` — is needed).  Cauchy–Schwarz in `s` with the splitting
`∂_θ km ε θ s = (∂_θ km ε θ s σ_η(s)^{-1/2})·σ_η(s)^{1/2}` gives
`(∫_s ∂_θ km · D_zG)² ≤ A_ε(θ) · ∫_s σ_η(s)(D_zG w s)² ds` with `A_ε(θ) = ∫_{Iθ}(∂_θ km ε θ s)² σ_η(s)^{-1} ds`,
and `A_ε(θ) ≤ C/ε³` uniformly in `θ` (since `|∂_θ km| ≤ 3 sup|sKerd ε| ≤ C/ε²` and
`σ_η^{-1} = sin(2·)^{η} ≤ 1`).  Then Jensen in `t` (the kernel `sKer δ` is a probability density),
integrate `θ` against `σ_η` (finite measure), and finally integrate over `z` with the weight
comparison `w(z)² ≤ 5 w(e^t)²` (`wExpCmp`) and the change of variables `y = e^t`, which bounds the
whole thing by `(C'/ε³) ∫_z w(z)² ∫_θ σ_η(θ)(D_zG z θ)² = (C'/ε³) ∫ dIntS G < ∞` (this is
`FourInts G`).  Hence (nonnegative, measurable) the functional is integrable. -/
theorem zmoll_mixIntS_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    MeasureTheory.IntegrableOn (fun z : ℝ =>
      Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) Work.Spaces.Iz := by
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  have hPr : Work.FTS.EllSol.EllPkgAux.Params δ ε := ⟨hε0, hε1, hδ0, hδ1⟩
  set Φ : ℝ → ℝ → ℝ := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε with hΦ
  -- strip-admissibility of the mollified datum (this is `mollAdm`)
  have hstrip : Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε :=
    Work.FTS.EllSol.EllPkgAux.MollAssem.mollAdmMFA G hT hF δ ε hPr
  -- hence it is `C^∞` on the open quadrant, so the slice functional is a.e. strongly measurable
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.FTS.EllSol.EllPkgAux.Strp := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ⟨hp1, by linarith, by linarith [hp3, Real.pi_pos]⟩
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => (hstrip.1 n).mono hsub)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ =>
      Work.EllipticEst.Core.mixIntS Φ z) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := Work.Blocks.StripMajorantAux.aesm_mixIntS_dzIter hsm 0
    simpa only [Work.Spaces.DzIter_zero] using h
  -- the pointwise domination by the logarithmic window average of `ttIntS G`
  obtain ⟨C, hC, hbound⟩ :=
    Work.FTS.EllSol.EllPkgAux.MollDom.mixIntS_zmoll_le_indicator G hT hF δ ε hPr
  -- the majorant is integrable on `(0,∞)`
  have htt : MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z)
      (Set.Ioi (0 : ℝ)) := hF.2.2.1.mono_set Set.Ioi_subset_Ici_self
  have hMajIoi : MeasureTheory.IntegrableOn (fun z : ℝ => C * ∫ t : ℝ,
      (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))
      (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllSol.EllPkgAux.MollDom.indicatorLog_integrable hδ0 htt (ttIntS_nonneg G)).const_mul C
  have hMajIz : MeasureTheory.IntegrableOn (fun z : ℝ => C * ∫ t : ℝ,
      (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))
      Work.Spaces.Iz := by
    have hEq : (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    rw [Work.Spaces.Iz]
    show MeasureTheory.Integrable (fun z : ℝ => C * ∫ t : ℝ,
      (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
    rw [hEq]
    exact hMajIoi
  -- assemble with the pointwise domination
  refine MeasureTheory.Integrable.mono' hMajIz haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)]
    with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.MollAssem.mixIntS_nonneg_mfa Φ z)]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · rw [← h0, mixIntS_zero]
    refine mul_nonneg hC.le (MeasureTheory.integral_nonneg (fun t => ?_))
    split_ifs with ht
    · exact ttIntS_nonneg G _
    · exact le_rfl
  · exact hbound z hpos

end Work.FTS.EllSol.EllPkgAux.MollDom
