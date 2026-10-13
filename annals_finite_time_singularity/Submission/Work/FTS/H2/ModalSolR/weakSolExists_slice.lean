/-
# `ModalSolR/weakSolExists_slice` — existence of the modal weak solution

The witness is the limit `Ψ = ModalSol.Psi α F` of the partial sums `ψ_N` of the mode series
`Σ_m acoeff α m F z · eFam m θ`.  The five clauses are

* local integrability: every point of the open quadrant has a closed box around it inside the
  quadrant; `Ψ` is a pointwise limit of the continuous `ψ_N` there, hence a.e. strongly
  measurable (`AEMeasurable.limsup` + `psiTrunc_tendsto_Psi`), and it is dominated by
  `C·z^{-1/2}` (`psiTrunc_bound_on`), whence integrable on the box by `Integrable.of_bound`;
* the weak identity `psi_weak_identity` (`PsiFacts`);
* the Dirichlet values `Psi_apply_zero`, `Psi_apply_pi_half` and the decay at `z → ∞`
  (domination by `C·z^{-1/2}`, which tends to `0` since `z^{-1/2} → 0` and `Ψ` vanishes at the
  endpoints);
* the a.e. continuity of the angular slices `Psi_slice_continuous` (`LimitFacts`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSolR.PsiFacts
import Submission.Work.FTS.H2.ModalSolR.LimitFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 3200000

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

theorem weakSolExists_slice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) :
    ∃ Ψ : ℝ → ℝ → ℝ,
      MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 ∧
      (∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
        HasCompactSupport (Function.uncurry φ) →
        tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
        (∫ p in Work.FTS.EllipticEst.Q0,
            Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
              * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
          = ∫ p in Work.FTS.EllipticEst.Q0,
              F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) ∧
      (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ContinuousOn (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2))) := by
  classical
  refine ⟨Work.FTS.H2.ModalSol.Psi α F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ## local integrability
    intro p hp
    obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    set ε : ℝ := min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) with hεdef
    have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hεz : ε ≤ p.1 / 2 := min_le_left _ _
    have hεθ : ε ≤ p.2 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hεπ : ε ≤ (π / 2 - p.2) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    set B : Set (ℝ × ℝ) := Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε)
      with hBdef
    have hBQ : B ⊆ Work.FTS.EllipticEst.Q0 := fun q hq => Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [hq.1.1, hεz, hz0], by linarith [hq.2.1, hεθ, hθ0],
        by linarith [hq.2.2, hεπ, hθ1]⟩
    have hBcomp : IsCompact B := isCompact_Icc.prod isCompact_Icc
    have hBmeas : MeasurableSet B := hBcomp.isClosed.measurableSet
    have hBfin : (volume : Measure (ℝ × ℝ)) B < ⊤ := hBcomp.measure_lt_top
    have hBnhds : B ∈ 𝓝 p := by
      refine Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        ⟨⟨sub_lt_self _ hε0, lt_add_of_pos_right _ hε0⟩,
          ⟨sub_lt_self _ hε0, lt_add_of_pos_right _ hε0⟩⟩) ?_
      intro q hq
      exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
    refine ⟨B, nhdsWithin_le_nhds hBnhds, ?_⟩
    -- the uniform bound `|ψ_N| ≤ C z^{-1/2}` on the angular range of `B`
    obtain ⟨C, hC0, hCbnd⟩ := psiTrunc_bound_on α hα hα1 horth hsm hL2
      (c := p.2 - ε) (d := p.2 + ε) (by linarith) (by linarith) (by linarith)
    have hθB : ∀ q ∈ B, q.2 ∈ Set.Icc (p.2 - ε) (p.2 + ε) := fun q hq => hq.2
    have hPsiB : ∀ q ∈ B,
        |Work.FTS.H2.ModalSol.Psi α F q.1 q.2| ≤ C * q.1 ^ (-(1 / 2) : ℝ) := by
      intro q hq
      have hq1 : 0 < q.1 := by linarith [hq.1.1, hεz, hz0]
      have hlim := psiTrunc_tendsto_Psi (z := q.1) (θ := q.2) α hα hα1 horth hsm hL2 hq1
        ⟨by linarith [hq.2.1, hεθ, hθ0], by linarith [hq.2.2, hεπ, hθ1]⟩
      exact le_of_tendsto hlim.abs
        (Filter.Eventually.of_forall (fun N => hCbnd N q.1 q.2 hq1 (hθB q hq)))
    -- a.e. strong measurability, as a pointwise limit of the continuous partial sums
    have hAESM : AEStronglyMeasurable (Function.uncurry (Work.FTS.H2.ModalSol.Psi α F))
        ((volume : Measure (ℝ × ℝ)).restrict B) := by
      have h1 : ∀ N : ℕ, AEMeasurable
          (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N))
          ((volume : Measure (ℝ × ℝ)).restrict B) := fun N =>
        ((continuousOn_uncurry_psiTrunc α hα hα1 hsm hL2 N).mono hBQ).aemeasurable hBmeas
      have h2 : AEMeasurable (fun q : ℝ × ℝ => limsup
          (fun N => Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N) q) atTop)
          ((volume : Measure (ℝ × ℝ)).restrict B) := AEMeasurable.limsup h1
      have haeeq : ∀ᵐ q ∂((volume : Measure (ℝ × ℝ)).restrict B),
          (fun q : ℝ × ℝ => limsup
            (fun N => Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N) q) atTop) q
          = Function.uncurry (Work.FTS.H2.ModalSol.Psi α F) q := by
        rw [ae_restrict_iff' hBmeas]
        refine Filter.Eventually.of_forall (fun q hq => ?_)
        have hq1 : 0 < q.1 := by linarith [hq.1.1, hεz, hz0]
        exact Filter.Tendsto.limsup_eq
          (psiTrunc_tendsto_Psi (z := q.1) (θ := q.2) α hα hα1 horth hsm hL2 hq1
            ⟨by linarith [hq.2.1, hεθ, hθ0], by linarith [hq.2.2, hεπ, hθ1]⟩)
      exact (h2.congr haeeq).aestronglyMeasurable
    -- integrability by the pointwise bound
    haveI : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict B) :=
      isFiniteMeasure_restrict.mpr (lt_top_iff_ne_top.mp hBfin)
    refine MeasureTheory.Integrable.of_bound hAESM (C * (p.1 - ε) ^ (-(1 / 2) : ℝ)) ?_
    rw [ae_restrict_iff' hBmeas]
    refine Filter.Eventually.of_forall (fun q hq => ?_)
    rw [Real.norm_eq_abs]
    refine le_trans (hPsiB q hq) ?_
    have hzε : 0 < p.1 - ε := by linarith [hεz, hz0]
    have hqle : p.1 - ε ≤ q.1 := by linarith [hq.1.1]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hzε hqle (by norm_num)) hC0.le
  · -- ## the weak identity
    intro φ hφ hφc hφs
    exact psi_weak_identity α hα hα1 horth hsm hL2 hφ hφc hφs
  · exact Work.FTS.H2.ModalSol.Psi_apply_zero α F
  · exact Work.FTS.H2.ModalSol.Psi_apply_pi_half α F
  · -- ## decay at `z → ∞`
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · have hfun : (fun z : ℝ => Work.FTS.H2.ModalSol.Psi α F z 0) = fun _ => (0 : ℝ) :=
        funext (fun z => Work.FTS.H2.ModalSol.Psi_apply_zero α F z)
      rw [← h0, hfun]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with hπ | hπ
    · have hfun : (fun z : ℝ => Work.FTS.H2.ModalSol.Psi α F z (π / 2)) = fun _ => (0 : ℝ) :=
        funext (fun z => Work.FTS.H2.ModalSol.Psi_apply_pi_half α F z)
      rw [hπ, hfun]
      exact tendsto_const_nhds
    · obtain ⟨c, d, hcd, hc0, hθcd, hd⟩ := exists_box_Icc_subset_Ioo h0 hπ
      obtain ⟨C, hC0, hCbnd⟩ := psiTrunc_bound_on α hα hα1 horth hsm hL2 hcd hc0 hd
      have hbnd : ∀ z : ℝ, 0 < z →
          |Work.FTS.H2.ModalSol.Psi α F z θ| ≤ C * z ^ (-(1 / 2) : ℝ) := by
        intro z hz
        have hlim := psiTrunc_tendsto_Psi (z := z) (θ := θ) α hα hα1 horth hsm hL2 hz
          ⟨lt_of_lt_of_le hc0 hθcd.1, lt_of_le_of_lt hθcd.2 hd⟩
        exact le_of_tendsto hlim.abs
          (Filter.Eventually.of_forall (fun N => hCbnd N z θ hz hθcd))
      refine squeeze_zero_norm' (a := fun z : ℝ => C * z ^ (-(1 / 2) : ℝ)) ?_ ?_
      · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
        rw [Real.norm_eq_abs]
        exact hbnd z hz
      · have h := (tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)).const_mul C
        simpa using h
  · -- ## a.e. continuity of the angular slices
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall
      (fun z hz => Psi_slice_continuous α hα hα1 horth hsm hL2 hz)

end Work.FTS.H2.ModalSolR
