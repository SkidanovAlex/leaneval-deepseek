/-
# `ModalSolR/PsiFacts` — continuity of the partial sums and the weak identity

* `exists_box_Icc_subset_Ioo` / `exists_box_Ioo_Icc`: elementary interval bookkeeping;
* `continuousOn_uncurry_psiTrunc`: the partial sums of the mode series are continuous on the
  open quadrant (from the continuity of `radGreen`, which is where `cmode_memLp` enters);
* `psi_weak_identity`: **the weak identity for the limit** `Psi α F`, obtained from the
  truncated identity `psiTrunc_weak_identity` by dominated convergence (the domination is the
  uniform bound `psiTrunc_bound_on` of `LimitFacts`) and the source-side limit
  `sourceSideLimit`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSol.ModeIdent.Defs
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.ModalSolR.PerMode
import Submission.Work.FTS.H2.ModalSolR.TruncIdent
import Submission.Work.FTS.H2.ModalSolR.LimitFacts
import Submission.Work.FTS.H2.ModalSolR.sourceSideLimit
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs

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

/-! ## Elementary interval bookkeeping -/

/-- An interior point of `(0,π/2)` lies in a closed subinterval with room to spare. -/
theorem exists_box_Icc_subset_Ioo {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    ∃ c d : ℝ, c < d ∧ 0 < c ∧ θ ∈ Set.Icc c d ∧ d < π / 2 :=
  ⟨θ / 2, (θ + π / 2) / 2, by linarith [Real.pi_pos], by linarith,
    ⟨le_of_lt (by linarith), le_of_lt (by linarith [Real.pi_pos])⟩,
    by linarith [Real.pi_pos]⟩

/-- An interior point of `(0,π/2)` is *inside* a closed subinterval with room to spare. -/
theorem exists_box_Ioo_Icc {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    ∃ c d : ℝ, c < d ∧ 0 < c ∧ c < θ ∧ θ < d ∧ d < π / 2 ∧ θ ∈ Set.Icc c d :=
  ⟨θ / 2, (θ + π / 2) / 2, by linarith [Real.pi_pos], by linarith, by linarith,
    by linarith [Real.pi_pos], by linarith [Real.pi_pos],
    ⟨le_of_lt (by linarith), le_of_lt (by linarith [Real.pi_pos])⟩⟩

/-! ## Continuity of the partial sums on the open quadrant -/

/-- The mode-`m` term of the partial sum is continuous on the open quadrant. -/
theorem continuousOn_acoeff_mul_eFam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.acoeff α m F p.1 *
      Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Work.FTS.EllipticEst.Q0 := by
  have hc : MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  have h1 : ContinuousOn (fun z => Work.FTS.PhiStar.Series.acoeff α m F z) (Set.Ioi 0) := by
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact radGreenContinuousOn hα hα1 m hc (Work.EllipticEst.ModalSolution.aesm_cmode hsm m)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).comp_continuousOn
      continuous_snd.continuousOn
  exact (h1.comp continuous_fst.continuousOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul h2

/-- The partial sums of the mode series are continuous on the open quadrant. -/
theorem continuousOn_uncurry_psiTrunc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) (N : ℕ) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N))
      Work.FTS.EllipticEst.Q0 := by
  have hfun : Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N)
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m F p.1 *
            Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    simp only [Function.uncurry, Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_apply]
  rw [hfun]
  exact continuousOn_finsetSum (Finset.range (N + 1))
    (fun m _ => continuousOn_acoeff_mul_eFam α hα hα1 hsm hL2 m)

/-! ## The weak identity for the limit -/

/-- **The weak identity for the modal solution.**  For every smooth test function `φ` compactly
supported in the open quadrant, `Psi α F` solves `bslOp α Ψ = F` weakly against the weight
`z ^ ((5-α)/α) cos θ`. -/
theorem psi_weak_identity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F φ : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, Work.FTS.H2.ModalSol.Psi α F p.1 p.2
        * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  classical
  obtain ⟨a, b, c, d, ha, hab, hc0, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hqpos : 0 < (5 - α) / α := div_pos (by linarith) hα
  set K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d with hKdef
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcomp.isClosed.measurableSet
  have hKfin : (volume : Measure (ℝ × ℝ)) K < ⊤ := hKcomp.measure_lt_top
  have hKne : K.Nonempty := ⟨((a + b) / 2, (c + d) / 2),
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hbsl0 : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ K,
      Work.Elliptic.bslOp α φ p.1 p.2 = 0 := fun p hp => bslOp_eq_zero_off_box hbox hp.2
  -- ## reduction of the integrals to the box
  have hvanL : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    fun N => setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by rw [hbsl0 p hp]; ring)
  have hvanLinf : (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.H2.ModalSol.Psi α F p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, Work.FTS.H2.ModalSol.Psi α F p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by rw [hbsl0 p hp]; ring)
  -- ## the two uniform bounds
  obtain ⟨M3, hM3⟩ := hKcomp.exists_bound_of_continuousOn ((continuousOn_bslOp hφsm).mono hKsub)
  have hM3nn : 0 ≤ M3 := le_trans (norm_nonneg _) (hM3 hKne.choose hKne.choose_spec)
  obtain ⟨C, hC0, hCbnd⟩ := psiTrunc_bound_on α hα hα1 horth hsm hL2
    (c := min c (π / 2 - d)) (d := d)
    (lt_of_le_of_lt (min_le_left c (π / 2 - d)) hcd)
    (lt_min hc0 (by linarith)) hd
  have hCann : 0 ≤ C * a ^ (-(1 / 2) : ℝ) := mul_nonneg hC0.le (Real.rpow_nonneg ha.le _)
  -- ## dominated convergence on the box
  have hDCT : Filter.Tendsto (fun N : ℕ => ∫ p in K,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop (nhds (∫ p in K, Work.FTS.H2.ModalSol.Psi α F p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ × ℝ => C * a ^ (-(1 / 2) : ℝ) * M3 * b ^ ((5 - α) / α)) ?_ ?_ ?_ ?_
    · intro N
      refine ContinuousOn.aestronglyMeasurable ?_ hKmeas
      refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
      · exact (continuousOn_uncurry_psiTrunc α hα hα1 hsm hL2 N).mono hKsub
      · exact (continuousOn_bslOp hφsm).mono hKsub
      · exact (continuousOn_fst.rpow_const
          (fun p hp => Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
          (Real.continuous_cos.comp_continuousOn continuousOn_snd)
    · exact MeasureTheory.integrableOn_const
        (C := C * a ^ (-(1 / 2) : ℝ) * M3 * b ^ ((5 - α) / α))
        (lt_top_iff_ne_top.mp hKfin)
    · intro N
      rw [ae_restrict_iff' hKmeas]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
      have hθd : p.2 ∈ Set.Icc (min c (π / 2 - d)) d :=
        ⟨le_trans (min_le_left _ _) hp.2.1, hp.2.2⟩
      have hψ : |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2|
          ≤ C * a ^ (-(1 / 2) : ℝ) := by
        refine le_trans (hCbnd N p.1 p.2 hp1 hθd) ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)) hC0.le
      have hbsl : |Work.Elliptic.bslOp α φ p.1 p.2| ≤ M3 := by
        have h := hM3 p hp
        rwa [Real.norm_eq_abs] at h
      have hw : |p.1 ^ ((5 - α) / α) * Real.cos p.2| ≤ b ^ ((5 - α) / α) := by
        rw [abs_mul]
        refine le_trans (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2)
          (abs_nonneg _)) ?_
        rw [mul_one, abs_of_nonneg (Real.rpow_nonneg hp1.le _)]
        exact Real.rpow_le_rpow hp1.le hp.1.2 hqpos.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hψ hbsl (abs_nonneg _) hCann) hw (abs_nonneg _)
        (mul_nonneg hCann hM3nn)
    · rw [ae_restrict_iff' hKmeas]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hlim := psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2
        (lt_of_lt_of_le ha hp.1.1)
        ⟨lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
      exact ((hlim.mul tendsto_const_nhds).mul tendsto_const_nhds)
  -- ## assembly
  have hLHS : Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.H2.ModalSol.Psi α F p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
    rw [hvanLinf]
    exact hDCT.congr' (Filter.Eventually.of_forall (fun N => (hvanL N).symm))
  have hseq : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, (∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    fun N => psiTrunc_weak_identity α hα hα1 horth hsm hL2 hφ hφc hφs N
  exact tendsto_nhds_unique hLHS
    (((sourceSideLimit (α := α) hsm hφ hφc hφs hL2)).congr'
      (Filter.Eventually.of_forall (fun N => (hseq N).symm)))

end Work.FTS.H2.ModalSolR
