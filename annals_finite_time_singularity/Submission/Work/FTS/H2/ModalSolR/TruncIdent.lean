/-
# `ModalSolR/TruncIdent` — the truncated weak identity

For every `N`, the partial sum `ψ_N = psiTrunc α F N` solves the weak equation against the truncated
source `Σ_{m ≤ N} cmode m F z · eFam m θ`:

  `∫_{Q0} ψ_N · (bslOp α φ) · w = ∫_{Q0} F_N · φ · w`,   `w = z^((5-α)/α) cos θ`,

for every test function `φ` smooth and compactly supported in the open quadrant.  The proof is an
induction on `N`, the step being the per-mode identity `perModeQ0` (and the `m = 0` mode vanishing
by the solvability condition `OrthCond F`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.ModalSolR.PerMode
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.ModalSolR.radGreenContinuousOn
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-! ## Integrability tools -/

/-- A function vanishing outside a measurable box `K ⊆ Q0` and integrable on `K` is integrable on
the open quadrant. -/
theorem integrableOn_Q0_of_integrableOn_box {f : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hKmeas : MeasurableSet K) (hKsub : K ⊆ Work.FTS.EllipticEst.Q0)
    (hint : MeasureTheory.IntegrableOn f K)
    (hzero : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, f p = 0) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 := by
  have heq : Work.FTS.EllipticEst.Q0.indicator f = K.indicator f := by
    funext p
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hKsub hp)]
    · by_cases hq : p ∈ Work.FTS.EllipticEst.Q0
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_mem hq, hzero p ⟨hq, hp⟩]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
  rw [← MeasureTheory.integrable_indicator_iff Work.FTS.EllipticEst.isOpen_Q0.measurableSet, heq]
  exact (MeasureTheory.integrable_indicator_iff hKmeas).mpr hint

/-- A function vanishing outside the closed box `[a,b] × [c,d]` and continuous on it is integrable
on the open quadrant. -/
theorem integrableOn_Q0_of_continuousOn_box {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (ha : 0 < a) (hc0 : 0 < c) (hd : d < π / 2)
    (hcont : ContinuousOn f (Set.Icc a b ×ˢ Set.Icc c d))
    (hzero : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ (Set.Icc a b ×ˢ Set.Icc c d), f p = 0) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 :=
  integrableOn_Q0_of_integrableOn_box (measurableSet_Icc.prod measurableSet_Icc)
    (fun p hp => Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩)
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)) hzero

/-- The mode-`m` term of the left-hand side is integrable on the quadrant. -/
theorem integrableOn_mode_L (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hc0 : 0 < c) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hAcont : ContinuousOn (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Icc a b) := by
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact (radGreenContinuousOn hα hα1 m hc2 hcm).mono
      (fun z hz => lt_of_lt_of_le ha hz.1)
  have hem : Continuous (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous
  refine integrableOn_Q0_of_continuousOn_box (a := a) (b := b) (c := c) (d := d)
    ha hc0 hd ?_ ?_
  · refine ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_) ?_
    · exact hAcont.comp continuousOn_fst (fun p hp => hp.1)
    · exact hem.comp_continuousOn continuousOn_snd
    · exact (continuousOn_bslOp hφsm).mono (fun p hp =>
        Work.FTS.EllipticEst.mem_Q0.mpr
          ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩)
    · exact (continuousOn_fst.rpow_const (fun p hp =>
        Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
        (Real.continuous_cos.comp_continuousOn continuousOn_snd)
  · intro p hp
    rw [bslOp_eq_zero_off_box hbox hp.2]
    ring

/-- The mode-`m` term of the right-hand side is integrable on the quadrant. -/
theorem integrableOn_mode_R (α : ℝ) (m : ℕ) {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c ≤ d) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hem : Continuous (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2
      * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((hem.comp_continuousOn continuousOn_snd).mul (hφsm.continuousOn.mono hKsub)).mul
      ((continuousOn_fst.rpow_const (fun p hp =>
        Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
        (Real.continuous_cos.comp_continuousOn continuousOn_snd))
  have hbase : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      Work.FTS.PhiStar.Series.cmode m F p.1
        * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable hc2 hcm ha hab hc0 hcd hg
  have hKint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    hbase.congr_fun (fun p _ => by ring) (measurableSet_Icc.prod measurableSet_Icc)
  refine integrableOn_Q0_of_integrableOn_box (measurableSet_Icc.prod measurableSet_Icc)
    hKsub hKint ?_
  intro p hp
  have hφ0 : φ p.1 p.2 = 0 := by
    by_cases h1 : p.1 ∈ Set.Ioo a b
    · exact test_vanishes_off_theta hbox (fun h2 => hp.2 ⟨⟨h1.1.le, h1.2.le⟩,
        ⟨h2.1.le, h2.2.le⟩⟩)
    · exact test_vanishes_off_z hbox h1
  rw [hφ0]
  ring

/-! ## Integrability of the truncated sums -/

/-- The left-hand side integrand is integrable on the quadrant. -/
theorem integrableOn_psiTrunc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F φ : ℝ → ℝ → ℝ}
    (hcF : ∀ m : ℕ, MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (haF : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hc0 : 0 < c) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) (N : ℕ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
        * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hfun : (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
      * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = (fun p : ℝ × ℝ => (∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.acoeff α m F p.1
              * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    funext p
    simp only [Work.FTS.PhiStar.Series.psiTrunc]
  rw [hfun]
  refine integrableOn_Q0_of_continuousOn_box (a := a) (b := b) (c := c) (d := d)
    ha hc0 hd ?_ ?_
  · refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine continuousOn_finsetSum _ fun m _ => ?_
      have hAcont : ContinuousOn (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Icc a b) := by
        simp only [Work.FTS.PhiStar.Series.acoeff]
        exact (radGreenContinuousOn hα hα1 m (hcF m) (haF m)).mono
          (fun z hz => lt_of_lt_of_le ha hz.1)
      exact (hAcont.comp continuousOn_fst (fun p hp => hp.1)).mul
        ((Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).comp_continuousOn
          continuousOn_snd)
    · exact (continuousOn_bslOp hφsm).mono (fun p hp =>
        Work.FTS.EllipticEst.mem_Q0.mpr
          ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩)
    · exact (continuousOn_fst.rpow_const (fun p hp =>
        Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
        (Real.continuous_cos.comp_continuousOn continuousOn_snd)
  · intro p hp
    rw [bslOp_eq_zero_off_box hbox hp.2]
    ring

/-- The truncated source integrand is integrable on the quadrant. -/
theorem integrableOn_truncSource (α : ℝ) {F φ : ℝ → ℝ → ℝ}
    (hcF : ∀ m : ℕ, MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (haF : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c ≤ d) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) (N : ℕ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hsum : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    induction N with
    | zero =>
      have hfun : (fun p : ℝ × ℝ =>
          (∑ m ∈ Finset.range (0 + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
          = (fun p : ℝ × ℝ =>
              (Work.FTS.PhiStar.Series.cmode 0 F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam 0 p.2)
                * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
        funext p
        rw [Finset.range_one, Finset.sum_singleton]
      rw [hfun]
      exact IntegrableOn.mono_set (integrableOn_mode_R α 0 (hcF 0) (haF 0) hφ hφc hφs ha hab
        hc0 hcd hd hbox) hKsub
    | succ N ih =>
      have hfun : (fun p : ℝ × ℝ =>
          (∑ m ∈ Finset.range (N + 1 + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
          = (fun p : ℝ × ℝ =>
              (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
                * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
              + (Work.FTS.PhiStar.Series.cmode (N + 1) F p.1
                  * Work.FTS.PhiStar.Gegenbauer.eFam (N + 1) p.2)
                  * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
        funext p
        rw [Finset.sum_range_succ]
        ring
      rw [hfun]
      exact ih.add (IntegrableOn.mono_set (integrableOn_mode_R α (N + 1) (hcF (N + 1))
        (haF (N + 1)) hφ hφc hφs ha hab hc0 hcd hd hbox) hKsub)
  refine integrableOn_Q0_of_integrableOn_box (measurableSet_Icc.prod measurableSet_Icc)
    hKsub hsum ?_
  intro p hp
  have hφ0 : φ p.1 p.2 = 0 := by
    by_cases h1 : p.1 ∈ Set.Ioo a b
    · exact test_vanishes_off_theta hbox (fun h2 => hp.2 ⟨⟨h1.1.le, h1.2.le⟩,
        ⟨h2.1.le, h2.2.le⟩⟩)
    · exact test_vanishes_off_z hbox h1
  rw [hφ0]
  ring

/-! ## The truncated weak identity -/

/-- **The truncated weak identity.** -/
theorem psiTrunc_weak_identity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F φ : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (N : ℕ) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0,
          (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  obtain ⟨a, b, c, d, ha, hab, hc0, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hcF : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) := fun m =>
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  have haF : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := fun m =>
    Work.EllipticEst.ModalSolution.aesm_cmode hsm m
  have hA0 : ∀ z, Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := acoeff_zero_of_orth horth α
  have hC0 : ∀ z, Work.FTS.PhiStar.Series.cmode 0 F z = 0 := cmode_zero_eq_zero horth
  have hL0ae : (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F 0 p.1 p.2
      * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      =ᵐ[(volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0] fun _ => 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp
    rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.range_one, Finset.sum_singleton, hA0 p.1]
    ring
  have hR0ae : (fun p : ℝ × ℝ => (∑ m ∈ Finset.range (0 + 1),
        Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      =ᵐ[(volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0] fun _ => 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp
    rw [Finset.range_one, Finset.sum_singleton, hC0 p.1]
    ring
  have hpsi : ∀ N : ℕ,
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F (N + 1) p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
              * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
            + (Work.FTS.PhiStar.Series.acoeff α (N + 1) F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam (N + 1) p.2)
                * (Work.Elliptic.bslOp α φ p.1 p.2)
                * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    intro N
    funext p
    simp only [Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_range_succ]
    ring
  have hsrc : ∀ N : ℕ,
      (fun p : ℝ × ℝ =>
          (∑ m ∈ Finset.range (N + 1 + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = (fun p : ℝ × ℝ =>
              (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
                * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
                * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
              + (Work.FTS.PhiStar.Series.cmode (N + 1) F p.1
                  * Work.FTS.PhiStar.Gegenbauer.eFam (N + 1) p.2)
                  * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    intro N
    funext p
    rw [Finset.sum_range_succ]
    ring
  induction N with
  | zero =>
    rw [MeasureTheory.integral_congr_ae hL0ae, MeasureTheory.integral_congr_ae hR0ae]
  | succ N ih =>
    have hIntL := integrableOn_psiTrunc α hα hα1 hcF haF hφ hφc hφs ha hc0 hd hbox N
    have hmodeL := integrableOn_mode_L α hα hα1 (N + 1) (hcF (N + 1)) (haF (N + 1))
      hφ hφc hφs ha hc0 hd hbox
    have hIntR := integrableOn_truncSource α hcF haF hφ hφc hφs ha hab.le hc0 hcd.le hd hbox N
    have hmodeR := integrableOn_mode_R α (N + 1) (hcF (N + 1)) (haF (N + 1))
      hφ hφc hφs ha hab.le hc0 hcd.le hd hbox
    have hper := perModeQ0 α hα hα1 (N + 1) (by omega) (hcF (N + 1)) (haF (N + 1)) hφ hφc hφs
    rw [hpsi N, MeasureTheory.integral_add hIntL hmodeL, ih, hper,
      ← MeasureTheory.integral_add hIntR hmodeR, ← hsrc N]

end Work.FTS.H2.ModalSolR
