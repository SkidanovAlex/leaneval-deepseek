import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxFrameBackup
import Submission.Work.BoseFixB1.stronglyMeasurable_frameIntegrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.framePerXBound`

The per-configuration frame bound at a single box `Ac ⊆ acube a`, with the *total* particle
number `n` as the Cauchy–Schwarz cardinality:

  `∫_q frameIntegrand volA Ac χ Ψ q x
     ≤ volA⁻¹ · n · κ² · (2π)³ · Σ_i 1_{Ac}(x_i) · ∫_{Ac} (Q_{Ac,i}Ψ)(x_{i↦z})² dz`.

Two differences with the siblings in `Submission/Work/BoseFixB1` are handled here:

* `n` is an arbitrary natural number (not `N + 1`), so the statement also covers `X n` at `n = 0`;
  the Cauchy–Schwarz step uses `n` directly (there is no need for the box count);
* the window `χ` is only assumed **continuous**, with `|χ| ≤ κ` — not `ContDiff ℝ ⊤` with
  `0 ≤ χ ≤ κ`.

The Plancherel step `slotPlancherel_cont` below is a copy of
`Work.BoseFixB1.framePlancherel_slot'` with the smoothness hypothesis weakened to continuity:
that proof uses `χ` only through continuity.  The window-weight step is replaced by
`slotFibre_sq_weight_le_abs`, which needs only `|χ z| ≤ κ` (no positivity of `χ` or of `κ`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

open Work.BoseFixB1 _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Plancherel for one slot** (the identity used by the frame bound). -/
private theorem slotPlancherel_cont {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) (x : X n) :
    MeasureTheory.Integrable (fun q : E3 =>
        ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
        + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2))
      ∧ (∫ q : E3,
          ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
          + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2))
        = (2 * Real.pi) ^ 3 *
            ∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2 := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)
  have hAc_lt : (volume : Measure E3) Ac < ∞ :=
    lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)
  -- bounds
  obtain ⟨Cχ, hCχ0, hCχ⟩ : ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ z ∈ Ac, ‖χ z‖ ≤ Cχ := by
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (acube_compact ha)
      hχc.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun z hz => le_trans (hC z (hAc hz)) (le_max_left _ _)⟩
  have contUpd : Continuous (fun z : E3 => Function.update x i z) :=
    (continuous_const : Continuous fun _ : E3 => x).update i continuous_id
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Ac, ‖Ψ (Function.update x i z)‖ ≤ M := by
    obtain ⟨C, hC⟩ := ((acube_compact ha).image contUpd).exists_bound_of_continuousOn
      (hΨ.continuousOn.mono (Set.subset_univ _))
    exact ⟨max C 0, le_max_right _ _, fun z hz =>
      le_trans (hC _ ⟨z, hAc hz, rfl⟩) (le_max_left _ _)⟩
  -- the fibre is bounded by `2M`
  have hslot : ∀ z ∈ Ac, ‖slotFibre volA Ac i Ψ x z‖ ≤ 2 * M := by
    intro z hz
    have hmean : ‖volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w)‖ ≤ M := by
      have hb : ∀ w ∈ Ac, ‖Ψ (Function.update x i w)‖ ≤ M := fun w hw => hM w hw
      have hInt : IntegrableOn (fun w : E3 => Ψ (Function.update x i w)) Ac volume :=
        IntegrableOn.of_bound hAc_lt
          ((hΨ.measurable.comp (measurable_update (f := x) (a := i))).aestronglyMeasurable) M
          (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
      have h1 : ‖∫ w in Ac, Ψ (Function.update x i w)‖ ≤ M * volA := by
        refine (norm_integral_le_integral_norm _).trans ?_
        have hmono := integral_mono_of_nonneg
          (μ := (volume : Measure E3).restrict Ac)
          (f := fun w => ‖Ψ (Function.update x i w)‖) (g := fun _ : E3 => M)
          (Eventually.of_forall fun w => norm_nonneg _) (integrable_const M)
          (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
        exact hmono.trans (le_of_eq (by
          rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol, smul_eq_mul,
            mul_comm]))
      rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hvolpos.le)]
      calc volA⁻¹ * ‖∫ w in Ac, Ψ (Function.update x i w)‖ ≤ volA⁻¹ * (M * volA) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hvolpos.le)
        _ = M := by
            rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hvolpos)]
            ring
    rw [slotFibre_eq volA x z hz]
    calc ‖Ψ (Function.update x i z) - volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w)‖
        ≤ ‖Ψ (Function.update x i z)‖
          + ‖volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM z hz) hmean
      _ = 2 * M := by ring
  -- the complex fibre
  set F : E3 → ℂ := fun z => ((χ z * slotFibre volA Ac i Ψ x z : ℝ) : ℂ) with hF
  have hFzero : ∀ z ∉ Ac, F z = 0 := by
    intro z hz
    simp only [hF]
    rw [fib_eq_zero_of_notMem hχsupp i Ψ x hz, Complex.ofReal_zero]
  have hFmeas : Measurable F := by
    refine Complex.continuous_ofReal.measurable.comp ?_
    refine Measurable.mul hχc.measurable ?_
    exact (SlotWord.measurable_boxQInd volA Ac hAcm i hΨ.measurable).comp
      (measurable_update (f := x) (a := i))
  have hFbound : ∀ z ∈ Ac, ‖F z‖ ≤ Cχ * (2 * M) := by
    intro z hz
    rw [show F z = ((χ z * slotFibre volA Ac i Ψ x z : ℝ) : ℂ) from rfl,
      norm_ofReal_eq_abs, abs_mul]
    exact mul_le_mul (hCχ z hz) (hslot z hz) (abs_nonneg _) hCχ0
  have hindF : Ac.indicator F = F := funext fun z => by
    by_cases hz : z ∈ Ac
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hFzero z hz]
  have hmem1 : MemLp F 1 volume := by
    rw [← hindF]
    exact (memLp_indicator_iff_restrict hAcm).mpr
      (MemLp.of_bound hFmeas.aestronglyMeasurable (Cχ * (2 * M))
        (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hFbound)))
  have hmem2 : MemLp F 2 volume := by
    rw [← hindF]
    exact (memLp_indicator_iff_restrict hAcm).mpr
      (MemLp.of_bound hFmeas.aestronglyMeasurable (Cχ * (2 * M))
        (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hFbound)))
  -- integrability of the Fourier integral
  have hFT : ∀ q : E3, Submission.BoseGases.kinFT F q
      = ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y := fun q => rfl
  have hIntK : ∀ q : E3, Integrable (fun y : E3 =>
      Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y) volume := by
    intro q
    have hdom : Integrable (fun y : E3 => Ac.indicator (fun _ => (Cχ * (2 * M))) y) volume :=
      (integrable_indicator_iff hAcm).mpr (integrableOn_const (C := Cχ * (2 * M)))
    refine Integrable.mono' hdom
      ((((Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg)).measurable).mul
          hFmeas).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    have h1 : ‖F y‖ ≤ (Ac.indicator (fun _ => (Cχ * (2 * M)))) y := by
      by_cases hy : y ∈ Ac
      · rw [Set.indicator_of_mem hy]; exact hFbound y hy
      · rw [hFzero y hy, norm_zero, Set.indicator_of_notMem hy]
    have hre : (-(Complex.I * (inner ℝ q y : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre, Real.exp_zero, one_mul]
    exact h1
  -- the real and imaginary parts
  have hRe : ∀ q : E3, (Submission.BoseGases.kinFT F q).re
      = ∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z) := by
    intro q
    rw [hFT q]
    change Complex.reCLM (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y) = _
    rw [← Complex.reCLM.integral_comp_comm (μ := volume)
      (φ := fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y) (hIntK q)]
    calc (∫ y : E3, (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y).re)
        = ∫ y : E3, Real.cos (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [hF, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
            sub_zero, Work.SmallBoxA0.win_exp_neg_inner_re]
      _ = ∫ y in Ac, Real.cos (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y) := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
          rw [fib_eq_zero_of_notMem hχsupp i Ψ x hy, mul_zero]
      _ = ∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z) := by
          rw [slotAmp_re_eq ha hAcm hAc hvol hvolpos hχc hΨ i x q]
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          ring
  have hIm : ∀ q : E3, (Submission.BoseGases.kinFT F q).im
      = ∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z) := by
    intro q
    rw [hFT q]
    change Complex.imCLM (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y) = _
    rw [← Complex.imCLM.integral_comp_comm (μ := volume)
      (φ := fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y) (hIntK q)]
    calc (∫ y : E3, (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * F y).im)
        = ∫ y : E3, -(Real.sin (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y)) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [hF, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Work.SmallBoxA0.win_exp_neg_inner_im]
          ring
      _ = -(∫ y : E3, Real.sin (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y)) :=
          integral_neg _
      _ = -(∫ y in Ac, Real.sin (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y)) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
            rw [fib_eq_zero_of_notMem hχsupp i Ψ x hy, mul_zero])]
      _ = ∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z) := by
          rw [slotAmp_im_eq ha hAcm hAc hvol hvolpos hχc hΨ i x q]
          refine congrArg Neg.neg ?_
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          ring
  -- the squared modulus
  have hnorm : ∀ q : E3, ‖Submission.BoseGases.kinFT F q‖ ^ 2
      = (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
        + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 := by
    intro q
    rw [Complex.sq_norm, Complex.normSq_apply, hRe q, hIm q]
    ring
  obtain ⟨hIntKin, hKin⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hmem1 hmem2
  refine ⟨hIntKin.congr (Eventually.of_forall fun q => by
    show ‖Submission.BoseGases.kinFT F q‖ ^ 2 = _
    exact hnorm q), ?_⟩
  have h2π : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  have hkin : (∫ q : E3, ‖Submission.BoseGases.kinFT F q‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖F z‖ ^ 2 := by
    have hh : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, ‖Submission.BoseGases.kinFT F q‖ ^ 2)
        = ∫ z : E3, ‖F z‖ ^ 2 := hKin
    rw [inv_mul_eq_iff_eq_mul₀ h2π] at hh
    exact hh
  calc (∫ q : E3,
        (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
          + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
      = ∫ q : E3, ‖Submission.BoseGases.kinFT F q‖ ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun q => by
          show (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
              + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
            = ‖Submission.BoseGases.kinFT F q‖ ^ 2
          exact (hnorm q).symm)
    _ = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖F z‖ ^ 2 := hkin
    _ = (2 * Real.pi) ^ 3 * ∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2 := by
        congr 1
        rw [show (fun z : E3 => ‖F z‖ ^ 2)
            = fun z : E3 => (χ z * slotFibre volA Ac i Ψ x z) ^ 2 from by
          funext z
          simp only [hF]
          rw [norm_ofReal_eq_abs, sq_abs]]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ac)
          (f := fun z : E3 => (χ z * slotFibre volA Ac i Ψ x z) ^ 2) (fun z hz => by
            rw [fib_eq_zero_of_notMem hχsupp i Ψ x hz]; ring)).symm

/-! ## The slot Cauchy–Schwarz with the total particle number -/

/-- **Sharp slot Cauchy–Schwarz** for one mode `g`, with the *total* particle number `n` as the
cardinality (the annihilation sum runs over all `n` slots; the indicator kills the empty ones). -/
private lemma boxTauAnnGen_sq_le_card_mul {n : ℕ} {volA : ℝ} (hvolpos : 0 < volA)
    {Ac : Set E3} {g : E3 → ℝ} {Ψ : X n → ℝ} (x : X n) :
    (boxTauAnnGen volA Ac g Ψ x) ^ 2
      ≤ volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 := by
  have hsq : (Real.sqrt volA)⁻¹ ^ 2 = volA⁻¹ := by rw [inv_pow, Real.sq_sqrt hvolpos.le]
  have hidem : ∀ (i : Fin n) (y : ℝ),
      (Ac.indicator (fun _ => (1 : ℝ)) (x i) * y) ^ 2
        = Ac.indicator (fun _ => (1 : ℝ)) (x i) * y ^ 2 := by
    intro i y
    by_cases h : x i ∈ Ac
    · rw [Set.indicator_of_mem h, one_mul, one_mul]
    · rw [Set.indicator_of_notMem h]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => Ac.indicator (fun _ => (1 : ℝ)) (x i) *
      ∫ z in Ac, g z * Ψ (Function.update x i z))
  rw [Finset.card_fin] at hcs
  have hsumeq : (∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        ∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      = ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hidem i _)
  calc (boxTauAnnGen volA Ac g Ψ x) ^ 2
      = volA⁻¹ * (∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            ∫ z in Ac, g z * Ψ (Function.update x i z))) ^ 2 := by
        rw [boxTauAnnGen, mul_pow, hsq]
    _ ≤ volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            ∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa using hcs) (inv_nonneg.mpr hvolpos.le)
    _ = volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 := by
        rw [hsumeq]; ring

/-! ## The frame integrand

The `q`-frame integrand is nonnegative and, by Cauchy–Schwarz over the slots, bounded by
`volA⁻¹ · n` times the sum of the slot amplitudes. -/

/-- The frame integrand is nonnegative. -/
private lemma frameIntegrand_nonneg (volA : ℝ) (Ac : Set E3) (χ : E3 → ℝ) {N : ℕ}
    (Ψ : X N → ℝ) (q : E3) (x : X N) : 0 ≤ frameIntegrand volA Ac χ Ψ q x := by
  have h : frameIntegrand volA Ac χ Ψ q x
      = (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
        + (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2 := rfl
  rw [h]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Cauchy–Schwarz over the slots**, with the total particle number `n` as cardinality. -/
private lemma frameIntegrand_le_card_mul {n : ℕ} {volA : ℝ} (hvolpos : 0 < volA)
    {Ac : Set E3} {χ : E3 → ℝ} {Ψ : X n → ℝ} (q : E3) (x : X n) :
    frameIntegrand volA Ac χ Ψ q x
      ≤ volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
            + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2) := by
  have hRe := boxTauAnnGen_sq_le_card_mul (n := n) (volA := volA) hvolpos (Ac := Ac)
    (g := boxWinModeReGen volA Ac χ q) (Ψ := Ψ) x
  have hIm := boxTauAnnGen_sq_le_card_mul (n := n) (volA := volA) hvolpos (Ac := Ac)
    (g := boxWinModeImGen volA Ac χ q) (Ψ := Ψ) x
  have hsplit : (∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
          + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2))
      = (∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
        + (∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hdef : frameIntegrand volA Ac χ Ψ q x
      = (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
        + (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2 := rfl
  rw [hdef, hsplit, mul_add]
  exact add_le_add hRe hIm

/-! ## Measurability of the frame integrand along `q` at fixed `x` -/

/-- For fixed `x` the frame integrand is (a.e.) strongly measurable as a function of `q`. -/
private lemma aestronglyMeasurable_frameIntegrand_axis {n : ℕ} {volA : ℝ}
    {Ac : Set E3} (hAcm : MeasurableSet Ac) {χ : E3 → ℝ} (hχc : Continuous χ)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (x : X n) :
    AEStronglyMeasurable (fun q : E3 => frameIntegrand volA Ac χ Ψ q x) volume := by
  have hRe := measurable_boxTauAnnGen_param (N := n) volA hAcm
    (measurable_boxWinModeReGen_uncurry (volA := volA) hAcm hχc) hΨ.measurable
  have hIm := measurable_boxTauAnnGen_param (N := n) volA hAcm
    (measurable_boxWinModeImGen_uncurry (volA := volA) hAcm hχc) hΨ.measurable
  have hRe' : Measurable (fun q : E3 =>
      boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) :=
    hRe.comp (measurable_id.prodMk measurable_const)
  have hIm' : Measurable (fun q : E3 =>
      boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) :=
    hIm.comp (measurable_id.prodMk measurable_const)
  have hgoal : (fun q : E3 => frameIntegrand volA Ac χ Ψ q x)
      = fun q : E3 => (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
          + (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2 := rfl
  rw [hgoal]
  exact ((hRe'.pow_const 2).add (hIm'.pow_const 2)).aestronglyMeasurable

/-! ## The window weight, with `|χ| ≤ κ` only -/

/-- **The window weight bound** `∫_Ac (χ·Q)² ≤ κ² ∫_Ac Q²`, for `|χ| ≤ κ` (no positivity of `χ`
or of `κ` is needed: the pointwise step is `(χ z)² ≤ κ²`, from `|χ z| ≤ κ ≤ |κ|`). -/
private lemma slotFibre_sq_weight_le_abs {n : ℕ} {a volA κ : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    {χ : E3 → ℝ} (hκ : ∀ z, |χ z| ≤ κ)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) (x : X n) :
    (∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2)
      ≤ κ ^ 2 * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 := by
  have hpt : ∀ z : E3, (χ z * slotFibre volA Ac i Ψ x z) ^ 2
      ≤ κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2 := by
    intro z
    have h2 : (χ z) ^ 2 ≤ κ ^ 2 := by
      have h3 : |χ z| ≤ |κ| := le_trans (hκ z) (le_abs_self κ)
      have h4 : (|χ z|) ^ 2 ≤ (|κ|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rwa [sq_abs, sq_abs] at h4
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hInt : IntegrableOn (fun z => κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2) Ac volume :=
    (integrableOn_slotFibre_sq ha hAcm hAc hΨ i x).const_mul (κ ^ 2)
  have hmono := integral_mono_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict Ac)
    (f := fun z => (χ z * slotFibre volA Ac i Ψ x z) ^ 2)
    (g := fun z => κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2)
    (Eventually.of_forall fun z => sq_nonneg _) hInt (Eventually.of_forall hpt)
  have hconst : (∫ z, κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict Ac))
      = κ ^ 2 * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 :=
    integral_const_mul _ _
  rw [hconst] at hmono
  exact hmono

/-! ## The per-configuration frame bound -/

theorem framePerXBound {n : ℕ} {a volA κ : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hκ : ∀ z, |χ z| ≤ κ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) (x : Submission.BoseGases.X n) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.frameIntegrand volA Ac χ Ψ q x)
      ∧ (∫ q : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.frameIntegrand volA Ac χ Ψ q x)
        ≤ volA⁻¹ * (n : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
            ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2 := by
  have hB : ∀ i : Fin n, Integrable (fun q : E3 =>
      (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
        + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2) :=
    fun i => (slotPlancherel_cont ha hAcm hAc hvol hvolpos hχc hχs hχsupp hΨ i x).1
  have hBnd : Integrable (fun q : E3 =>
      volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
          + (∫ z in Ac, boxWinModeImGen volA Ac χ q z
              * Ψ (Function.update x i z)) ^ 2)) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ (fun i _ => (hB i).const_mul _)
  have hInt : Integrable (fun q : E3 => frameIntegrand volA Ac χ Ψ q x) :=
    Integrable.mono' hBnd (aestronglyMeasurable_frameIntegrand_axis hAcm hχc hΨ x)
      (Eventually.of_forall fun q => by
        rw [Real.norm_of_nonneg (frameIntegrand_nonneg volA Ac χ Ψ q x)]
        exact frameIntegrand_le_card_mul hvolpos q x)
  refine ⟨hInt, ?_⟩
  have hmain := integral_mono_of_nonneg
    (f := fun q : E3 => frameIntegrand volA Ac χ Ψ q x)
    (g := fun q : E3 => volA⁻¹ * (n : ℝ) * ∑ i : Fin n,
        Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
            + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2))
    (Eventually.of_forall fun q => frameIntegrand_nonneg volA Ac χ Ψ q x)
    hBnd (Eventually.of_forall fun q => frameIntegrand_le_card_mul hvolpos q x)
  have hval : (∫ q, volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
          + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2))
      = volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ((2 * Real.pi) ^ 3 * ∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hB i).const_mul _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact (slotPlancherel_cont ha hAcm hAc hvol hvolpos hχc hχs hχsupp hΨ i x).2
  rw [hval] at hmain
  have hkey : (∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ((2 * Real.pi) ^ 3 * ∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2))
      ≤ (2 * Real.pi) ^ 3 * κ ^ 2 * ∑ i : Fin n,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hw := slotFibre_sq_weight_le_abs (volA := volA) ha hAcm hAc hκ hΨ i x
    have h2πnn : (0 : ℝ) ≤ (2 * Real.pi) ^ 3 := by positivity
    have hind : 0 ≤ Ac.indicator (fun _ => (1 : ℝ)) (x i) := by
      by_cases h : x i ∈ Ac
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    have hw' : Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2)
        ≤ Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (κ ^ 2 * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2) :=
      mul_le_mul_of_nonneg_left hw hind
    have hb : (2 * Real.pi) ^ 3 * (Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2))
        ≤ (2 * Real.pi) ^ 3 * (Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (κ ^ 2 * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2)) :=
      mul_le_mul_of_nonneg_left hw' h2πnn
    linarith [hb]
  refine hmain.trans ?_
  calc volA⁻¹ * (n : ℝ) * (∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ((2 * Real.pi) ^ 3 * ∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2))
      ≤ volA⁻¹ * (n : ℝ) * ((2 * Real.pi) ^ 3 * κ ^ 2
          * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg (inv_nonneg.mpr hvolpos.le) (by positivity))
    _ = volA⁻¹ * (n : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3
          * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 := by ring


end Work.BoseFixB1B.pairRung
