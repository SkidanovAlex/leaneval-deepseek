import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.SlotWord.measurable_boxQInd
import Submission.Work.SmallBoxA0.WinModeReIm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxFrameBackup` — a self-contained proof of the slot swap

The slot-swap identity used by the frame bound, proved here directly from the corpus peel of
the centred box (`BoseGases.abox_integral_peel`):

  `∫_x 1_Ac(x_i)·∫_{z∈Ac}H(x_{i↦z}) = |Ac|·∫_x 1_Ac(x_i)·H x`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `∫_{acube a} 1_Ac = volA`. -/
lemma setIntegral_indicator_one_eq {a volA : ℝ} {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) :
    (∫ y in Submission.BoseGases.acube a, Ac.indicator (fun _ => (1 : ℝ)) y) = volA := by
  have h1 : (∫ y in Submission.BoseGases.acube a,
        Ac.indicator (fun _ => (1 : ℝ)) y) = ∫ _y in Ac, (1 : ℝ) := by
    rw [← integral_indicator hAcm]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    by_cases h : y ∈ Ac
    · exact absurd (hAc h) hy
    · rw [Set.indicator_of_notMem h]
  rw [h1, MeasureTheory.setIntegral_const, Measure.real_def, ← hvol]
  simp

/-- Inserting a point of `A` into a slot of a box configuration keeps it in the box. -/
lemma update_mem_abox' {n : ℕ} {a : ℝ} {A : Set E3} (hA : A ⊆ Submission.BoseGases.acube a)
    {x : X n} (hx : x ∈ abox n a) (i : Fin n) {z : E3} (hz : z ∈ A) :
    Function.update x i z ∈ abox n a := by
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact hA hz
  · rw [Function.update_of_ne hj]
    exact hx j

/-- **The slot swap.** -/
theorem slotSwap_abox' {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (i : Fin n) {H : Submission.BoseGases.X n → ℝ} (hH : Measurable H) {K : ℝ} (hK : 0 ≤ K)
    (hHb : ∀ x ∈ Submission.BoseGases.abox n a, |H x| ≤ K) :
    (∫ x in Submission.BoseGases.abox n a,
        Ac.indicator (fun _ => (1 : ℝ)) (x i) * (∫ z in Ac, H (Function.update x i z)))
      = volA * ∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i) * H x := by
  rcases n with _ | m
  · exact Fin.elim0 i
  · haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)
    -- integrability of the outer integrand
    have hIntOut : IntegrableOn (fun x : X (m + 1) =>
        Ac.indicator (fun _ => (1 : ℝ)) (x i) * (∫ z in Ac, H (Function.update x i z)))
        (abox (m + 1) a) volume := by
      have hupd : Measurable (fun p : X (m + 1) × E3 => H (Function.update p.1 i p.2)) :=
        hH.comp measurable_update'
      refine IntegrableOn.of_bound (abox_compact (m + 1) ha).measure_lt_top
        ((((measurable_const.indicator hAcm).comp (measurable_pi_apply i)).mul
          ((hupd.stronglyMeasurable).integral_prod_right
            (ν := (volume : Measure E3).restrict Ac)).measurable)).aestronglyMeasurable
        (1 * (K * volA)) ?_
      rw [ae_restrict_iff' (abox_measurable (m + 1) a)]
      refine ae_of_all _ (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have hind : |Ac.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (1 : ℝ) := by
        by_cases h : x i ∈ Ac
        · rw [Set.indicator_of_mem h, abs_one]
        · rw [Set.indicator_of_notMem h, abs_zero]; norm_num
      have hinner : |∫ z in Ac, H (Function.update x i z)| ≤ K * volA := by
        have hb : ∀ z ∈ Ac, |H (Function.update x i z)| ≤ K :=
          fun z hz => hHb _ (update_mem_abox' hAc hx i hz)
        have hI : IntegrableOn (fun z : E3 => H (Function.update x i z)) Ac volume :=
          IntegrableOn.of_bound
            (lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le))
            ((hH.comp (measurable_update (f := x) (a := i))).aestronglyMeasurable) K
            (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
        refine (abs_integral_le_integral_abs).trans ?_
        have hmono := integral_mono_of_nonneg
          (μ := (volume : Measure E3).restrict Ac)
          (f := fun z => |H (Function.update x i z)|) (g := fun _ : E3 => K)
          (Eventually.of_forall fun z => abs_nonneg _) (integrable_const K)
          (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ hb))
        exact hmono.trans (le_of_eq (by
          rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol, smul_eq_mul,
            mul_comm]))
      calc |Ac.indicator (fun _ => (1 : ℝ)) (x i)|
            * |∫ z in Ac, H (Function.update x i z)| ≤ 1 * (K * volA) :=
            mul_le_mul hind hinner (abs_nonneg _) (by norm_num)
        _ = 1 * (K * volA) := rfl
    -- left-hand side: peel and evaluate the `y`-integral
    rw [abox_integral_peel (n := m) (ℓ := a) i _ hIntOut]
    have hstep : ∀ r : X m, (∫ y : E3 in acube a,
        Ac.indicator (fun _ => (1 : ℝ)) (kcInsN m i (y, r) i)
          * (∫ z in Ac, H (Function.update (kcInsN m i (y, r)) i z)))
        = (∫ y in acube a, Ac.indicator (fun _ => (1 : ℝ)) y)
          * (∫ z in Ac, H (kcInsN m i (z, r))) := by
      intro r
      have hpt : ∀ y : E3,
          Ac.indicator (fun _ => (1 : ℝ)) (kcInsN m i (y, r) i)
            * (∫ z in Ac, H (Function.update (kcInsN m i (y, r)) i z))
          = (∫ z in Ac, H (kcInsN m i (z, r))) * Ac.indicator (fun _ => (1 : ℝ)) y := by
        intro y
        rw [kc_insN_apply_same m i y r]
        have hz : (∫ z in Ac, H (Function.update (kcInsN m i (y, r)) i z))
            = ∫ z in Ac, H (kcInsN m i (z, r)) :=
          integral_congr_ae (Eventually.of_forall fun z => by
            simp only [update_kcInsN])
        rw [hz]
        ring
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, mul_comm]
    rw [show (∫ r : X m, (∫ y : E3 in acube a,
          Ac.indicator (fun _ => (1 : ℝ)) (kcInsN m i (y, r) i)
            * (∫ z in Ac, H (Function.update (kcInsN m i (y, r)) i z)))
          ∂((volume : Measure (X m)).restrict (abox m a)))
        = (∫ y in acube a, Ac.indicator (fun _ => (1 : ℝ)) y)
          * ∫ r : X m, (∫ z in Ac, H (kcInsN m i (z, r)))
              ∂((volume : Measure (X m)).restrict (abox m a)) from
      (by rw [integral_congr_ae (Eventually.of_forall hstep), integral_const_mul])]
    rw [setIntegral_indicator_one_eq hAcm hAc hvol]
    -- right-hand side: peel
    have hIntR : IntegrableOn (fun x : X (m + 1) =>
        Ac.indicator (fun _ => (1 : ℝ)) (x i) * H x) (abox (m + 1) a) volume := by
      refine IntegrableOn.of_bound (abox_compact (m + 1) ha).measure_lt_top
        ((((measurable_const.indicator hAcm).comp (measurable_pi_apply i)).mul hH)).aestronglyMeasurable
        (1 * K) ?_
      rw [ae_restrict_iff' (abox_measurable (m + 1) a)]
      refine ae_of_all _ (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have hind : |Ac.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (1 : ℝ) := by
        by_cases h : x i ∈ Ac
        · rw [Set.indicator_of_mem h, abs_one]
        · rw [Set.indicator_of_notMem h, abs_zero]; norm_num
      exact (mul_le_mul hind (hHb x hx) (abs_nonneg _) (by norm_num)).trans
        (le_of_eq (by ring))
    rw [abox_integral_peel (n := m) (ℓ := a) i _ hIntR]
    have hstep2 : ∀ r : X m, (∫ y : E3 in acube a,
        Ac.indicator (fun _ => (1 : ℝ)) (kcInsN m i (y, r) i) * H (kcInsN m i (y, r)))
        = ∫ z in Ac, H (kcInsN m i (z, r)) := by
      intro r
      have hp : ∀ y : E3, Ac.indicator (fun _ => (1 : ℝ)) (kcInsN m i (y, r) i)
            * H (kcInsN m i (y, r))
          = Ac.indicator (fun z : E3 => H (kcInsN m i (z, r))) y := by
        intro y
        rw [kc_insN_apply_same m i y r]
        by_cases h : y ∈ Ac
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h]
      rw [show (∫ y : E3 in acube a,
            Ac.indicator (fun _ => (1 : ℝ)) (kcInsN m i (y, r) i) * H (kcInsN m i (y, r)))
          = ∫ y : E3 in acube a,
              Ac.indicator (fun z : E3 => H (kcInsN m i (z, r))) y from
        integral_congr_ae (Eventually.of_forall hp)]
      rw [show (∫ y : E3 in acube a,
            Ac.indicator (fun z : E3 => H (kcInsN m i (z, r))) y)
          = ∫ y : E3, Ac.indicator (fun z : E3 => H (kcInsN m i (z, r))) y from
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
          by_cases h : y ∈ Ac
          · exact absurd (hAc h) hy
          · simp [Set.indicator_of_notMem h])]
      rw [integral_indicator hAcm]
    rw [integral_congr_ae (Eventually.of_forall hstep2)]


/-! ## The Plancherel identity for one slot -/

/-- The norm of a real complex number. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- The windowed fibre vanishes off the box. -/
lemma fib_eq_zero_of_notMem {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (i : Fin n) (Ψ : X n → ℝ) (x : X n) {z : E3}
    (hz : z ∉ Ac) :
    χ z * slotFibre volA Ac i Ψ x z = 0 := by
  rw [hχsupp z hz, zero_mul]

/-- **Plancherel for one slot** (the identity used by the frame bound). -/
theorem framePlancherel_slot' {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
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
      hχc.continuous.continuousOn
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
    refine Measurable.mul hχc.continuous.measurable ?_
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
          rw [slotAmp_re_eq ha hAcm hAc hvol hvolpos hχc.continuous hΨ i x q]
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
          simp only [hF, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
            zero_add, Work.SmallBoxA0.win_exp_neg_inner_im]
          ring
      _ = -(∫ y : E3, Real.sin (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y)) :=
          integral_neg _
      _ = -(∫ y in Ac, Real.sin (inner ℝ q y) * (χ y * slotFibre volA Ac i Ψ x y)) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
            rw [fib_eq_zero_of_notMem hχsupp i Ψ x hy, mul_zero])]
      _ = ∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z) := by
          rw [slotAmp_im_eq ha hAcm hAc hvol hvolpos hχc.continuous hΨ i x q]
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

end Work.BoseFixB1
