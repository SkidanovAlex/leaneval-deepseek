import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.boxQInd_update_eq
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1.tBamp_boxQInd_integrableOn_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.integrableFsKinTBampN`

`p`-integrability of the FS-faithful spectral kinetic integrand at the box mean-free projection
`Q_{B,i} = boxQInd volA Ac i Ψ`:

    p ↦ fsKinCoeff c₀ ‖p‖ · ((a³)⁻¹ ∫_{abox n a} ‖tBamp χ p (Q_{B,i}Ψ) i x‖² dx).

The object has to decay in `p` even though `fsKinCoeff c₀ ‖·‖` *grows* like `‖p‖²`, and the
projection `Q_{B,i}Ψ` is not smooth (it carries the indicator of `Ac`).  The resolution is the
exact split

    tBamp χ p (Q_{B,i}Ψ) i x = tBamp χ p Ψ i x − c(x)·tBamp χ p 1 i x,
    c(x) = |A|⁻¹∫_A Ψ(x_{i←w})dw,

which holds because the window `χ` vanishes off `Ac` (`χ·1_A = χ`), so the box indicator
disappears inside the amplitude; both remaining amplitudes are the windowed Fourier transforms of
**smooth compactly supported** fibres and obey the uniform `(1+‖p‖)⁻³` decay `tBamp_decay`.
`|c|` is bounded uniformly on the box, so the squared amplitude is `≤ C/(1+‖p‖)^6`, the box
integral gains a factor `|abox| = (a³)^n`, and `fsKinCoeff c₀ ‖p‖ ≤ (2+2c₀²)(1+‖p‖)²` turns the
whole integrand into a multiple of `(1+‖p‖)^(-4)`, which is integrable in dimension three
(`integrable_one_add_norm`).
-/

namespace Work.BoseFixB1B.pairRung

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## 1. The windowed amplitude of a bounded continuous state is integrable -/

private theorem integrable_tBamp_kernel {n : ℕ} {χ : ℝ³ → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (p : ℝ³) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) (i : Fin n) (x : Submission.BoseGases.X n) :
    Integrable (fun z : ℝ³ => (χ z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Ψ (Function.update x i z) : ℂ)) := by
  have hcont : Continuous (fun z : ℝ³ => (χ z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Ψ (Function.update x i z) : ℂ)) := by
    refine Continuous.mul (Continuous.mul ?_ ?_) ?_
    · exact Complex.continuous_ofReal.comp hχc
    · refine Complex.continuous_exp.comp ?_
      refine Continuous.neg ?_
      exact continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))
    · exact Complex.continuous_ofReal.comp
        (hΨc.comp (Continuous.update continuous_const i continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hχs ?_
  intro z hz
  rw [Function.mem_support] at hz
  exact subset_tsupport χ (Function.mem_support.mpr (fun hχz => hz (by rw [hχz]; simp)))

/-! ## 2. The exact split of the box-projected amplitude -/

private theorem tBamp_boxQInd_eq {n : ℕ} {volA : ℝ} {Ac : Set ℝ³} {χ : ℝ³ → ℝ}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z : ℝ³, z ∉ Ac → χ z = 0)
    (i : Fin n) {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ)
    (x : Submission.BoseGases.X n) (p : ℝ³) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x
      = Work.SmallBoxTBWord.tBamp χ p Ψ i x
        - (((1 / volA) * ∫ w in Ac, Ψ (Function.update x i w) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x := by
  classical
  set c : ℝ := (1 / volA) * ∫ w in Ac, Ψ (Function.update x i w) with hc
  have hInt1 : Integrable (fun z : ℝ³ => (χ z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Ψ (Function.update x i z) : ℂ)) :=
    integrable_tBamp_kernel hχc hχs p hΨc i x
  have hInt2 : Integrable (fun z : ℝ³ => (χ z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((1 : ℝ) : ℂ)) :=
    integrable_tBamp_kernel hχc hχs p continuous_const i x
  -- the window swallows the box indicator
  have hchiC : ∀ z : ℝ³,
      (χ z : ℂ) * ((Ac.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) = (χ z : ℂ) := by
    intro z
    have hchi : χ z * (Ac.indicator (fun _ => (1 : ℝ)) z) = χ z := by
      by_cases hz : z ∈ Ac
      · rw [Set.indicator_of_mem hz, mul_one]
      · rw [Set.indicator_of_notMem hz, mul_zero, hχsupp z hz]
    calc (χ z : ℂ) * ((Ac.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ)
        = ((χ z * (Ac.indicator (fun _ => (1 : ℝ)) z) : ℝ) : ℂ) := by push_cast; ring
      _ = (χ z : ℂ) := by rw [hchi]
  -- the pointwise identity of the integrands
  have hpt : ∀ z : ℝ³,
      (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z)) : ℂ)
      = (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)
        - (c : ℂ) * ((χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ((1 : ℝ) : ℂ)) := by
    intro z
    have hbc := Work.BoseFixB1.boxQInd_update_eq volA Ac i Ψ x z
    rw [hbc, ← hc]
    rw [show ((Ac.indicator (fun _ => (1 : ℝ)) z * (Ψ (Function.update x i z) - c) : ℝ) : ℂ)
        = ((Ac.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) * ((Ψ (Function.update x i z) : ℂ) - (c : ℂ))
      from by push_cast; ring]
    calc (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (((Ac.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) *
            ((Ψ (Function.update x i z) : ℂ) - (c : ℂ)))
        = ((χ z : ℂ) * ((Ac.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ((Ψ (Function.update x i z) : ℂ) - (c : ℂ)) := by ring
      _ = (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ((Ψ (Function.update x i z) : ℂ) - (c : ℂ)) := by rw [hchiC]
      _ = (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Ψ (Function.update x i z) : ℂ)
          - (c : ℂ) * ((χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((1 : ℝ) : ℂ)) := by push_cast; ring
  -- integrate
  have hL : Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x
      = ∫ z : ℝ³, ((χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Ψ (Function.update x i z) : ℂ)
          - (c : ℂ) * ((χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((1 : ℝ) : ℂ))) := by
    rw [Work.SmallBoxTBWord.tBamp]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hX : Work.SmallBoxTBWord.tBamp χ p Ψ i x
      = ∫ z : ℝ³, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ) := rfl
  have hY : Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x
      = ∫ z : ℝ³, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((1 : ℝ) : ℂ) := rfl
  rw [hL, hX, hY]
  rw [MeasureTheory.integral_sub hInt1 (hInt2.const_mul (c : ℂ)),
    MeasureTheory.integral_const_mul]

/-! ## 3. Real arithmetic: the growth of `[r−c]₊²` against the `(1+r)⁻⁶` decay -/

private lemma fsKinCoeff_mul_div_le {c₀ r P : ℝ} (hr : 0 ≤ r) (hP : 0 ≤ P) :
    Submission.BoseGases.fsKinCoeff c₀ r * (P / (1 + r) ^ 6)
      ≤ (2 + 2 * c₀ ^ 2) * P * ((1 + r) ^ 4)⁻¹ := by
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have hfs : Submission.BoseGases.fsKinCoeff c₀ r ≤ (2 + 2 * c₀ ^ 2) * (1 + r) ^ 2 := by
    have hmax : max (r - c₀) 0 ≤ r + |c₀| :=
      max_le (by linarith [neg_le_abs c₀]) (by positivity)
    have h1 : Submission.BoseGases.fsKinCoeff c₀ r ≤ (r + |c₀|) ^ 2 := by
      rw [Submission.BoseGases.fsKinCoeff]
      exact pow_le_pow_left₀ (le_max_right _ _) hmax 2
    have h2 : (r + |c₀|) ^ 2 ≤ (2 + 2 * c₀ ^ 2) * (1 + r) ^ 2 := by
      have hc : |c₀| ^ 2 = c₀ ^ 2 := sq_abs c₀
      nlinarith [sq_nonneg (r - |c₀|), abs_nonneg c₀, sq_nonneg r, sq_nonneg (1 + r), hc]
    linarith [h1, h2]
  have hstep : Submission.BoseGases.fsKinCoeff c₀ r * (P / (1 + r) ^ 6)
      ≤ ((2 + 2 * c₀ ^ 2) * (1 + r) ^ 2) * (P / (1 + r) ^ 6) :=
    mul_le_mul_of_nonneg_right hfs (div_nonneg hP (by positivity))
  have hEq : ((2 + 2 * c₀ ^ 2) * (1 + r) ^ 2) * (P / (1 + r) ^ 6)
      = (2 + 2 * c₀ ^ 2) * P * ((1 + r) ^ 4)⁻¹ := by
    field_simp
  exact le_of_le_of_eq hstep hEq

/-! ## 4. The target -/

theorem integrableFsKinTBampN {n : ℕ} {a volA c₀ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Ac → χ z = 0)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
  classical
  have hχcont : Continuous χ := hχc.continuous
  have hΨcont : Continuous Ψ := hΨc.continuous
  -- the two decay bounds
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n) ha hχc hχs hΨc
  obtain ⟨C₂, hC₂0, hC₂⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n) ha hχc hχs
    (Φ := fun _ : Submission.BoseGases.X n => (1 : ℝ)) contDiff_const
  -- a sup bound for `Ψ` on the box
  obtain ⟨B0, hB0⟩ :=
    (Submission.BoseGases.abox_compact n ha).exists_bound_of_continuousOn hΨcont.continuousOn
  have hB0' : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ max B0 0 := by
    intro x hx
    have h1 := hB0 x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  -- the box `Ac` has finite volume
  have hfinAc : (volume : Measure ℝ³) Ac < ⊤ := by
    have h1 : (volume : Measure ℝ³) Ac ≤ (volume : Measure ℝ³) (Submission.BoseGases.acube a) :=
      measure_mono hAc
    have h2 : (volume : Measure ℝ³) (Submission.BoseGases.acube a) < ⊤ := by
      rw [Submission.BoseGases.acube_volume a ha.le]
      exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt h1 h2
  -- inserting a point of `Ac` in slot `i` keeps a box configuration in the box
  have hmem_upd : ∀ x ∈ Submission.BoseGases.abox n a, ∀ w ∈ Ac,
      Function.update x i w ∈ Submission.BoseGases.abox n a := by
    intro x hx w hw
    rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
    intro j
    rw [Function.update_apply]
    by_cases hj : j = i
    · rw [if_pos hj]; exact hAc hw
    · rw [if_neg hj]; exact hx j
  -- the uniform bound on the box mean
  set M : ℝ := (1 / volA) * (max B0 0 * (volume : Measure ℝ³).real Ac) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : (0 : ℝ) ≤ (volume : Measure ℝ³).real Ac := measureReal_nonneg
    have h2 : (0 : ℝ) < 1 / volA := by positivity
    exact mul_nonneg h2.le (mul_nonneg (le_max_right _ _) h1)
  have hcc : ∀ x ∈ Submission.BoseGases.abox n a,
      |(1 / volA) * ∫ w in Ac, Ψ (Function.update x i w)| ≤ M := by
    intro x hx
    rw [hMdef]
    have hint : |∫ w in Ac, Ψ (Function.update x i w)| ≤ max B0 0 * (volume : Measure ℝ³).real Ac := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³)) (s := Ac)
        (f := fun w => Ψ (Function.update x i w)) (C := max B0 0) hfinAc
        (fun w hw => by
          rw [Real.norm_eq_abs]
          exact hB0' _ (hmem_upd x hx w hw))
      rwa [Real.norm_eq_abs] at h
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / volA)]
    exact mul_le_mul_of_nonneg_left hint (by positivity)
  -- the amplitude decays like `(1+‖p‖)⁻³`
  set Cq : ℝ := C₁ + M * C₂ with hCqdef
  have hCq0 : 0 ≤ Cq := by
    rw [hCqdef]
    exact add_nonneg hC₁0 (mul_nonneg hM0 hC₂0)
  have hamp : ∀ (p : ℝ³) (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n a →
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖
        ≤ Cq / (1 + ‖p‖) ^ 3 := by
    intro p x hx
    rw [tBamp_boxQInd_eq hχcont hχs hχsupp i hΨcont x p]
    have h2 := hC₂ x hx i p
    have h3 := hcc x hx
    have hnorm : ‖(((1 / volA) * ∫ w in Ac, Ψ (Function.update x i w) : ℝ) : ℂ)
            * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖
        = |(1 / volA) * ∫ w in Ac, Ψ (Function.update x i w)|
          * ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hCqdef]
    calc ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x
          - (((1 / volA) * ∫ w in Ac, Ψ (Function.update x i w) : ℝ) : ℂ)
            * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖
        ≤ ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
          + ‖(((1 / volA) * ∫ w in Ac, Ψ (Function.update x i w) : ℝ) : ℂ)
            * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ :=
          norm_sub_le _ _
      _ = ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
          + |(1 / volA) * ∫ w in Ac, Ψ (Function.update x i w)|
            * ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := by
          rw [hnorm]
      _ ≤ C₁ / (1 + ‖p‖) ^ 3 + M * (C₂ / (1 + ‖p‖) ^ 3) :=
          add_le_add (hC₁ x hx i p) (mul_le_mul h3 h2 (norm_nonneg _) hM0)
      _ = (C₁ + M * C₂) / (1 + ‖p‖) ^ 3 := by rw [← mul_div_assoc, ← add_div]
  -- the box integral of the squared amplitude
  have hInt : ∀ p : ℝ³, ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2
      ≤ ((a ^ 3) ^ n) * (Cq / (1 + ‖p‖) ^ 3) ^ 2 := by
    intro p
    have hvolbox : (volume : Measure (Submission.BoseGases.X n)).real
        (Submission.BoseGases.abox n a) = (a ^ 3) ^ n := by
      rw [MeasureTheory.Measure.real_def, Submission.BoseGases.abox_volume n a ha.le,
        ENNReal.toReal_ofReal (by positivity)]
    haveI : IsFiniteMeasure
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n a)) := by
      rw [MeasureTheory.isFiniteMeasure_restrict]
      exact (Submission.BoseGases.abox_lt_top n a ha.le).ne
    have hle := MeasureTheory.integral_mono_of_nonneg
      (μ := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n a))
      (f := fun x : Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      (g := fun _ : Submission.BoseGases.X n => (Cq / (1 + ‖p‖) ^ 3) ^ 2)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (MeasureTheory.integrable_const _)
      ((MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n a)).mono
        (fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hamp p x hx) 2))
    calc ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2
        ≤ ∫ x in Submission.BoseGases.abox n a, (Cq / (1 + ‖p‖) ^ 3) ^ 2 := hle
      _ = ((a ^ 3) ^ n) * (Cq / (1 + ‖p‖) ^ 3) ^ 2 := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvolbox]
  -- the dominating function
  set P : ℝ := (a ^ 3)⁻¹ * ((a ^ 3) ^ n * Cq ^ 2) with hPdef
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    have h1 : (0 : ℝ) ≤ (a ^ 3)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ (a ^ 3) ^ n * Cq ^ 2 := by positivity
    exact mul_nonneg h1 h2
  have hEq : ∀ p : ℝ³, (a ^ 3)⁻¹ * (((a ^ 3) ^ n) * (Cq / (1 + ‖p‖) ^ 3) ^ 2)
      = P / (1 + ‖p‖) ^ 6 := by
    intro p
    have hX : (Cq / (1 + ‖p‖) ^ 3) ^ 2 = Cq ^ 2 / (1 + ‖p‖) ^ 6 := by
      rw [div_pow, ← pow_mul]
    rw [hX, hPdef]
    ring
  have hdom : Integrable (fun p : ℝ³ => (2 + 2 * c₀ ^ 2) * P * ((1 + ‖p‖) ^ 4)⁻¹) := by
    have hbase : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4 : ℝ))) volume :=
      integrable_one_add_norm (E := ℝ³) (μ := (volume : Measure ℝ³)) (r := 4) (by
        rw [finrank_euclideanSpace_fin]
        norm_num)
    refine (hbase.const_mul ((2 + 2 * c₀ ^ 2) * P)).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    have hpos : (0 : ℝ) < 1 + ‖p‖ := by positivity
    calc ((2 + 2 * c₀ ^ 2) * P) * (1 + ‖p‖) ^ (-(4 : ℝ))
        = ((2 + 2 * c₀ ^ 2) * P) * (((1 + ‖p‖) ^ (4 : ℝ)))⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hpos)]
      _ = ((2 + 2 * c₀ ^ 2) * P) * (((1 + ‖p‖) ^ 4))⁻¹ := by
          rw [show (1 + ‖p‖) ^ (4 : ℝ) = (1 + ‖p‖) ^ 4 from Real.rpow_natCast (1 + ‖p‖) 4]
      _ = (2 + 2 * c₀ ^ 2) * P * ((1 + ‖p‖) ^ 4)⁻¹ := by ring
  -- joint measurability of the box-integral
  have hmeasInt : StronglyMeasurable (fun p : ℝ³ => ∫ x in Submission.BoseGases.abox n a,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
    have hp := (Work.BoseFixB1.measurable_tBamp_boxQInd_pair (n := n) (volA := volA) hAcm
      hχcont hΨcont.measurable i).stronglyMeasurable
    have := hp.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n a))
    simpa using this
  have haesm : AEStronglyMeasurable (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) volume := by
    have hcont' : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c₀ ‖p‖) :=
      ((continuous_norm.sub continuous_const).max continuous_const).pow 2
    exact (hcont'.aestronglyMeasurable).mul (hmeasInt.aestronglyMeasurable.const_mul _)
  -- the pointwise domination
  have hpoint : ∀ᵐ p : ℝ³ ∂(volume : Measure ℝ³),
      ‖Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)‖
      ≤ (2 + 2 * c₀ ^ 2) * P * ((1 + ‖p‖) ^ 4)⁻¹ := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hIp : 0 ≤ ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 :=
      MeasureTheory.setIntegral_nonneg (Submission.BoseGases.abox_measurable n a)
        (fun x _ => sq_nonneg _)
    have hnonneg : 0 ≤ Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖p‖)
        (mul_nonneg (by positivity) hIp)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        ≤ Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
            (((a ^ 3) ^ n) * (Cq / (1 + ‖p‖) ^ 3) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hInt p) (by positivity))
            (Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖p‖)
      _ = Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * (P / (1 + ‖p‖) ^ 6) := by
          rw [hEq p]
      _ ≤ (2 + 2 * c₀ ^ 2) * P * ((1 + ‖p‖) ^ 4)⁻¹ :=
          fsKinCoeff_mul_div_le (norm_nonneg p) hP0
  exact hdom.mono' haesm hpoint

end

end Work.BoseFixB1B.pairRung
