import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.FibreSpec.tBamp_slotPiece_ampSq_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.integrableOn_tBamp_boxQInd_abox`

The **(R3)-integrability side condition** of the slot-word / cube-window chapter in its general
form: for a measurable window `χ` of finite `L¹`-norm carried by a measurable set `A ⊆ acube L` of
finite measure, and a continuous state `Φ`, the squared modulus of the windowed amplitude

  `tBamp χ p Ψ i x = ∫ z, χ z · e^{−i⟪p,z⟫} · Ψ (x_{i←z})`,   `Ψ = Q_{A,i}(slotPiece A S Φ)`,

is `IntegrableOn` the ambient box `abox N L`.

## The argument

`tBamp` is an integral over `ℝ³` of a function supported (modulo the `χ z = 0` factor) in
`tsupport χ ⊆ A ⊆ acube L`.  For `x ∈ abox N L` and `z ∈ A` the updated configuration
`x_{i←z}` lies again in `abox N L`, where `Φ` is bounded by `M = sup_{abox N L} |Φ|`
(`Φ` is continuous and the box is compact).  The slot piece is bounded by `M` too (it is an
indicator times `Φ`), and the box mean `|A|⁻¹∫_A slotPiece(x_{i←z}) dz` is bounded by `M`
because the mean is an average over a set on which the integrand is bounded by `M` — the
volume factor cancels, including in the degenerate case `|A| = 0` (where the mean vanishes).
Hence on the box `|Ψ| ≤ 2M`, and therefore

  `‖tBamp χ p Ψ i x‖ ≤ (2M)·∫ z, |χ z|`   for `x ∈ abox N L`.

This constant dominates the (a.e.-strongly measurable) integrand on the finite-measure box, so
`Integrable.of_bound` closes.  Measurability of the amplitude is
`StronglyMeasurable.integral_prod_right'` applied to the jointly measurable integrand
`(x,z) ↦ χ z · e^{−i⟪p,z⟫} · Ψ(x_{i←z})`.

Everything is fully general in `A`, `χ`, `volA`; the specialisations used by the chapter
(`A = dlBox L d u`, `χ = chiB L d u`, `volA = boxMass L d u`) are immediate instances.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector
open Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The general (R3)-integrability.**  If `A` is a measurable subset of the cube `acube L` of
finite measure, `volA` its volume, `χ` a measurable window of finite `L¹`-norm carried by `A`,
and `Φ` continuous, then the squared windowed amplitude of `Q_{A,i}(slotPiece A S Φ)` is
integrable over `abox N L`. -/
private theorem integrableOn_tBamp_boxQInd_abox_general {N : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Set ℝ³} (hA : MeasurableSet A) (hAsub : A ⊆ Submission.BoseGases.acube L)
    (hAfin : (volume : Measure ℝ³) A < ⊤) (volA : ℝ)
    (hvolA : volA = (volume : Measure ℝ³).real A)
    {χ : ℝ³ → ℝ} (hχmeas : Measurable χ)
    (hχint : MeasureTheory.Integrable (fun z : ℝ³ => |χ z|))
    (hχsupp : ∀ z : ℝ³, χ z ≠ 0 → z ∈ A)
    {S : Finset (Fin N)} {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ)
    (i : Fin N) (p : ℝ³) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i x‖ ^ 2)
      (Submission.BoseGases.abox N L) := by
  classical
  haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N L)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi N L]; infer_instance
  set Ψ : Submission.BoseGases.X N → ℝ :=
    Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ) with hΨdef
  -- ## The uniform bound `M` on the state
  obtain ⟨M₀, hM₀⟩ := (Submission.BoseGases.abox_compact N hL).exists_bound_of_continuousOn
    hΦ.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMbound : ∀ y ∈ Submission.BoseGases.abox N L, |Φ y| ≤ M := fun y hy =>
    le_trans (by simpa [Real.norm_eq_abs] using hM₀ y hy) (le_max_left _ _)
  have hΨ0le : ∀ y ∈ Submission.BoseGases.abox N L,
      |Work.PerSector.slotPiece A S Φ y| ≤ M := by
    intro y hy
    rw [Work.PerSector.slotPiece]
    by_cases h : y ∈ Work.PerSector.slotSet A S
    · rw [Set.indicator_of_mem h]; exact hMbound y hy
    · rw [Set.indicator_of_notMem h]; simpa using hMnn
  have hmem_update : ∀ {y : Submission.BoseGases.X N}, y ∈ Submission.BoseGases.abox N L →
      ∀ z ∈ A, Function.update y i z ∈ Submission.BoseGases.abox N L := by
    intro y hy z hz
    rw [Submission.BoseGases.mem_abox_iff] at hy ⊢
    intro j
    rw [Function.update_apply]
    by_cases hj : j = i
    · rw [if_pos hj]; exact hAsub hz
    · rw [if_neg hj]; exact hy j
  -- ## The projection is bounded by `2M` on the box
  have hΨbound : ∀ y ∈ Submission.BoseGases.abox N L, |Ψ y| ≤ 2 * M := by
    intro y hy
    rw [hΨdef]
    have h1 : |Work.PerSector.slotPiece A S Φ y| ≤ M := hΨ0le y hy
    have h2 : |(1 / volA) * ∫ z in A,
        Work.PerSector.slotPiece A S Φ (Function.update y i z)| ≤ M := by
      have hint : ‖∫ z in A, Work.PerSector.slotPiece A S Φ (Function.update y i z)‖
          ≤ M * (volume : Measure ℝ³).real A := by
        refine norm_setIntegral_le_of_norm_le_const hAfin (fun z hz => ?_)
        rw [Real.norm_eq_abs]
        exact hΨ0le _ (hmem_update hy z hz)
      have hvolnn : 0 ≤ volA := by rw [hvolA]; exact measureReal_nonneg
      calc |(1 / volA) * ∫ z in A, Work.PerSector.slotPiece A S Φ (Function.update y i z)|
          = volA⁻¹ * |∫ z in A,
              Work.PerSector.slotPiece A S Φ (Function.update y i z)| := by
            rw [one_div, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolnn)]
        _ ≤ volA⁻¹ * (M * (volume : Measure ℝ³).real A) :=
            mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hvolnn)
        _ = M * (volA⁻¹ * volA) := by rw [hvolA]; ring
        _ ≤ M * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hMnn
            rcases eq_or_lt_of_le hvolnn with h | h
            · rw [← h]; simp
            · exact le_of_eq (inv_mul_cancel₀ (ne_of_gt h))
        _ = M := mul_one M
    have hind : |A.indicator (fun _ => (1 : ℝ)) (y i)| ≤ 1 := by
      by_cases h : y i ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    have hEq : Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ) y
        = A.indicator (fun _ => (1 : ℝ)) (y i) *
          (Work.PerSector.slotPiece A S Φ y -
            (1 / volA) * ∫ z in A,
              Work.PerSector.slotPiece A S Φ (Function.update y i z)) := by
      simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]; ring
    rw [hEq, abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (y i)| *
          |Work.PerSector.slotPiece A S Φ y -
            (1 / volA) * ∫ z in A, Work.PerSector.slotPiece A S Φ (Function.update y i z)|
        ≤ 1 * (|Work.PerSector.slotPiece A S Φ y| +
            |(1 / volA) * ∫ z in A,
              Work.PerSector.slotPiece A S Φ (Function.update y i z)|) :=
          mul_le_mul hind (abs_sub _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (M + M) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
      _ = 2 * M := by ring
  -- ## Measurability of the amplitude
  have hΨmeas : Measurable Ψ := by
    rw [hΨdef]
    exact Work.SlotWord.measurable_boxQInd volA A hA i
      (Work.PerSector.slotPiece_measurable A hA S hΦ.measurable)
  have hnorm_exp : ∀ z : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    intro z
    rw [show -(Complex.I * (inner ℝ p z : ℂ)) = ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I by
      rw [Complex.ofReal_neg]; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hexpcont : Continuous (fun q : Submission.BoseGases.X N × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) := by fun_prop
  have htbamp : Measurable (fun x : Submission.BoseGases.X N =>
      Work.SmallBoxTBWord.tBamp χ p Ψ i x) := by
    have h1 : Measurable (fun q : Submission.BoseGases.X N × ℝ³ => (χ q.2 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχmeas.comp measurable_snd)
    have h2 : Measurable (fun q : Submission.BoseGases.X N × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) := hexpcont.measurable
    have h3 : Measurable (fun q : Submission.BoseGases.X N × ℝ³ =>
        (Ψ (Function.update q.1 i q.2) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (hΨmeas.comp (measurable_update' (X := fun _ : Fin N => ℝ³) (a := i)))
    have hjoint : Measurable (fun q : Submission.BoseGases.X N × ℝ³ =>
        (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
          (Ψ (Function.update q.1 i q.2) : ℂ)) := (h1.mul h2).mul h3
    have hSM := hjoint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
    simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable
  have haesm : AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L)) :=
    (htbamp.norm.pow_const 2).aestronglyMeasurable
  -- ## The pointwise bound on the amplitude integrand
  have hintegrand_bound : ∀ x ∈ Submission.BoseGases.abox N L, ∀ z : ℝ³,
      ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Ψ (Function.update x i z) : ℂ)‖ ≤ (2 * M) * |χ z| := by
    intro x hx z
    rw [norm_mul, norm_mul, hnorm_exp z, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, mul_one]
    rcases eq_or_ne (χ z) 0 with hz | hz
    · rw [hz]; simp
    · have hzA : z ∈ A := hχsupp z hz
      have hxz : Function.update x i z ∈ Submission.BoseGases.abox N L := hmem_update hx z hzA
      nlinarith [hΨbound _ hxz, abs_nonneg (χ z)]
  -- ## The amplitude is bounded on the box
  obtain ⟨K, hKnn, hKbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Submission.BoseGases.abox N L,
      ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ≤ K := by
    refine ⟨(2 * M) * ∫ z, |χ z|, ?_, ?_⟩
    · have h0 : 0 ≤ ∫ z, |χ z| := integral_nonneg (fun z => abs_nonneg _)
      exact mul_nonneg (by linarith) h0
    · intro x hx
      have hupd : Measurable (fun z : ℝ³ => Function.update x i z) :=
        (measurable_update' (X := fun _ : Fin N => ℝ³) (a := i)).comp
          (measurable_const.prodMk measurable_id)
      have hexpz : Measurable (fun z : ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) :=
        (by fun_prop : Continuous (fun z : ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))).measurable
      have hzj : Measurable (fun z : ℝ³ =>
          (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Ψ (Function.update x i z) : ℂ)) :=
        ((Complex.continuous_ofReal.measurable.comp hχmeas).mul hexpz).mul
          (Complex.continuous_ofReal.measurable.comp (hΨmeas.comp hupd))
      have hint : MeasureTheory.Integrable (fun z : ℝ³ =>
          ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Ψ (Function.update x i z) : ℂ)‖) := by
        refine (hχint.const_mul (2 * M)).mono' hzj.norm.aestronglyMeasurable ?_
        filter_upwards with z
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hintegrand_bound x hx z
      rw [Work.SmallBoxTBWord.tBamp]
      calc ‖∫ z, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (Ψ (Function.update x i z) : ℂ)‖
          ≤ ∫ z, ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (Ψ (Function.update x i z) : ℂ)‖ := MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ z, (2 * M) * |χ z| := MeasureTheory.integral_mono_ae hint
              (hχint.const_mul (2 * M)) (Eventually.of_forall (hintegrand_bound x hx))
        _ = (2 * M) * ∫ z, |χ z| := MeasureTheory.integral_const_mul (2 * M) (fun z => |χ z|)
  -- ## Integrability
  refine MeasureTheory.Integrable.of_bound haesm (K ^ 2) ?_
  filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable N L)] with x hx
  have h1 : ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hKbd x hx) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
  exact h1

theorem integrableOn_tBamp_boxQInd_abox {N : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAsub : A ⊆ Submission.BoseGases.acube L)
    (hAfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤)
    (volA : ℝ)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχmeas : Measurable χ)
    (hχint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => |χ z|))
    (hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ A)
    {S : Finset (Fin N)} {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ)
    (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i x‖ ^ 2)
      (Submission.BoseGases.abox N L) :=
  integrableOn_tBamp_boxQInd_abox_general hL hA hAsub hAfin volA hvolA hχmeas hχint hχsupp
    hΦ i p

end Work.BoseB1Cube
