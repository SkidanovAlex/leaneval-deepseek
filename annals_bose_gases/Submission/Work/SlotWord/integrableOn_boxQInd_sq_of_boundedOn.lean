import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn`

The (R3)-integrability of one FS-faithful box projection squared, on the ambient box: if the state
`Ψ` is measurable and bounded by `C` on `abox M a`, if the box `A` sits inside the ambient cube
`acube a`, and if `volA = |A|`, then `x ↦ (Q_{A,i}Ψ x)²` is `IntegrableOn (abox M a)`.

Pointwise, FS's mean-free projection is

  `Q_{A,i}Ψ x = 1_A(x_i) · (Ψ x − |A|⁻¹ ∫_A Ψ(x with i-th coordinate = z) dz)`,

so on the box `|Q_{A,i}Ψ x| ≤ 2C`: the first factor is bounded by `C` by hypothesis, and the box
mean is bounded by `C` because `A ⊆ acube a` while the *other* coordinates of `x ∈ abox M a` also
lie in `acube a` — hence the integrand `Ψ(·, z)` of the mean stays inside the box, where `|Ψ| ≤ C`.

The box `abox M a` has finite measure (`A ⊆ acube a` has finite measure, and the box is a finite
product of cubes), and the projection is a.e.-strongly measurable: the mean is a parametric
Bochner integral of a *measurable* integrand (`(x,z) ↦ Ψ (update x i z)` is measurable, as
`Function.update` is), so `AEStronglyMeasurable.integral_prod_right'` applies.  Integrability then
follows from `Integrable.of_bound`.

This is the integrability side condition (R3) used by `cnPlusBoxInd_slotFibre`: there the state is
the (continuous, hence box-bounded) slot piece of a smooth state and `C` is `sup_{abox M L}|Φ|`.
-/

open MeasureTheory Metric Filter
open scoped Topology Real

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The box mean is bounded by the sup bound.**  If `|f| ≤ C` on `A` and `A` has finite measure,
then `|(1/|A|)∫_A f| ≤ C` — where `|A| = volume.real A`, and where the degenerate case
`|A| = 0` is handled by the `1/0 = 0` convention together with `∫_A f = 0` (as `A` is null). -/
private lemma abs_inv_mul_setIntegral_le_of_bound {A : Set ℝ³} {f : ℝ³ → ℝ} {C : ℝ}
    (hA : MeasurableSet A) (hfin : (volume : Measure ℝ³) A < ⊤) (hC : 0 ≤ C)
    (hb : ∀ z ∈ A, |f z| ≤ C) :
    |(1 / (volume : Measure ℝ³).real A) * ∫ z in A, f z| ≤ C := by
  set v : ℝ := (volume : Measure ℝ³).real A with hv
  have hvnn : 0 ≤ v := by rw [hv]; exact measureReal_nonneg
  have hINE : |(∫ z in A, f z)| ≤ ∫ z in A, |f z| := by
    rw [show (∫ z in A, f z) = ∫ z, f z ∂((volume : Measure ℝ³).restrict A) from rfl,
      show (∫ z in A, |f z|) = ∫ z, |f z| ∂((volume : Measure ℝ³).restrict A) from rfl]
    exact norm_integral_le_integral_norm f
  have hgint : Integrable (fun _ : ℝ³ => C) ((volume : Measure ℝ³).restrict A) := by
    rw [integrable_const_iff]
    exact Or.inr (isFiniteMeasure_restrict.mpr (ne_of_lt hfin))
  have hae : ∀ᵐ z ∂((volume : Measure ℝ³).restrict A), |f z| ≤ C := by
    rw [ae_restrict_iff' hA]
    exact Eventually.of_forall fun z hz => hb z hz
  have hle : (∫ z in A, |f z|) ≤ ∫ z in A, C :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hgint hae
  have hval : (∫ z in A, C) = v * C := by
    rw [setIntegral_const, smul_eq_mul, ← hv]
  have hvv : v⁻¹ * v ≤ 1 := by
    rcases eq_or_lt_of_le hvnn with h | h
    · rw [← h]; simp
    · exact le_of_eq (inv_mul_cancel₀ (ne_of_gt h))
  calc |(1 / v) * ∫ z in A, f z|
      = v⁻¹ * |(∫ z in A, f z)| := by
        rw [one_div, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvnn)]
    _ ≤ v⁻¹ * (v * C) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hvnn)
        calc |(∫ z in A, f z)| ≤ ∫ z in A, |f z| := hINE
          _ ≤ ∫ z in A, C := hle
          _ = v * C := hval
    _ = (v⁻¹ * v) * C := by ring
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right hvv hC
    _ = C := one_mul C

theorem integrableOn_boxQInd_sq_of_boundedOn {M : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) {a volA : ℝ} (hAa : A ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {Ψ : Submission.BoseGases.X M → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Submission.BoseGases.abox M a, |Ψ x| ≤ C) (i : Fin M) :
    MeasureTheory.IntegrableOn (fun x => (Work.UBBInputs8.boxQInd volA A i Ψ x)^2)
      (Submission.BoseGases.abox M a) := by
  classical
  -- ## Finiteness of the measures involved
  -- The ambient cube has finite measure for *every* side length: for `a < 0` it is contained in
  -- `{0}`.
  have hacube_lt : (volume : Measure ℝ³) (Submission.BoseGases.acube a) < ⊤ := by
    rcases le_or_gt 0 a with ha | ha
    · exact Submission.BoseGases.acube_lt_top a ha
    · have hsub : Submission.BoseGases.acube a ⊆ ({0} : Set ℝ³) := by
        intro y hy
        rw [Set.mem_singleton_iff]
        rw [Submission.BoseGases.mem_acube_iff] at hy
        ext m
        have h1 : -a / 2 ≤ y m := (hy m).1
        have h2 : y m ≤ a / 2 := (hy m).2
        have h3 : y m = 0 := by linarith
        simpa using h3
      exact lt_of_le_of_lt (measure_mono hsub) (by simp)
  have hAfin : (volume : Measure ℝ³) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAa) hacube_lt
  haveI hcubeFin : IsFiniteMeasure ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube a)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hacube_lt)
  haveI hboxFin :
      IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X M)).restrict
        (Submission.BoseGases.abox M a)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi M a]
    infer_instance
  -- ## A.e.-strong measurability
  -- The parametric integrand of the box mean is measurable in `(x,z)`.
  have hjoint : Measurable
      (fun p : Submission.BoseGases.X M × ℝ³ => Ψ (Function.update p.1 i p.2)) :=
    hΨ.comp (measurable_update' (a := i))
  have hint : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X M => ∫ z in A, Ψ (Function.update x i z))
      ((volume : Measure (Submission.BoseGases.X M)).restrict (Submission.BoseGases.abox M a)) :=
    hjoint.aestronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure (Submission.BoseGases.X M)).restrict (Submission.BoseGases.abox M a))
      (ν := (volume : Measure ℝ³).restrict A)
  have hInd : Measurable
      (fun x : Submission.BoseGases.X M => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (Measurable.indicator measurable_const hA).comp (measurable_pi_apply i)
  have hP : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X M => Work.UBBInputs8.boxPInd volA A i Ψ x)
      ((volume : Measure (Submission.BoseGases.X M)).restrict (Submission.BoseGases.abox M a)) :=
    ((hint.const_mul (1 / volA)).mul hInd.aestronglyMeasurable).congr
      (Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, Work.UBBInputs8.boxPInd])
  have hQ : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X M => Work.UBBInputs8.boxQInd volA A i Ψ x)
      ((volume : Measure (Submission.BoseGases.X M)).restrict (Submission.BoseGases.abox M a)) :=
    ((hInd.aestronglyMeasurable.mul hΨ.aestronglyMeasurable).sub hP).congr
      (Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, Pi.sub_apply, Work.UBBInputs8.boxQInd])
  have haesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X M => (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X M)).restrict (Submission.BoseGases.abox M a)) :=
    hQ.pow 2
  -- ## The pointwise bound on the box
  have hbound : ∀ x ∈ Submission.BoseGases.abox M a,
      |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * C := by
    intro x hx
    have hx0 : x ∈ Submission.BoseGases.abox M a := hx
    rw [Submission.BoseGases.mem_abox_iff] at hx
    -- FS's projection as the box indicator times the deviation from the box mean
    have hQeq : Work.UBBInputs8.boxQInd volA A i Ψ x
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) := by
      simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
      ring
    rw [hQeq]
    by_cases hxi : x i ∈ A
    · rw [Set.indicator_of_mem hxi, one_mul]
      have h1 : |Ψ x| ≤ C := hC x hx0
      have h2 : |(1 / volA) * ∫ z in A, Ψ (Function.update x i z)| ≤ C := by
        rw [hvol]
        refine abs_inv_mul_setIntegral_le_of_bound hA hAfin hC0 ?_
        intro z hz
        -- the mean's integrand stays in the box, since `A ⊆ acube a` and `x ∈ abox M a`
        refine hC (Function.update x i z) ?_
        rw [Submission.BoseGases.mem_abox_iff]
        intro j
        rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj]; exact hAa hz
        · rw [if_neg hj]; exact hx j
      calc |Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)|
          ≤ |Ψ x| + |(1 / volA) * ∫ z in A, Ψ (Function.update x i z)| := abs_sub _ _
        _ ≤ C + C := add_le_add h1 h2
        _ = 2 * C := by ring
    · -- off the box the projection vanishes identically
      rw [Set.indicator_of_notMem hxi, zero_mul, abs_zero]
      linarith
  -- ## Assembling the integrability
  refine Integrable.of_bound haesm ((2 * C) ^ 2) ?_
  filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable M a)] with x hx
  have habs := hbound x hx
  have hsq : (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2 ≤ (2 * C) ^ 2 :=
    sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  calc ‖(Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2‖
      = (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ (2 * C) ^ 2 := hsq

end Work.SlotWord
