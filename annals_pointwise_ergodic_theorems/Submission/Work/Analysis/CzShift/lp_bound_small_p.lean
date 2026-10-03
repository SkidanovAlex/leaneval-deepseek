/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Analysis.CzShift.cz_decomp_1d_banach
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
import Submission.Port.Aesm

/-!
# The `L^p` bound (`1 < p < 2`) for shifted Calderón–Zygmund operators

Appendix B of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. **195** (2022): a finite sum of convolution operators whose
kernel family satisfies

* an `L²` bound `‖T‖_{2→2} ≤ A₂` (`hL2`), and
* the off-diagonal ("Hörmander") condition `hoff` with constant `Ak`,

is bounded on `L^p(ℝ;H)` for every `1 < p < 2`, with norm controlled by `C_p (A₂² + Ak + 1)`.

The proof combines the weak-type `(1,1)` bound `weak_type_one_of_hoff` (constant
`(24A₂² + 4Ak + 100)/α`, itself a finite-sum Calderón–Zygmund argument on top of
`Work.Analysis.CzShift.cz_decomp_1d_banach`) with the `L²` bound by Marcinkiewicz interpolation
(`Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit`), which
gives the `L^p` bound with constant `(12 A₀ 2^(p-1)/(p-1) + 16 A₂²/(2-p))^(1/p)`, i.e. at most
`C_p (A₂² + Ak + 1)` because `A₀ ≤ 100 (A₂² + Ak + 1)` and `(A₂²+Ak+1)^(1/p) ≤ A₂²+Ak+1`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Filter

open scoped ENNReal Interval

noncomputable section

set_option autoImplicit false

variable {ι : Type*}

/-- Translates of an a.e. strongly measurable function are a.e. strongly measurable: the map
`y ↦ x - y` preserves Lebesgue measure. -/
lemma aestronglyMeasurable_comp_sub {φ : ℝ → ℂ} (hφ : AEStronglyMeasurable φ volume) (x : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => φ (x - y)) volume := by
  have hneg : MeasurePreserving (fun y : ℝ => -y) (volume : Measure ℝ) volume :=
    ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  have hsub : (fun y : ℝ => x - y) = (fun w : ℝ => x + w) ∘ (fun y : ℝ => -y) := by
    funext y; simp [sub_eq_add_neg]
  have hmp : MeasurePreserving (fun y : ℝ => x - y) (volume : Measure ℝ) volume := by
    rw [hsub]
    exact (measurePreserving_add_left volume x).comp hneg
  exact hφ.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving

/-- Translates of an a.e. strongly measurable function are a.e. strongly measurable. -/
lemma aestronglyMeasurable_comp_sub_const {φ : ℝ → ℂ} (hφ : AEStronglyMeasurable φ volume)
    (m : ℝ) : AEStronglyMeasurable (fun y : ℝ => φ (y - m)) volume := by
  have h1 : AEStronglyMeasurable (fun x : ℝ => φ (x + (-m))) volume :=
    hφ.comp_quasiMeasurePreserving
      (measurePreserving_add_right (volume : Measure ℝ) (-m)).quasiMeasurePreserving
  simpa only [sub_eq_add_neg] using h1

/-- The convolution kernel `y ↦ K (x - y)` times an integrable `H`-valued function is integrable,
provided `K` is bounded and a.e. strongly measurable. -/
lemma integrable_kernel_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) {f : ℝ → H} (hf : Integrable f volume)
    (hKm : AEStronglyMeasurable K volume) (x : ℝ) :
    Integrable (fun y : ℝ => K (x - y) • f y) volume :=
  hf.bdd_smul C (aestronglyMeasurable_comp_sub hKm x) (Eventually.of_forall fun y => hC (x - y))

/-- `czOp` is additive on integrable functions (used for the Marcinkiewicz hypothesis). -/
lemma czOp_add {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    {f g : ℝ → H} (hf : Integrable f volume) (hg : Integrable g volume) :
    czOp D K ε (f + g) = czOp D K ε f + czOp D K ε g := by
  funext x
  simp only [czOp, Pi.add_apply]
  have hterm : ∀ i ∈ D, ε i • ∫ y, K i (x - y) • (f y + g y) ∂volume
      = ε i • ∫ y, K i (x - y) • f y ∂volume + ε i • ∫ y, K i (x - y) • g y ∂volume := by
    intro i hi
    obtain ⟨C, hC⟩ := hKbdd i hi
    have hi1 : Integrable (fun y : ℝ => K i (x - y) • f y) volume :=
      integrable_kernel_smul hC hf (hKmeas i hi) x
    have hi2 : Integrable (fun y : ℝ => K i (x - y) • g y) volume :=
      integrable_kernel_smul hC hg (hKmeas i hi) x
    have hsplit : (fun y : ℝ => K i (x - y) • (f y + g y))
        = fun y : ℝ => K i (x - y) • f y + K i (x - y) • g y := by
      funext y; rw [smul_add]
    have hstep : (∫ y, K i (x - y) • (f y + g y) ∂volume)
        = (∫ y, K i (x - y) • f y ∂volume) + (∫ y, K i (x - y) • g y ∂volume) := by
      rw [hsplit]
      exact integral_add hi1 hi2
    rw [hstep, smul_add]
  rw [Finset.sum_congr rfl hterm]
  exact Finset.sum_add_distrib (s := D)
    (f := fun i => ε i • ∫ y, K i (x - y) • f y ∂volume)
    (g := fun i => ε i • ∫ y, K i (x - y) • g y ∂volume)

/-! ## Measurability of the convolution integrands -/

/-- `(x, y) ↦ f (x - y)` is a.e. strongly measurable on the product. -/
lemma aesm_sub_left_right {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f (p.1 - p.2)) (volume.prod volume) :=
  (AEStronglyMeasurable.mono_ac
    (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure ℝ) volume).absolutelyContinuous
    hf).comp_measurable measurable_sub

/-- `(x, y) ↦ f (x - m)` is a.e. strongly measurable on the product. -/
lemma aesm_fst_sub {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) (m : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f (p.1 - m)) (volume.prod volume) :=
  AEStronglyMeasurable.comp_fst (aestronglyMeasurable_comp_sub_const hf m)

/-- `czOp` is a.e. strongly measurable. -/
lemma aestronglyMeasurable_czOp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
    {f : ℝ → H} (hf : Integrable f volume) :
    AEStronglyMeasurable (czOp D K ε f) volume := by
  have hterm : ∀ i ∈ D, AEStronglyMeasurable (fun x : ℝ => ∫ y, K i (x - y) • f y ∂volume) volume := by
    intro i hi
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => K i (p.1 - p.2)) (volume.prod volume) :=
      aesm_sub_left_right (hKmeas i hi)
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (volume.prod volume) :=
      hf.aestronglyMeasurable.comp_snd
    exact (h1.smul h2).integral_prod_right'
  have hsum : AEStronglyMeasurable
      (∑ i ∈ D, fun x : ℝ => ε i • ∫ y, K i (x - y) • f y ∂volume) volume :=
    Finset.aestronglyMeasurable_sum D fun i hi => (hterm i hi).const_smul (ε i)
  convert hsum using 1
  funext x
  simp only [czOp, Finset.sum_apply]

/-- Finite sums of a.e. measurable `ℝ≥0∞`-valued functions. -/
lemma lintegral_finsetSum_of_aemeasurable {α ι' : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι') {f : ι' → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫⁻ a, f i a ∂μ := by
  classical
  revert hf
  refine Finset.induction (motive := fun s => (∀ i ∈ s, AEMeasurable (f i) μ) →
      ∫⁻ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫⁻ a, f i a ∂μ) ?_ ?_ s
  · intro _; simp
  · intro j s hj ih hf
    have h1 : (∫⁻ a, ∑ i ∈ insert j s, f i a ∂μ) = ∫⁻ a, f j a + ∑ i ∈ s, f i a ∂μ := by
      congr 1 with a
      exact Finset.sum_insert hj
    rw [h1, lintegral_add_left' (hf j (Finset.mem_insert_self j s)),
      ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)), Finset.sum_insert hj]


/-- Finite sums of a.e. measurable `ℝ≥0∞`-valued functions are a.e. measurable. -/
lemma aemeasurable_finsetSum {α ι' : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι') {f : ι' → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∑ i ∈ s, f i a) μ := by
  classical
  revert hf
  refine Finset.induction (motive := fun s => (∀ i ∈ s, AEMeasurable (f i) μ) →
      AEMeasurable (fun a => ∑ i ∈ s, f i a) μ) ?_ ?_ s
  · intro _
    simpa using (aemeasurable_const : AEMeasurable (fun _ : α => (0 : ℝ≥0∞)) μ)
  · intro j s hj ih hf
    have h1 : (fun a => ∑ i ∈ insert j s, f i a) = fun a => f j a + ∑ i ∈ s, f i a := by
      funext a; rw [Finset.sum_insert hj]
    rw [h1]
    exact (hf j (Finset.mem_insert_self j s)).add
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-- Change of variables `x = u + m` in a lintegral over `{|x - m| ≥ 50 R}`. -/
lemma lintegral_shift_set (f : ℝ → ℝ≥0∞) (m R : ℝ) :
    ∫⁻ x in {x : ℝ | 50 * R ≤ |x - m|}, f x ∂volume
      = ∫⁻ u in {u : ℝ | 50 * R ≤ |u|}, f (u + m) ∂volume := by
  have hmeas : MeasurableSet {x : ℝ | 50 * R ≤ |x - m|} :=
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_id.sub measurable_const))
  have hmeas' : MeasurableSet {u : ℝ | 50 * R ≤ |u|} :=
    measurableSet_le measurable_const measurable_abs
  rw [← lintegral_indicator hmeas f, ← lintegral_indicator hmeas' (fun u => f (u + m)),
    ← lintegral_add_right_eq_self
      (fun x => {x : ℝ | 50 * R ≤ |x - m|}.indicator f x) m]
  refine lintegral_congr fun u => ?_
  by_cases hu : 50 * R ≤ |u|
  · have hu' : u + m ∈ {x : ℝ | 50 * R ≤ |x - m|} := by
      rw [Set.mem_ofPred_eq, show u + m - m = u by ring]; exact hu
    rw [Set.indicator_of_mem hu',
      Set.indicator_of_mem (show u ∈ {u : ℝ | 50 * R ≤ |u|} from hu)]
  · have hu' : u + m ∉ {x : ℝ | 50 * R ≤ |x - m|} := by
      rw [Set.mem_ofPred_eq, show u + m - m = u by ring]; exact hu
    rw [Set.indicator_of_notMem hu',
      Set.indicator_of_notMem (show u ∉ {u : ℝ | 50 * R ≤ |u|} from hu)]

/-- **Pointwise bound for the bad part.**  For a mean-zero `β`, the operator applied to `β` is
bounded pointwise by the lintegral of the "difference kernels" against `‖β‖`. -/
lemma czOp_badpointwise {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H]
    (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
    (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (m : ℝ) (β : ℝ → H) (hβint : Integrable β volume) (hmean : ∫ x, β x ∂volume = 0)
    (x : ℝ) :
    ‖czOp D K ε β x‖ₑ ≤ ∫⁻ y, (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ ∂volume := by
  have hzero : ∀ i ∈ D, (∫ y, K i (x - m) • β y ∂volume) = 0 := by
    intro i hi
    have h := ((ContinuousLinearMap.lsmul ℂ ℂ) (K i (x - m))).integral_comp_comm hβint
    rw [hmean, map_zero] at h
    simpa only [ContinuousLinearMap.lsmul_apply] using h
  have hdiff : ∀ i ∈ D,
      (∫ y, K i (x - y) • β y ∂volume) = ∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume := by
    intro i hi
    obtain ⟨C, hC⟩ := hKbdd i hi
    have h1 : Integrable (fun y : ℝ => K i (x - y) • β y) volume :=
      integrable_kernel_smul hC hβint (hKmeas i hi) x
    have h2 : Integrable (fun y : ℝ => K i (x - m) • β y) volume := hβint.smul _
    have hsplit : (fun y : ℝ => (K i (x - y) - K i (x - m)) • β y)
        = fun y : ℝ => K i (x - y) • β y - K i (x - m) • β y := by
      funext y; rw [sub_smul]
    rw [hsplit, integral_sub h1 h2, hzero i hi, sub_zero]
  have hcz : czOp D K ε β x
      = ∑ i ∈ D, ε i • ∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume := by
    rw [czOp]
    exact Finset.sum_congr rfl fun i hi => by rw [hdiff i hi]
  rw [hcz]
  have hεi : ∀ i ∈ D, ‖ε i‖ₑ ≤ 1 := by
    intro i hi
    have h1 : (‖ε i‖₊ : ℝ) ≤ 1 := by simpa using hε i hi
    have h2 : ‖ε i‖₊ ≤ 1 := NNReal.coe_le_one.mp h1
    simpa [enorm_eq_nnnorm] using h2
  have hstep : ∀ i ∈ D, ‖ε i • ∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume‖ₑ
      ≤ ∫⁻ y, ‖K i (x - y) - K i (x - m)‖ₑ * ‖β y‖ₑ ∂volume := by
    intro i hi
    calc ‖ε i • ∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume‖ₑ
        = ‖ε i‖ₑ * ‖∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume‖ₑ := enorm_smul _ _
      _ ≤ 1 * ‖∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume‖ₑ := by
          gcongr
          exact hεi i hi
      _ = ‖∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume‖ₑ := one_mul _
      _ ≤ ∫⁻ y, ‖(K i (x - y) - K i (x - m)) • β y‖ₑ ∂volume :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖K i (x - y) - K i (x - m)‖ₑ * ‖β y‖ₑ ∂volume :=
          lintegral_congr fun y => by rw [enorm_smul]
  refine (enorm_sum_le _ _).trans ?_
  calc ∑ i ∈ D, ‖ε i • ∫ y, (K i (x - y) - K i (x - m)) • β y ∂volume‖ₑ
      ≤ ∑ i ∈ D, ∫⁻ y, ‖K i (x - y) - K i (x - m)‖ₑ * ‖β y‖ₑ ∂volume :=
        Finset.sum_le_sum hstep
    _ = ∫⁻ y, ∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ * ‖β y‖ₑ ∂volume :=
        (lintegral_finsetSum_of_aemeasurable D fun i hi =>
          (AEMeasurable.mul
            ((aestronglyMeasurable_comp_sub (hKmeas i hi) x).sub
              (aestronglyMeasurable_const :
                AEStronglyMeasurable (fun _ : ℝ => K i (x - m)) volume)).enorm
            hβint.aestronglyMeasurable.enorm).congr
            (Eventually.of_forall fun y => by simp only [Pi.mul_apply, Pi.sub_apply])).symm
    _ = ∫⁻ y, (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ ∂volume := by
        refine lintegral_congr fun y => ?_
        rw [← Finset.sum_mul]

/-- **Off-diagonal (`L¹`) bound for a single bad function.**  If `β` is supported in
`Ioo (m - R/2) (m + R/2)` with `∫ β = 0`, then away from `{|x - m| < 50 R}` the operator applied
to `β` is controlled by `Ak ∫ ‖β‖`. -/
lemma badpart_lintegral_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H]
    (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (Ak : ℝ)
    (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1) (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak)
    (β : ℝ → H) (m R : ℝ) (hR : 0 < R) (hβint : Integrable β volume)
    (hsupp : ∀ x, β x ≠ 0 → |x - m| ≤ R / 2)
    (hmean : ∫ x, β x ∂volume = 0)
    (E : Set ℝ) (hEmeas : MeasurableSet E) (hE : ∀ x, x ∉ E → 50 * R ≤ |x - m|) :
    ∫⁻ x in Eᶜ, ‖czOp D K ε β x‖ₑ ∂volume ≤ ENNReal.ofReal Ak * ∫⁻ x, ‖β x‖ₑ ∂volume := by
  have hEc : MeasurableSet Eᶜ := hEmeas.compl
  have hmeas_y : ∀ i ∈ D, ∀ y : ℝ,
      AEMeasurable (fun x : ℝ => ‖K i (x - y) - K i (x - m)‖ₑ) volume := fun i hi y =>
    ((aestronglyMeasurable_comp_sub_const (hKmeas i hi) y).sub
      (aestronglyMeasurable_comp_sub_const (hKmeas i hi) m)).enorm
  have hAEM : AEMeasurable (fun p : ℝ × ℝ =>
      (∑ i ∈ D, ‖K i (p.1 - p.2) - K i (p.1 - m)‖ₑ) * ‖β p.2‖ₑ) (volume.prod volume) := by
    refine AEMeasurable.mul ?_ hβint.aestronglyMeasurable.comp_snd.enorm
    exact aemeasurable_finsetSum D fun i hi =>
      ((aesm_sub_left_right (hKmeas i hi)).sub (aesm_fst_sub (hKmeas i hi) m)).enorm
  have hAEMind : AEMeasurable (Function.uncurry (fun x y : ℝ => Eᶜ.indicator (fun x =>
      (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ) x)) (volume.prod volume) := by
    refine (hAEM.indicator (hEc.preimage measurable_fst)).congr ?_
    filter_upwards with p
    rcases p with ⟨x, y⟩
    simp only [Function.uncurry]
    by_cases hx : x ∈ Eᶜ
    · rw [Set.indicator_of_mem (show ((x, y) : ℝ × ℝ) ∈ Prod.fst ⁻¹' Eᶜ from hx),
        Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (show ((x, y) : ℝ × ℝ) ∉ Prod.fst ⁻¹' Eᶜ from hx),
        Set.indicator_of_notMem hx]
  have hy : ∀ y : ℝ, (∫⁻ x in Eᶜ,
        (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ ∂volume)
      ≤ ‖β y‖ₑ * ENNReal.ofReal Ak := by
    intro y
    by_cases hβy : β y = 0
    · simp [hβy]
    · have hy' : |y - m| ≤ R / 2 := hsupp y hβy
      have hper : ∀ i ∈ D, (∫⁻ x in Eᶜ, ‖K i (x - y) - K i (x - m)‖ₑ ∂volume)
          ≤ ∫⁻ u in {u : ℝ | 50 * R ≤ |u|},
              ENNReal.ofReal ‖K i (u - (y - m)) - K i u‖ ∂volume := by
        intro i hi
        refine le_trans (lintegral_mono_set fun x hx => hE x hx) ?_
        refine (lintegral_shift_set (fun z => ‖K i (z - y) - K i (z - m)‖ₑ) m R).le.trans (le_of_eq ?_)
        refine lintegral_congr fun u => ?_
        rw [show u + m - y = u - (y - m) by ring, show u + m - m = u by ring, ← ofReal_norm]
      have hoff' := hoff R hR (y - m) (by simpa using hy')
      calc (∫⁻ x in Eᶜ, (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ ∂volume)
          = (∫⁻ x in Eᶜ, (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) ∂volume) * ‖β y‖ₑ := by
            refine lintegral_mul_const'' _ ?_
            exact aemeasurable_finsetSum D fun i hi => (hmeas_y i hi y).restrict
        _ = (∑ i ∈ D, ∫⁻ x in Eᶜ, ‖K i (x - y) - K i (x - m)‖ₑ ∂volume) * ‖β y‖ₑ := by
            rw [lintegral_finsetSum_of_aemeasurable D (fun i hi => (hmeas_y i hi y).restrict)]
        _ ≤ ENNReal.ofReal Ak * ‖β y‖ₑ := by
            gcongr
            exact (Finset.sum_le_sum hper).trans hoff'
        _ = ‖β y‖ₑ * ENNReal.ofReal Ak := mul_comm _ _
  calc ∫⁻ x in Eᶜ, ‖czOp D K ε β x‖ₑ ∂volume
      = ∫⁻ x, Eᶜ.indicator (fun x => ‖czOp D K ε β x‖ₑ) x ∂volume :=
        (lintegral_indicator hEc _).symm
    _ ≤ ∫⁻ x, Eᶜ.indicator (fun x => ∫⁻ y,
          (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ ∂volume) x ∂volume := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Eᶜ
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          exact czOp_badpointwise D K ε hε hKmeas hKbdd m β hβint hmean x
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    _ = ∫⁻ x, ∫⁻ y, Eᶜ.indicator (fun x =>
          (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ) x ∂volume ∂volume := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ Eᶜ
        · rw [Set.indicator_of_mem hx]
          refine lintegral_congr fun y => ?_
          rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, ← lintegral_zero]
          exact lintegral_congr fun y => by rw [Set.indicator_of_notMem hx]
    _ = ∫⁻ y, ∫⁻ x, Eᶜ.indicator (fun x =>
          (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ) x ∂volume ∂volume :=
        lintegral_lintegral_swap hAEMind
    _ = ∫⁻ y, ∫⁻ x in Eᶜ,
          (∑ i ∈ D, ‖K i (x - y) - K i (x - m)‖ₑ) * ‖β y‖ₑ ∂volume ∂volume := by
        refine lintegral_congr fun y => ?_
        exact lintegral_indicator hEc _
    _ ≤ ∫⁻ y, ‖β y‖ₑ * ENNReal.ofReal Ak ∂volume := lintegral_mono hy
    _ = ENNReal.ofReal Ak * ∫⁻ y, ‖β y‖ₑ ∂volume := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

lemma ofReal_setIntegral_norm_le_lintegral_enorm {H : Type*} [NormedAddCommGroup H]
    (f : ℝ → H) {s : Set ℝ} (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ x in s, ‖f x‖ ∂volume) ≤ ∫⁻ x in s, ‖f x‖ₑ ∂volume := by
  have hpt : ∀ x, ENNReal.ofReal (s.indicator (fun x => ‖f x‖) x)
      = s.indicator (fun x => ‖f x‖ₑ) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ofReal_norm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [← integral_indicator hs (f := fun x => ‖f x‖),
    ← lintegral_indicator hs (f := fun x => ‖f x‖ₑ)]
  refine le_trans ?_ (le_of_eq (lintegral_congr hpt))
  by_cases hint : Integrable (s.indicator (fun x => ‖f x‖)) volume
  · exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => by
        by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]))
  · rw [integral_undef hint, ENNReal.ofReal_zero]
    positivity

/-- **Weak type `(1,1)`** for `czOp` from the off-diagonal condition and the `L²` bound. -/
theorem weak_type_one_of_hoff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (Ak A2 : ℝ) (hAk : 0 ≤ Ak) (hA2 : 0 < A2) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
    (hKmeas : ∀ i ∈ D, MeasureTheory.AEStronglyMeasurable (K i) MeasureTheory.volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak)
    (hL2 : ∀ f : ℝ → H, MeasureTheory.Integrable f →
      MeasureTheory.MemLp f 2 MeasureTheory.volume →
      MeasureTheory.eLpNorm (czOp D K ε f) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.volume)
    (f : ℝ → H) (hf : MeasureTheory.Integrable f) (α : ℝ) (hα : 0 < α) :
    MeasureTheory.volume {x : ℝ | α < ‖czOp D K ε f x‖}
      ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α)
          * MeasureTheory.eLpNorm f 1 MeasureTheory.volume := by
  classical
  obtain ⟨A, c, g, b, hAc, hdisj, hlow, hhigh, hbdef, hgout, hgin, hfout, hgbd, hUm, hfsum,
    hgmeas, hgint, hgL2, hbint, hbmean⟩ := cz_decomp_1d_banach (E := H) f hf α hα
  have hMnn : 0 ≤ ∫ x, ‖f x‖ ∂volume := integral_nonneg fun x => norm_nonneg _
  -- the exceptional set
  set m : ℕ → ℝ := fun j => (A j + c j) / 2 with hmdef
  set Len : ℕ → ℝ := fun j => c j - A j with hLdef
  set E : Set ℝ := ⋃ j, Set.Ioo (m j - 50 * Len j) (m j + 50 * Len j) with hEdef
  have hLnn : ∀ j, 0 ≤ Len j := fun j => sub_nonneg.mpr (hAc j)
  have hEmem : ∀ j, Set.Ioo (m j - 50 * Len j) (m j + 50 * Len j) ⊆ E := fun j => by
    rw [hEdef]
    exact Set.subset_iUnion (fun i => Set.Ioo (m i - 50 * Len i) (m i + 50 * Len i)) j
  have hEcompl : ∀ x : ℝ, x ∉ E → ∀ j, 50 * Len j ≤ |x - m j| := by
    intro x hx j
    by_contra hcon
    rw [not_le] at hcon
    have h1 : m j - 50 * Len j < x := by linarith [(abs_lt.mp hcon).1]
    have h2 : x < m j + 50 * Len j := by linarith [(abs_lt.mp hcon).2]
    exact hx (hEmem j ⟨h1, h2⟩)
  have hUmeas : MeasurableSet (⋃ j, Set.Ioo (A j) (c j)) :=
    MeasurableSet.iUnion fun j => measurableSet_Ioo
  have hEmeas : MeasurableSet E := by
    rw [hEdef]
    exact MeasurableSet.iUnion fun j => measurableSet_Ioo
  have hEc : MeasurableSet Eᶜ := hEmeas.compl
  have hgint' : MeasureTheory.Integrable g MeasureTheory.volume := by
    refine ⟨hgmeas, ?_⟩
    have h1 : (∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖g x‖ₑ ∂volume)
        = ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖f x‖ₑ ∂volume := by
      refine setLIntegral_congr_fun hUmeas.compl fun x hx => ?_
      rw [hgout x (by simpa using hx)]
    have h2 : (∫⁻ x in (⋃ j, Set.Ioo (A j) (c j)), ‖g x‖ₑ ∂volume)
        ≤ ENNReal.ofReal (2 * α) * volume (⋃ j, Set.Ioo (A j) (c j)) := by
      refine (setLIntegral_mono_ae ?_ ?_).trans_eq (setLIntegral_const _ _)
      · exact aemeasurable_const
      · filter_upwards [hgbd] with x hx _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx
    have h3 : (∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖f x‖ₑ ∂volume)
        ≤ ∫⁻ x, ‖f x‖ₑ ∂volume := by
          simpa only [Measure.restrict_univ] using lintegral_mono_set (μ := volume)
            (Set.subset_univ ((⋃ j, Set.Ioo (A j) (c j))ᶜ))
    calc (∫⁻ x, ‖g x‖ₑ ∂volume)
        = (∫⁻ x in (⋃ j, Set.Ioo (A j) (c j)), ‖g x‖ₑ ∂volume)
          + ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖g x‖ₑ ∂volume :=
          (lintegral_add_compl _ hUmeas).symm
      _ = (∫⁻ x in (⋃ j, Set.Ioo (A j) (c j)), ‖g x‖ₑ ∂volume)
          + ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j))ᶜ, ‖f x‖ₑ ∂volume := by rw [h1]
      _ ≤ ENNReal.ofReal (2 * α) * volume (⋃ j, Set.Ioo (A j) (c j))
          + ∫⁻ x, ‖f x‖ₑ ∂volume := add_le_add h2 h3
      _ ≤ ENNReal.ofReal (2 * α) * ENNReal.ofReal (α⁻¹ * (∫ x, ‖f x‖ ∂volume))
          + ENNReal.ofReal (∫ x, ‖f x‖ ∂volume) := by
          refine add_le_add ?_ (le_of_eq ?_)
          · gcongr
          · exact (ofReal_integral_norm_eq_lintegral_enorm hf).symm
      _ = ENNReal.ofReal (3 * (∫ x, ‖f x‖ ∂volume)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          field_simp
          ring
      _ < ⊤ := ENNReal.ofReal_lt_top

  have hbint' : MeasureTheory.Integrable (f - g) MeasureTheory.volume := hf.sub hgint'
  have hgood : MeasureTheory.volume {x : ℝ | α / 2 < ‖czOp D K ε g x‖}
      ≤ ENNReal.ofReal (16 * A2 ^ 2 * (∫ x, ‖f x‖ ∂volume) / α) := by
    have hTgmeas : AEStronglyMeasurable (czOp D K ε g) volume :=
      aestronglyMeasurable_czOp D K ε hKmeas hgint'
    have hg2 : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume)
        ≤ ENNReal.ofReal (4 * α * (∫ x, ‖f x‖ ∂volume)) := by
      simpa only [ofReal_norm] using hgL2
    have hMemLp : MemLp g 2 volume := by
      rw [MeasureTheory.memLp_iff]
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := hgmeas) (by norm_num : (2:ℝ≥0∞) ≠ 0)
        (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
      exact lt_of_le_of_lt hg2 ENNReal.ofReal_lt_top
    have hL2g := hL2 g hgint' hMemLp
    have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := (volume : Measure ℝ)) (p := 2)
      (by norm_num) (by norm_num) (f := czOp D K ε g) (ENNReal.ofReal (α / 2))
    have hsub : {x : ℝ | α / 2 < ‖czOp D K ε g x‖}
        ⊆ {x : ℝ | ENNReal.ofReal (α / 2) ≤ ‖czOp D K ε g x‖ₑ} := by
      intro x hx
      rw [Set.mem_ofPred_eq] at hx ⊢
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx.le
    have hne' : (ENNReal.ofReal (α / 2)) ^ (2:ℝ) ≠ 0 := by
      rw [ENNReal.rpow_two]
      exact pow_ne_zero 2 (ENNReal.ofReal_ne_zero_iff.mpr (by linarith))
    have htop' : (ENNReal.ofReal (α / 2)) ^ (2:ℝ) ≠ ⊤ := by
      rw [ENNReal.rpow_two]
      exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hcheb' : (ENNReal.ofReal (α / 2)) ^ (2:ℝ) * MeasureTheory.volume
        {x : ℝ | ENNReal.ofReal (α / 2) ≤ ‖czOp D K ε g x‖ₑ}
        ≤ (eLpNorm (czOp D K ε g) 2 volume) ^ (2:ℝ) := by
      simpa only [ENNReal.toReal_ofNat] using hcheb
    have hbnd : (eLpNorm (czOp D K ε g) 2 volume) ^ (2:ℝ)
        ≤ ENNReal.ofReal (4 * A2 ^ 2 * α * (∫ x, ‖f x‖ ∂volume)) := by
      calc (eLpNorm (czOp D K ε g) 2 volume) ^ (2:ℝ)
          ≤ (ENNReal.ofReal A2 * eLpNorm g 2 volume) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow hL2g (by norm_num)
        _ = (ENNReal.ofReal A2) ^ (2:ℝ) * (eLpNorm g 2 volume) ^ (2:ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ = ENNReal.ofReal (A2 ^ 2) * (eLpNorm g 2 volume) ^ (2:ℝ) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hA2.le (by norm_num), Real.rpow_ofNat]
        _ = ENNReal.ofReal (A2 ^ 2) * (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume) := by
            congr 1
            have h := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal
              (μ := (volume : Measure ℝ)) (p := 2)
              (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤) g
            rw [show (2:ℝ≥0∞).toReal = 2 by norm_num] at h
            exact h
        _ ≤ ENNReal.ofReal (A2 ^ 2) * ENNReal.ofReal (4 * α * (∫ x, ‖f x‖ ∂volume)) := by
            gcongr
        _ = ENNReal.ofReal (4 * A2 ^ 2 * α * (∫ x, ‖f x‖ ∂volume)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    have harith : ((α / 2) ^ 2)⁻¹ * (4 * A2 ^ 2 * α * (∫ x, ‖f x‖ ∂volume))
        = 16 * A2 ^ 2 * (∫ x, ‖f x‖ ∂volume) / α := by
      have h : ((α / 2) ^ 2)⁻¹ * (4 * α) = 16 / α := by
        field_simp
        ring
      calc ((α / 2) ^ 2)⁻¹ * (4 * A2 ^ 2 * α * (∫ x, ‖f x‖ ∂volume))
          = (((α / 2) ^ 2)⁻¹ * (4 * α)) * (A2 ^ 2 * (∫ x, ‖f x‖ ∂volume)) := by ring
        _ = (16 / α) * (A2 ^ 2 * (∫ x, ‖f x‖ ∂volume)) := by rw [h]
        _ = 16 * A2 ^ 2 * (∫ x, ‖f x‖ ∂volume) / α := by ring
    calc MeasureTheory.volume {x : ℝ | α / 2 < ‖czOp D K ε g x‖}
        ≤ MeasureTheory.volume {x : ℝ | ENNReal.ofReal (α / 2) ≤ ‖czOp D K ε g x‖ₑ} :=
          measure_mono (μ := (volume : Measure ℝ)) hsub
      _ = ((ENNReal.ofReal (α / 2)) ^ (2:ℝ))⁻¹ *
            ((ENNReal.ofReal (α / 2)) ^ (2:ℝ) * MeasureTheory.volume
              {x : ℝ | ENNReal.ofReal (α / 2) ≤ ‖czOp D K ε g x‖ₑ}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne' htop', one_mul]
      _ ≤ ((ENNReal.ofReal (α / 2)) ^ (2:ℝ))⁻¹
            * ((eLpNorm (czOp D K ε g) 2 volume) ^ (2:ℝ)) := by
          gcongr
      _ ≤ ((ENNReal.ofReal (α / 2)) ^ (2:ℝ))⁻¹
            * ENNReal.ofReal (4 * A2 ^ 2 * α * (∫ x, ‖f x‖ ∂volume)) := by
          gcongr
      _ = ENNReal.ofReal (16 * A2 ^ 2 * (∫ x, ‖f x‖ ∂volume) / α) := by
          have hsq : (ENNReal.ofReal (α / 2)) ^ (2:ℝ) = ENNReal.ofReal ((α / 2) ^ 2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ α / 2)]
          have hinv : (ENNReal.ofReal ((α / 2) ^ 2))⁻¹
              = ENNReal.ofReal (((α / 2) ^ 2)⁻¹) :=
            (ENNReal.ofReal_inv_of_pos (pow_pos (by linarith) 2)).symm
          rw [hsq, hinv, ← ENNReal.ofReal_mul (by positivity), harith]
  have hImeas : ∀ j, MeasurableSet (Set.Ioo (A j) (c j)) := fun j => measurableSet_Ioo
  have hbmeas : ∀ j, AEStronglyMeasurable (b j) volume := by
    intro j
    have h1 : b j = (Set.Ioo (A j) (c j)).indicator
        (fun x => f x - (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t)) := by
      funext x
      rw [hbdef j x]
      by_cases hx : x ∈ Set.Ioo (A j) (c j)
      · rw [if_pos hx, Set.indicator_of_mem hx]
      · rw [if_neg hx, Set.indicator_of_notMem hx]
    rw [h1]
    exact (hf.aestronglyMeasurable.sub aestronglyMeasurable_const).indicator measurableSet_Ioo
  have hb_lin : ∀ j, (∫⁻ x, ‖b j x‖ₑ ∂volume)
      ≤ 2 * ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume := by
    intro j
    set mean : H := (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) with hm
    have hpt : (fun x => ‖b j x‖ₑ)
        ≤ (Set.Ioo (A j) (c j)).indicator (fun x => ‖f x‖ₑ + ‖mean‖ₑ) := by
      intro x
      change ‖b j x‖ₑ ≤ (Set.Ioo (A j) (c j)).indicator (fun x => ‖f x‖ₑ + ‖mean‖ₑ) x
      by_cases hx : x ∈ Set.Ioo (A j) (c j)
      · rw [Set.indicator_of_mem hx, hbdef j x, if_pos hx, hm]
        exact enorm_sub_le
      · rw [Set.indicator_of_notMem hx, hbdef j x, if_neg hx, enorm_zero]
    have hmean_le : ‖mean‖ₑ * volume (Set.Ioo (A j) (c j))
        ≤ ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume := by
      have hAcj := hAc j
      have hnorm : ‖mean‖ * (c j - A j) ≤ ∫ x in (A j)..(c j), ‖f x‖ := by
        rw [hm, norm_smul]
        by_cases hℓ : c j - A j = 0
        · rw [hℓ, mul_zero]
          exact intervalIntegral.integral_nonneg hAcj (fun u _ => norm_nonneg _)
        · have hpos : 0 < c j - A j := lt_of_le_of_ne (sub_nonneg.mpr hAcj) (Ne.symm hℓ)
          rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
          calc (c j - A j)⁻¹ * ‖∫ t in (A j)..(c j), f t‖ * (c j - A j)
              = ‖∫ t in (A j)..(c j), f t‖ := by field_simp
            _ ≤ ∫ t in (A j)..(c j), ‖f t‖ :=
                intervalIntegral.norm_integral_le_integral_norm hAcj
      calc ‖mean‖ₑ * volume (Set.Ioo (A j) (c j))
          = ENNReal.ofReal (‖mean‖ * (c j - A j)) := by
            rw [Real.volume_Ioo, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        _ ≤ ENNReal.ofReal (∫ x in (A j)..(c j), ‖f x‖) := ENNReal.ofReal_le_ofReal hnorm
        _ = ENNReal.ofReal (∫ x in Set.Ioo (A j) (c j), ‖f x‖) := by
            rw [setIntegral_Ioo_eq_intervalIntegral (A j) (c j) hAcj (fun x => ‖f x‖)]
        _ ≤ ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume :=
            ofReal_setIntegral_norm_le_lintegral_enorm f measurableSet_Ioo
    calc (∫⁻ x, ‖b j x‖ₑ ∂volume)
        ≤ ∫⁻ x, (Set.Ioo (A j) (c j)).indicator (fun x => ‖f x‖ₑ + ‖mean‖ₑ) x ∂volume :=
          lintegral_mono hpt
      _ = ∫⁻ x in Set.Ioo (A j) (c j), (‖f x‖ₑ + ‖mean‖ₑ) ∂volume :=
          lintegral_indicator measurableSet_Ioo _
      _ = (∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume)
            + ‖mean‖ₑ * volume (Set.Ioo (A j) (c j)) := by
          rw [lintegral_add_left' ((hf.aestronglyMeasurable.enorm).restrict), setLIntegral_const]
      _ ≤ (∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume)
            + ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume := add_le_add le_rfl hmean_le
      _ = 2 * ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume := by rw [two_mul]
  have hb_fin : ∀ j, (∫⁻ x, ‖b j x‖ₑ ∂volume)
      ≤ ENNReal.ofReal (2 * (∫ x, ‖f x‖ ∂volume)) := by
    intro j
    refine (hb_lin j).trans ?_
    calc 2 * (∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume)
        ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂volume := by
          refine mul_le_mul_right ?_ 2
          have h := lintegral_mono_set (μ := volume) (f := fun x => ‖f x‖ₑ)
            (Set.subset_univ (Set.Ioo (A j) (c j)))
          rwa [Measure.restrict_univ] at h
      _ = 2 * ENNReal.ofReal (∫ x, ‖f x‖ ∂volume) := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hf]
      _ = ENNReal.ofReal (2 * (∫ x, ‖f x‖ ∂volume)) := by
          rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hb_int : ∀ j, Integrable (b j) volume := fun j =>
    ⟨hbmeas j, lt_of_le_of_lt (hb_fin j) ENNReal.ofReal_lt_top⟩
  have hbsum : (∑' j, (∫⁻ x, ‖b j x‖ₑ ∂volume))
      ≤ ENNReal.ofReal (2 * (∫ x, ‖f x‖ ∂volume)) := by
    calc (∑' j, (∫⁻ x, ‖b j x‖ₑ ∂volume))
        ≤ ∑' j, 2 * ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume :=
          ENNReal.tsum_le_tsum fun j => hb_lin j
      _ = 2 * ∑' j, ∫⁻ x in Set.Ioo (A j) (c j), ‖f x‖ₑ ∂volume := ENNReal.tsum_mul_left
      _ = 2 * ∫⁻ x in (⋃ j, Set.Ioo (A j) (c j)), ‖f x‖ₑ ∂volume := by
          rw [← lintegral_iUnion hImeas (fun j k hjk => hdisj j k hjk)]
      _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂volume := by
          refine mul_le_mul_right ?_ 2
          simpa only [Measure.restrict_univ] using lintegral_mono_set (μ := volume)
            (Set.subset_univ ((⋃ j, Set.Ioo (A j) (c j))))
      _ = ENNReal.ofReal (2 * (∫ x, ‖f x‖ ∂volume)) := by
          rw [← ofReal_integral_norm_eq_lintegral_enorm hf,
            show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hB : ∀ x, f x - g x = ∑' j, b j x := by
    intro x
    by_cases hx : ∃ j, x ∈ Set.Ioo (A j) (c j)
    · obtain ⟨j₀, hj₀⟩ := hx
      have huniq : ∀ j, j ≠ j₀ → b j x = 0 := by
        intro j hj
        rw [hbdef j x, if_neg]
        intro hmem
        exact Set.disjoint_left.mp (hdisj j j₀ hj) hmem hj₀
      rw [tsum_eq_single j₀ huniq, hbdef j₀ x, if_pos hj₀, hgin j₀ x hj₀]
    · have hj : ∀ j, x ∉ Set.Ioo (A j) (c j) := not_exists.mp hx
      have hz : (∑' j, b j x) = 0 := by
        rw [tsum_congr (fun j => by rw [hbdef j x, if_neg (hj j)]), tsum_zero]
      have hgx : g x = f x := hgout x (by
        intro hmem
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
        exact hj k hk)
      rw [hz, hgx, sub_self]
  have hsupp : ∀ j x, b j x ≠ 0 → |x - m j| ≤ Len j / 2 := by
    intro j x hx
    rw [hbdef j x] at hx
    by_cases hmem : x ∈ Set.Ioo (A j) (c j)
    · rw [if_pos hmem] at hx
      rw [abs_le]
      constructor
      · simp only [hmdef, hLdef]; linarith [hmem.1, hmem.2]
      · simp only [hmdef, hLdef]; linarith [hmem.1, hmem.2]
    · rw [if_neg hmem] at hx
      exact absurd rfl hx
  have hmean : ∀ j, ∫ x, b j x ∂volume = 0 := by
    intro j
    have h1 : b j = (Set.Ioo (A j) (c j)).indicator (b j) := by
      funext x
      by_cases hx : x ∈ Set.Ioo (A j) (c j)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hbdef j x, if_neg hx]
    rw [h1, integral_indicator measurableSet_Ioo, hbmean j]
  have hbad : ∫⁻ x in Eᶜ, ‖czOp D K ε (f - g) x‖ₑ ∂volume
      ≤ ENNReal.ofReal (2 * Ak * (∫ x, ‖f x‖ ∂volume)) := by
    have hTB : ∀ x, czOp D K ε (f - g) x = ∑' j, czOp D K ε (b j) x := by
      intro x
      have hsumm : ∀ i ∈ D, Summable (fun j => ∫ y, K i (x - y) • b j y ∂volume) := by
        intro i hi
        obtain ⟨C, hC⟩ := hKbdd i hi
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
        have hbnd2 : ∀ j, (∫⁻ y, ‖K i (x - y) • b j y‖ₑ ∂volume)
            ≤ ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume := by
          intro j
          calc ∫⁻ y, ‖K i (x - y) • b j y‖ₑ ∂volume
              = ∫⁻ y, ‖K i (x - y)‖ₑ * ‖b j y‖ₑ ∂volume :=
                lintegral_congr fun y => by rw [enorm_smul]
            _ ≤ ∫⁻ y, ENNReal.ofReal C * ‖b j y‖ₑ ∂volume := by
                refine lintegral_mono fun y => ?_
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hC (x - y))
            _ = ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        refine Summable.of_norm_bounded
          (g := fun j => C * (∫⁻ y, ‖b j y‖ₑ ∂volume).toReal) ?_ fun j => ?_
        · have hsum0 : Summable (fun j => (∫⁻ y, ‖b j y‖ₑ ∂volume).toReal) :=
            ENNReal.summable_toReal (ne_of_lt (lt_of_le_of_lt hbsum ENNReal.ofReal_lt_top))
          exact hsum0.mul_left C
        · have htop : (ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume) ≠ ⊤ :=
            ne_of_lt (lt_of_le_of_lt (mul_le_mul_right (hb_fin j) (ENNReal.ofReal C))
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
          calc ‖∫ y, K i (x - y) • b j y ∂volume‖
              ≤ ∫ y, ‖K i (x - y) • b j y‖ ∂volume := norm_integral_le_integral_norm _
            _ = (∫⁻ y, ‖K i (x - y) • b j y‖ₑ ∂volume).toReal :=
                integral_norm_eq_lintegral_enorm ((aestronglyMeasurable_comp_sub
                  (hKmeas i hi) x).smul (hbmeas j))
            _ ≤ (ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume).toReal :=
                ENNReal.toReal_mono htop (hbnd2 j)
            _ = C * (∫⁻ y, ‖b j y‖ₑ ∂volume).toReal := by
                rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0]
      have hper : ∀ i ∈ D, (∫ y, K i (x - y) • (f - g) y ∂volume)
          = ∑' j, ∫ y, K i (x - y) • b j y ∂volume := by
        intro i hi
        obtain ⟨C, hC⟩ := hKbdd i hi
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
        have hbnd2 : ∀ j, (∫⁻ y, ‖K i (x - y) • b j y‖ₑ ∂volume)
            ≤ ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume := by
          intro j
          calc ∫⁻ y, ‖K i (x - y) • b j y‖ₑ ∂volume
              = ∫⁻ y, ‖K i (x - y)‖ₑ * ‖b j y‖ₑ ∂volume :=
                lintegral_congr fun y => by rw [enorm_smul]
            _ ≤ ∫⁻ y, ENNReal.ofReal C * ‖b j y‖ₑ ∂volume := by
                refine lintegral_mono fun y => ?_
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hC (x - y))
            _ = ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        have hpt : (fun y => K i (x - y) • (f - g) y)
            = fun y => ∑' j, K i (x - y) • b j y := by
          funext y
          rw [Pi.sub_apply, hB y]
          by_cases hy : ∃ j, y ∈ Set.Ioo (A j) (c j)
          · obtain ⟨j₀, hj₀⟩ := hy
            have huniq : ∀ j, j ≠ j₀ → b j y = 0 := by
              intro j hj
              rw [hbdef j y, if_neg]
              intro hmem
              exact Set.disjoint_left.mp (hdisj j j₀ hj) hmem hj₀
            rw [tsum_eq_single j₀ huniq,
              tsum_eq_single j₀ (fun j hj => by rw [huniq j hj, smul_zero])]
          · have hz : ∀ j, b j y = 0 := fun j => by
              rw [hbdef j y, if_neg (not_exists.mp hy j)]
            rw [tsum_congr hz, tsum_zero,
              tsum_congr (fun j => by rw [hz j, smul_zero]), tsum_zero, smul_zero]
        rw [hpt, integral_tsum]
        · intro j
          exact (aestronglyMeasurable_comp_sub (hKmeas i hi) x).smul (hbmeas j)
        · refine ne_of_lt (lt_of_le_of_lt
            (b := ENNReal.ofReal (C * (2 * (∫ x, ‖f x‖ ∂volume)))) ?_ ENNReal.ofReal_lt_top)
          calc ∑' j, ∫⁻ y, ‖K i (x - y) • b j y‖ₑ ∂volume
              ≤ ∑' j, ENNReal.ofReal C * ∫⁻ y, ‖b j y‖ₑ ∂volume :=
                ENNReal.tsum_le_tsum fun j => (hbnd2 j)
            _ = ENNReal.ofReal C * ∑' j, ∫⁻ y, ‖b j y‖ₑ ∂volume := ENNReal.tsum_mul_left
            _ ≤ ENNReal.ofReal C * ENNReal.ofReal (2 * (∫ x, ‖f x‖ ∂volume)) := by
                gcongr
            _ = ENNReal.ofReal (C * (2 * (∫ x, ‖f x‖ ∂volume))) := by
                rw [← ENNReal.ofReal_mul hC0]
      rw [czOp]
      calc ∑ i ∈ D, ε i • ∫ y, K i (x - y) • (f - g) y ∂volume
          = ∑ i ∈ D, ∑' j, ε i • ∫ y, K i (x - y) • b j y ∂volume := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [hper i hi]
            by_cases hc : ε i = 0
            · rw [hc, zero_smul]
              simp only [zero_smul, tsum_zero]
            · exact (Summable.tsum_const_smul (ε i) (hsumm i hi)).symm
        _ = ∑' j, ∑ i ∈ D, ε i • ∫ y, K i (x - y) • b j y ∂volume := by
            refine (Summable.tsum_finsetSum ?_).symm
            intro i hi
            exact (hsumm i hi).const_smul (ε i)
        _ = ∑' j, czOp D K ε (b j) x := by
            refine tsum_congr fun j => ?_
            rw [czOp]
    calc ∫⁻ x in Eᶜ, ‖czOp D K ε (f - g) x‖ₑ ∂volume
        ≤ ∫⁻ x in Eᶜ, ∑' j, ‖czOp D K ε (b j) x‖ₑ ∂volume := by
          refine lintegral_mono fun x => ?_
          rw [hTB x]
          exact enorm_tsum_le_tsum_enorm
      _ = ∑' j, ∫⁻ x in Eᶜ, ‖czOp D K ε (b j) x‖ₑ ∂volume := by
          rw [lintegral_tsum]
          intro j
          exact (aestronglyMeasurable_czOp D K ε hKmeas (hb_int j)).enorm.restrict
      _ ≤ ∑' j, ENNReal.ofReal Ak * ∫⁻ x, ‖b j x‖ₑ ∂volume := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          by_cases hj : Len j = 0
          · have hAcj : c j = A j := by
              have hLj : Len j = c j - A j := rfl
              linarith [hAc j, hj]
            have hIempty : Set.Ioo (A j) (c j) = ∅ := by rw [hAcj, Set.Ioo_self]
            have hbj : b j = 0 := by
              funext y
              have hy : y ∉ Set.Ioo (A j) (c j) := by rw [hIempty]; exact Set.notMem_empty y
              rw [hbdef j y, if_neg hy]
              rfl
            have hT0 : czOp D K ε (0 : ℝ → H) = 0 := by
              funext y
              simp [czOp]
            rw [hbj, hT0]
            simp
          · have hLpos : 0 < Len j := lt_of_le_of_ne (hLnn j) (Ne.symm hj)
            exact badpart_lintegral_le D K ε Ak hε hKmeas hKbdd hoff (b j) (m j) (Len j) hLpos
              (hb_int j) (hsupp j) (hmean j) E hEmeas (fun x hx => hEcompl x hx j)
      _ = ENNReal.ofReal Ak * ∑' j, ∫⁻ x, ‖b j x‖ₑ ∂volume := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal Ak * ENNReal.ofReal (2 * (∫ x, ‖f x‖ ∂volume)) := by
          gcongr
      _ = ENNReal.ofReal (2 * Ak * (∫ x, ‖f x‖ ∂volume)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hEvol : MeasureTheory.volume E
      ≤ ENNReal.ofReal (100 * α⁻¹ * (∫ x, ‖f x‖ ∂volume)) := by
    have hlen : (∑' j, ENNReal.ofReal (Len j))
        ≤ ENNReal.ofReal (α⁻¹ * (∫ x, ‖f x‖ ∂volume)) := by
      have h1 : (∑' j, ENNReal.ofReal (Len j)) = volume (⋃ j, Set.Ioo (A j) (c j)) := by
        rw [MeasureTheory.measure_iUnion (fun j k hjk => hdisj j k hjk)
          (fun j => measurableSet_Ioo)]
        refine tsum_congr fun j => ?_
        simp only [Real.volume_Ioo, hLdef]
      rw [h1]
      exact hUm
    calc MeasureTheory.volume E
        ≤ ∑' j, MeasureTheory.volume
            (Set.Ioo (m j - 50 * Len j) (m j + 50 * Len j)) := by
          rw [hEdef]
          exact measure_iUnion_le _
      _ = ∑' j, ENNReal.ofReal (100 * Len j) := by
          refine tsum_congr fun j => ?_
          rw [Real.volume_Ioo]
          congr 1
          simp only [hmdef, hLdef]
          ring
      _ = 100 * ∑' j, ENNReal.ofReal (Len j) := by
          have hfun : (fun j => ENNReal.ofReal (100 * Len j))
              = fun j => (100 : ℝ≥0∞) * ENNReal.ofReal (Len j) := by
            funext j
            rw [show (100 : ℝ≥0∞) = ENNReal.ofReal 100 by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 100)]
          rw [hfun, ENNReal.tsum_mul_left]
      _ ≤ 100 * ENNReal.ofReal (α⁻¹ * (∫ x, ‖f x‖ ∂volume)) := by
          refine mul_le_mul_right hlen 100
      _ = ENNReal.ofReal (100 * α⁻¹ * (∫ x, ‖f x‖ ∂volume)) := by
          rw [show (100 : ℝ≥0∞) = ENNReal.ofReal 100 by norm_num,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hsubset : {x : ℝ | α < ‖czOp D K ε f x‖} ⊆
      E ∪ ({x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε g x‖}
        ∪ {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε (f - g) x‖}) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · rcases lt_or_ge (α / 2) ‖czOp D K ε g x‖ with hg | hg
      · exact Or.inr (Or.inl ⟨hxE, hg⟩)
      · refine Or.inr (Or.inr ⟨hxE, ?_⟩)
        by_contra hcon
        rw [not_lt] at hcon
        rw [Set.mem_ofPred_eq] at hx
        have hsum : czOp D K ε f x = czOp D K ε g x + czOp D K ε (f - g) x := by
          have h1 : czOp D K ε (g + (f - g)) = czOp D K ε g + czOp D K ε (f - g) :=
            czOp_add D K ε hKmeas hKbdd hgint' hbint'
          have h2 : g + (f - g) = f := by
            funext y
            simp only [Pi.add_apply, Pi.sub_apply]
            abel
          rw [h2] at h1
          exact congrFun h1 x
        rw [hsum] at hx
        linarith [norm_add_le (czOp D K ε g x) (czOp D K ε (f - g) x)]
  have hfin : MeasureTheory.volume {x : ℝ | α < ‖czOp D K ε f x‖}
      ≤ MeasureTheory.volume E
        + MeasureTheory.volume {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε g x‖}
        + MeasureTheory.volume {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε (f - g) x‖} := by
    refine le_trans (measure_mono (μ := (volume : Measure ℝ)) hsubset) ?_
    refine le_trans (measure_union_le (μ := (volume : Measure ℝ)) _ _) ?_
    have h2 := measure_union_le (μ := (volume : Measure ℝ))
      ({x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε g x‖})
      ({x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε (f - g) x‖})
    rw [add_assoc]
    exact add_le_add le_rfl h2
  have hTBmeas : AEStronglyMeasurable (czOp D K ε (f - g)) volume :=
    aestronglyMeasurable_czOp D K ε hKmeas hbint'
  have hvol2 : MeasureTheory.volume {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε (f - g) x‖}
      ≤ ENNReal.ofReal (4 * Ak * (∫ x, ‖f x‖ ∂volume) / α) := by
    have hne : ENNReal.ofReal (α / 2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    have htop : ENNReal.ofReal (α / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hMarkov := mul_meas_ge_le_lintegral₀ (μ := (volume : Measure ℝ))
      (f := Eᶜ.indicator (fun x => ‖czOp D K ε (f - g) x‖ₑ))
      (hTBmeas.enorm.indicator hEc) (ENNReal.ofReal (α / 2))
    have hsub : {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε (f - g) x‖} ⊆
        {x : ℝ | ENNReal.ofReal (α / 2)
          ≤ Eᶜ.indicator (fun x => ‖czOp D K ε (f - g) x‖ₑ) x} := by
      intro x hx
      obtain ⟨hxE, hlt⟩ := hx
      rw [Set.mem_ofPred_eq]
      rw [Set.indicator_of_mem (show x ∈ Eᶜ from hxE), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hlt.le
    calc MeasureTheory.volume {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε (f - g) x‖}
        ≤ MeasureTheory.volume {x : ℝ | ENNReal.ofReal (α / 2)
            ≤ Eᶜ.indicator (fun x => ‖czOp D K ε (f - g) x‖ₑ) x} :=
          measure_mono (μ := (volume : Measure ℝ)) hsub
      _ = (ENNReal.ofReal (α / 2))⁻¹ * (ENNReal.ofReal (α / 2) * MeasureTheory.volume
            {x : ℝ | ENNReal.ofReal (α / 2)
              ≤ Eᶜ.indicator (fun x => ‖czOp D K ε (f - g) x‖ₑ) x}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]
      _ ≤ (ENNReal.ofReal (α / 2))⁻¹ * ∫⁻ x,
            Eᶜ.indicator (fun x => ‖czOp D K ε (f - g) x‖ₑ) x ∂volume := by
          gcongr
      _ = (ENNReal.ofReal (α / 2))⁻¹ * ∫⁻ x in Eᶜ,
            ‖czOp D K ε (f - g) x‖ₑ ∂volume := by
          rw [lintegral_indicator hEc]
      _ ≤ (ENNReal.ofReal (α / 2))⁻¹
            * ENNReal.ofReal (2 * Ak * (∫ x, ‖f x‖ ∂volume)) := by
          gcongr
      _ = ENNReal.ofReal (4 * Ak * (∫ x, ‖f x‖ ∂volume) / α) := by
          rw [← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          ring

  have hvol1 : MeasureTheory.volume {x : ℝ | x ∉ E ∧ α / 2 < ‖czOp D K ε g x‖}
      ≤ ENNReal.ofReal (16 * A2 ^ 2 * (∫ x, ‖f x‖ ∂volume) / α) :=
    le_trans (measure_mono fun _ hx => hx.2) hgood
  have hconst : MeasureTheory.volume {x : ℝ | α < ‖czOp D K ε f x‖}
      ≤ ENNReal.ofReal (((24 * A2 ^ 2 + 4 * Ak + 100) / α) * (∫ x, ‖f x‖ ∂volume)) := by
    refine le_trans hfin ?_
    refine le_trans (add_le_add (add_le_add hEvol hvol1) hvol2) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show 100 * α⁻¹ * (∫ x, ‖f x‖ ∂volume) = 100 * (∫ x, ‖f x‖ ∂volume) / α by ring,
      show (24 * A2 ^ 2 + 4 * Ak + 100) / α * (∫ x, ‖f x‖ ∂volume)
        = (24 * A2 ^ 2 + 4 * Ak + 100) * (∫ x, ‖f x‖ ∂volume) / α by ring,
      ]
    rw [← add_div, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hα.le
    nlinarith [sq_nonneg A2, hMnn, hAk]
  refine le_trans hconst ?_
  have hE1 : MeasureTheory.eLpNorm f 1 MeasureTheory.volume
      = ENNReal.ofReal (∫ x, ‖f x‖ ∂volume) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), ofReal_integral_norm_eq_lintegral_enorm hf]
  rw [hE1, ENNReal.ofReal_mul (by positivity)]

/-- **The `L^p` bound, `1 < p < 2`, by Marcinkiewicz interpolation** between the weak-type
`(1,1)` bound `weak_type_one_of_hoff` and the given `L²` bound. -/
theorem lp_bound_small_p {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (Ak A2 : ℝ)
      (hAk : 0 ≤ Ak) (hA2 : 0 < A2) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
      (hKmeas : ∀ i ∈ D, MeasureTheory.AEStronglyMeasurable (K i) MeasureTheory.volume)
      (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
      (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak)
      (hL2 : ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D K ε f) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.volume),
      ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.eLpNorm (czOp D K ε f) (ENNReal.ofReal p) MeasureTheory.volume
          ≤ ENNReal.ofReal (C * (A2 ^ 2 + Ak + 1))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  refine ⟨(1200 * 2 ^ (p - 1) / (p - 1) + 16 / (2 - p)) ^ (1 / p), ?_, ?_⟩
  · have h2p : (0:ℝ) < 2 ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (0:ℝ) < p - 1 := by linarith
    have h2 : (0:ℝ) < 2 - p := by linarith
    have h3 : (0:ℝ) < 1200 * 2 ^ (p - 1) / (p - 1) := div_pos (by positivity) h1
    have h4 : (0:ℝ) < 16 / (2 - p) := div_pos (by norm_num) h2
    exact Real.rpow_pos_of_pos (by linarith) _
  · intro ι' H _ _ _ D K ε Ak A2 hAk hA2 hε hKmeas hKbdd hoff hL2 f hf
    letI : MeasurableSpace H := borel H
    have hA0pos : (0:ℝ) < 24 * A2 ^ 2 + 4 * Ak + 100 := by positivity
    have hA2ne : ENNReal.ofReal A2 ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hA2
    have hweak : ∀ (g : ℝ → H) (lam : ℝ), Integrable g volume → 0 < lam →
        volume {x : ℝ | lam < ‖czOp D K ε g x‖}
          ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / lam) * eLpNorm g 1 volume :=
      fun g lam hg hlam =>
        weak_type_one_of_hoff D K ε Ak A2 hAk hA2 hε hKmeas hKbdd hoff hL2 g hg lam hlam
    have hstrong : ∀ g : ℝ → H, Integrable g volume →
        eLpNorm (czOp D K ε g) 2 volume ≤ ENNReal.ofReal A2 * eLpNorm g 2 volume := by
      intro g hg
      by_cases hm : MemLp g 2 volume
      · exact hL2 g hg hm
      · have htop : eLpNorm g 2 volume = ⊤ := by
          by_contra h
          exact hm (lt_top_iff_ne_top.mpr h)
        rw [htop, ENNReal.mul_top hA2ne]
        exact le_top
    have hadd : ∀ f g : ℝ → H, Integrable f volume → Integrable g volume →
        czOp D K ε (f + g) = czOp D K ε f + czOp D K ε g :=
      fun f g hf hg => czOp_add D K ε hKmeas hKbdd hf hg
    have hmain := Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (T := czOp D K ε)
      (A0 := 24 * A2 ^ 2 + 4 * Ak + 100) (A1 := A2)
      hadd hA0pos hA2 hweak hstrong hp1 hp2 f hf
    have hconst :
        (12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1) / (p - 1) + 16 * A2 ^ 2 / (2 - p))
            ^ (1 / p)
          ≤ (1200 * 2 ^ (p - 1) / (p - 1) + 16 / (2 - p)) ^ (1 / p) * (A2 ^ 2 + Ak + 1) := by
      set S : ℝ := A2 ^ 2 + Ak + 1 with hS
      set K0 : ℝ := 1200 * 2 ^ (p - 1) / (p - 1) + 16 / (2 - p) with hK0
      have hp1' : (0:ℝ) < p - 1 := by linarith
      have hp2' : (0:ℝ) < 2 - p := by linarith
      have h2p : (0:ℝ) < 2 ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num) _
      have hS1 : 1 ≤ S := by rw [hS]; nlinarith [sq_nonneg A2, hAk]
      have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS1
      have hK0pos : 0 < K0 := by rw [hK0]; positivity
      have hA0le : 24 * A2 ^ 2 + 4 * Ak + 100 ≤ 100 * S := by rw [hS]; nlinarith
      have hA2le : A2 ^ 2 ≤ S := by rw [hS]; nlinarith [hAk]
      have hKle : 12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1) / (p - 1)
          + 16 * A2 ^ 2 / (2 - p) ≤ S * K0 := by
        rw [hK0]
        have h12 : 12 * (24 * A2 ^ 2 + 4 * Ak + 100) ≤ 1200 * S := by nlinarith [hA0le]
        have h1 : 12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1) / (p - 1)
            ≤ S * (1200 * 2 ^ (p - 1) / (p - 1)) := by
          have hnum : 12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1)
              ≤ 1200 * 2 ^ (p - 1) * S := by nlinarith [h12, h2p]
          rw [show S * (1200 * 2 ^ (p - 1) / (p - 1)) = 1200 * 2 ^ (p - 1) * S / (p - 1) by ring]
          exact div_le_div_of_nonneg_right hnum hp1'.le
        have h3 : 16 * A2 ^ 2 / (2 - p) ≤ S * (16 / (2 - p)) := by
          rw [show S * (16 / (2 - p)) = 16 * S / (2 - p) by ring]
          exact div_le_div_of_nonneg_right (by nlinarith [hA2le]) hp2'.le
        linarith
      have hKnonneg : (0:ℝ) ≤ 12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1) / (p - 1)
          + 16 * A2 ^ 2 / (2 - p) := by
        have h1 : (0:ℝ) ≤ 12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1) / (p - 1) :=
          div_nonneg (by positivity) hp1'.le
        have h2 : (0:ℝ) ≤ 16 * A2 ^ 2 / (2 - p) := div_nonneg (by positivity) hp2'.le
        linarith
      have hSpow : S ^ (1 / p) ≤ S := by
        calc S ^ (1 / p) ≤ S ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hS1 (by
                rw [div_le_iff₀ (by linarith : (0:ℝ) < p)]; linarith)
          _ = S := Real.rpow_one S
      calc (12 * (24 * A2 ^ 2 + 4 * Ak + 100) * 2 ^ (p - 1) / (p - 1)
            + 16 * A2 ^ 2 / (2 - p)) ^ (1 / p)
          ≤ (S * K0) ^ (1 / p) := Real.rpow_le_rpow hKnonneg hKle (by positivity)
        _ = S ^ (1 / p) * K0 ^ (1 / p) := Real.mul_rpow hSpos.le hK0pos.le
        _ ≤ S * K0 ^ (1 / p) :=
            mul_le_mul_of_nonneg_right hSpow (Real.rpow_nonneg hK0pos.le _)
        _ = K0 ^ (1 / p) * S := by ring
    refine hmain.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) _

end

end Work.Analysis.CzShift
