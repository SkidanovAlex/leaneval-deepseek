import Mathlib
import Submission.Work.Analysis.CzShift.adjoint_defs

/-!
# The formal adjointness of the finite sum of shifted convolution operators

This is the analytic core behind `Work.Analysis.CzShift.adjoint_l2_bound`: the formal `L²`
adjoint of `czOp D K ε` is `czOp D (adjKernel K) (adjSigns ε)`.  The proof is the standard
Fubini argument: expand both pairings into double integrals, use that `f, g ∈ L¹` and that
every `K i` is a.e. strongly measurable and bounded to justify Fubini, then swap the two
integration variables.

The auxiliary lemmas below isolate the two ingredients that are not in Mathlib:

* `integrable_kernel_inner_prod`: the integrand `(x, y) ↦ K i (x - y) * ⟪g x, f y⟫` is
  integrable for the product measure (dominated by `‖g x‖ * ‖f y‖`);
* `integrable_shiftKernel_smul` / `integrable_adjKernel_smul`: the inner integrands
  `y ↦ K i (x - y) • f y` and `y ↦ adjKernel K i (x - y) • g y` are integrable, which is
  what allows `ContinuousLinearMap.integral_comp_comm` to move the inner product inside the
  Bochner integral.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Filter

/-- `AEStronglyMeasurable` is preserved when composing (on the inside) with `p ↦ p.1 - p.2`,
for the product measure: `(x, y) ↦ x - y` is quasi-measure-preserving. -/
private lemma aestronglyMeasurable_sub_prod {K : ℝ → ℂ} (hK : AEStronglyMeasurable K volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => K (p.1 - p.2)) (volume.prod volume) := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun p => h (p.1 - p.2), hh.comp_measurable (measurable_fst.sub measurable_snd), ?_⟩
  exact (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant volume volume).ae_eq heq

/-- `AEStronglyMeasurable` is preserved when composing with `y ↦ x - y`. -/
private lemma aestronglyMeasurable_sub_left {K : ℝ → ℂ} (hK : AEStronglyMeasurable K volume)
    (x : ℝ) : AEStronglyMeasurable (fun y => K (x - y)) volume := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun y => h (x - y), hh.comp_measurable (measurable_const.sub measurable_id), ?_⟩
  exact (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae_eq heq

/-- `AEStronglyMeasurable` is preserved when composing with `y ↦ -(x - y)`. -/
private lemma aestronglyMeasurable_negSub {K : ℝ → ℂ} (hK : AEStronglyMeasurable K volume)
    (x : ℝ) : AEStronglyMeasurable (fun y => star (K (-(x - y)))) volume := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun y => star (h (-(x - y))),
    continuous_star.comp_stronglyMeasurable
      (hh.comp_measurable ((measurable_const.sub measurable_id).neg)), ?_⟩
  filter_upwards [((MeasureTheory.quasiMeasurePreserving_neg_of_right_invariant volume).comp
    (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant volume x)).ae heq] with y hy
  exact congrArg star hy

/-- `AEStronglyMeasurable` is preserved by the formal adjoint of the kernel family. -/
private lemma aestronglyMeasurable_adjKernel {ι : Type*} {K : ι → ℝ → ℂ} {i : ι}
    (hK : AEStronglyMeasurable (K i) volume) : AEStronglyMeasurable (adjKernel K i) volume := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun x => star (h (-x)),
    continuous_star.comp_stronglyMeasurable (hh.comp_measurable measurable_neg), ?_⟩
  filter_upwards [(MeasureTheory.quasiMeasurePreserving_neg_of_right_invariant volume).ae heq]
    with x hx
  exact congrArg star hx

/-- `y ↦ K (x - y) • F y` is integrable when `K` is a.e. strongly measurable and bounded and
`F ∈ L¹`. -/
private lemma integrable_shiftKernel_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : ℝ → ℂ} {F : ℝ → H} (hK : AEStronglyMeasurable K volume)
    (hKb : ∃ C, ∀ x, ‖K x‖ ≤ C) (hF : Integrable F) (x : ℝ) :
    Integrable (fun y => K (x - y) • F y) volume := by
  obtain ⟨C, hC⟩ := hKb
  refine Integrable.mono' (hF.norm.const_mul (max C 0))
    (continuous_smul.comp_aestronglyMeasurable₂ (aestronglyMeasurable_sub_left hK x)
      hF.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (le_trans (hC _) (le_max_left C 0)) (norm_nonneg _)

/-- `y ↦ adjKernel K i (x - y) • F y` is integrable when `K i` is a.e. strongly measurable and
bounded and `F ∈ L¹`. -/
private lemma integrable_adjKernel_smul {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (K : ι → ℝ → ℂ) (i : ι) {F : ℝ → H}
    (hK : AEStronglyMeasurable (K i) volume)
    (hKb : ∃ C, ∀ x, ‖K i x‖ ≤ C) (hF : Integrable F) (x : ℝ) :
    Integrable (fun y => adjKernel K i (x - y) • F y) volume := by
  obtain ⟨C, hC⟩ := hKb
  have hC' : ∀ z, ‖adjKernel K i z‖ ≤ C := by
    intro z; rw [adjKernel_apply, norm_star]; exact hC _
  have hmeas : AEStronglyMeasurable (fun y : ℝ => adjKernel K i (x - y)) volume := by
    simpa only [adjKernel_apply] using aestronglyMeasurable_negSub hK x
  refine Integrable.mono' (hF.norm.const_mul (max C 0))
    (continuous_smul.comp_aestronglyMeasurable₂ hmeas hF.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (le_trans (hC' _) (le_max_left C 0)) (norm_nonneg _)

/-- The integrand `p ↦ K (p.1 - p.2) * ⟪g p.1, f p.2⟫` of the double integral is integrable with
respect to the product measure. -/
private lemma integrable_kernel_inner_prod {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : ℝ → ℂ} {f g : ℝ → H} (hK : AEStronglyMeasurable K volume)
    (hKb : ∃ C, ∀ x, ‖K x‖ ≤ C) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => K (p.1 - p.2) * inner ℂ (g p.1) (f p.2))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hKb
  have hmeas_inner : AEStronglyMeasurable (fun p : ℝ × ℝ => inner ℂ (g p.1) (f p.2))
      (volume.prod volume) :=
    (hg.aestronglyMeasurable.comp_fst (ν := volume)).inner
      (hf.aestronglyMeasurable.comp_snd (μ := volume))
  refine Integrable.mono' ((hg.norm.mul_prod hf.norm).const_mul (max C 0))
    ((aestronglyMeasurable_sub_prod hK).mul hmeas_inner) (Eventually.of_forall fun p => ?_)
  rw [norm_mul]
  calc ‖K (p.1 - p.2)‖ * ‖inner ℂ (g p.1) (f p.2)‖
      ≤ ‖K (p.1 - p.2)‖ * (‖g p.1‖ * ‖f p.2‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ max C 0 * (‖g p.1‖ * ‖f p.2‖) :=
        mul_le_mul_of_nonneg_right (le_trans (hC _) (le_max_left _ _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Pointwise expansion of the pairing `⟪g x, czOp D K ε f x⟫` as a finite sum of iterated
integrals. -/
private lemma inner_czOp {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (f g : ℝ → H) (x : ℝ)
    (hInt : ∀ i ∈ D, Integrable (fun y => K i (x - y) • f y) volume) :
    inner ℂ (g x) (czOp D K ε f x)
      = ∑ i ∈ D, ε i * ∫ y, K i (x - y) * inner ℂ (g x) (f y) := by
  simp only [czOp]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_smul_right]
  have h1 : (∫ y, K i (x - y) * inner ℂ (g x) (f y))
      = ∫ y, (innerSL ℂ (g x)) (K i (x - y) • f y) :=
    integral_congr_ae (Eventually.of_forall fun y =>
      (inner_smul_right (g x) (f y) (K i (x - y))).symm)
  rw [h1]
  exact congrArg (fun z => ε i * z)
    (ContinuousLinearMap.integral_comp_comm (innerSL ℂ (g x)) (hInt i hi)).symm

/-- Pointwise expansion of the pairing `⟪czOp D (adjKernel K) (adjSigns ε) g x, f x⟫`. -/
private lemma inner_czOp_adj {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (f g : ℝ → H) (x : ℝ)
    (hInt : ∀ i ∈ D, Integrable (fun y => adjKernel K i (x - y) • g y) volume) :
    inner ℂ (czOp D (adjKernel K) (adjSigns ε) g x) (f x)
      = ∑ i ∈ D, ε i * ∫ y, K i (y - x) * inner ℂ (g y) (f x) := by
  simp only [czOp, adjSigns]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_smul_left, starRingEnd_apply, star_star]
  have h1 : (∫ y, K i (y - x) * inner ℂ (g y) (f x))
      = ∫ y, (innerSLFlip ℂ (f x)) (adjKernel K i (x - y) • g y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [innerSLFlip_apply_apply, inner_smul_left]
    simp only [adjKernel_apply, neg_sub, starRingEnd_apply, star_star]
  rw [h1]
  exact congrArg (fun z => ε i * z)
    (ContinuousLinearMap.integral_comp_commSL (by intro r z; simp)
      (innerSLFlip ℂ (f x)) (hInt i hi)).symm

/-- Fubini's theorem in the form needed here: for an integrable `F` on `ℝ × ℝ`, the iterated
integrals in the two orders agree. -/
private lemma double_integral_swap (F : ℝ → ℝ → ℂ)
    (hF : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (volume.prod volume)) :
    ∫ x, ∫ y, F y x ∂volume ∂volume = ∫ x, ∫ y, F x y ∂volume ∂volume := by
  have h := integral_integral_swap (μ := volume) (ν := volume) (f := fun a b => F b a) hF.swap
  simpa using h

/-- **The formal adjointness identity** for the convolution operator `czOp D K ε`, in the
conjugate-free form: for integrable `f` and `g`,
`∫ x, ⟪g x, czOp D K ε f x⟫ = ∫ x, ⟪czOp D (adjKernel K) (adjSigns ε) g x, f x⟫`,
i.e. `czOp D (adjKernel K) (adjSigns ε)` is the `L²`-adjoint of `czOp D K ε` (equivalently
`∫ ⟪T f, g⟫ = ∫ ⟪f, T* g⟫`, since `⟪u, v⟫ = conj ⟪v, u⟫`).  The proof is Fubini on
`K i (x - y) * ⟪g x, f y⟫` (absolutely convergent since `f, g ∈ L¹` and `K i` is bounded,
by `norm_inner_le_norm`) followed by the measure-preserving swap `(x, y) ↦ (y, x)`.  Useful
ingredients: `ContinuousLinearMap.integral_comp_comm` applied to `innerSL ℂ (g x)`,
`inner_sum`, `sum_inner`, `MeasureTheory.integral_integral_swap`. -/
theorem czOp_adjoint_pairing {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (hKmeas : ∀ i ∈ D, MeasureTheory.AEStronglyMeasurable (K i) MeasureTheory.volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (f g : ℝ → H) (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) :
    ∫ x, inner ℂ (g x) (czOp D K ε f x) ∂MeasureTheory.volume
      = ∫ x, inner ℂ (czOp D (adjKernel K) (adjSigns ε) g x) (f x) ∂MeasureTheory.volume := by
  have hΦ : ∀ i ∈ D, Integrable (fun p : ℝ × ℝ => K i (p.1 - p.2) * inner ℂ (g p.1) (f p.2))
      (volume.prod volume) :=
    fun i hi => integrable_kernel_inner_prod (hKmeas i hi) (hKbdd i hi) hf hg
  have key : ∀ i ∈ D, (∫ x, ∫ y, K i (x - y) * inner ℂ (g x) (f y) ∂volume ∂volume)
      = ∫ p, K i (p.1 - p.2) * inner ℂ (g p.1) (f p.2) ∂(volume.prod volume) :=
    fun i hi => (integral_prod _ (hΦ i hi)).symm
  have hL : (∫ x, inner ℂ (g x) (czOp D K ε f x) ∂volume)
      = ∑ i ∈ D, ε i * ∫ p, K i (p.1 - p.2) * inner ℂ (g p.1) (f p.2)
          ∂(volume.prod volume) := by
    calc ∫ x, inner ℂ (g x) (czOp D K ε f x) ∂volume
        = ∫ x, ∑ i ∈ D, ε i * (∫ y, K i (x - y) * inner ℂ (g x) (f y) ∂volume)
            ∂volume := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          exact inner_czOp D K ε f g x
            (fun i hi => integrable_shiftKernel_smul (hKmeas i hi) (hKbdd i hi) hf x)
      _ = ∑ i ∈ D, ∫ x, ε i * (∫ y, K i (x - y) * inner ℂ (g x) (f y) ∂volume)
            ∂volume :=
          integral_finsetSum D (fun i hi => ((hΦ i hi).integral_prod_left).const_mul (ε i))
      _ = ∑ i ∈ D, ε i * ∫ x, (∫ y, K i (x - y) * inner ℂ (g x) (f y) ∂volume)
            ∂volume := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [integral_const_mul]
      _ = ∑ i ∈ D, ε i * ∫ p, K i (p.1 - p.2) * inner ℂ (g p.1) (f p.2)
            ∂(volume.prod volume) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [key i hi]
  have hR : (∫ x, inner ℂ (czOp D (adjKernel K) (adjSigns ε) g x) (f x) ∂volume)
      = ∑ i ∈ D, ε i * ∫ p, K i (p.1 - p.2) * inner ℂ (g p.1) (f p.2)
          ∂(volume.prod volume) := by
    calc ∫ x, inner ℂ (czOp D (adjKernel K) (adjSigns ε) g x) (f x) ∂volume
        = ∫ x, ∑ i ∈ D, ε i * (∫ y, K i (y - x) * inner ℂ (g y) (f x) ∂volume)
            ∂volume := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          exact inner_czOp_adj D K ε f g x
            (fun i hi => integrable_adjKernel_smul K i (hKmeas i hi) (hKbdd i hi) hg x)
      _ = ∑ i ∈ D, ∫ x, ε i * (∫ y, K i (y - x) * inner ℂ (g y) (f x) ∂volume)
            ∂volume :=
          integral_finsetSum D (fun i hi => ((hΦ i hi).swap.integral_prod_left).const_mul (ε i))
      _ = ∑ i ∈ D, ε i * ∫ x, (∫ y, K i (y - x) * inner ℂ (g y) (f x) ∂volume)
            ∂volume := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [integral_const_mul]
      _ = ∑ i ∈ D, ε i * ∫ x, (∫ y, K i (x - y) * inner ℂ (g x) (f y) ∂volume)
            ∂volume := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [double_integral_swap (fun a b => K i (a - b) * inner ℂ (g a) (f b)) (hΦ i hi)]
      _ = ∑ i ∈ D, ε i * ∫ p, K i (p.1 - p.2) * inner ℂ (g p.1) (f p.2)
            ∂(volume.prod volume) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [key i hi]
  exact hL.trans hR.symm

/-- The same adjointness identity in the conjugate form `∫ x, ⟪T f x, g x⟫ = ∫ x, ⟪f x, T* g x⟫`.
It is equivalent to `czOp_adjoint_pairing` because `⟪u, v⟫ = conj ⟪v, u⟫`; here it is derived
from the conjugate-free form applied to the adjoint kernel family, using that `adjKernel` and
`adjSigns` are involutions. -/
theorem czOp_adjoint_pairing_conj {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (hKmeas : ∀ i ∈ D, MeasureTheory.AEStronglyMeasurable (K i) MeasureTheory.volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (f g : ℝ → H) (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) :
    ∫ x, inner ℂ (czOp D K ε f x) (g x) ∂MeasureTheory.volume
      = ∫ x, inner ℂ (f x) (czOp D (adjKernel K) (adjSigns ε) g x) ∂MeasureTheory.volume := by
  have hK' : ∀ i ∈ D, AEStronglyMeasurable (adjKernel K i) volume :=
    fun i hi => aestronglyMeasurable_adjKernel (hKmeas i hi)
  have hKb' : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖adjKernel K i x‖ ≤ C := by
    intro i hi
    obtain ⟨C, hC⟩ := hKbdd i hi
    exact ⟨C, fun x => by rw [adjKernel_apply, norm_star]; exact hC _⟩
  have h := czOp_adjoint_pairing D (adjKernel K) (adjSigns ε) hK' hKb' g f hg hf
  have hKK : adjKernel (adjKernel K) = K := by funext i x; simp [adjKernel_apply]
  have hee : adjSigns (adjSigns ε) = ε := by funext i; simp [adjSigns]
  rw [hKK, hee] at h
  exact h.symm

end Work.Analysis.CzShift
