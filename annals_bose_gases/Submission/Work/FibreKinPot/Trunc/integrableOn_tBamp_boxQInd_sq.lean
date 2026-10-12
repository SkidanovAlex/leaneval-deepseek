import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.FibreWord.SliceAE
import Submission.Work.FibreWord.fibPiece_ae_eq_zero_of_fibMass_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FibreKinPot.Trunc

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## Auxiliary lemmas

The two ingredients of the bound are proved from scratch here (they are the generic
hypothesis-based versions of the corresponding private lemmas of
`Work.SlotWord.integrableOn_tBamp_slotPiece_ampSq`, with continuity/compact support of the window
replaced by bare integrability of `|χ|`, and with a merely measurable window and state). -/

/-- **The windowed amplitude is bounded by the window mass times the sup bound.**  If `|χ|` is
integrable, `χ` vanishes off `acube L`, and `Ψ` is bounded by `B ≥ 0` on the ambient box `abox N L`,
then for `x ∈ abox N L` the amplitude is bounded by `B · ∫z, |χ z|`: off the support of `χ` the
integrand vanishes, while on it the updated configuration stays in the box. -/
private theorem norm_tBamp_le_of_integrable {N : ℕ} {L : ℝ} {χ : ℝ³ → ℝ}
    (hχint : MeasureTheory.Integrable (fun z : ℝ³ => |χ z|))
    (hχsupp : ∀ z : ℝ³, χ z ≠ 0 → z ∈ Submission.BoseGases.acube L)
    {Ψ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y ∈ Submission.BoseGases.abox N L, |Ψ y| ≤ B)
    (i : Fin N) (p : ℝ³) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N L) :
    ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ≤ B * ∫ z : ℝ³, |χ z| := by
  have hint : MeasureTheory.Integrable (fun z : ℝ³ => |χ z| * B) := hχint.mul_const B
  have hexp : ∀ z : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    intro z
    rw [Complex.norm_exp]
    simp
  have hpt : ∀ z : ℝ³,
      ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Ψ (Function.update x i z) : ℂ)‖ ≤ |χ z| * B := by
    intro z
    simp only [norm_mul, hexp z, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases hz : χ z = 0
    · rw [hz]; simp
    · have hzA : z ∈ Submission.BoseGases.acube L := hχsupp z hz
      have hmem : Function.update x i z ∈ Submission.BoseGases.abox N L := by
        rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
        intro j
        rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj]; exact hzA
        · rw [if_neg hj]; exact hx j
      exact mul_le_mul_of_nonneg_left (hb _ hmem) (abs_nonneg _)
  calc ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
      = ‖∫ z, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)‖ := by simp only [Work.SmallBoxTBWord.tBamp]
    _ ≤ ∫ z, ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, |χ z| * B :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = B * ∫ z, |χ z| := by rw [integral_mul_const]; ring

/-- The amplitude `x ↦ tBamp χ p Ψ i x` is measurable for a measurable window `χ` and a measurable
state `Ψ`: the integrand `(x,z) ↦ χ z · e^{−i⟪p,z⟫} · Ψ (x_{i←z})` is jointly measurable, so the
parametric Bochner integral is strongly measurable (`StronglyMeasurable.integral_prod_right'`). -/
private theorem measurable_tBamp_of_measurable {N : ℕ} {χ : ℝ³ → ℝ} (hχ : Measurable χ)
    (p : ℝ³) {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) (i : Fin N) :
    Measurable (fun x : Submission.BoseGases.X N => Work.SmallBoxTBWord.tBamp χ p Ψ i x) := by
  have hprod : Continuous (fun q : Submission.BoseGases.X N × ℝ³ => (p, q.2)) :=
    continuous_const.prodMk continuous_snd
  have hinner_c : Continuous (fun q : Submission.BoseGases.X N × ℝ³ => (inner ℝ p q.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp hprod)
  have hexp_meas : Measurable (fun q : Submission.BoseGases.X N × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner_c).neg)).measurable
  have hJ : Measurable (fun q : Submission.BoseGases.X N × ℝ³ =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
        (Ψ (Function.update q.1 i q.2) : ℂ)) := by
    refine Measurable.mul (Measurable.mul ?_ hexp_meas) ?_
    · exact Complex.continuous_ofReal.measurable.comp (hχ.comp measurable_snd)
    · exact Complex.continuous_ofReal.measurable.comp (hΨ.comp measurable_update')
  have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable

/-- **The (R3)-integrability of the squared windowed amplitude of a box projection.**  Let `L > 0`,
`A` a measurable subset of the ambient cube `acube L` of finite measure with `volA = |A|`, `χ` a
measurable window with `Integrable (fun z => |χ z|)` and supported in `acube L`
(`χ z ≠ 0 → z ∈ acube L`), and `Ψ` a measurable state bounded by `M ≥ 0` on the ambient box
`abox N L`.  Then the squared modulus of the windowed amplitude of FS's mean-free box projection
`Q_{A,i}Ψ` is integrable over `abox N L`.

The proof is a uniform bound: `|Q_{A,i}Ψ y| ≤ 2M` on `abox N L`
(`Work.SlotWord.abs_boxQInd_le`), because `A ⊆ acube L` keeps the box mean inside `abox N L`; hence
for `x ∈ abox N L` the amplitude integrand is pointwise bounded by `|χ z| · 2M` (the points where
`χ` is nonzero lie in `acube L`, so `x_{i←z}` stays in the box), giving
`‖tBamp χ p (Q_{A,i}Ψ) i x‖ ≤ 2M · ∫ z, |χ z|`.  `abox N L` has finite measure
(`Submission.BoseGases.restrict_abox_eq_pi` plus the `Measure.pi` instance), the amplitude is
a.e.-strongly measurable (`StronglyMeasurable.integral_prod_right'` applied to the measurable joint
map `(x,z) ↦ χ z · e^{−i⟪p,z⟫} · Q_{A,i}Ψ (x_{i←z})`), and `MeasureTheory.Integrable.of_bound`
closes. -/
theorem integrableOn_tBamp_boxQInd_sq {N : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAL : A ⊆ Submission.BoseGases.acube L)
    (hAfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤)
    {volA : ℝ} (hvol : volA = MeasureTheory.volume.real A)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχmeas : Measurable χ)
    (hχint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => |χ z|))
    (hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ Submission.BoseGases.acube L)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨmeas : Measurable Ψ) {M : ℝ} (hM : 0 ≤ M)
    (hΨb : ∀ y ∈ Submission.BoseGases.abox N L, |Ψ y| ≤ M)
    (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
      (Submission.BoseGases.abox N L) := by
  -- The projected state is bounded by `2M` on the box
  have hQb : ∀ x ∈ Submission.BoseGases.abox N L,
      |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * M :=
    Work.SlotWord.abs_boxQInd_le L hA hvol hAfin hAL hM hΨb i
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith
  -- The amplitude is pointwise bounded by the window mass times `2M`
  have hbamp : ∀ x ∈ Submission.BoseGases.abox N L,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖
        ≤ (2 * M) * ∫ z : ℝ³, |χ z| :=
    fun x hx => norm_tBamp_le_of_integrable hχint hχsupp h2M hQb i p hx
  -- Measurability of the squared amplitude
  have hQm : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxQInd volA A i Ψ x) :=
    Work.SlotWord.measurable_boxQInd volA A hA i hΨmeas
  have hampm : Measurable (fun x : Submission.BoseGases.X N =>
      Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x) :=
    measurable_tBamp_of_measurable hχmeas p hQm i
  have hsqm : Measurable (fun x : Submission.BoseGases.X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) :=
    hampm.norm.pow_const 2
  -- Integrability on the (finite-measure) box from the uniform bound
  refine MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top N L hL.le) hsqm.aestronglyMeasurable
    (((2 * M) * ∫ z : ℝ³, |χ z|) ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N L)]
    with x hx
  have h1 : ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖
      ≤ (2 * M) * ∫ z : ℝ³, |χ z| := hbamp x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

end

end Work.FibreKinPot.Trunc
