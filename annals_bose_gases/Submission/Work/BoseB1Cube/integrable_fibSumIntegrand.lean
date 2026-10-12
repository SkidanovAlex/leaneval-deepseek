import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.fibSumFibreAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The joint a.e. strong measurability of the slot kernel

The `u`-dependence of the localised kernel sits in the two cutoff factors
`χ_{B(u)}(z) = χ(z/ℓ)·χ_M((ℓd)⁻¹•z − u)` of `wSmall1Pair`; the numerator `g₀ v h = v(1−w₀)` is
`u`-independent and only a.e. strongly measurable.  Everything except `g₀` is a composition of a
jointly continuous cutoff with continuous projections, and `g₀` is handled by
`Work.UBBInputs2.aemeasurable_comp_sub_coord`. -/

/-- Joint a.e. strong measurability of the `i`-th slot kernel in `(u, x, y)` over
`(volume.prod volume).prod (volume.restrict (acube ℓ))`. -/
private theorem aesm_wSmall1Pair_slot {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} {n : ℕ} (i : Fin n) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.wSmall1Pair h M ℓ d q.1.1 (q.1.2 i) q.2)
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
  have hg0 : AEMeasurable (Submission.BoseGases.g0 v h) (MeasureTheory.volume : Measure E3) :=
    (Classical.choose_spec h).2.rhs_integrable.aestronglyMeasurable.aemeasurable
  have hsub : Continuous (fun q : (E3 × Submission.BoseGases.X n) × E3 => q.1.2 i - q.2) := by
    fun_prop
  have hnum : MeasureTheory.AEStronglyMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.g0 v h (q.1.2 i - q.2))
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    Work.UBBInputs2.aemeasurable_comp_sub_coord (N := n) hg0 i ℓ
  have hcsC : Continuous (fun x : E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) x) :=
    (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)
  have hden1 : MeasureTheory.AEStronglyMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.convScaleSmall M (ℓ * d) (q.1.2 i - q.2))
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    (hcsC.comp hsub).aestronglyMeasurable
  have hden2 : MeasureTheory.AEStronglyMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.convScale ℓ (q.1.2 i - q.2))
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    ((Submission.BoseGases.convScale_continuous ℓ).comp hsub).aestronglyMeasurable
  have hchi1 : AEMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiScale ℓ (q.1.2 i) *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (q.1.2 i) - q.1.1))
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    ((((Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop)).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))).aestronglyMeasurable).aemeasurable
  have hchi2 : AEMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiScale ℓ q.2 *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.2 - q.1.1))
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    ((((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))).aestronglyMeasurable).aemeasurable
  have hmid : AEMeasurable
      (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.g0 v h (q.1.2 i - q.2)
          / Submission.BoseGases.convScaleSmall M (ℓ * d) (q.1.2 i - q.2)
          / Submission.BoseGases.convScale ℓ (q.1.2 i - q.2))
      (((MeasureTheory.volume : Measure E3).prod
          (MeasureTheory.volume : Measure (Submission.BoseGases.X n))).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    (hnum.aemeasurable.div hden1.aemeasurable).div hden2.aemeasurable
  refine (((hchi1.mul hmid).mul hchi2).aestronglyMeasurable).congr ?_
  filter_upwards with q
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
    Submission.BoseGases.wSmallScaled, Submission.BoseGases.chiSmallB, Pi.mul_apply]

/-- Joint integrability of the `(u,x)`-integrand of the sliding fibre sum
`Work.BoseFixB1.fibSum h M ℓ d u Φ = ∫ x in abox n ℓ, Φ x ^ 2 * ∑ i, ∫ y in acube ℓ,
wSmall1Pair h M ℓ d u (x i) y` over `(volume.restrict s).prod (volume.restrict (abox n ℓ))`.
The integrand vanishes off the fixed cube `K := acube ((1+d)/d)` in `u`
(`Work.BoseB1Cube.wSmall1Pair_eq_zero_of_notMem_acube`), and on `K` it is bounded by
`‖Φ‖_∞² · n · C₀` with `C₀ := chiSupAbs * chiSmallDecay M * (2 * (chiSupAbs * chiSmallDecay M)
/ smallConvLower M * (8 * π * a v))` the uniform fibre bound of
`Work.BoseFixB1.wSmall1Pair_fibre_abs_le`; use the indicator dominator on `K ×ˢ univ`
(finite product measure) with `Integrable.mono'`, and `aestronglyMeasurable_int_y_uz` for the
a.e. strong measurability of `(u,z) ↦ ∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y`. -/
theorem integrable_fibSumIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ)
    (s : Set (EuclideanSpace ℝ (Fin 3))) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Φ p.2 ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict s).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) := by
  classical
  -- ## 1. a.e. strong measurability of the integrand
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × Submission.BoseGases.X n =>
        Φ p.2 ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y)
      (((MeasureTheory.volume : Measure E3).restrict s).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
    have hAB : ((MeasureTheory.volume : Measure E3).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        ≤ ((MeasureTheory.volume : Measure E3).prod
            (MeasureTheory.volume : Measure (Submission.BoseGases.X n))) :=
      Measure.prod_mono le_rfl Measure.restrict_le_self
    have hfib : ∀ i : Fin n, MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × Submission.BoseGases.X n => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y)
        ((MeasureTheory.volume : Measure E3).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) := by
      intro i
      have hker : MeasureTheory.AEStronglyMeasurable
          (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
            Submission.BoseGases.wSmall1Pair h M ℓ d q.1.1 (q.1.2 i) q.2)
          (((MeasureTheory.volume : Measure E3).prod
              ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ))).prod
            ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
        (aesm_wSmall1Pair_slot (v := v) h (M := M) hM (ℓ := ℓ) (d := d) (n := n) i).mono_measure
          (Measure.prod_mono hAB le_rfl)
      exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (ν := (MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hker
    have hsum : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × Submission.BoseGases.X n =>
          ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y)
        ((MeasureTheory.volume : Measure E3).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) :=
      (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hfib i)).congr
        (Filter.Eventually.of_forall (fun p => by simp only [Finset.sum_apply]))
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × Submission.BoseGases.X n =>
          Φ p.2 ^ 2 * ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y)
        ((MeasureTheory.volume : Measure E3).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) :=
      (((hΦ.measurable.pow_const 2).comp measurable_snd).aestronglyMeasurable).mul hsum
    exact h3.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  -- ## 2. the uniform fibre bound, the dominating function and its integrability
  set C₀ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
      (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        / Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * _root_.BoseGases.a v)) with hCdef
  have hfib_le : ∀ u z : E3,
      |∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y|
        ≤ |C₀| := by
    intro u z
    exact le_trans (Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R) hv_supp hR hv
      hvrad h (M := M) hM (ℓ := ℓ) (d := d) hℓ hd hRd hRχ u z) (le_abs_self C₀)
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦ.continuousOn
  set A : ℝ := CΦ ^ 2 * ((n : ℝ) * |C₀|) with hAdef
  set K : Set E3 := Submission.BoseGases.acube ((1 + d) / d) with hKdef
  have hKmeas : MeasurableSet K := Submission.BoseGases.acube_measurable ((1 + d) / d)
  have hfinK : ((MeasureTheory.volume : Measure E3).restrict s) K ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (Measure.restrict_le_self (s := s) K) ?_)
    exact Submission.BoseGases.acube_lt_top ((1 + d) / d) (by positivity)
  have hfinBox : ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact ne_of_lt (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
  have hfin_prod : (((MeasureTheory.volume : Measure E3).restrict s).prod
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))) (K ×ˢ Set.univ) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hfinK hfinBox
  have hdom : MeasureTheory.Integrable
      (fun p : E3 × Submission.BoseGases.X n => A * (K.indicator (fun _ => (1 : ℝ))) p.1)
      (((MeasureTheory.volume : Measure E3).restrict s).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
    have hrewrite : (fun p : E3 × Submission.BoseGases.X n =>
          A * (K.indicator (fun _ => (1 : ℝ))) p.1)
        = fun p : E3 × Submission.BoseGases.X n =>
          A * ((K ×ˢ Set.univ).indicator (fun _ => (1 : ℝ)) p) := by
      funext p
      by_cases hp : p.1 ∈ K
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ K ×ˢ Set.univ from ⟨hp, Set.mem_univ _⟩)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ K ×ˢ Set.univ from fun hc => hp hc.1)]
    rw [hrewrite]
    refine MeasureTheory.Integrable.const_mul ?_ A
    rw [MeasureTheory.integrable_indicator_iff (hKmeas.prod MeasurableSet.univ)]
    exact MeasureTheory.integrableOn_const hfin_prod
  -- ## 3. dominance of the integrand by the indicator function
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  have hmem : ∀ᵐ p ∂(((MeasureTheory.volume : Measure E3).restrict s).prod
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))), p.2 ∈ Submission.BoseGases.abox n ℓ := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      ((Submission.BoseGases.abox_measurable n ℓ).preimage measurable_snd)]
    exact Filter.Eventually.of_forall
      (fun _ => MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ))
  filter_upwards [hmem] with p hp
  have hΦb : |Φ p.2| ≤ CΦ := by
    have h := hCΦ p.2 hp
    rwa [Real.norm_eq_abs] at h
  by_cases hu : p.1 ∈ K
  · rw [Set.indicator_of_mem hu, mul_one]
    have hΦ2 : Φ p.2 ^ 2 ≤ CΦ ^ 2 := by
      rw [← sq_abs (Φ p.2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hΦb 2
    have hsum_le : |∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y| ≤ (n : ℝ) * |C₀| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h := Finset.sum_le_card_nsmul Finset.univ
        (fun i : Fin n => |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y|) |C₀|
        (fun i _ => hfib_le p.1 (p.2 i))
      simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ p.2))]
    calc Φ p.2 ^ 2 * |∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y|
        ≤ CΦ ^ 2 * ((n : ℝ) * |C₀|) := mul_le_mul hΦ2 hsum_le (abs_nonneg _) (sq_nonneg CΦ)
      _ = A := by rw [hAdef]
  · rw [Set.indicator_of_notMem hu, mul_zero]
    have hzero : ∀ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 (p.2 i) y) = 0 := by
      intro i
      rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun y => wSmall1Pair_eq_zero_of_notMem_acube h hM hℓ hd hu (p.2 i) y)), integral_zero]
    rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const_zero, mul_zero, Real.norm_eq_abs,
      abs_zero]

end

end Work.BoseB1Cube
