import Mathlib
import Submission.Work.HP.JcVolDefs

/-!
# The model integral `∫_{ℝ²} m0 d = 4d/(d+2)`

`m0 d u = if qbar u ≤ 1 then 1 - (√(qbar u))^d else 0`, where `qbar u = max ((u 0)^2) ((u 1)^2)`.
Since `√(qbar u) = max |u 0| |u 1|`, the integrand is the function `1 - max(|x|,|y|)^d` on the
unit square `[-1,1]²` (and `0` outside), so the integral is
`4 - ∫_{[-1,1]²} max(|x|,|y|)^d = 4 - 8/(d+2) = 4d/(d+2)`.

The second integral is computed with the layer-cake formula

`∫⁻ ω, ofReal (G (f ω)) ∂μ = ∫⁻ t in Ioi 0, μ {a | t ≤ f a} * ofReal (G' t)`

(`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`) applied to `f = max(|·|,|·|)` and
`G t = t^d` (so `G' t = d t^{d-1}`); the level sets of `f` inside the square are
`[-1,1]² \ (-t,t)²`, of measure `4 - 4t²`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Work.HP

/-! ## Helper definitions -/

/-- The `L^∞` coordinate `max |x| |y|` on the plane `ℝ × ℝ`. -/
def imRmax (p : ℝ × ℝ) : ℝ := max |p.1| |p.2|

/-- The unit square `[-1,1] × [-1,1]` in the plane. -/
def imSq : Set (ℝ × ℝ) := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1

/-- The model integrand `m0` transported to the plane `ℝ × ℝ`. -/
def imG (d : ℕ) (p : ℝ × ℝ) : ℝ := if imRmax p ≤ 1 then 1 - imRmax p ^ d else 0

/-- The model integrand on `Fin 2 → ℝ` (the same expression in the coordinates). -/
def imG1 (d : ℕ) (x : Fin 2 → ℝ) : ℝ := imG d (x 0, x 1)

/-! ## Elementary facts -/

lemma imRmax_continuous : Continuous imRmax := by unfold imRmax; fun_prop

lemma imRmax_nonneg (p : ℝ × ℝ) : 0 ≤ imRmax p :=
  le_trans (abs_nonneg _) (le_max_left _ _)

lemma imRmax_lt_iff (t : ℝ) (p : ℝ × ℝ) :
    imRmax p < t ↔ p ∈ Set.Ioo (-t) t ×ˢ Set.Ioo (-t) t := by
  rw [imRmax, max_lt_iff, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo, abs_lt, abs_lt]

lemma imSq_eq : {p : ℝ × ℝ | imRmax p ≤ 1} = imSq := by
  ext p
  rw [imSq, Set.mem_prod, Set.mem_Icc, Set.mem_Icc, Set.mem_ofPred_eq, imRmax, max_le_iff,
    abs_le, abs_le]

lemma imSq_measurableSet : MeasurableSet imSq := by
  rw [← imSq_eq]
  exact (isClosed_le imRmax_continuous continuous_const).measurableSet

lemma imSq_volume : (volume : Measure (ℝ × ℝ)) imSq = 4 := by
  have h2 : (volume : Measure ℝ) (Set.Icc (-1:ℝ) 1) = 2 := by
    rw [Real.volume_Icc]; norm_num
  rw [imSq, Measure.volume_eq_prod, Measure.prod_prod, h2]
  norm_num

/-! ## The measure of the level sets of `imRmax` in the square -/

lemma imLevelMeasure (t : ℝ) (ht : 0 < t) :
    (volume.restrict imSq) {p : ℝ × ℝ | t ≤ imRmax p} = ENNReal.ofReal (4 - 4 * t^2) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | t ≤ imRmax p} :=
    (isClosed_le continuous_const imRmax_continuous).measurableSet
  rw [Measure.restrict_apply hmeas]
  have hset : {p : ℝ × ℝ | t ≤ imRmax p} ∩ imSq
      = imSq \ (Set.Ioo (-t) t ×ˢ Set.Ioo (-t) t) := by
    ext p
    have hlt := imRmax_lt_iff t p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun hc => absurd (hlt.mpr hc) (not_lt.mpr h1)⟩
    · rintro ⟨h2, h3⟩
      exact ⟨le_of_not_gt fun hc => h3 (hlt.mp hc), h2⟩
  rw [hset]
  have hB : (volume : Measure (ℝ × ℝ)) (Set.Ioo (-t) t ×ˢ Set.Ioo (-t) t)
      = ENNReal.ofReal (4 * t^2) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo,
      show t - -t = 2 * t from by ring]
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * t)]
    congr 1
    ring
  by_cases ht1 : t ≤ 1
  · have hsub : Set.Ioo (-t) t ×ˢ Set.Ioo (-t) t ⊆ imSq := by
      rintro p ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_Ioo] at h1 h2
      simp only [imSq, Set.mem_prod, Set.mem_Icc]
      exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
    have hfin : (volume : Measure (ℝ × ℝ))
        (Set.Ioo (-t) t ×ˢ Set.Ioo (-t) t) ≠ ∞ := by rw [hB]; exact ENNReal.ofReal_ne_top
    rw [MeasureTheory.measure_sdiff hsub
        (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet hfin,
      imSq_volume, hB, ENNReal.ofReal_sub _ (by positivity)]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num]
  · have ht1' : 1 < t := not_le.mp ht1
    have hempty : imSq \ (Set.Ioo (-t) t ×ˢ Set.Ioo (-t) t) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro p ⟨h2, h3⟩
      have h4 : imRmax p ≤ 1 := by rw [← imSq_eq] at h2; exact h2
      exact h3 ((imRmax_lt_iff t p).mp (lt_of_le_of_lt h4 ht1'))
    rw [hempty, measure_empty, ENNReal.ofReal_eq_zero.mpr]
    nlinarith

/-! ## Transfer to the plane -/

lemma imSqrtMaxSq (a b : ℝ) : Real.sqrt (max (a^2) (b^2)) = max |a| |b| := by
  rw [← sq_abs a, ← sq_abs b]
  have h : max (|a|^2) (|b|^2) = (max |a| |b|)^2 := by
    rcases le_total |a| |b| with hle | hle
    · rw [max_eq_right hle, max_eq_right (by nlinarith [abs_nonneg a, abs_nonneg b, hle])]
    · rw [max_eq_left hle, max_eq_left (by nlinarith [abs_nonneg a, abs_nonneg b, hle])]
  rw [h, Real.sqrt_sq]
  positivity

lemma imMaxAbsLeOne (a b : ℝ) : max |a| |b| ≤ 1 ↔ max (a^2) (b^2) ≤ 1 := by
  rw [max_le_iff, max_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith [abs_nonneg a, h1, sq_abs a],
      by nlinarith [abs_nonneg b, h2, sq_abs b]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by nlinarith [abs_nonneg a, sq_abs a, h1], by nlinarith [abs_nonneg b, sq_abs b, h2]⟩

lemma imM0Eq (d : ℕ) (u : EuclideanSpace ℝ (Fin 2)) : m0 d u = imG1 d (WithLp.ofLp u) := by
  have hc : qbar u ≤ 1 ↔ max |u 0| |u 1| ≤ 1 := (imMaxAbsLeOne (u 0) (u 1)).symm
  have hs : Real.sqrt (qbar u) = max |u 0| |u 1| := by
    rw [qbar]; exact imSqrtMaxSq (u 0) (u 1)
  rw [m0, imG1, imG, imRmax]
  by_cases h : qbar u ≤ 1
  · rw [ite_eq_left h, ite_eq_left (hc.mp h), hs]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hc.mpr h'))]

lemma imG1_eq (d : ℕ) (x : Fin 2 → ℝ) :
    imG1 d x = imG d (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) x) := by
  have hp : MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) x = (x 0, x 1) := rfl
  rw [imG1, hp]

lemma imTransfer (d : ℕ) :
    ∫ u : EuclideanSpace ℝ (Fin 2), m0 d u = ∫ p : ℝ × ℝ, imG d p := by
  have h2 : ∫ x : Fin 2 → ℝ, imG1 d x = ∫ p : ℝ × ℝ, imG d p := by
    rw [← (MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).integral_comp'
          (g := imG d)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (imG1_eq d x).symm)
  calc ∫ u : EuclideanSpace ℝ (Fin 2), m0 d u
      = ∫ u : EuclideanSpace ℝ (Fin 2), imG1 d (WithLp.ofLp u) :=
        integral_congr_ae (Filter.Eventually.of_forall fun u => imM0Eq d u)
    _ = ∫ x : Fin 2 → ℝ, imG1 d x :=
        (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
          (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding (g := imG1 d)
    _ = ∫ p : ℝ × ℝ, imG d p := h2

/-! ## The one-dimensional integral -/

lemma imIntegralPowPred (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    ∫ t in (0:ℝ)..x, (d:ℝ) * t^(d-1) = x ^ d := by
  rw [intervalIntegral.integral_const_mul, integral_pow (d-1)]
  have hexp : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hcast : (((d - 1 : ℕ) : ℝ) + 1) = (d:ℝ) := by
    rw [Nat.cast_pred (by omega : 0 < d)]; ring
  rw [hexp, hcast, zero_pow (by omega : d ≠ 0), sub_zero]
  have hd0 : (d:ℝ) ≠ 0 := by positivity
  field_simp

lemma imOneD (d : ℕ) (hd : 1 ≤ d) :
    ∫ t in (0:ℝ)..1, (4 - 4 * t^2) * ((d:ℝ) * t^(d-1)) = 8 / ((d:ℝ) + 2) := by
  have hdecomp : ∀ t : ℝ, (4 - 4 * t^2) * ((d:ℝ) * t^(d-1))
      = (4 * (d:ℝ)) * t^(d-1) - (4 * (d:ℝ)) * t^(d+1) := by
    intro t
    have h1 : t ^ (d + 1) = t ^ (d - 1) * t ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [h1]; ring
  simp_rw [hdecomp]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow (d-1), integral_pow (d+1)]
    have hexp : d - 1 + 1 = d := Nat.sub_add_cancel hd
    have hexp2 : d + 1 + 1 = d + 2 := by omega
    have hcast : (((d - 1 : ℕ) : ℝ) + 1) = (d:ℝ) := by
      rw [Nat.cast_pred (by omega : 0 < d)]; ring
    have hcast2 : (((d + 1 : ℕ) : ℝ) + 1) = ((d:ℝ) + 2) := by push_cast; ring
    rw [hexp, hexp2, hcast, hcast2, one_pow, one_pow,
      zero_pow (by omega : d ≠ 0), zero_pow (by omega : d + 2 ≠ 0), sub_zero]
    have hd2 : (d:ℝ) + 2 ≠ 0 := by positivity
    have hd0 : (d:ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _

/-! ## The one-dimensional `lintegral` -/

lemma imLintegralOneD (d : ℕ) (hd : 1 ≤ d) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal ((4 - 4 * t^2) * ((d:ℝ) * t^(d-1)))
      = ENNReal.ofReal (8 / ((d:ℝ) + 2)) := by
  set H : ℝ → ℝ := fun t => (4 - 4 * t^2) * ((d:ℝ) * t^(d-1)) with hH
  have hcont : Continuous H := by rw [hH]; fun_prop
  have hnonneg : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ H t := by
    intro t ht ht1
    rw [hH]
    refine mul_nonneg (by nlinarith [ht, ht1, sq_nonneg t]) ?_
    exact mul_nonneg (Nat.cast_nonneg d) (pow_nonneg ht.le _)
  have hsplit : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (H t)
      = ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (H t) := by
    have hset : Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr (not_le.mp h1)
      · rintro (⟨h, _⟩ | h)
        · exact h
        · linarith
    have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi 1) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      simp only [Set.mem_Ioc] at ht1
      simp only [Set.mem_Ioi] at ht2
      linarith
    have hzero : ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (H t) = 0 := by
      have hneg : ∀ t ∈ Set.Ioi (1:ℝ), ENNReal.ofReal (H t) = (0 : ℝ≥0∞) := by
        intro t ht
        have ht1 : 1 < t := ht
        have hsq : 1 < t ^ 2 := by nlinarith [ht1, sq_nonneg (t - 1)]
        have h4 : 4 - 4 * t ^ 2 < 0 := by nlinarith [hsq]
        have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hpos : 0 < (d:ℝ) * t ^ (d - 1) :=
          mul_pos hdpos (pow_pos (by linarith : (0:ℝ) < t) _)
        rw [ENNReal.ofReal_eq_zero]
        exact (mul_neg_of_neg_of_pos h4 hpos).le
      rw [show (∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (H t))
          = ∫⁻ t in Set.Ioi (1:ℝ), (0 : ℝ≥0∞) from
        setLIntegral_congr_fun measurableSet_Ioi hneg]
      simp
    rw [hset, lintegral_union measurableSet_Ioi hdisj, hzero, add_zero]
  rw [hsplit]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hcont.intervalIntegrable 0 1))
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun t ht => by
        simp only [Set.mem_Ioc] at ht
        exact hnonneg t ht.1 ht.2)))]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact imOneD d hd

/-! ## Integrability and the layer-cake computation -/

lemma imIntegrableOn (d : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => imRmax p ^ d) imSq volume := by
  refine IntegrableOn.of_bound (by rw [imSq_volume]; norm_num)
    (imRmax_continuous.pow d).aestronglyMeasurable 1 ?_
  rw [ae_restrict_iff' imSq_measurableSet]
  refine Filter.Eventually.of_forall fun p hp => ?_
  have h1 : imRmax p ≤ 1 := by rw [← imSq_eq] at hp; exact hp
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (imRmax_nonneg p) d)]
  exact pow_le_one₀ (imRmax_nonneg p) h1

lemma imLayerCake (d : ℕ) (hd : 1 ≤ d) :
    ∫ p in imSq, imRmax p ^ d ∂volume = 8 / ((d:ℝ) + 2) := by
  have hnn : 0 ≤ᵐ[volume.restrict imSq] imRmax :=
    Filter.Eventually.of_forall fun p => imRmax_nonneg p
  have hgint : ∀ t > 0, IntervalIntegrable (fun t : ℝ => (d:ℝ) * t^(d-1)) volume 0 t :=
    fun t _ => (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
  have hgnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), 0 ≤ (d:ℝ) * t^(d-1) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht =>
        mul_nonneg (Nat.cast_nonneg d) (pow_nonneg ht.le _))
  have key := lintegral_comp_eq_lintegral_meas_le_mul (μ := volume.restrict imSq)
    (f := imRmax) (g := fun t : ℝ => (d:ℝ) * t^(d-1)) hnn
    imRmax_continuous.aemeasurable hgint hgnn
  have hL : (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..imRmax ω, (d:ℝ) * t^(d-1))
        ∂(volume.restrict imSq))
      = (∫⁻ p in imSq, ENNReal.ofReal (imRmax p ^ d)) := by
    rw [show (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..imRmax ω, (d:ℝ) * t^(d-1))
          ∂(volume.restrict imSq))
        = ∫⁻ ω, ENNReal.ofReal (imRmax ω ^ d) ∂(volume.restrict imSq) from
      lintegral_congr fun ω => by rw [imIntegralPowPred d hd]]
  have hR : (∫⁻ t in Set.Ioi 0,
        (volume.restrict imSq) {a | t ≤ imRmax a} * ENNReal.ofReal ((d:ℝ) * t^(d-1)))
      = ENNReal.ofReal (8 / ((d:ℝ) + 2)) := by
    rw [show (∫⁻ t in Set.Ioi 0,
          (volume.restrict imSq) {a | t ≤ imRmax a} * ENNReal.ofReal ((d:ℝ) * t^(d-1)))
        = ∫⁻ t in Set.Ioi 0,
            ENNReal.ofReal ((4 - 4 * t^2) * ((d:ℝ) * t^(d-1))) from
      setLIntegral_congr_fun measurableSet_Ioi (fun t ht => by
        rw [imLevelMeasure t ht,
          ENNReal.ofReal_mul' (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg ht.le _))])]
    exact imLintegralOneD d hd
  have hlin : (∫⁻ p in imSq, ENNReal.ofReal (imRmax p ^ d)) = ENNReal.ofReal (8 / ((d:ℝ) + 2)) :=
    hL.symm.trans (key.trans hR)
  have hfin : ∫ p in imSq, imRmax p ^ d ∂volume
      = (∫⁻ p in imSq, ENNReal.ofReal (imRmax p ^ d)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => pow_nonneg (imRmax_nonneg p) d)
      (imRmax_continuous.pow d).aestronglyMeasurable
  rw [hfin, hlin, ENNReal.toReal_ofReal (by positivity)]

/-! ## The main theorem -/

lemma imG_eq_indicator (d : ℕ) :
    imG d = imSq.indicator (fun p : ℝ × ℝ => 1 - imRmax p ^ d) := by
  classical
  funext p
  rw [imG, Set.indicator_apply]
  by_cases hp : imRmax p ≤ 1
  · have hp' : p ∈ imSq := by rw [← imSq_eq]; exact hp
    rw [ite_eq_left hp, ite_eq_left hp']
  · have hp' : p ∉ imSq := by rw [← imSq_eq]; exact hp
    rw [ite_eq_right hp, ite_eq_right hp']

lemma imIntegrableOn_one : IntegrableOn (fun _ : ℝ × ℝ => (1:ℝ)) imSq volume :=
  IntegrableOn.of_bound (by rw [imSq_volume]; norm_num)
    aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun _ => by simp)

lemma imG_integral (d : ℕ) (hd : 1 ≤ d) :
    ∫ p : ℝ × ℝ, imG d p = 4 * (d:ℝ) / ((d:ℝ) + 2) := by
  rw [imG_eq_indicator d, MeasureTheory.integral_indicator imSq_measurableSet,
    MeasureTheory.integral_sub imIntegrableOn_one (imIntegrableOn d),
    MeasureTheory.setIntegral_const, imLayerCake d hd]
  simp only [Measure.real, smul_eq_mul, mul_one]
  rw [show ((volume : Measure (ℝ × ℝ)) imSq).toReal = 4 from by rw [imSq_volume]; norm_num]
  have hd2 : (d:ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem IntegralModel (d : ℕ) : ∫ u : EuclideanSpace ℝ (Fin 2), m0 d u = 4 * (d:ℝ) / ((d:ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [m0]
  · rw [imTransfer d]
    exact imG_integral d hd

end Work.HP
