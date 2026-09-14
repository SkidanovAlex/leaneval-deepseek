import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.GaussianMeasure.gaussian_tail_upper
import Submission.Commons.Analysis.GaussianMeasure.gaussian_tail_lower
import Submission.Commons.Analysis.GaussianMeasure.gaussian_total_mass_one
import Submission.Commons.Analysis.GaussianMeasure.gauss_cdf_tail_split
import Submission.Commons.Analysis.GaussianMeasure.gaussian_cdf_strictMono

open MeasureTheory Set Filter
open scoped Real BigOperators ENNReal

namespace Commons.Analysis.GaussianMeasure

noncomputable section


private lemma nrm_sq {n : ℕ} (v : Fin n → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, (v i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · congr 1; funext i; rw [Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

private lemma exp_prod {n : ℕ} (v : Fin n → ℝ) :
    Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = ∏ i, Real.exp (-Real.pi * (v i) ^ 2) := by
  rw [nrm_sq, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

private lemma coord_tail {n : ℕ} (i : Fin n) (R : ℝ) :
    (∫ v : (Fin n → ℝ), (if R < v i then 1 else 0) *
        Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) := by
  have hprod : ∀ v : (Fin n → ℝ),
      (if R < v i then 1 else 0) * Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = ∏ j : Fin n, ((if j = i then (if R < v j then 1 else 0) else 1) * Real.exp (-Real.pi * (v j) ^ 2)) := by
    intro v
    rw [exp_prod v, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => (if R < v j then 1 else 0))]
    simp
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod (E := fun _ : Fin n => ℝ)
      (f := fun j t => (if j = i then (if R < t then 1 else 0) else 1) * Real.exp (-Real.pi * t ^ 2))]
  rw [Finset.prod_eq_single i]
  · have : (∫ t : ℝ, (if i = i then (if R < t then 1 else 0) else 1) * Real.exp (-Real.pi * t ^ 2))
        = ∫ t : ℝ, (if R < t then 1 else 0) * Real.exp (-Real.pi * t ^ 2) := by
      apply integral_congr_ae; filter_upwards with t; simp
    rw [this]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    rw [Set.indicator_apply]
    by_cases h : R < t <;> simp [h]
  · intro j _ hji
    have : (∫ t : ℝ, (if j = i then (if R < t then 1 else 0) else 1) * Real.exp (-Real.pi * t ^ 2))
        = ∫ t : ℝ, Real.exp (-Real.pi * t ^ 2) := by
      apply integral_congr_ae; filter_upwards with t; simp [hji]
    rw [this, integral_gaussian]
    rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma coord_tail_set {n : ℕ} (i : Fin n) (R : ℝ) :
    (∫ v in {v : (Fin n → ℝ) | R < v i},
        Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = ∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2) := by
  rw [← coord_tail i R]
  rw [← integral_indicator]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : R < v i <;> simp [h]
  · exact measurableSet_lt measurable_const (measurable_pi_apply i)

private lemma integrable_gaussian (n : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
  have hc : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Complex.exp (-(Real.pi : ℂ) * (‖y‖ ^ 2 : ℝ))) := by
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin n))
      (b := (Real.pi : ℂ)) (c := 0) (w := 0)
      (by simp [Complex.ofReal_re]; exact Real.pi_pos)
    simpa using h
  have hr := hc.re
  refine hr.congr ?_
  filter_upwards with y
  rw [show RCLike.re (Complex.exp (-(Real.pi : ℂ) * (‖y‖ ^ 2 : ℝ)))
        = Complex.re (Complex.exp (-(Real.pi : ℂ) * (‖y‖ ^ 2 : ℝ))) by
      rw [RCLike.re_eq_complex_re]]
  rw [Complex.exp_re]
  rw [show (-(Real.pi : ℂ) * (‖y‖ ^ 2 : ℝ)) = (((-Real.pi * ‖y‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.ofReal_im, Complex.ofReal_re]
  simp

private lemma integrable_gaussian_fin (n : ℕ) :
    Integrable (fun v : (Fin n → ℝ) =>
      Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
  have h := ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
      (g := fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖y‖ ^ 2)))
  simpa only [Function.comp_def] using h.mpr (integrable_gaussian n)

private lemma setIntegral_toLp {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ y in s, g y)
      = ∫ v in (fun v : Fin n → ℝ => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))) ⁻¹' s,
          g (WithLp.toLp 2 v) :=
  ((PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding g s).symm

-- E: ball split
private theorem gaussian_ball_split (n : ℕ) (R : ℝ) :
    (∫ y in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R}, Real.exp (-Real.pi * ‖y‖ ^ 2))
      + (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2)) = 1 := by
  have hInt := integrable_gaussian n
  have htot : (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-Real.pi * ‖y‖ ^ 2)) = 1 :=
    Commons.Analysis.GaussianMeasure.gaussian_total_mass_one (EuclideanSpace ℝ (Fin n))
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R} :=
    measurableSet_le measurable_norm measurable_const
  have hcompl := MeasureTheory.setIntegral_compl
    (s := {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R}) hmeas hInt
  have hset : ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R})ᶜ = {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖} := by
    ext y; simp [not_le]
  rw [hset] at hcompl
  rw [hcompl, htot]
  ring

-- C: slice lower bound
private theorem gaussian_ball_tail_ge_one_dim (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (_hR : 0 ≤ R) :
    (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) ≤
      ∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2) := by
  have hin : 0 < n := hn
  let i : Fin n := ⟨0, hin⟩
  have htr : (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2))
      = ∫ v in {v : Fin n → ℝ | R < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖},
          Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    rw [setIntegral_toLp (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖y‖ ^ 2))
      {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}]
    rfl
  rw [htr, ← coord_tail_set (n := n) i R]
  refine setIntegral_mono_set ?_ ?_ ?_
  · exact (integrable_gaussian_fin n).integrableOn
  · exact Filter.Eventually.of_forall (fun v => Real.exp_nonneg _)
  · refine Filter.Eventually.of_forall (fun v hv => ?_)
    have hv' : R < v i := hv
    have h1 : v i ≤ |v i| := le_abs_self _
    have h2 : |v i| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
      have := PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) i
      simpa using this
    show R < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖
    linarith


-- 1D: ∫_{|t|>R} exp(-πt²) = 2 ∫_{t>R} exp(-πt²)
private lemma abs_tail_eq (R : ℝ) (hR : 0 ≤ R) :
    (∫ t : ℝ, (if R < |t| then 1 else 0) * Real.exp (-Real.pi * t ^ 2))
      = 2 * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) := by
  have hmeas : MeasurableSet {t : ℝ | R < |t|} :=
    measurableSet_lt measurable_const measurable_abs
  have hf_int : Integrable (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) :=
    integrable_exp_neg_mul_sq Real.pi_pos
  have h1 : (∫ t : ℝ, (if R < |t| then 1 else 0) * Real.exp (-Real.pi * t ^ 2))
      = ∫ t in {t : ℝ | R < |t|}, Real.exp (-Real.pi * t ^ 2) := by
    rw [← integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : R < |t| <;> simp [h]
  rw [h1]
  have hset : {t : ℝ | R < |t|} = Set.Ioi R ∪ Set.Iio (-R) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro h
      by_cases ht : 0 ≤ t
      · left; rwa [abs_of_nonneg ht] at h
      · right; rw [abs_of_neg (lt_of_not_ge ht)] at h; linarith
    · rintro (h | h)
      · rw [abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR h))]; exact h
      · rw [abs_of_neg (lt_of_lt_of_le h (by linarith))]; linarith
  rw [hset]
  have hdisj : Disjoint (Set.Ioi R) (Set.Iio (-R)) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    simp only [Set.mem_Ioi] at ht1
    simp only [Set.mem_Iio] at ht2
    linarith
  rw [setIntegral_union hdisj measurableSet_Iio hf_int.integrableOn hf_int.integrableOn]
  have hneg : (∫ t in Set.Iio (-R), Real.exp (-Real.pi * t ^ 2))
      = ∫ t in Set.Ioi R, Real.exp (-Real.pi * t ^ 2) := by
    rw [← MeasureTheory.integral_Iic_eq_integral_Iio (x := -R)
      (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2))]
    rw [← integral_comp_neg_Ioi (c := R)
      (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [hneg]
  ring

-- Fubini: ∫_{v : R < |v i|} g = ∫_t (if R<|t| then 1 else 0) e^{-πt²}
private lemma coord_abs_tail {n : ℕ} (i : Fin n) (R : ℝ) :
    (∫ v in {v : Fin n → ℝ | R < |v i|},
        Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = ∫ t : ℝ, (if R < |t| then 1 else 0) * Real.exp (-Real.pi * t ^ 2) := by
  have hmeas : MeasurableSet {v : Fin n → ℝ | R < |v i|} :=
    measurableSet_lt measurable_const (measurable_pi_apply i).abs
  have h1 : (∫ v in {v : Fin n → ℝ | R < |v i|},
        Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = ∫ v : (Fin n → ℝ), (if R < |v i| then 1 else 0) *
          Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    rw [← integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with v
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : R < |v i| <;> simp [h]
  rw [h1]
  have hprod : ∀ v : (Fin n → ℝ),
      (if R < |v i| then 1 else 0) * Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = ∏ j : Fin n, ((if j = i then (if R < |v j| then 1 else 0) else 1) * Real.exp (-Real.pi * (v j) ^ 2)) := by
    intro v
    rw [exp_prod v, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => (if R < |v j| then 1 else 0))]
    simp
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod (E := fun _ : Fin n => ℝ)
      (f := fun j t => (if j = i then (if R < |t| then 1 else 0) else 1) * Real.exp (-Real.pi * t ^ 2))]
  rw [Finset.prod_eq_single i]
  · have : (∫ t : ℝ, (if i = i then (if R < |t| then 1 else 0) else 1) * Real.exp (-Real.pi * t ^ 2))
        = ∫ t : ℝ, (if R < |t| then 1 else 0) * Real.exp (-Real.pi * t ^ 2) := by
      apply integral_congr_ae; filter_upwards with t; simp
    rw [this]
  · intro j _ hji
    have : (∫ t : ℝ, (if j = i then (if R < |t| then 1 else 0) else 1) * Real.exp (-Real.pi * t ^ 2))
        = ∫ t : ℝ, Real.exp (-Real.pi * t ^ 2) := by
      apply integral_congr_ae; filter_upwards with t; simp [hji]
    rw [this, integral_gaussian]
    rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one]
  · intro h; exact absurd (Finset.mem_univ i) h

-- volume of the box
private lemma volumeReal_box {n : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure (Fin n → ℝ)).real
      (Set.Icc (fun _ : Fin n => -R) (fun _ => R)) = (2 * R) ^ n := by
  have hab : (fun _ : Fin n => -R) ≤ (fun _ => R) := fun i => by
    show -R ≤ R; linarith
  rw [MeasureTheory.measureReal_def, Real.volume_Icc_pi_toReal hab]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  ring

-- D: n-dimensional tail upper bound
private theorem gaussian_ball_tail_upper_aux (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2))
      ≤ 2 * n * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2))
        + (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2) := by
  have htr := setIntegral_toLp (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖y‖ ^ 2))
      {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}
  rw [htr]
  rw [show (fun v : Fin n → ℝ => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))) ⁻¹'
        {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}
      = {v : Fin n → ℝ | R < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖} from by
    ext v; exact Set.mem_preimage]
  set T : Set (Fin n → ℝ) := {v : Fin n → ℝ | R < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖} with hT
  set Bad : Set (Fin n → ℝ) := {v : Fin n → ℝ | ∃ i, R < |v i|} with hBad
  set Box : Set (Fin n → ℝ) := Set.Icc (fun _ : Fin n => -R) (fun _ => R) with hBox
  set g : (Fin n → ℝ) → ℝ := fun v => Real.exp (-Real.pi * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2) with hg
  change (∫ v in T, g v) ≤ 2 * n * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) + (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2)
  have hgint : Integrable g := by rw [hg]; exact integrable_gaussian_fin n
  have hTmeas : MeasurableSet T := by
    rw [hT]
    exact measurableSet_lt measurable_const (by fun_prop)
  have hBad_eq : Bad = ⋃ i : Fin n, ({v : Fin n → ℝ | R < |v i|}) := by
    rw [hBad]; ext v; simp [Set.mem_iUnion]
  have hBadmeas : MeasurableSet Bad := by
    rw [hBad_eq]
    exact MeasurableSet.iUnion (fun i : Fin n => measurableSet_lt measurable_const (measurable_pi_apply i).abs)
  have hBoxmeas : MeasurableSet Box := by rw [hBox]; exact measurableSet_Icc
  have hcover : T ⊆ Bad ∪ Box := by
    intro v hv
    by_cases hb : v ∈ Bad
    · exact Or.inl hb
    · refine Or.inr ?_
      rw [hBad] at hb
      simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hb
      rw [hBox, Set.mem_Icc]
      exact ⟨fun i => by linarith [neg_le_abs (v i), hb i],
             fun i => by linarith [le_abs_self (v i), hb i]⟩
  have hBadBox : Disjoint Bad Box := by
    rw [Set.disjoint_left]
    intro v hv1 hv2
    rw [hBad] at hv1
    simp only [Set.mem_ofPred_eq] at hv1
    rw [hBox, Set.mem_Icc] at hv2
    obtain ⟨i, hi⟩ := hv1
    have h1 : |v i| ≤ R := abs_le.mpr ⟨hv2.1 i, hv2.2 i⟩
    linarith
  have hdisj : Disjoint (T ∩ Bad) (T ∩ Box) := by
    rw [Set.disjoint_left]
    intro v hv1 hv2
    exact Set.disjoint_left.mp hBadBox hv1.2 hv2.2
  have hTeq : T ∩ Bad ∪ T ∩ Box = T := by
    apply Set.Subset.antisymm
    · rintro v (hv | hv) <;> exact hv.1
    · intro v hv
      rcases hcover hv with hb | hx
      · exact Or.inl ⟨hv, hb⟩
      · exact Or.inr ⟨hv, hx⟩
  have hsplit : (∫ v in T, g v) = (∫ v in T ∩ Bad, g v) + (∫ v in T ∩ Box, g v) := by
    have hun := setIntegral_union (f := g) hdisj (hTmeas.inter hBoxmeas)
      (hgint.integrableOn (s := T ∩ Bad)) (hgint.integrableOn (s := T ∩ Box))
    rw [hTeq] at hun
    exact hun
  have hBi : ∀ i : Fin n, MeasurableSet ({v : Fin n → ℝ | R < |v i|}) :=
    fun i => measurableSet_lt measurable_const (measurable_pi_apply i).abs
  have hsummand_int : ∀ i : Fin n,
      Integrable (fun v : Fin n → ℝ => ({v : Fin n → ℝ | R < |v i|}).indicator g v) :=
    fun i => hgint.indicator (hBi i)
  have hD1 : (∫ v in Bad, g v) ≤ 2 * n * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) := by
    have hstep1 : (∫ v in Bad, g v) ≤
        ∫ v, ∑ i : Fin n, ({v : Fin n → ℝ | R < |v i|}).indicator g v := by
      rw [← integral_indicator hBadmeas]
      refine integral_mono (hgint.indicator hBadmeas)
        (integrable_finsetSum Finset.univ (fun i _ => hsummand_int i)) (fun v => ?_)
      by_cases hv : v ∈ Bad
      · rw [Set.indicator_of_mem hv]
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hBad_eq ▸ hv)
        have h2 : ({v : Fin n → ℝ | R < |v i|}).indicator g v ≤
            ∑ j : Fin n, ({v : Fin n → ℝ | R < |v j|}).indicator g v :=
          Finset.single_le_sum (f := fun j : Fin n => ({v : Fin n → ℝ | R < |v j|}).indicator g v) (fun j _ => by
            by_cases hj : v ∈ ({v : Fin n → ℝ | R < |v j|})
            · rw [Set.indicator_of_mem hj]; exact Real.exp_nonneg _
            · rw [Set.indicator_of_notMem hj]) (Finset.mem_univ i)
        calc g v = ({v : Fin n → ℝ | R < |v i|}).indicator g v := (Set.indicator_of_mem hi g).symm
          _ ≤ _ := h2
      · rw [Set.indicator_of_notMem hv]
        exact Finset.sum_nonneg (fun j _ => by
          by_cases hj : v ∈ ({v : Fin n → ℝ | R < |v j|})
          · rw [Set.indicator_of_mem hj]; exact Real.exp_nonneg _
          · rw [Set.indicator_of_notMem hj])
    have hstep2 : (∫ v, ∑ i : Fin n, ({v : Fin n → ℝ | R < |v i|}).indicator g v)
        = ∑ i : Fin n, (∫ v in ({v : Fin n → ℝ | R < |v i|}), g v) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hsummand_int i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hBi i)]
    have hcoord : ∀ i : Fin n, (∫ v in ({v : Fin n → ℝ | R < |v i|}), g v)
        = 2 * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) := by
      intro i
      rw [hg]
      rw [coord_abs_tail i R, abs_tail_eq R hR]
    calc (∫ v in Bad, g v)
        ≤ ∫ v, ∑ i : Fin n, ({v : Fin n → ℝ | R < |v i|}).indicator g v := hstep1
      _ = ∑ i : Fin n, (∫ v in ({v : Fin n → ℝ | R < |v i|}), g v) := hstep2
      _ = ∑ i : Fin n, 2 * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) := by
            apply Finset.sum_congr rfl; intro i _; exact hcoord i
      _ = 2 * n * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
  have hD2 : (∫ v in T ∩ Box, g v) ≤ (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2) := by
    have hpoint : ∀ v ∈ T ∩ Box, g v ≤ Real.exp (-Real.pi * R ^ 2) := by
      intro v hv
      have hvT : v ∈ T := hv.1
      rw [hT] at hvT
      simp only [Set.mem_ofPred_eq] at hvT
      rw [hg]
      apply Real.exp_le_exp.mpr
      have hnm : R < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := hvT
      have hsq : R ^ 2 ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
        nlinarith [hR, hnm, norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))]
      nlinarith [Real.pi_pos, hsq]
    have hBoxvol_ne : volume Box ≠ ∞ := by
      rw [hBox, Real.volume_Icc_pi]
      exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
    have hconst_int : IntegrableOn (fun _ : Fin n → ℝ => Real.exp (-Real.pi * R ^ 2)) (T ∩ Box) :=
      IntegrableOn.mono (integrableOn_const (μ := volume) (s := Box) hBoxvol_ne)
        Set.inter_subset_right (le_refl _)
    calc (∫ v in T ∩ Box, g v)
        ≤ (∫ _ in T ∩ Box, Real.exp (-Real.pi * R ^ 2)) :=
          setIntegral_mono_on (hgint.integrableOn) hconst_int (hTmeas.inter hBoxmeas) hpoint
      _ = ((volume : Measure (Fin n → ℝ)).real (T ∩ Box)) * Real.exp (-Real.pi * R ^ 2) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ((volume : Measure (Fin n → ℝ)).real Box) * Real.exp (-Real.pi * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact measureReal_mono Set.inter_subset_right
      _ = (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2) := by rw [volumeReal_box R hR]
  have hTB_le : (∫ v in T ∩ Bad, g v) ≤ (∫ v in Bad, g v) := by
    refine setIntegral_mono_set hgint.integrableOn ?_ ?_
    · exact Filter.Eventually.of_forall (fun v => Real.exp_nonneg _)
    · exact Filter.Eventually.of_forall (fun v hv => hv.2)
  calc (∫ v in T, g v) = (∫ v in T ∩ Bad, g v) + (∫ v in T ∩ Box, g v) := hsplit
    _ ≤ (∫ v in Bad, g v) + (∫ v in T ∩ Box, g v) := by linarith [hTB_le]
    _ ≤ 2 * n * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2)) + (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2) := by
          linarith [hD1, hD2]


/-- `R ↦ R ^ k * exp (-c * R ^ 2)` tends to `0` at `+∞` for `c > 0`. -/
private lemma tendsto_pow_mul_exp_neg_mul_sq_atTop (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun R : ℝ => R ^ k * Real.exp (-c * R ^ 2)) Filter.atTop (nhds 0) := by
  have ho : (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-c * x ^ 2))
      =o[Filter.atTop] fun x : ℝ => Real.exp (-(1 / 2) * x) :=
    rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hc (k : ℝ)
  have ho' : (fun R : ℝ => R ^ k * Real.exp (-c * R ^ 2))
      =o[Filter.atTop] fun x : ℝ => Real.exp (-(1 / 2) * x) := by
    refine ho.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards with x
    rw [Real.rpow_natCast]
  have hgz : Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) Filter.atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by norm_num)
  exact ho'.tendsto_zero_of_tendsto hgz

/-- From `(1 - ε) * R < q ≤ R` with `R > 0` we get `|q / R - 1| < ε`. -/
private lemma abs_div_sub_one_lt {R q ε : ℝ} (hR : 0 < R) (hlo : (1 - ε) * R < q)
    (hhi : q ≤ R) : |q / R - 1| < ε := by
  have h1 : 1 - ε < q / R := by
    rw [lt_div_iff₀ hR]; linarith
  have h2 : q / R ≤ 1 := by
    rw [div_le_one hR]; exact hhi
  rw [abs_lt]
  constructor <;> linarith

/-- Main case `ε ≤ 1/2`: for large `R`, the quantile `q` of the one-dimensional Gaussian
at the mass of the `n`-dimensional ball of radius `R` satisfies `(1-ε) R < q ≤ R`. -/
private theorem main_bound (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ q : ℝ,
      (∫ x in Set.Iic q, Real.exp (-Real.pi * x ^ 2))
        = (∫ y in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R}, Real.exp (-Real.pi * ‖y‖ ^ 2)) →
      (1 - ε) * R < q ∧ q ≤ R := by
  have hd1 : 0 < 1 - ε := by linarith
  have hIic_eq : ∀ t : ℝ, (∫ x in Set.Iic t, Real.exp (-Real.pi * x ^ 2))
      = ∫ x in Set.Iio t, Real.exp (-Real.pi * x ^ 2) :=
    fun t => MeasureTheory.integral_Iic_eq_integral_Iio (x := t)
      (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2))
  have hsplit' : ∀ t : ℝ, (∫ x in Set.Iic t, Real.exp (-Real.pi * x ^ 2))
      + (∫ x in Set.Ioi t, Real.exp (-Real.pi * x ^ 2)) = 1 := by
    intro t
    rw [hIic_eq t]
    exact gauss_cdf_tail_split t
  have hFmono : StrictMono (fun t : ℝ => ∫ x in Set.Iic t, Real.exp (-Real.pi * x ^ 2)) :=
    gaussian_cdf_strictMono
  have hTa : StrictAnti (fun s : ℝ => ∫ x in Set.Ioi s, Real.exp (-Real.pi * x ^ 2)) := by
    have heq : (fun s : ℝ => ∫ x in Set.Ioi s, Real.exp (-Real.pi * x ^ 2))
        = fun s : ℝ => 1 - ∫ x in Set.Iic s, Real.exp (-Real.pi * x ^ 2) := by
      funext s; linarith [hsplit' s]
    rw [heq]
    intro a b hab
    have := hFmono hab
    linarith
  have hc : 0 < Real.pi * (ε * (2 - ε)) := by
    have : 0 < 2 - ε := by linarith
    positivity
  have htend := tendsto_pow_mul_exp_neg_mul_sq_atTop (n + 1) hc
  have hlt : ∀ᶠ R : ℝ in Filter.atTop,
      ((↑n : ℝ) / Real.pi + 2 ^ n) * (1 - ε)
        * (R ^ (n + 1) * Real.exp (-(Real.pi * (ε * (2 - ε))) * R ^ 2))
        < Real.exp (-3 * Real.pi) :=
    (htend.const_mul (((↑n : ℝ) / Real.pi + 2 ^ n) * (1 - ε))).eventually_lt_const
      (by rw [mul_zero]; exact Real.exp_pos _)
  have hdom : ∀ᶠ R : ℝ in Filter.atTop,
      ((↑n : ℝ) / Real.pi + 2 ^ n) * R ^ n * Real.exp (-Real.pi * R ^ 2)
        < Real.exp (-3 * Real.pi) / ((1 - ε) * R)
            * Real.exp (-Real.pi * ((1 - ε) * R) ^ 2) := by
    filter_upwards [hlt, Filter.eventually_ge_atTop (2 : ℝ)] with R hltR hR2
    have hRpos : (0 : ℝ) < R := by linarith
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity : (0 : ℝ) < (1 - ε) * R)]
    have hexp : Real.exp (-(Real.pi * (ε * (2 - ε))) * R ^ 2)
          * Real.exp (-Real.pi * ((1 - ε) * R) ^ 2) = Real.exp (-Real.pi * R ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hL : ((↑n : ℝ) / Real.pi + 2 ^ n) * R ^ n * Real.exp (-Real.pi * R ^ 2) * ((1 - ε) * R)
        = (((↑n : ℝ) / Real.pi + 2 ^ n) * (1 - ε)
            * (R ^ (n + 1) * Real.exp (-(Real.pi * (ε * (2 - ε))) * R ^ 2)))
          * Real.exp (-Real.pi * ((1 - ε) * R) ^ 2) := by
      rw [← hexp, pow_succ]
      ring
    rw [hL]
    exact mul_lt_mul_of_pos_right hltR (Real.exp_pos _)
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hdom
  refine ⟨max R₀ 2, le_max_right _ _, ?_⟩
  intro R hR q hq
  have hRge : R₀ ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : 2 ≤ R := le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hFq : (∫ x in Set.Iic q, Real.exp (-Real.pi * x ^ 2))
      + (∫ x in Set.Ioi q, Real.exp (-Real.pi * x ^ 2)) = 1 := hsplit' q
  have hGR := gaussian_ball_split n R
  have hT1q : (∫ x in Set.Ioi q, Real.exp (-Real.pi * x ^ 2))
      = (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
    linarith [hFq, hGR, hq]
  have hTn_ge : (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2))
      ≤ (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2)) :=
    gaussian_ball_tail_ge_one_dim n hn R (le_of_lt hRpos)
  have hA := gaussian_tail_upper R hRpos
  have hD := gaussian_ball_tail_upper_aux n R (le_of_lt hRpos)
  have hstep1 : 2 * (↑n : ℝ) * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2))
      ≤ ((↑n : ℝ) / Real.pi) * R ^ n * Real.exp (-Real.pi * R ^ 2) := by
    have hinv : 1 / R ≤ R ^ n := by
      rw [div_le_iff₀ hRpos]
      calc (1 : ℝ) ≤ R ^ (n + 1) := one_le_pow₀ hR1
        _ = R ^ n * R := by rw [pow_succ]
    have hnn : (0 : ℝ) ≤ (↑n : ℝ) / Real.pi * Real.exp (-Real.pi * R ^ 2) := by positivity
    calc 2 * (↑n : ℝ) * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2))
        ≤ 2 * (↑n : ℝ) * (Real.exp (-Real.pi * R ^ 2) / (2 * Real.pi * R)) := by
          apply mul_le_mul_of_nonneg_left hA; positivity
      _ = ((↑n : ℝ) / Real.pi * Real.exp (-Real.pi * R ^ 2)) * (1 / R) := by ring_nf
      _ ≤ ((↑n : ℝ) / Real.pi * Real.exp (-Real.pi * R ^ 2)) * R ^ n :=
          mul_le_mul_of_nonneg_left hinv hnn
      _ = ((↑n : ℝ) / Real.pi) * R ^ n * Real.exp (-Real.pi * R ^ 2) := by ring
  have hstep2 : (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2)
      = 2 ^ n * R ^ n * Real.exp (-Real.pi * R ^ 2) := by rw [mul_pow]
  have hTn_ub : (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2))
      ≤ ((↑n : ℝ) / Real.pi + 2 ^ n) * R ^ n * Real.exp (-Real.pi * R ^ 2) := by
    calc _ ≤ 2 * (↑n : ℝ) * (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2))
              + (2 * R) ^ n * Real.exp (-Real.pi * R ^ 2) := hD
      _ ≤ ((↑n : ℝ) / Real.pi) * R ^ n * Real.exp (-Real.pi * R ^ 2)
              + 2 ^ n * R ^ n * Real.exp (-Real.pi * R ^ 2) := by
            rw [hstep2]; linarith [hstep1]
      _ = ((↑n : ℝ) / Real.pi + 2 ^ n) * R ^ n * Real.exp (-Real.pi * R ^ 2) := by ring
  have hT1_lb : Real.exp (-3 * Real.pi) / ((1 - ε) * R)
        * Real.exp (-Real.pi * ((1 - ε) * R) ^ 2)
      ≤ ∫ x in Set.Ioi ((1 - ε) * R), Real.exp (-Real.pi * x ^ 2) := by
    have hs : 1 ≤ (1 - ε) * R := by nlinarith [hε2, hε, hR2]
    exact gaussian_tail_lower ((1 - ε) * R) hs
  have hdomR : ((↑n : ℝ) / Real.pi + 2 ^ n) * R ^ n * Real.exp (-Real.pi * R ^ 2)
      < Real.exp (-3 * Real.pi) / ((1 - ε) * R)
          * Real.exp (-Real.pi * ((1 - ε) * R) ^ 2) := hR₀ R hRge
  have hTn_lt : (∫ y in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, Real.exp (-Real.pi * ‖y‖ ^ 2))
      < ∫ x in Set.Ioi ((1 - ε) * R), Real.exp (-Real.pi * x ^ 2) :=
    lt_of_le_of_lt hTn_ub (lt_of_lt_of_le hdomR hT1_lb)
  constructor
  · by_contra hcon
    push_neg at hcon
    have h : (∫ x in Set.Ioi q, Real.exp (-Real.pi * x ^ 2))
          < ∫ x in Set.Ioi ((1 - ε) * R), Real.exp (-Real.pi * x ^ 2) := by
      rw [hT1q]; exact hTn_lt
    rcases lt_or_eq_of_le hcon with hlt' | heq'
    · have h' := hTa hlt'
      linarith
    · rw [heq'] at h
      exact absurd h (lt_irrefl _)
  · by_contra hcon
    push_neg at hcon
    have h : (∫ x in Set.Ioi q, Real.exp (-Real.pi * x ^ 2))
        < ∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2) := hTa hcon
    have h2 : (∫ x in Set.Ioi R, Real.exp (-Real.pi * x ^ 2))
        ≤ ∫ x in Set.Ioi q, Real.exp (-Real.pi * x ^ 2) := by rw [hT1q]; exact hTn_ge
    linarith

theorem gaussian_ball_quantile_asymptotic (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ q : ℝ,
      (∫ x : ℝ in {x : ℝ | x ≤ q}, Real.exp (-Real.pi * x ^ 2)) =
        ∫ y in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R}, Real.exp (-Real.pi * ‖y‖ ^ 2) →
      |q / R - 1| < ε := by
  intro ε hε
  by_cases hε2 : ε ≤ 1 / 2
  · obtain ⟨R₀, hR₀2, hR₀⟩ := main_bound n hn ε hε hε2
    refine ⟨R₀, fun R hR q hq => ?_⟩
    have hR2 : 2 ≤ R := le_trans hR₀2 hR
    have hRpos : 0 < R := by linarith
    obtain ⟨hlo, hhi⟩ := hR₀ R hR q hq
    exact abs_div_sub_one_lt hRpos hlo hhi
  · push_neg at hε2
    obtain ⟨R₀, hR₀2, hR₀⟩ := main_bound n hn (1 / 2) (by norm_num) (le_refl (1 / 2))
    refine ⟨R₀, fun R hR q hq => ?_⟩
    have hR2 : 2 ≤ R := le_trans hR₀2 hR
    have hRpos : 0 < R := by linarith
    obtain ⟨hlo, hhi⟩ := hR₀ R hR q hq
    have h14 := abs_div_sub_one_lt (ε := 1 / 2) hRpos hlo hhi
    linarith

end

end Commons.Analysis.GaussianMeasure