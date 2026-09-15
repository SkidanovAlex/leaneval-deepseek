import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Convex.Contractible
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.MeasureTheory.tendsto_eLpNorm_mul_exp_neg_sq

noncomputable section
set_option hygiene false
open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology FourierTransform

namespace Commons.Analysis.Fourier

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-- The complex-affine shift `x ↦ x + s • η` on `ℝᵈ`, as a point of `ℂᵈ`. -/
def cshift (η : ℝᵈ) (s : ℂ) (x : ℝᵈ) : ℂᵈ := fun i => (x i : ℂ) + s * (η i : ℂ)

@[simp] lemma cshift_apply (η : ℝᵈ) (s : ℂ) (x : ℝᵈ) (i : Fin d) :
    cshift η s x i = (x i : ℂ) + s * (η i : ℂ) := rfl

lemma cshift_re (η : ℝᵈ) (s : ℂ) (x : ℝᵈ) (i : Fin d) :
    (cshift η s x i).re = x i + s.re * η i := by
  simp [cshift, Complex.add_re, Complex.mul_re]

lemma cshift_im (η : ℝᵈ) (s : ℂ) (x : ℝᵈ) (i : Fin d) :
    (cshift η s x i).im = s.im * η i := by
  simp [cshift, Complex.add_im, Complex.mul_im]

lemma sum_sq_eq_norm_sq (p : ℝᵈ) : (∑ i, (p i) ^ 2) = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma sum_sq_gauss (K : ℝ) (hK : 0 < K) :
    Integrable (fun p : ℝᵈ => Real.exp (-(∑ i, (p i) ^ 2) / (2 * K))) volume := by
  have h1 : Integrable (fun v : ℝᵈ => Real.exp (-(1/(2*K)) * ‖v‖ ^ 2)) volume := by
    have hb : 0 < (((1/(2*K) : ℝ)) : ℂ).re := by
      simp only [Complex.ofReal_re]
      positivity
    have h2 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℝᵈ) hb 0 0
    have h3 : Integrable (fun v : ℝᵈ =>
        (Complex.exp (-(((1/(2*K):ℝ):ℂ)) * ((‖v‖ : ℂ)) ^ 2)).re) volume := by
      simpa using h2.re
    refine h3.congr ?_
    filter_upwards with v
    have hcast : (-(((1/(2*K):ℝ):ℂ)) * ((‖v‖ : ℂ)) ^ 2) = (((-(1/(2*K)) * ‖v‖^2 : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_pow (‖v‖) 2, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
    rw [hcast, Complex.exp_ofReal_re]
  refine h1.congr ?_
  filter_upwards with p
  rw [sum_sq_eq_norm_sq]
  ring_nf

lemma abs_le_max_abs_of_mem_uIoc {a b u : ℝ} (hu : u ∈ Set.uIoc a b) :
    |u| ≤ max |a| |b| := by
  have h1 : u ∈ Set.Icc (min a b) (max a b) := by
    simpa [Set.uIcc] using Set.uIoc_subset_uIcc hu
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp h1
  apply abs_le.mpr
  constructor
  · have h2 : -(max |a| |b|) ≤ min a b := by
      apply le_min
      · linarith [neg_abs_le a, le_max_left |a| |b|]
      · linarith [neg_abs_le b, le_max_right |a| |b|]
    linarith
  · have h3 : max a b ≤ max |a| |b| :=
      max_le (le_trans (le_abs_self a) (le_max_left _ _)) (le_trans (le_abs_self b) (le_max_right _ _))
    linarith

lemma neg_div_le_of (A P R K : ℝ) (hK : 0 < K) (h : P / 2 - R ≤ A) :
    -A / K ≤ -P / (2 * K) + R / K := by
  rw [div_le_iff₀ hK]
  have h1 : (-P / (2 * K) + R / K) * K = -P / 2 + R := by
    field_simp
  rw [h1]
  linarith

/-- Integrability of a Gaussian-damped entire function along a line in `ℂᵈ`, uniformly in the
real part of the shift parameter. -/
lemma integrable_cshift_gen (H : ℂᵈ → ℂ) (hcontH : Continuous H) (η : ℝᵈ) {C K B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : 0 < K)
    (hdecay : ∀ z : ℂᵈ,
      ‖H z‖ ≤ C * Real.exp (-(∑ i, (z i).re ^ 2) / K + B * (∑ i, (z i).im ^ 2)))
    (c0 c1 : ℂ) (a b : ℝ) :
    Integrable (Function.uncurry (fun (t : ℝ) (p : ℝᵈ) =>
        H (cshift η (c0 + (t : ℂ) * c1) p)))
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  set ν : Measure ℝ := volume.restrict (Set.uIoc a b) with hν
  haveI hνfin : IsFiniteMeasure ν := by
    rw [hν, isFiniteMeasure_restrict, Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  set Sη : ℝ := ∑ i, (η i) ^ 2 with hSηdef
  have hSη : 0 ≤ Sη := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set M : ℝ := max |a| |b| with hM
  have hMnn : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
  set Rr : ℝ := |c0.re| + M * |c1.re| with hRr
  set Ri : ℝ := |c0.im| + M * |c1.im| with hRi
  have hRrnn : 0 ≤ Rr := by rw [hRr]; positivity
  have hRinn : 0 ≤ Ri := by rw [hRi]; positivity
  set bound : ℝᵈ → ℝ := fun p =>
    (C * Real.exp (B * Ri ^ 2 * Sη) * Real.exp (Rr ^ 2 * Sη / K)) *
      Real.exp (-(∑ i, (p i) ^ 2) / (2 * K)) with hbounddef
  have hbound_int : Integrable bound volume := by
    have h0 : Integrable (fun p : ℝᵈ => Real.exp (-(∑ i, (p i) ^ 2) / (2 * K))) volume :=
      sum_sq_gauss (d := d) K hK
    have h1 : Integrable (fun p : ℝᵈ =>
        (C * Real.exp (B * Ri ^ 2 * Sη) * Real.exp (Rr ^ 2 * Sη / K)) *
          Real.exp (-(∑ i, (p i) ^ 2) / (2 * K))) volume := h0.const_mul _
    rw [hbounddef]
    exact h1
  have hbound_prod : Integrable (fun q : ℝ × ℝᵈ => bound q.2) (ν.prod (volume : Measure ℝᵈ)) :=
    hbound_int.comp_snd ν
  refine Integrable.mono' hbound_prod ?_ ?_
  · have hcont : Continuous (fun q : ℝ × ℝᵈ =>
        H (cshift η (c0 + (q.1 : ℂ) * c1) q.2)) :=
      hcontH.comp (by
        apply continuous_pi
        intro i
        simp only [cshift_apply]
        fun_prop)
    exact hcont.aestronglyMeasurable
  · have hae : ∀ᵐ q ∂(ν.prod (volume : Measure ℝᵈ)), q.1 ∈ Set.uIoc a b := by
      have hprod : (ν.prod (volume : Measure ℝᵈ))
          = ((volume : Measure ℝ).prod (volume : Measure ℝᵈ)).restrict
              ((Set.uIoc a b) ×ˢ (Set.univ : Set ℝᵈ)) := by
        rw [hν, ← Measure.prod_restrict]; simp
      rw [hprod]
      filter_upwards [ae_restrict_mem (μ := ((volume : Measure ℝ).prod (volume : Measure ℝᵈ)))
          (s := (Set.uIoc a b) ×ˢ (Set.univ : Set ℝᵈ))
          (measurableSet_uIoc.prod MeasurableSet.univ)] with q hq
      exact (Set.mem_prod.mp hq).1
    filter_upwards [hae] with q hq
    obtain ⟨t, p⟩ := q
    have ht : |t| ≤ M := by rw [hM]; exact abs_le_max_abs_of_mem_uIoc hq
    have hd := hdecay (cshift η (c0 + (t : ℂ) * c1) p)
    have hre : (∑ i, ((cshift η (c0 + (t : ℂ) * c1) p) i).re ^ 2)
        = ∑ i, (p i + (c0.re + t * c1.re) * η i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      rw [cshift_re]
      simp [Complex.add_re, Complex.mul_re]
    have him : (∑ i, ((cshift η (c0 + (t : ℂ) * c1) p) i).im ^ 2)
        = (c0.im + t * c1.im) ^ 2 * Sη := by
      rw [hSηdef, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [cshift_im]
      simp [Complex.add_im, Complex.mul_im]
      ring
    have hA : |c0.re + t * c1.re| ≤ Rr := by
      rw [hRr]
      calc |c0.re + t * c1.re| ≤ |c0.re| + |t * c1.re| := abs_add_le _ _
        _ = |c0.re| + |t| * |c1.re| := by rw [abs_mul]
        _ ≤ |c0.re| + M * |c1.re| := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
    have hA2 : (c0.re + t * c1.re) ^ 2 ≤ Rr ^ 2 := by
      rw [sq_le_sq]
      rwa [abs_of_nonneg hRrnn]
    have hBi : (c0.im + t * c1.im) ^ 2 ≤ Ri ^ 2 := by
      have hAi : |c0.im + t * c1.im| ≤ Ri := by
        rw [hRi]
        calc |c0.im + t * c1.im| ≤ |c0.im| + |t * c1.im| := abs_add_le _ _
          _ = |c0.im| + |t| * |c1.im| := by rw [abs_mul]
          _ ≤ |c0.im| + M * |c1.im| := by
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
      rw [sq_le_sq]
      rwa [abs_of_nonneg hRinn]
    have hsum_u : (∑ i, ((c0.re + t * c1.re) * η i) ^ 2) ≤ Rr ^ 2 * Sη := by
      rw [hSηdef, show (∑ i, ((c0.re + t * c1.re) * η i) ^ 2)
            = (c0.re + t * c1.re) ^ 2 * ∑ i, (η i) ^ 2 from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact mul_le_mul_of_nonneg_right hA2 hSη
    have hlb : (1/2) * (∑ i, (p i) ^ 2) - Rr ^ 2 * Sη
        ≤ ∑ i, (p i + (c0.re + t * c1.re) * η i) ^ 2 := by
      have hpt : ∀ i, (1/2) * (p i) ^ 2 - ((c0.re + t * c1.re) * η i) ^ 2
          ≤ (p i + (c0.re + t * c1.re) * η i) ^ 2 := by
        intro i; nlinarith [sq_nonneg (p i + 2 * ((c0.re + t * c1.re) * η i))]
      calc (1/2) * (∑ i, (p i) ^ 2) - Rr ^ 2 * Sη
          ≤ (∑ i, (1/2) * (p i) ^ 2) - (∑ i, ((c0.re + t * c1.re) * η i) ^ 2) := by
            rw [Finset.mul_sum]; linarith [hsum_u]
        _ = ∑ i, ((1/2) * (p i) ^ 2 - ((c0.re + t * c1.re) * η i) ^ 2) := by
            rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i, (p i + (c0.re + t * c1.re) * η i) ^ 2 := Finset.sum_le_sum (fun i _ => hpt i)
    have hexp : -(∑ i, ((cshift η (c0 + (t : ℂ) * c1) p) i).re ^ 2) / K
          + B * (∑ i, ((cshift η (c0 + (t : ℂ) * c1) p) i).im ^ 2)
        ≤ B * Ri ^ 2 * Sη + Rr ^ 2 * Sη / K - (∑ i, (p i) ^ 2) / (2 * K) := by
      rw [hre, him]
      have h1 := neg_div_le_of (∑ i, (p i + (c0.re + t * c1.re) * η i) ^ 2)
        (∑ i, (p i) ^ 2) (Rr ^ 2 * Sη) K hK (by linarith [hlb])
      have h2 : B * ((c0.im + t * c1.im) ^ 2 * Sη) ≤ B * (Ri ^ 2 * Sη) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBi hSη) hB
      calc (-∑ i, (p i + (c0.re + t * c1.re) * η i) ^ 2) / K + B * ((c0.im + t * c1.im) ^ 2 * Sη)
          ≤ ((-∑ i, (p i) ^ 2) / (2 * K) + Rr ^ 2 * Sη / K) + B * (Ri ^ 2 * Sη) :=
            add_le_add h1 h2
        _ = B * Ri ^ 2 * Sη + Rr ^ 2 * Sη / K - (∑ i, (p i) ^ 2) / (2 * K) := by ring
    calc ‖H (cshift η (c0 + (t : ℂ) * c1) p)‖
        ≤ C * Real.exp (-(∑ i, ((cshift η (c0 + (t : ℂ) * c1) p) i).re ^ 2) / K
            + B * (∑ i, ((cshift η (c0 + (t : ℂ) * c1) p) i).im ^ 2)) := hd
      _ ≤ C * Real.exp (B * Ri ^ 2 * Sη + Rr ^ 2 * Sη / K - (∑ i, (p i) ^ 2) / (2 * K)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = bound p := by
          rw [hbounddef]
          have hE : B * Ri ^ 2 * Sη + Rr ^ 2 * Sη / K - (∑ i, (p i) ^ 2) / (2 * K)
              = B * Ri ^ 2 * Sη + (Rr ^ 2 * Sη / K + (-(∑ i, (p i) ^ 2) / (2 * K))) := by ring
          rw [hE, Real.exp_add, Real.exp_add]
          ring

lemma cshift_decay_bound (H : ℂᵈ → ℂ) (η : ℝᵈ) {C K B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : 0 < K)
    (hdecay : ∀ z : ℂᵈ,
      ‖H z‖ ≤ C * Real.exp (-(∑ i, (z i).re ^ 2) / K + B * (∑ i, (z i).im ^ 2)))
    (s : ℂ) (x : ℝᵈ) :
    ‖H (cshift η s x)‖ ≤
      C * Real.exp (B * ‖s‖ ^ 2 * (∑ i, (η i) ^ 2) + ‖s‖ ^ 2 * (∑ i, (η i) ^ 2) / K
        - (∑ i, (x i) ^ 2) / (2 * K)) := by
  set Sη : ℝ := ∑ i, (η i) ^ 2 with hSηdef
  have hSη : 0 ≤ Sη := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hd := hdecay (cshift η s x)
  have hre : (∑ i, ((cshift η s x) i).re ^ 2) = ∑ i, (x i + s.re * η i) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [cshift_re]
  have him : (∑ i, ((cshift η s x) i).im ^ 2) = s.im ^ 2 * Sη := by
    rw [hSηdef, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; rw [cshift_im]; ring
  have hns : ‖s‖ ^ 2 = s.re * s.re + s.im * s.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hre_le : s.re ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith [hns, sq_nonneg s.im]
  have him_le : s.im ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith [hns, sq_nonneg s.re]
  have hsum_u : (∑ i, (s.re * η i) ^ 2) ≤ ‖s‖ ^ 2 * Sη := by
    rw [hSηdef, show (∑ i, (s.re * η i) ^ 2) = s.re ^ 2 * ∑ i, (η i) ^ 2 from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
    exact mul_le_mul_of_nonneg_right hre_le hSη
  have hlb : (1/2) * (∑ i, (x i) ^ 2) - ‖s‖ ^ 2 * Sη ≤ ∑ i, (x i + s.re * η i) ^ 2 := by
    have hpt : ∀ i, (1/2) * (x i) ^ 2 - (s.re * η i) ^ 2 ≤ (x i + s.re * η i) ^ 2 := by
      intro i; nlinarith [sq_nonneg (x i + 2 * (s.re * η i))]
    calc (1/2) * (∑ i, (x i) ^ 2) - ‖s‖ ^ 2 * Sη
        ≤ (∑ i, (1/2) * (x i) ^ 2) - (∑ i, (s.re * η i) ^ 2) := by
          rw [Finset.mul_sum]; linarith [hsum_u]
      _ = ∑ i, ((1/2) * (x i) ^ 2 - (s.re * η i) ^ 2) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, (x i + s.re * η i) ^ 2 := Finset.sum_le_sum (fun i _ => hpt i)
  have hexp : -(∑ i, ((cshift η s x) i).re ^ 2) / K + B * (∑ i, ((cshift η s x) i).im ^ 2)
      ≤ B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K - (∑ i, (x i) ^ 2) / (2 * K) := by
    rw [hre, him]
    have h1 := neg_div_le_of (∑ i, (x i + s.re * η i) ^ 2) (∑ i, (x i) ^ 2) (‖s‖ ^ 2 * Sη) K hK
      (by linarith [hlb])
    have h2 : B * (s.im ^ 2 * Sη) ≤ B * (‖s‖ ^ 2 * Sη) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right him_le hSη) hB
    calc (-∑ i, (x i + s.re * η i) ^ 2) / K + B * (s.im ^ 2 * Sη)
        ≤ ((-∑ i, (x i) ^ 2) / (2 * K) + ‖s‖ ^ 2 * Sη / K) + B * (‖s‖ ^ 2 * Sη) :=
          add_le_add h1 h2
      _ = B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K - (∑ i, (x i) ^ 2) / (2 * K) := by ring
  exact le_trans hd (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC)

lemma continuous_cshift_fixed (η : ℝᵈ) (x : ℝᵈ) :
    Continuous (fun s : ℂ => cshift η s x) := by
  apply continuous_pi
  intro i
  simp only [cshift_apply]
  fun_prop

lemma continuous_Gfun (H : ℂᵈ → ℂ) (hcontH : Continuous H) (η : ℝᵈ) {C K B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : 0 < K)
    (hdecay : ∀ z : ℂᵈ,
      ‖H z‖ ≤ C * Real.exp (-(∑ i, (z i).re ^ 2) / K + B * (∑ i, (z i).im ^ 2))) :
    Continuous (fun s : ℂ => ∫ x : ℝᵈ, H (cshift η s x)) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  set r : ℝ := ‖s₀‖ + 1 with hr
  have hrpos : 0 < r := by positivity
  set Sη : ℝ := ∑ i, (η i) ^ 2 with hSηdef
  have hSη : 0 ≤ Sη := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set bound : ℝᵈ → ℝ := fun x =>
    (C * Real.exp (B * r ^ 2 * Sη) * Real.exp (r ^ 2 * Sη / K)) *
      Real.exp (-(∑ i, (x i) ^ 2) / (2 * K)) with hbound
  have hbound_int : Integrable bound volume := by
    have h0 : Integrable (fun x : ℝᵈ => Real.exp (-(∑ i, (x i) ^ 2) / (2 * K))) volume :=
      sum_sq_gauss (d := d) K hK
    have h1 : Integrable (fun x : ℝᵈ =>
        (C * Real.exp (B * r ^ 2 * Sη) * Real.exp (r ^ 2 * Sη / K)) *
          Real.exp (-(∑ i, (x i) ^ 2) / (2 * K))) volume := h0.const_mul _
    rw [hbound]; exact h1
  refine continuousAt_of_dominated (μ := (volume : Measure ℝᵈ))
    (F := fun (s : ℂ) (x : ℝᵈ) => H (cshift η s x)) (x₀ := s₀) ?_ ?_ hbound_int ?_
  · filter_upwards [Metric.ball_mem_nhds s₀ one_pos] with s hs
    have hcont : Continuous (fun x : ℝᵈ => H (cshift η s x)) :=
      hcontH.comp (by apply continuous_pi; intro i; simp only [cshift_apply]; fun_prop)
    exact hcont.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds s₀ one_pos] with s hs
    filter_upwards with x
    have hsle : ‖s‖ ≤ r := by
      have h1 : dist s s₀ < 1 := Metric.mem_ball.mp hs
      rw [dist_eq_norm] at h1
      have h2 : ‖s‖ ≤ ‖s - s₀‖ + ‖s₀‖ := by
        calc ‖s‖ = ‖(s - s₀) + s₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖s - s₀‖ + ‖s₀‖ := norm_add_le _ _
      rw [hr]; linarith
    have h := cshift_decay_bound H η hC hB hK hdecay s x
    rw [← hSηdef] at h
    have hss : ‖s‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg s]
    have hexp : B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K - (∑ i, (x i) ^ 2) / (2 * K)
        ≤ (B * r ^ 2 * Sη + r ^ 2 * Sη / K) + (-(∑ i, (x i) ^ 2) / (2 * K)) := by
      have h1 : B * ‖s‖ ^ 2 * Sη ≤ B * r ^ 2 * Sη :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hss hB) hSη
      have h2 : ‖s‖ ^ 2 * Sη / K ≤ r ^ 2 * Sη / K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hss hSη) hK.le
      have hsum : B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K ≤ B * r ^ 2 * Sη + r ^ 2 * Sη / K :=
        add_le_add h1 h2
      calc B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K - (∑ i, (x i) ^ 2) / (2 * K)
          = (B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K) + (-(∑ i, (x i) ^ 2) / (2 * K)) := by ring
        _ ≤ (B * r ^ 2 * Sη + r ^ 2 * Sη / K) + (-(∑ i, (x i) ^ 2) / (2 * K)) :=
            add_le_add hsum le_rfl
    rw [hbound]
    calc ‖H (cshift η s x)‖
        ≤ C * Real.exp (B * ‖s‖ ^ 2 * Sη + ‖s‖ ^ 2 * Sη / K - (∑ i, (x i) ^ 2) / (2 * K)) := h
      _ ≤ C * Real.exp ((B * r ^ 2 * Sη + r ^ 2 * Sη / K) + (-(∑ i, (x i) ^ 2) / (2 * K))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = (C * Real.exp (B * r ^ 2 * Sη) * Real.exp (r ^ 2 * Sη / K)) *
            Real.exp (-(∑ i, (x i) ^ 2) / (2 * K)) := by
          rw [Real.exp_add, Real.exp_add]; ring
  · filter_upwards with a
    exact (hcontH.comp (continuous_cshift_fixed η a)).continuousAt

lemma integrable_cshift_gen' (H : ℂᵈ → ℂ) (hcontH : Continuous H) (η : ℝᵈ) {C K B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : 0 < K)
    (hdecay : ∀ z : ℂᵈ,
      ‖H z‖ ≤ C * Real.exp (-(∑ i, (z i).re ^ 2) / K + B * (∑ i, (z i).im ^ 2)))
    (c1 c0 : ℂ) (a b : ℝ) :
    Integrable (Function.uncurry (fun (t : ℝ) (p : ℝᵈ) =>
        H (cshift η ((t : ℂ) * c1 + c0) p)))
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  have h := integrable_cshift_gen H hcontH η hC hB hK hdecay c0 c1 a b
  refine h.congr ?_
  filter_upwards with q
  obtain ⟨t, p⟩ := q
  simp only [Function.uncurry_apply_pair]
  rw [show c0 + (t : ℂ) * c1 = (t : ℂ) * c1 + c0 by ring]

lemma integrable_interval_integral (f : ℝ → ℝᵈ → ℂ) {a b : ℝ}
    (h : Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc a b)).prod volume)) :
    Integrable (fun p => ∫ x in a..b, f x p) volume := by
  have h1 := h.integral_prod_right
  rcases le_total a b with hab | hab
  · have heq : (fun p => ∫ x in a..b, f x p)
        = fun p => ∫ x, f x p ∂(volume.restrict (Set.uIoc a b)) := by
      funext p
      rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
    rw [heq]; exact h1
  · have heq : (fun p => ∫ x in a..b, f x p)
        = fun p => - ∫ x, f x p ∂(volume.restrict (Set.uIoc a b)) := by
      funext p
      rw [intervalIntegral.integral_of_ge hab, Set.uIoc_of_ge hab]
    rw [heq]; exact h1.neg

lemma differentiable_cshift_fixed (η : ℝᵈ) (x : ℝᵈ) :
    Differentiable ℂ (fun s : ℂ => cshift η s x) := by
  apply differentiable_pi.mpr
  intro i
  simp only [cshift_apply]
  fun_prop

lemma isConservativeOn_Gfun (H : ℂᵈ → ℂ) (hH : Differentiable ℂ H) (η : ℝᵈ) {C K B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : 0 < K)
    (hdecay : ∀ z : ℂᵈ,
      ‖H z‖ ≤ C * Real.exp (-(∑ i, (z i).re ^ 2) / K + B * (∑ i, (z i).im ^ 2))) :
    Complex.IsConservativeOn (fun s : ℂ => ∫ x : ℝᵈ, H (cshift η s x)) Set.univ := by
  have hcontH : Continuous H := hH.continuous
  intro z w _
  refine eq_neg_of_add_eq_zero_left ?_
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  set A1 : ℝᵈ → ℂ := fun p => ∫ x in z.re..w.re, H (cshift η ((x : ℂ) + (z.im : ℂ) * Complex.I) p) with hA1
  set A2 : ℝᵈ → ℂ := fun p => ∫ x in z.re..w.re, H (cshift η ((x : ℂ) + (w.im : ℂ) * Complex.I) p) with hA2
  set A3 : ℝᵈ → ℂ := fun p => ∫ y in z.im..w.im, H (cshift η ((w.re : ℂ) + (y : ℂ) * Complex.I) p) with hA3
  set A4 : ℝᵈ → ℂ := fun p => ∫ y in z.im..w.im, H (cshift η ((z.re : ℂ) + (y : ℂ) * Complex.I) p) with hA4
  have hm1 : Integrable A1 volume := by
    rw [hA1]; refine integrable_interval_integral _ ?_
    simpa [mul_one] using
      integrable_cshift_gen' H hcontH η hC hB hK hdecay 1 ((z.im : ℂ) * Complex.I) z.re w.re
  have hm2 : Integrable A2 volume := by
    rw [hA2]; refine integrable_interval_integral _ ?_
    simpa [mul_one] using
      integrable_cshift_gen' H hcontH η hC hB hK hdecay 1 ((w.im : ℂ) * Complex.I) z.re w.re
  have hm3 : Integrable A3 volume := by
    rw [hA3]; refine integrable_interval_integral _ ?_
    exact integrable_cshift_gen H hcontH η hC hB hK hdecay (w.re : ℂ) Complex.I z.im w.im
  have hm4 : Integrable A4 volume := by
    rw [hA4]; refine integrable_interval_integral _ ?_
    exact integrable_cshift_gen H hcontH η hC hB hK hdecay (z.re : ℂ) Complex.I z.im w.im
  have e1 : (∫ x in z.re..w.re, (∫ p : ℝᵈ, H (cshift η ((x : ℂ) + (z.im : ℂ) * Complex.I) p)))
      = ∫ p : ℝᵈ, A1 p := by
    rw [hA1, intervalIntegral_integral_swap]
    simpa [mul_one] using
      integrable_cshift_gen' H hcontH η hC hB hK hdecay 1 ((z.im : ℂ) * Complex.I) z.re w.re
  have e2 : (∫ x in z.re..w.re, (∫ p : ℝᵈ, H (cshift η ((x : ℂ) + (w.im : ℂ) * Complex.I) p)))
      = ∫ p : ℝᵈ, A2 p := by
    rw [hA2, intervalIntegral_integral_swap]
    simpa [mul_one] using
      integrable_cshift_gen' H hcontH η hC hB hK hdecay 1 ((w.im : ℂ) * Complex.I) z.re w.re
  have e3 : (∫ y in z.im..w.im, (∫ p : ℝᵈ, H (cshift η ((w.re : ℂ) + (y : ℂ) * Complex.I) p)))
      = ∫ p : ℝᵈ, A3 p := by
    rw [hA3, intervalIntegral_integral_swap]
    exact integrable_cshift_gen H hcontH η hC hB hK hdecay (w.re : ℂ) Complex.I z.im w.im
  have e4 : (∫ y in z.im..w.im, (∫ p : ℝᵈ, H (cshift η ((z.re : ℂ) + (y : ℂ) * Complex.I) p)))
      = ∫ p : ℝᵈ, A4 p := by
    rw [hA4, intervalIntegral_integral_swap]
    exact integrable_cshift_gen H hcontH η hC hB hK hdecay (z.re : ℂ) Complex.I z.im w.im
  have hbdy :
      (∫ x in z.re..w.re, (∫ p : ℝᵈ, H (cshift η ((x : ℂ) + (z.im : ℂ) * Complex.I) p)))
      - (∫ x in z.re..w.re, (∫ p : ℝᵈ, H (cshift η ((x : ℂ) + (w.im : ℂ) * Complex.I) p)))
      + Complex.I • (∫ y in z.im..w.im, (∫ p : ℝᵈ, H (cshift η ((w.re : ℂ) + (y : ℂ) * Complex.I) p)))
      - Complex.I • (∫ y in z.im..w.im, (∫ p : ℝᵈ, H (cshift η ((z.re : ℂ) + (y : ℂ) * Complex.I) p)))
      = ∫ p : ℝᵈ, (((A1 - A2) + Complex.I • A3) - Complex.I • A4) p := by
    rw [e1, e2, e3, e4]
    symm
    have h12 : Integrable (fun p : ℝᵈ => A1 p - A2 p) volume := hm1.sub hm2
    have h3' : Integrable (fun p : ℝᵈ => Complex.I • A3 p) volume := hm3.smul Complex.I
    have h123 : Integrable (fun p : ℝᵈ => (A1 p - A2 p) + Complex.I • A3 p) volume := h12.add h3'
    have h4' : Integrable (fun p : ℝᵈ => Complex.I • A4 p) volume := hm4.smul Complex.I
    rw [← integral_sub hm1 hm2, ← integral_smul, ← integral_add h12 h3', ← integral_smul,
        ← integral_sub h123 h4']
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  rw [hbdy]
  have hzero : ∀ p : ℝᵈ, (((A1 - A2) + Complex.I • A3) - Complex.I • A4) p = 0 := by
    intro p
    show (∫ x in z.re..w.re, H (cshift η ((x : ℂ) + (z.im : ℂ) * Complex.I) p))
      - (∫ x in z.re..w.re, H (cshift η ((x : ℂ) + (w.im : ℂ) * Complex.I) p))
      + Complex.I • (∫ y in z.im..w.im, H (cshift η ((w.re : ℂ) + (y : ℂ) * Complex.I) p))
      - Complex.I • (∫ y in z.im..w.im, H (cshift η ((z.re : ℂ) + (y : ℂ) * Complex.I) p)) = 0
    exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (fun s : ℂ => H (cshift η s p)) z w
      ((hH.comp (differentiable_cshift_fixed η p)).differentiableOn)
  simp only [hzero, integral_zero]

theorem contour_shift (H : ℂᵈ → ℂ) (hH : Differentiable ℂ H) (η : ℝᵈ) {C K B : ℝ}
    (hC : 0 < C) (hB : 0 ≤ B) (hK : 0 < K)
    (hdecay : ∀ z : ℂᵈ,
      ‖H z‖ ≤ C * Real.exp (-(∑ i, (z i).re ^ 2) / K + B * (∑ i, (z i).im ^ 2))) :
    ∫ x : ℝᵈ, H (fun i => (x i : ℂ))
      = ∫ x : ℝᵈ, H (fun i => (x i : ℂ) + Complex.I * (η i : ℂ)) := by
  set G : ℂ → ℂ := fun s => ∫ x : ℝᵈ, H (cshift η s x) with hG
  have hcons : Complex.IsConservativeOn G Set.univ :=
    isConservativeOn_Gfun H hH η hC.le hB hK hdecay
  have hcont : Continuous G := continuous_Gfun H hH.continuous η hC.le hB hK hdecay
  have hGd : Differentiable ℂ G := by
    have hd : DifferentiableOn ℂ G Set.univ :=
      (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).mp
        ⟨hcons, hcont.continuousOn⟩
    rwa [differentiableOn_univ] at hd
  have hshift : ∀ t : ℝ,
      (fun y : ℝᵈ => cshift η (t : ℂ) (y + (-(t • η)))) = fun y => (fun i => (y i : ℂ)) := by
    intro t
    funext y i
    simp only [cshift_apply]
    simp
  have hreal : ∀ t : ℝ, G (t : ℂ) = ∫ y : ℝᵈ, H (fun i => (y i : ℂ)) := by
    intro t
    rw [hG]; simp only
    rw [(integral_add_right_eq_self (fun y : ℝᵈ => H (cshift η (t : ℂ) y)) (-(t • η))).symm]
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    funext i
    simp only [cshift_apply]
    simp
  have hI : G Complex.I = ∫ x : ℝᵈ, H (fun i => (x i : ℂ) + Complex.I * (η i : ℂ)) := by
    rw [hG]; simp only
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have h0 : G 0 = ∫ x : ℝᵈ, H (fun i => (x i : ℂ)) := by
    rw [hG]; simp only
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    funext i
    simp [cshift_apply]
  have hana : AnalyticOnNhd ℂ (fun z => G z - G 0) Set.univ :=
    ((hGd.sub (differentiable_const (c := G 0))).differentiableOn).analyticOnNhd isOpen_univ
  have hclosure : (0 : ℂ) ∈ closure ({z : ℂ | G z - G 0 = (0 : ℂ)} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.mem_ofPred_eq, hreal (ε / 2), h0, sub_self]
    · rw [Set.mem_singleton_iff]
      intro h
      have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h
      linarith
    · have hnorm : ‖(((ε / 2 : ℝ)) : ℂ)‖ = ε / 2 := by
        have h1 : ‖(((ε / 2 : ℝ)) : ℂ)‖ ^ 2 = (ε / 2) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
        nlinarith [norm_nonneg (((ε / 2 : ℝ)) : ℂ), h1]
      rw [dist_eq_norm, zero_sub, norm_neg, hnorm]
      linarith
  have hfinal : G Complex.I - G 0 = 0 :=
    AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure (z₀ := (0:ℂ))
      hana (analyticOnNhd_const (v := (0:ℂ)) (s := (Set.univ : Set ℂ)))
      isPreconnected_univ (Set.mem_univ 0) hclosure (Set.mem_univ Complex.I)
  rw [← h0, ← hI]
  exact (sub_eq_zero.mp hfinal).symm

def cvec (x : ℝᵈ) : ℂᵈ := fun i => (x i : ℂ)

noncomputable def imVec (z : ℂᵈ) : ℝᵈ := (EuclideanSpace.equiv (Fin d) ℝ).symm fun i => (z i).im

lemma norm_imVec (z : ℂᵈ) : Real.sqrt (∑ i, (z i).im ^ 2) = ‖imVec z‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [imVec, Real.norm_eq_abs, sq_abs]

lemma imVec_apply (z : ℂᵈ) (i : Fin d) : imVec z i = (z i).im := rfl

noncomputable def Hfun (F : ℂᵈ → ℂ) (M : ℝ) (ξ : ℝᵈ) (z : ℂᵈ) : ℂ :=
  F z * Complex.exp (-(∑ i, (z i) ^ 2) / ((M : ℂ) ^ 2))
      * Complex.exp (-(2 * Real.pi * Complex.I) * (∑ i, (ξ i : ℂ) * z i))

lemma Hfun_diff (F : ℂᵈ → ℂ) (hF : Differentiable ℂ F) (M : ℝ) (ξ : ℝᵈ) :
    Differentiable ℂ (Hfun F M ξ) := by
  unfold Hfun
  fun_prop

lemma neg_div_sq_re (M : ℝ) (c : ℂ) : (-c / ((M:ℂ)^2)).re = -c.re / M^2 := by
  rw [Complex.div_re, Complex.neg_re, Complex.neg_im]
  rw [← Complex.ofReal_pow M 2]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal, mul_zero, add_zero, zero_add]
  by_cases hM : M = 0
  · subst hM; simp
  · field_simp
    ring

lemma neg_div_sq_im (M : ℝ) (c : ℂ) : (-c / ((M:ℂ)^2)).im = -c.im / M^2 := by
  rw [Complex.div_im, Complex.neg_re, Complex.neg_im]
  rw [← Complex.ofReal_pow M 2]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal, mul_zero, add_zero, zero_add]
  by_cases hM : M = 0
  · subst hM; simp
  · field_simp
    ring

lemma neg_two_pi_I_mul_re (W : ℂ) :
    (-(2 * Real.pi * Complex.I) * W).re = 2 * Real.pi * W.im := by
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

lemma Hfun_shift_bound (F : ℂᵈ → ℂ) {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hgrowth : ∀ z : ℂᵈ, ‖F z‖ ≤ A * Real.exp (σ * Real.sqrt (∑ i, (z i).im ^ 2)))
    (M : ℝ) (hM : 0 < M) (ξ : ℝᵈ) (hξ : 0 < ‖ξ‖) (x : ℝᵈ) :
    ‖Hfun F M ξ (cshift ((-(M / ‖ξ‖)) • ξ) Complex.I x)‖
      ≤ A * Real.exp 1 * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M)
          * Real.exp (-(∑ i, (x i) ^ 2) / (M ^ 2)) := by
  set η : ℝᵈ := (-(M / ‖ξ‖)) • ξ with hη
  have hηnorm : ‖η‖ = M := by
    rw [hη, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hM hξ)]
    field_simp
  set z : ℂᵈ := cshift η Complex.I x with hz
  have hzi_re : ∀ i, (z i).re = x i := by intro i; rw [hz]; simp [cshift_re]
  have hzi_im : ∀ i, (z i).im = η i := by intro i; rw [hz]; simp [cshift_im]
  have hFr : ‖F z‖ ≤ A * Real.exp (σ * M) := by
    have h1 := hgrowth z
    rw [norm_imVec z] at h1
    have h2 : imVec z = η := by ext i; rw [imVec_apply, hzi_im]
    rwa [h2, hηnorm] at h1
  have hzsq_re : (∑ i, (z i) ^ 2).re = (∑ i, (x i) ^ 2) - M ^ 2 := by
    rw [Complex.re_sum]
    have hterm : ∀ i, ((z i) ^ 2).re = (x i) ^ 2 - (η i) ^ 2 := by
      intro i; rw [sq, sq, Complex.mul_re, hzi_re, hzi_im]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
      show (∑ i, (η i) ^ 2) = M ^ 2 from by rw [sum_sq_eq_norm_sq, hηnorm]]
  have hWim : (∑ i, (ξ i : ℂ) * z i).im = -(M * ‖ξ‖) := by
    rw [Complex.im_sum]
    have hterm : ∀ i, ((ξ i : ℂ) * z i).im = ξ i * η i := by
      intro i
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hzi_im]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have hinner : ∑ i, ξ i * η i = -(M / ‖ξ‖) * (∑ i, (ξ i) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [show η i = -(M / ‖ξ‖) * ξ i from by rw [hη]; simp]
      ring
    rw [hinner, sum_sq_eq_norm_sq]
    field_simp
  have hGauss : ‖Complex.exp (-(∑ i, (z i) ^ 2) / ((M:ℂ)^2))‖
      = Real.exp (1 - (∑ i, (x i) ^ 2) / M ^ 2) := by
    rw [Complex.norm_exp, neg_div_sq_re, hzsq_re]
    congr 1
    field_simp
    ring
  have hOsc : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (∑ i, (ξ i : ℂ) * z i))‖
      = Real.exp (-(2 * Real.pi * ‖ξ‖) * M) := by
    rw [Complex.norm_exp, neg_two_pi_I_mul_re, hWim]
    congr 1
    ring
  calc ‖Hfun F M ξ z‖
      = ‖F z‖ * ‖Complex.exp (-(∑ i, (z i) ^ 2) / ((M:ℂ)^2))‖
          * ‖Complex.exp (-(2 * Real.pi * Complex.I) * (∑ i, (ξ i : ℂ) * z i))‖ := by
        rw [Hfun]; simp only [norm_mul]
    _ ≤ (A * Real.exp (σ * M)) * Real.exp (1 - (∑ i, (x i) ^ 2) / M ^ 2)
          * Real.exp (-(2 * Real.pi * ‖ξ‖) * M) := by
        rw [hGauss, hOsc]; gcongr
    _ = A * Real.exp 1 * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M)
          * Real.exp (-(∑ i, (x i) ^ 2) / M ^ 2) := by
        rw [show (A * Real.exp (σ * M)) * Real.exp (1 - (∑ i, (x i) ^ 2) / M ^ 2)
              * Real.exp (-(2 * Real.pi * ‖ξ‖) * M)
            = A * (Real.exp (σ * M) * Real.exp (1 - (∑ i, (x i) ^ 2) / M ^ 2)
              * Real.exp (-(2 * Real.pi * ‖ξ‖) * M)) from by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        rw [show Real.exp (σ * M + (1 - (∑ i, (x i) ^ 2) / M ^ 2) + -(2 * Real.pi * ‖ξ‖) * M)
            = Real.exp (1 + (-(2 * Real.pi * ‖ξ‖ - σ) * M) + -(∑ i, (x i) ^ 2) / M ^ 2) from by
          congr 1; ring]
        rw [Real.exp_add, Real.exp_add]
        ring

lemma sqrt_gaussian_integral (M : ℝ) (hM : 0 < M) :
    ∫ x : ℝᵈ, Real.exp (-(∑ i, (x i) ^ 2) / (M ^ 2)) = (M * Real.sqrt Real.pi) ^ d := by
  have hb : 0 < (1 / M ^ 2 : ℝ) := by positivity
  have h1 : ∫ x : ℝᵈ, Real.exp (-(1 / M ^ 2) * ‖x‖ ^ 2)
      = (Real.pi / (1/M^2)) ^ ((d:ℝ)/2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace, Fintype.card_fin]
  have h2 : Real.pi / (1 / M^2) = (M * Real.sqrt Real.pi)^2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_nonneg]; field_simp
  have h3 : ((M * Real.sqrt Real.pi)^2 : ℝ) ^ ((d:ℝ)/2) = (M * Real.sqrt Real.pi)^d := by
    rw [← Real.rpow_natCast (M * Real.sqrt Real.pi) 2, ← Real.rpow_mul (by positivity),
      show (((2:ℕ):ℝ)) * ((d:ℝ)/2) = (d:ℝ) by push_cast; ring,
      Real.rpow_natCast (M * Real.sqrt Real.pi) d]
  rw [h2, h3] at h1
  rw [← h1]
  apply integral_congr_ae
  filter_upwards with x
  rw [sum_sq_eq_norm_sq]
  congr 1
  ring

lemma sqrt_gaussian_integrable (M : ℝ) (hM : 0 < M) :
    Integrable (fun x : ℝᵈ => Real.exp (-(∑ i, (x i) ^ 2) / (M ^ 2))) volume := by
  have h := sum_sq_gauss (d := d) (M^2/2) (by positivity)
  refine h.congr ?_
  filter_upwards with x
  rw [show 2 * (M ^ 2 / 2) = M^2 by ring]

lemma Hfun_integral_bound (F : ℂᵈ → ℂ) (hF : Differentiable ℂ F)
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hgrowth : ∀ z : ℂᵈ, ‖F z‖ ≤ A * Real.exp (σ * Real.sqrt (∑ i, (z i).im ^ 2)))
    (M : ℝ) (hM : 0 < M) (ξ : ℝᵈ) (hξ : 0 < ‖ξ‖) :
    ‖∫ x : ℝᵈ, Hfun F M ξ (cvec x)‖
      ≤ A * Real.exp 1 * (M * Real.sqrt Real.pi) ^ d
          * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M) := by
  set η : ℝᵈ := (-(M / ‖ξ‖)) • ξ with hη
  have hηnorm : ‖η‖ = M := by
    rw [hη, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hM hξ)]
    field_simp
  have hdecay : ∀ z : ℂᵈ, ‖Hfun F M ξ z‖ ≤
      (A * Real.exp σ * Real.exp (2 * Real.pi * ‖ξ‖)) *
        Real.exp (-(∑ i, (z i).re ^ 2) / (M^2)
          + (σ + 2 * Real.pi * ‖ξ‖ + 1 / M^2) * (∑ i, (z i).im ^ 2)) := by
    intro z
    have hSnn : 0 ≤ ∑ i, (z i).im ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hle : Real.sqrt (∑ i, (z i).im ^ 2) ≤ 1 + ∑ i, (z i).im ^ 2 := by
      nlinarith [Real.sq_sqrt hSnn, Real.sqrt_nonneg (∑ i, (z i).im ^ 2)]
    have hFb : ‖F z‖ ≤ A * Real.exp σ * Real.exp (σ * (∑ i, (z i).im ^ 2)) := by
      calc ‖F z‖ ≤ A * Real.exp (σ * Real.sqrt (∑ i, (z i).im ^ 2)) := hgrowth z
        _ ≤ A * Real.exp (σ * (1 + ∑ i, (z i).im ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hA.le
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hσ.le)
        _ = A * Real.exp σ * Real.exp (σ * (∑ i, (z i).im ^ 2)) := by
            rw [mul_add, mul_one, Real.exp_add]; ring
    have hGb : ‖Complex.exp (-(∑ i, (z i) ^ 2) / ((M:ℂ)^2))‖
        ≤ Real.exp (-(∑ i, (z i).re ^ 2) / (M^2) + (∑ i, (z i).im ^ 2) / (M^2)) := by
      rw [Complex.norm_exp, neg_div_sq_re]
      apply Real.exp_le_exp.mpr
      have hre : (∑ i, (z i)^2).re = (∑ i, (z i).re^2) - (∑ i, (z i).im^2) := by
        rw [Complex.re_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [sq, sq, Complex.mul_re]; ring
      rw [hre]
      exact le_of_eq (by ring)
    have hOb : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (∑ i, (ξ i : ℂ) * z i))‖
        ≤ Real.exp (2 * Real.pi * ‖ξ‖) * Real.exp (2 * Real.pi * ‖ξ‖ * (∑ i, (z i).im ^ 2)) := by
      rw [Complex.norm_exp, neg_two_pi_I_mul_re]
      have him : (∑ i, (ξ i : ℂ) * z i).im = ∑ i, ξ i * (z i).im := by
        rw [Complex.im_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rw [him]
      have hcs : ∑ i, ξ i * (z i).im ≤ Real.sqrt (∑ i, (ξ i)^2) * Real.sqrt (∑ i, (z i).im^2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ξ i) (fun i => (z i).im)
      have hsq : Real.sqrt (∑ i, (ξ i)^2) = ‖ξ‖ := by
        rw [sum_sq_eq_norm_sq, Real.sqrt_sq (norm_nonneg ξ)]
      rw [hsq] at hcs
      have h2 : 2 * Real.pi * (∑ i, ξ i * (z i).im)
          ≤ 2 * Real.pi * (‖ξ‖ * (1 + ∑ i, (z i).im^2)) := by
        have h4 : ∑ i, ξ i * (z i).im ≤ ‖ξ‖ * (1 + ∑ i, (z i).im^2) :=
          le_trans hcs (mul_le_mul_of_nonneg_left hle (norm_nonneg ξ))
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
      calc Real.exp (2 * Real.pi * ∑ i, ξ i * (z i).im)
          ≤ Real.exp (2 * Real.pi * (‖ξ‖ * (1 + ∑ i, (z i).im^2))) := Real.exp_le_exp.mpr h2
        _ = Real.exp (2 * Real.pi * ‖ξ‖) * Real.exp (2 * Real.pi * ‖ξ‖ * (∑ i, (z i).im^2)) := by
            rw [show 2 * Real.pi * (‖ξ‖ * (1 + ∑ i, (z i).im^2))
                = 2 * Real.pi * ‖ξ‖ + 2 * Real.pi * ‖ξ‖ * (∑ i, (z i).im^2) by ring,
              Real.exp_add]
    calc ‖Hfun F M ξ z‖
        = ‖F z‖ * ‖Complex.exp (-(∑ i, (z i) ^ 2) / ((M:ℂ)^2))‖
            * ‖Complex.exp (-(2 * Real.pi * Complex.I) * (∑ i, (ξ i : ℂ) * z i))‖ := by
          rw [Hfun]; simp only [norm_mul]
      _ ≤ (A * Real.exp σ * Real.exp (σ * (∑ i, (z i).im^2)))
            * Real.exp (-(∑ i, (z i).re^2)/(M^2) + (∑ i, (z i).im^2)/(M^2))
            * (Real.exp (2 * Real.pi * ‖ξ‖) * Real.exp (2 * Real.pi * ‖ξ‖ * (∑ i, (z i).im^2))) := by
          exact mul_le_mul (mul_le_mul hFb hGb (norm_nonneg _) (by positivity)) hOb
            (by positivity) (by positivity)
      _ = (A * Real.exp σ * Real.exp (2 * Real.pi * ‖ξ‖))
            * Real.exp (-(∑ i, (z i).re^2)/(M^2)
              + (σ + 2 * Real.pi * ‖ξ‖ + 1/M^2) * (∑ i, (z i).im^2)) := by
          rw [show -(∑ i, (z i).re^2)/(M^2) + (σ + 2*Real.pi*‖ξ‖ + 1/M^2)*(∑ i, (z i).im^2)
              = σ * (∑ i, (z i).im^2)
                + (2*Real.pi*‖ξ‖*(∑ i, (z i).im^2))
                + (-(∑ i, (z i).re^2)/(M^2) + (∑ i, (z i).im^2)/(M^2)) by ring]
          simp only [Real.exp_add]
          ring
  have hHdiff : Differentiable ℂ (Hfun F M ξ) := Hfun_diff F hF M ξ
  have hsh := contour_shift (Hfun F M ξ) hHdiff η
    (C := A * Real.exp σ * Real.exp (2 * Real.pi * ‖ξ‖))
    (B := σ + 2 * Real.pi * ‖ξ‖ + 1 / M^2) (K := M^2)
    (by positivity) (by positivity) (by positivity) hdecay
  have hEq : (fun x : ℝᵈ => Hfun F M ξ (cvec x))
      = (fun x => Hfun F M ξ (fun i => (x i : ℂ))) := by funext x; rfl
  rw [hEq, hsh]
  calc ‖∫ x : ℝᵈ, Hfun F M ξ (fun i => (x i : ℂ) + Complex.I * (η i : ℂ))‖
      ≤ ∫ x : ℝᵈ, ‖Hfun F M ξ (fun i => (x i : ℂ) + Complex.I * (η i : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝᵈ, (A * Real.exp 1 * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M))
          * Real.exp (-(∑ i, (x i) ^ 2) / (M ^ 2)) := by
        apply integral_mono_of_nonneg
        · filter_upwards with x; positivity
        · exact (sqrt_gaussian_integrable M hM).const_mul _
        · filter_upwards with x
          exact Hfun_shift_bound F hσ hA hgrowth M hM ξ hξ x
    _ = (A * Real.exp 1 * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M))
          * ∫ x : ℝᵈ, Real.exp (-(∑ i, (x i) ^ 2) / (M ^ 2)) := by
        rw [integral_const_mul]
    _ = A * Real.exp 1 * (M * Real.sqrt Real.pi) ^ d
          * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M) := by
        rw [sqrt_gaussian_integral M hM]; ring


theorem fourier_Lp_ae_eq_zero_of_entire_growth {d : ℕ} (σ A : ℝ) (hσ : 0 < σ) (hA : 0 < A)
    (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (hgrowth : ∀ z : Fin d → ℂ,
      ‖F z‖ ≤ A * Real.exp (σ * Real.sqrt (∑ i, (z i).im ^ 2)))
    (g : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hg : g =ᵐ[MeasureTheory.volume] fun x : EuclideanSpace ℝ (Fin d) => F (fun i => (x i : ℂ))) :
    ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      σ / (2 * Real.pi) < ‖ξ‖ →
      ((FourierTransform.fourier g :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0 := by
  set f : ℝᵈ → ℂ := fun x => F (cvec x) with hfdef
  have hfmem0 : MemLp (fun x : ℝᵈ => F (fun i => (x i : ℂ))) 2 (volume : Measure ℝᵈ) :=
    (Lp.memLp g).ae_eq hg
  have hfmem : MemLp f 2 (volume : Measure ℝᵈ) := hfmem0
  have hfbound : ∀ x : ℝᵈ, ‖f x‖ ≤ A := by
    intro x
    change ‖F (cvec x)‖ ≤ A
    have h := hgrowth (cvec x)
    simpa [cvec] using h
  have htoLp : hfmem.toLp f = g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp hfmem, hg] with x hx hgx
    rw [hx, hgx]
    rfl
  set M : ℕ → ℝ := fun n => (n : ℝ) + 1 with hMdef
  set gn : ℕ → ℝᵈ → ℂ := fun n x =>
    f x * (Real.exp (-(∑ i, (x i) ^ 2) / (M n) ^ 2) : ℂ) with hgndef
  have hconv := Commons.Analysis.MeasureTheory.tendsto_eLpNorm_mul_exp_neg_sq (f := f) hfmem
  have gauss_le_one : ∀ (n : ℕ) (x : ℝᵈ),
      Real.exp (-(∑ i, (x i) ^ 2) / (M n) ^ 2) ≤ 1 := by
    intro n x
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => sq_nonneg _))) (by positivity)
  have hgm : ∀ n : ℕ, MemLp (gn n) 2 (volume : Measure ℝᵈ) := by
    intro n
    refine hfmem.of_le (hfmem.aestronglyMeasurable.mul (by fun_prop)) ?_
    filter_upwards with x
    simp only [hgndef, norm_mul]
    rw [show ‖(↑(Real.exp (-(∑ i, (x i) ^ 2) / (M n) ^ 2)) : ℂ)‖
          = Real.exp (-(∑ i, (x i) ^ 2) / (M n) ^ 2) from by
      rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]]
    calc ‖f x‖ * Real.exp (-(∑ i, (x i) ^ 2) / (M n) ^ 2)
        ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (gauss_le_one n x) (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  have hLpT : Tendsto (fun n : ℕ => (hgm n).toLp (gn n)) atTop (𝓝 (hfmem.toLp f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hkey : ∀ n : ℕ, ‖(hgm n).toLp (gn n) - hfmem.toLp f‖
        = (MeasureTheory.eLpNorm (gn n - f) 2 (volume : Measure ℝᵈ)).toReal := by
      intro n
      rw [← MemLp.toLp_sub (hgm n) hfmem, Lp.norm_toLp]
    simp only [hkey]
    have hc := hconv
    simp only [hgndef] at hc
    refine (ENNReal.tendsto_toReal ?_).comp hc
    simp
  have hLpT' : Tendsto (fun n : ℕ => 𝓕 ((hgm n).toLp (gn n))) atTop (𝓝 (𝓕 g)) := by
    have hcont : Continuous (𝓕 : Lp ℂ 2 (volume : Measure ℝᵈ) → Lp ℂ 2 (volume : Measure ℝᵈ)) :=
      ContinuousFourier.continuous_fourier
    have h1 : Tendsto (fun n : ℕ => 𝓕 ((hgm n).toLp (gn n))) atTop (𝓝 (𝓕 (hfmem.toLp f))) :=
      hcont.continuousAt.tendsto.comp hLpT
    rwa [htoLp] at h1
  have htim := MeasureTheory.tendstoInMeasure_of_tendsto_Lp (p := 2) (μ := (volume : Measure ℝᵈ)) hLpT'
  obtain ⟨ns, hns_mono, hns_ae⟩ := htim.exists_seq_tendsto_ae
  have h1m : ∀ n : ℕ, MemLp (gn (ns n)) 1 (volume : Measure ℝᵈ) := by
    intro n
    rw [MeasureTheory.memLp_one_iff_integrable]
    refine Integrable.mono'
      ((sum_sq_gauss (d := d) ((M (ns n))^2/2) (by positivity)).const_mul A)
      ((hgm (ns n)).aestronglyMeasurable) ?_
    filter_upwards with x
    simp only [hgndef, norm_mul]
    rw [show ‖(↑(Real.exp (-(∑ i, (x i) ^ 2) / (M (ns n)) ^ 2)) : ℂ)‖
          = Real.exp (-(∑ i, (x i) ^ 2) / (M (ns n)) ^ 2) from by
      rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]]
    calc ‖f x‖ * Real.exp (-(∑ i, (x i) ^ 2) / (M (ns n)) ^ 2)
        ≤ A * Real.exp (-(∑ i, (x i) ^ 2) / (M (ns n)) ^ 2) :=
          mul_le_mul_of_nonneg_right (hfbound x) (Real.exp_nonneg _)
      _ = A * Real.exp (-(∑ i, (x i) ^ 2) / (2 * ((M (ns n))^2/2))) := by
          rw [show 2 * ((M (ns n))^2/2) = (M (ns n))^2 by ring]
  have hid : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ∀ n : ℕ, ((𝓕 ((hgm (ns n)).toLp (gn (ns n))) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ
        = 𝓕 (gn (ns n)) ξ := by
    have h : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ∀ n : ℕ,
        ((𝓕 ((hgm (ns n)).toLp (gn (ns n))) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ
          = 𝓕 (gn (ns n)) ξ := by
      rw [ae_all_iff]
      intro n
      exact Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral (h1m n) (hgm (ns n))
    exact h
  filter_upwards [hns_ae, hid] with ξ hξ_tend hξid
  intro hξR
  refine tendsto_nhds_unique hξ_tend ?_
  have hrepr : ∀ n : ℕ, 𝓕 (gn (ns n)) ξ
      = ∫ x : ℝᵈ, Hfun F (M (ns n)) ξ (cvec x) := by
    intro n
    rw [Real.fourier_eq', hgndef, hfdef]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Hfun, cvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    have hS : (-2 * (Real.pi : ℂ) * (∑ i, (ξ i : ℂ) * (x i : ℂ))) * Complex.I
        = -(2 * (Real.pi : ℂ) * Complex.I) * (∑ i, (ξ i : ℂ) * (x i : ℂ)) := by ring
    rw [hS]
    ring
  have hbound : ∀ n : ℕ, ‖𝓕 (gn (ns n)) ξ‖ ≤
      A * Real.exp 1 * (M (ns n) * Real.sqrt Real.pi) ^ d
        * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M (ns n)) := by
    intro n
    rw [hrepr n]
    refine Hfun_integral_bound F hF hσ hA hgrowth (M (ns n)) (by positivity) ξ ?_
    have hpos : 0 < σ / (2 * Real.pi) := div_pos hσ (by positivity)
    linarith
  have hg_lim : Tendsto (fun n : ℕ => A * Real.exp 1 * (M (ns n) * Real.sqrt Real.pi) ^ d
      * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M (ns n))) atTop (𝓝 0) := by
    have hc : 0 < 2 * Real.pi * ‖ξ‖ - σ := by
      have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
      have hlt := (div_lt_iff₀ h2pi).mp hξR
      nlinarith [hlt, norm_nonneg ξ]
    have hMtop : Tendsto (fun n : ℕ => M (ns n)) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => (ns n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop hns_mono)
      simpa [hMdef] using tendsto_atTop_add_const_right atTop 1 h1
    have hsub : Tendsto (fun n : ℕ => (2 * Real.pi * ‖ξ‖ - σ) * M (ns n)) atTop atTop :=
      Tendsto.const_mul_atTop hc hMtop
    have hcomp : Tendsto (fun n : ℕ => ((2 * Real.pi * ‖ξ‖ - σ) * M (ns n)) ^ d
        * Real.exp (-((2 * Real.pi * ‖ξ‖ - σ) * M (ns n)))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp hsub
    have h2 : Tendsto (fun n : ℕ => (M (ns n)) ^ d
        * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M (ns n))) atTop (𝓝 0) := by
      have h3 := hcomp.const_mul ((2 * Real.pi * ‖ξ‖ - σ)⁻¹ ^ d)
      rw [mul_zero] at h3
      refine h3.congr' ?_
      filter_upwards with n
      have hthis : (2 * Real.pi * ‖ξ‖ - σ)⁻¹ * ((2 * Real.pi * ‖ξ‖ - σ) * M (ns n)) = M (ns n) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      rw [← mul_assoc, ← mul_pow, hthis]
      congr 1
      ring
    have h4 : Tendsto (fun n : ℕ => A * Real.exp 1 * (Real.sqrt Real.pi) ^ d
        * ((M (ns n)) ^ d * Real.exp (-(2 * Real.pi * ‖ξ‖ - σ) * M (ns n)))) atTop (𝓝 0) := by
      have := h2.const_mul (A * Real.exp 1 * (Real.sqrt Real.pi) ^ d)
      rwa [mul_zero] at this
    refine h4.congr' ?_
    filter_upwards with n
    rw [mul_pow]; ring
  exact squeeze_zero_norm (fun n => by rw [hξid n]; exact hbound n) hg_lim

end Commons.Analysis.Fourier