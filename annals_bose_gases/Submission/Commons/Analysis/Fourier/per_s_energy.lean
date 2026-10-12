import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Commons.Analysis.Fourier.gaussian_heat_ft
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace SchwartzMap FourierTransform ComplexConjugate
open Complex hiding exp

namespace Commons.Analysis.Fourier

abbrev V3 := EuclideanSpace ℝ (Fin 3)

def gaussR (s : ℝ) (q : V3) : ℝ := Real.exp (-(Real.pi * s * ‖q‖ ^ 2))
def heatR (s : ℝ) (z : V3) : ℝ := s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z‖ ^ 2) / s)
def gaussC (s : ℝ) (q : V3) : ℂ := cexp (-(↑(Real.pi * s) * (↑‖q‖ : ℂ) ^ 2))
def heatC (s : ℝ) (z : V3) : ℂ :=
  (↑(s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(↑(Real.pi / s) * (↑‖z‖ : ℂ) ^ 2))

lemma gaussR_eq (s : ℝ) (q : V3) : (gaussR s q : ℂ) = gaussC s q := by
  unfold gaussR gaussC
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma heatR_eq (s : ℝ) (z : V3) : (heatR s z : ℂ) = heatC s z := by
  unfold heatR heatC
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma kernel_ft (s : ℝ) (hs : 0 < s) (z : V3) :
    (∫ q : V3, gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, z⟫) : ℂ) * Complex.I)) = heatC s z := by
  unfold gaussC heatC
  exact gaussian_heat_ft hs z

lemma gaussC_integrable (s : ℝ) (hs : 0 < s) : Integrable (fun q : V3 => gaussC s q) := by
  have hI := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V3)
    (b := (↑(Real.pi * s) : ℂ)) (show 0 < ((↑(Real.pi * s) : ℂ).re) by simp [Real.pi_pos, hs])
    (c := (0 : ℂ)) (w := (0 : V3))
  simpa [gaussC] using hI

lemma gaussC_continuous (s : ℝ) : Continuous (fun q : V3 => gaussC s q) := by
  dsimp [gaussC]
  fun_prop

lemma cexp_norm_eq_one (x : ℝ) : ‖cexp (↑x * I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma char_split (q x y : V3) :
    cexp ((↑(2 * Real.pi * ⟪q, x - y⟫) : ℂ) * Complex.I) =
      cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) *
        cexp (-((↑(2 * Real.pi * ⟪q, y⟫) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_sub_right]
  push_cast
  ring

lemma ft_eq_integral_cexp (g : V3 → ℂ) (q : V3) :
    (∫ y : V3, g y * cexp (-((↑(2 * Real.pi * ⟪q, y⟫) : ℂ) * Complex.I)))
      = 𝓕 g q := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  rw [smul_eq_mul]
  have hE : cexp (-((↑(2 * Real.pi * ⟪q, y⟫) : ℂ) * Complex.I)) =
      cexp ((↑(-2 * Real.pi * ⟪y, q⟫) : ℂ) * Complex.I) := by
    congr 1
    rw [real_inner_comm y q]
    push_cast
    ring
  rw [hE, mul_comm]

lemma ft_neg_eq_integral_cexp (g : V3 → ℂ) (q : V3) :
    (∫ x : V3, g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I))
      = 𝓕 g (-q) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  have hE : cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) =
      cexp ((↑(-2 * Real.pi * ⟪x, -q⟫) : ℂ) * Complex.I) := by
    congr 1
    rw [← real_inner_comm q x, inner_neg_right x q]
    push_cast
    ring
  rw [hE, mul_comm]

lemma ft_norm_le (g : V3 → ℂ) (q : V3) (hg : Integrable g) : ‖𝓕 g q‖ ≤ ∫ y, ‖g y‖ := by
  rw [Real.fourier_eq]
  calc
    ‖∫ y : V3, 𝐞 (-⟪y, q⟫) • g y‖ ≤ ∫ y : V3, ‖𝐞 (-⟪y, q⟫) • g y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : V3, ‖g y‖ := by
      apply integral_congr_ae
      filter_upwards with y
      simp

def kernelDouble (g : V3 → ℂ) (s : ℝ) (x : V3) (y q : V3) : ℂ :=
  g y * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x - y⟫) : ℂ) * Complex.I))

lemma kernelDouble_integrable {g : V3 → ℂ} (hg : Integrable g) (s : ℝ) (hs : 0 < s) (x : V3) :
    Integrable (fun p : V3 × V3 =>
      g p.1 * (gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, x - p.1⟫) : ℂ) * Complex.I)))
      (volume.prod volume) := by
  have hb : Integrable (fun p : V3 × V3 => ‖g p.1‖ * ‖gaussC s p.2‖) (volume.prod volume) :=
    (hg.norm.mul_prod (gaussC_integrable s hs).norm)
  refine hb.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : V3 × V3 => g p.1) (volume.prod volume) := hg.1.comp_fst
    have hcont : Continuous (fun p : V3 × V3 =>
        gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, x - p.1⟫) : ℂ) * Complex.I)) := by
      dsimp [gaussC]
      fun_prop
    exact h1.mul hcont.aestronglyMeasurable
  · filter_upwards with p
    calc
      ‖g p.1 * (gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, x - p.1⟫) : ℂ) * Complex.I))‖
          ≤ ‖g p.1‖ * ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, x - p.1⟫) : ℂ) * Complex.I)‖ := by
            exact norm_mul_le _ _
      _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * ‖cexp ((↑(2 * Real.pi * ⟪p.2, x - p.1⟫) : ℂ) * Complex.I)‖) := by
            gcongr
            exact norm_mul_le _ _
      _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * 1) := by
            gcongr
            exact le_of_eq (cexp_norm_eq_one (2 * Real.pi * ⟪p.2, x - p.1⟫))
      _ = ‖g p.1‖ * ‖gaussC s p.2‖ := by ring

lemma inner_heat_eq {g : V3 → ℂ} (hg : Integrable g) {s : ℝ} (hs : 0 < s) (x : V3) :
    (∫ y : V3, g y * heatC s (x - y))
      = ∫ q : V3, gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q) := by
  -- substitute the heat kernel by its Fourier representation, pointwise in y
  have hsub : (fun y : V3 => g y * heatC s (x - y)) = fun y => (∫ q : V3,
      g y * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x - y⟫) : ℂ) * Complex.I))) := by
    funext y
    rw [← kernel_ft s hs (x - y)]
    rw [← MeasureTheory.integral_const_mul (g y)]
  calc
    (∫ y : V3, g y * heatC s (x - y))
        = ∫ y : V3, (∫ q : V3,
            g y * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x - y⟫) : ℂ) * Complex.I))) := by
          rw [hsub]
    _ = ∫ q : V3, (∫ y : V3,
            g y * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x - y⟫) : ℂ) * Complex.I))) := by
          rw [integral_integral_swap (kernelDouble_integrable hg s hs x)]
    _ = ∫ q : V3, gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q) := by
          apply integral_congr_ae
          filter_upwards with q
          calc
            (∫ y : V3,
                g y * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x - y⟫) : ℂ) * Complex.I)))
                = ∫ y : V3,
                    gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) *
                      (g y * cexp (-((↑(2 * Real.pi * ⟪q, y⟫) : ℂ) * Complex.I))) := by
                  apply integral_congr_ae
                  filter_upwards with y
                  rw [char_split q x y]
                  ring
            _ = gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) *
                  (∫ y : V3, g y * cexp (-((↑(2 * Real.pi * ⟪q, y⟫) : ℂ) * Complex.I))) := by
                  exact MeasureTheory.integral_const_mul
                    (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I))
                    (fun y : V3 => g y * cexp (-((↑(2 * Real.pi * ⟪q, y⟫) : ℂ) * Complex.I)))
            _ = gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q) := by
                  rw [ft_eq_integral_cexp]

lemma outer_integrable {g : V3 → ℂ} (hg : Integrable g) (hĝ : Integrable (fun q : V3 => 𝓕 g q))
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun p : V3 × V3 =>
      g p.1 * (gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2))
      (volume.prod volume) := by
  let C : ℝ := ∫ y : V3, ‖g y‖
  have hC : 0 ≤ C := integral_nonneg (by intro y; exact norm_nonneg _)
  have hb : Integrable (fun p : V3 × V3 => C * (‖g p.1‖ * ‖gaussC s p.2‖))
      (volume.prod volume) := by
    have hprod : Integrable (fun p : V3 × V3 => ‖g p.1‖ * ‖gaussC s p.2‖) (volume.prod volume) :=
      (hg.norm.mul_prod (gaussC_integrable s hs).norm)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod.const_mul C
  refine hb.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : V3 × V3 => g p.1) (volume.prod volume) := hg.1.comp_fst
    have hcont : Continuous (fun p : V3 × V3 =>
        gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)) := by
      dsimp [gaussC]
      fun_prop
    have h3 : AEStronglyMeasurable (fun p : V3 × V3 => 𝓕 g p.2) (volume.prod volume) := hĝ.1.comp_snd
    exact h1.mul (hcont.aestronglyMeasurable.mul h3)
  · filter_upwards with p
    calc
      ‖g p.1 * (gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2)‖
          ≤ ‖g p.1‖ * ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2‖ := by
            exact norm_mul_le _ _
      _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * ‖𝓕 g p.2‖) := by
            have h1 : ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2‖
                ≤ ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖ * ‖𝓕 g p.2‖ := by
                  exact norm_mul_le _ _
            have h2 : ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖
                ≤ ‖gaussC s p.2‖ := by
                  calc
                    ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖
                        ≤ ‖gaussC s p.2‖ * ‖cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖ := by
                          exact norm_mul_le _ _
                    _ = ‖gaussC s p.2‖ := by
                          rw [cexp_norm_eq_one (2 * Real.pi * ⟪p.2, p.1⟫)]
                          ring
            calc
              ‖g p.1‖ * ‖gaussC s p.2 * cexp _ * 𝓕 g p.2‖
                  ≤ ‖g p.1‖ * (‖gaussC s p.2 * cexp _‖ * ‖𝓕 g p.2‖) := by
                    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
              _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * ‖𝓕 g p.2‖) := by
                    gcongr
      _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * C) := by
            gcongr
            exact ft_norm_le g p.2 hg
      _ = C * (‖g p.1‖ * ‖gaussC s p.2‖) := by
            ring

lemma position_eq_momentum {g : V3 → ℂ} (hg : Integrable g) (hĝ : Integrable (fun q : V3 => 𝓕 g q))
    {s : ℝ} (hs : 0 < s) :
    (∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y)))
      = ∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q := by
  calc
    (∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y)))
        = ∫ x : V3, g x *
            (∫ q : V3, gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [inner_heat_eq hg hs x]
    _ = ∫ x : V3, ∫ q : V3,
            g x * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← MeasureTheory.integral_const_mul (g x)]
    _ = ∫ q : V3, ∫ x : V3,
            g x * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)) := by
          rw [integral_integral_swap (outer_integrable hg hĝ s hs)]
    _ = ∫ q : V3, gaussC s q * (𝓕 g q) *
            (∫ x : V3, g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I)) := by
          apply integral_congr_ae
          filter_upwards with q
          calc
            (∫ x : V3,
                g x * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)))
                = ∫ x : V3,
                    (gaussC s q * 𝓕 g q) * (g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I)) := by
                  apply integral_congr_ae
                  filter_upwards with x
                  ring
            _ = (gaussC s q * 𝓕 g q) *
                  (∫ x : V3, g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I)) := by
                  exact MeasureTheory.integral_const_mul (gaussC s q * 𝓕 g q)
                    (fun x : V3 => g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I))
    _ = ∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q := by
          apply integral_congr_ae
          filter_upwards with q
          rw [ft_neg_eq_integral_cexp]
          ring

theorem per_s_energy_complex {g : V3 → ℂ} (hg : Integrable g) (hĝ : Integrable (fun q : V3 => 𝓕 g q))
    {s : ℝ} (hs : 0 < s) :
    (∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q)
      = (∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y))) :=
  (position_eq_momentum hg hĝ hs).symm


lemma complex_eq_ofReal_iff_im_eq_zero {z : ℂ} : z = (z.re : ℂ) ↔ z.im = 0 := by
  constructor
  · intro h
    rw [h, ofReal_im]
  · intro hz
    apply Complex.ext <;> simp [hz]

lemma ofReal_re_eq_self_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  (complex_eq_ofReal_iff_im_eq_zero.mpr hz)

lemma conj_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} (h : α → ℂ) :
    conj (∫ x, h x ∂μ) = ∫ x, conj (h x) ∂μ := by
  simpa using (LinearIsometry.integral_comp_comm conjLIE.toLinearIsometry h).symm

lemma conj_cexp_apply (z : ℂ) : conj (cexp z) = cexp (conj z) := by
  rw [← Complex.exp_conj]

lemma ofReal_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} (h : α → ℝ) :
    (↑(∫ x, h x ∂μ) : ℂ) = ∫ x, (h x : ℂ) ∂μ := by
  simpa using (LinearIsometry.integral_comp_comm (E := ℝ) (F := ℂ) ofRealLI h).symm

lemma conj_ofReal_mul_I (r : ℝ) : conj ((r : ℂ) * I) = -(r : ℂ) * I := by
  rw [map_mul, conj_ofReal, conj_I]
  ring

lemma fourier_neg_eq_conj_of_real_valued {f : V3 → ℂ} (hf : ∀ x : V3, (f x).im = 0) (q : V3) :
    (𝓕 f) (-q) = conj ((𝓕 f) q) := by
  rw [← Real.fourierInv_eq_fourier_neg]
  rw [Real.fourierInv_eq', Real.fourier_eq', conj_integral]
  apply integral_congr_ae
  filter_upwards with v
  have hfr : conj (f v) = f v := by
    rw [ofReal_re_eq_self_of_im_eq_zero (hf v), conj_ofReal]
  rw [smul_eq_mul, smul_eq_mul, map_mul, conj_cexp_apply, conj_ofReal_mul_I, hfr]
  congr 1
  congr 1
  rw [real_inner_comm q v]
  push_cast
  ring


lemma complex_norm_sq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  have h : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  calc
    ((‖z‖ ^ 2 : ℝ) : ℂ) = (Complex.normSq z : ℂ) := by rw [h]
    _ = conj z * z := Complex.normSq_eq_conj_mul_self
    _ = z * conj z := by ring

lemma momentum_cast {f : V3 → ℂ} (hf : ∀ x : V3, (f x).im = 0) (s : ℝ) (q : V3) :
    (((‖𝓕 f q‖ ^ 2) * gaussR s q : ℝ) : ℂ) = (𝓕 f q) * (𝓕 f (-q)) * gaussC s q := by
  rw [Complex.ofReal_mul]
  rw [complex_norm_sq_mul_conj]
  rw [gaussR_eq]
  rw [← fourier_neg_eq_conj_of_real_valued hf q]

lemma inner_real_cast {f : V3 → ℂ} (hf : ∀ x : V3, (f x).im = 0) (s : ℝ) (x : V3) :
    (↑(∫ y : V3, (f y).re * heatR s (x - y)) : ℂ) = ∫ y : V3, (f y) * heatC s (x - y) := by
  rw [ofReal_integral]
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.ofReal_mul]
  rw [← ofReal_re_eq_self_of_im_eq_zero (hf y)]
  rw [heatR_eq]

lemma position_real_cast {f : V3 → ℂ} (hf : ∀ x : V3, (f x).im = 0) (s : ℝ) :
    (↑(∫ x : V3, (f x).re * (∫ y : V3, (f y).re * heatR s (x - y))) : ℂ)
      = ∫ x : V3, (f x) * (∫ y : V3, (f y) * heatC s (x - y)) := by
  rw [ofReal_integral]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.ofReal_mul]
  rw [← ofReal_re_eq_self_of_im_eq_zero (hf x)]
  rw [inner_real_cast hf s x]

lemma momentum_real_cast {f : V3 → ℂ} (hf : ∀ x : V3, (f x).im = 0) (s : ℝ) :
    (↑(∫ q : V3, ‖𝓕 f q‖ ^ 2 * gaussR s q) : ℂ) = ∫ q : V3, (𝓕 f q) * (𝓕 f (-q)) * gaussC s q := by
  rw [ofReal_integral]
  apply integral_congr_ae
  filter_upwards with q
  exact momentum_cast hf s q

lemma per_s_energy_of {g : V3 → ℂ} (hg : ∀ x : V3, (g x).im = 0)
    (hgi : Integrable g) (hĝ : Integrable (fun q : V3 => 𝓕 g q)) {s : ℝ} (hs : 0 < s) :
    (∫ q : V3, ‖𝓕 g q‖ ^ 2 * gaussR s q)
      = ∫ x : V3, (g x).re * (∫ y : V3, (g y).re * heatR s (x - y)) := by
  apply Complex.ofReal_inj.mp
  calc
    (↑(∫ q : V3, ‖𝓕 g q‖ ^ 2 * gaussR s q) : ℂ)
        = ∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q := momentum_real_cast hg s
    _ = ∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y)) := per_s_energy_complex hgi hĝ hs
    _ = (↑(∫ x : V3, (g x).re * (∫ y : V3, (g y).re * heatR s (x - y))) : ℂ) :=
          (position_real_cast hg s).symm



/-- For each `s > 0`, the position-side regularised double integral equals the
momentum-side expression, for real-valued Schwartz `f` on `ℝ³`:

`∫_q ‖f̂(q)‖² exp(−πs‖q‖²) = ∫_x f(x) ∫_y f(y) s^{−3/2} exp(−π‖x−y‖²/s)`. -/
theorem per_s_energy (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hreal : ∀ x : EuclideanSpace ℝ (Fin 3), (f x).im = 0) {s : ℝ} (hs : 0 < s) :
    (∫ q : EuclideanSpace ℝ (Fin 3),
        ‖((𝓕 (f : EuclideanSpace ℝ (Fin 3) → ℂ)) q)‖ ^ 2 *
          Real.exp (-(Real.pi * s * ‖q‖ ^ 2)))
      = (∫ x : EuclideanSpace ℝ (Fin 3), (f x).re *
          (∫ y : EuclideanSpace ℝ (Fin 3), (f y).re *
            (s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s)))) := by
  have hĝ : Integrable (fun q : V3 => 𝓕 (f : V3 → ℂ) q) := by
    have hc : (fun q : V3 => 𝓕 (f : V3 → ℂ) q) = fun q : V3 => (SchwartzMap.fourierTransformCLM ℂ f) q := by
      funext q
      exact congrFun (SchwartzMap.fourier_coe (E := ℂ) f).symm q
    rw [hc]
    exact (SchwartzMap.fourierTransformCLM ℂ f).integrable
  have h := per_s_energy_of (g := (f : V3 → ℂ)) hreal f.integrable hĝ hs
  simpa [gaussR, heatR] using h

end Commons.Analysis.Fourier