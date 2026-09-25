import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs
import Submission.Work.BourgainPlan.Maximal.fourierInv_dilate_lintegral

/-!
# Kernel size of an annulus symbol family

`annulusKernel_size`: a smooth symbol family `b`, supported in the dyadic annuli
`1/2 < |2^m ξ| < 2` with `k`-th derivatives bounded by `C_k · 2^{m k}` (frequency scale `2^{-m}`),
has an inverse Fourier transform bounded by `C · 2^{-m} · (1 + 2^{-m} |z|)^{-N}`, uniformly in `m`,
for every `N`.

The proof is the standard integration-by-parts computation: the support pins the integral of each
derivative to an interval of length `4·2^{-m}`, and the `N`-fold integration by parts against the
character `e(ξz)` produces the factor `(2π|z|)^{-N}`, whence the factor `(2^{-m}|z|)^{-N}`.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal Topology

/-! ## 1. Support of an annulus symbol and of its derivatives -/

/-- If a function vanishes on an open set, so does its derivative (the derivative of a function that
is identically zero near `x` is zero at `x`, regardless of differentiability assumptions). -/
lemma annulusK_deriv_eq_zero_of_eq_zero_on_open {g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ x ∈ U, g x = 0) : ∀ x ∈ U, deriv g x = 0 := by
  intro x hx
  have hmem : U ∈ 𝓝 x := hU.mem_nhds hx
  have hev : g =ᶠ[𝓝 x] (0 : ℝ → ℂ) :=
    Filter.eventually_of_mem hmem (fun y hy => by simpa using hg y hy)
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

/-- The annulus condition: `b m` vanishes for `|ξ| > 2^{1-m}`. -/
lemma annulusK_eq_zero (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b) (m : ℤ) :
    ∀ ξ, (2 : ℝ) ^ (1 - m) < |ξ| → b m ξ = 0 := by
  intro ξ hξ
  by_contra hne
  have hlt : |(2 : ℝ) ^ m * ξ| < 2 := (hb.1 m ξ hne).2
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) m)] at hlt
  have h2 : (2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m) = 2 := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
        show m + (1 - m) = (1 : ℤ) by ring, zpow_one]
  have hlt' : (2 : ℝ) ^ m * |ξ| < (2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m) := by
    rw [h2]; exact hlt
  exact absurd (lt_of_mul_lt_mul_left hlt' (le_of_lt (zpow_pos (by norm_num : (0:ℝ) < 2) m)))
    (not_lt.mpr hξ.le)

/-- Every iterated derivative of `b m` vanishes for `|ξ| > 2^{1-m}`. -/
lemma annulusK_iteratedDeriv_eq_zero (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (m : ℤ) (k : ℕ) :
    ∀ ξ, (2 : ℝ) ^ (1 - m) < |ξ| → iteratedDeriv k (b m) ξ = 0 := by
  induction k with
  | zero => intro ξ hξ; simpa using annulusK_eq_zero b hb m ξ hξ
  | succ k ih =>
      intro ξ hξ
      rw [iteratedDeriv_succ]
      exact annulusK_deriv_eq_zero_of_eq_zero_on_open
        (isOpen_lt continuous_const continuous_abs) (fun x hx => ih x hx) ξ hξ

/-- `b m` has compact support (it is supported in `[-2^{1-m}, 2^{1-m}]`). -/
lemma annulusK_hasCompactSupport (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b) (m : ℤ) :
    HasCompactSupport (b m) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((2 : ℝ) ^ (1 - m))) ((2 : ℝ) ^ (1 - m))) isCompact_Icc ?_
  intro x hx
  have hle : |x| ≤ (2 : ℝ) ^ (1 - m) := by
    by_contra hcon
    exact hx (annulusK_eq_zero b hb m x (not_le.mp hcon))
  rw [abs_le] at hle
  exact hle

/-- So does every iterated derivative. -/
lemma annulusK_hasCompactSupport_iteratedDeriv (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (m : ℤ) (k : ℕ) : HasCompactSupport (iteratedDeriv k (b m)) := by
  induction k with
  | zero => simpa using annulusK_hasCompactSupport b hb m
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Hence every iterated derivative is integrable. -/
lemma annulusK_integrable (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) (k : ℕ) :
    Integrable (iteratedDeriv k (b m)) :=
  (ContDiff.continuous_iteratedDeriv k (hsmooth m) (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
    (annulusK_hasCompactSupport_iteratedDeriv b hb m k)

/-! ## 2. Fourier decay through the `N`-th derivative -/

/-- The uniform bound `‖𝓕⁻ f z‖ ≤ ∫ ‖f‖`. -/
lemma annulusK_fourierInv_le_integral (f : ℝ → ℂ) (z : ℝ) :
    ‖FourierTransform.fourierInv f z‖ ≤ ∫ x, ‖f x‖ := by
  rw [fourierInv_eq_polyE_integral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with x
  rw [norm_mul, norm_polyE, one_mul]

/-- The decay estimate: for `z ≠ 0`, `‖𝓕⁻ f z‖ ≤ (2π|z|)^{-N} ∫ ‖f^{(N)}‖`.
This is the `N`-fold integration by parts of `e(ξz)` applied to `f`. -/
lemma annulusK_fourierInv_iteratedDeriv_le (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hint : ∀ n : ℕ, Integrable (iteratedDeriv n f)) (n : ℕ) {z : ℝ} (hz : z ≠ 0) :
    ‖FourierTransform.fourierInv f z‖ ≤ ((2 * Real.pi * |z|) ^ n)⁻¹ * ∫ x, ‖iteratedDeriv n f x‖ := by
  have h := Real.fourier_iteratedDeriv (f := f) (N := (⊤ : ℕ∞)) hf (fun n _ => hint n)
    (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)
  set W : ℝ := (2 * Real.pi * |z|) ^ n with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  have hnorm : ‖FourierTransform.fourier (iteratedDeriv n f) (-z)‖
      = W * ‖FourierTransform.fourier f (-z)‖ := by
    rw [h]
    simp only [norm_smul, norm_pow]
    rw [show ‖(2 : ℂ) * ↑Real.pi * Complex.I * ↑(-z)‖ = 2 * Real.pi * |z| from by
      simp [abs_of_pos Real.pi_pos], hW]
  have hle : ‖FourierTransform.fourier (iteratedDeriv n f) (-z)‖ ≤ ∫ x, ‖iteratedDeriv n f x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hX : ‖FourierTransform.fourier f (-z)‖ ≤ W⁻¹ * ∫ x, ‖iteratedDeriv n f x‖ := by
    have h1 := mul_le_mul_of_nonneg_left (hnorm ▸ hle) (le_of_lt (inv_pos.mpr hWpos))
    rwa [← mul_assoc, inv_mul_cancel₀ hWpos.ne', one_mul] at h1
  rw [Real.fourierInv_eq_fourier_neg]
  exact hX

/-! ## 3. The integral of the `k`-th derivative -/

/-- The support of `iteratedDeriv k (b m)` has length `4·2^{-m}`, so the integral of its modulus is
at most `C_k·2^{m k}·4·2^{-m}`. -/
lemma annulusK_integral_iteratedDeriv_le (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) (k : ℕ) (Ck : ℝ)
    (hCk : ∀ ξ, ‖iteratedDeriv k (b m) ξ‖ ≤ Ck * (2 : ℝ) ^ (m * k)) :
    ∫ x, ‖iteratedDeriv k (b m) x‖ ≤ Ck * (2 : ℝ) ^ (m * k) * (4 * (2 : ℝ) ^ (-m)) := by
  have hr : (0:ℝ) < (2 : ℝ) ^ (1 - m) := zpow_pos (by norm_num : (0:ℝ) < 2) (1 - m)
  have hsupp := annulusK_iteratedDeriv_eq_zero b hb m k
  have hzero : ∀ x ∉ Set.Icc (-((2 : ℝ) ^ (1 - m))) ((2 : ℝ) ^ (1 - m)),
      ‖iteratedDeriv k (b m) x‖ = 0 := by
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    have habs : (2 : ℝ) ^ (1 - m) < |x| := by
      rcases hx with h | h
      · rw [abs_of_neg (by linarith [hr])]; linarith [hr]
      · rw [abs_of_pos (by linarith [hr])]; linarith [hr]
    rw [hsupp x habs, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hmono : ∫ x in Set.Icc (-((2 : ℝ) ^ (1 - m))) ((2 : ℝ) ^ (1 - m)),
        ‖iteratedDeriv k (b m) x‖
      ≤ ∫ x in Set.Icc (-((2 : ℝ) ^ (1 - m))) ((2 : ℝ) ^ (1 - m)),
          (Ck * (2 : ℝ) ^ (m * k)) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc ?_
    · exact (annulusK_integrable b hb hsmooth m k).norm.integrableOn
    · refine integrableOn_const (C := Ck * (2 : ℝ) ^ (m * k)) ?_ ?_
      · rw [Real.volume_Icc]; simp
      · rw [enorm_mul]
        exact ENNReal.mul_ne_top (by simp) (by simp)
    · intro x hx; exact hCk x
  refine hmono.trans (le_of_eq ?_)
  rw [setIntegral_const, Real.volume_real_Icc,
      max_eq_left (by linarith [hr] : (0:ℝ) ≤ (2 : ℝ) ^ (1 - m) - -((2 : ℝ) ^ (1 - m))),
      smul_eq_mul]
  have h2r : (2 : ℝ) ^ (1 - m) - -((2 : ℝ) ^ (1 - m)) = 4 * (2 : ℝ) ^ (-m) := by
    rw [show (1 : ℤ) - m = 1 + (-m) by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
    ring
  rw [h2r]; ring

/-! ## 4. The pure arithmetic packing of the two regimes -/

/-- The two inequalities the two regimes produce (`2^{-m}|z| ≤ 1`, resp. `≥ 1`) are both dominated
by `C · 2^{-m} · (1 + 2^{-m}|z|)^{-N}` for one constant `C`. -/
lemma annulusK_pack (N : ℕ) (C0 CN : ℝ) (h0 : 0 ≤ C0) (hN : 0 ≤ CN) :
    ∃ C : ℝ, 0 < C ∧
      (∀ d t : ℝ, 0 < d → 0 ≤ t → t ≤ 1 →
        4 * C0 * d ≤ C * d * (1 + t) ^ (-(N:ℝ))) ∧
      (∀ d t : ℝ, 0 < d → 1 ≤ t →
        4 * ((2 * Real.pi) ^ N)⁻¹ * CN * d * t ^ (-(N:ℝ)) ≤ C * d * (1 + t) ^ (-(N:ℝ))) := by
  refine ⟨4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1), ?_, ?_, ?_⟩
  · have hX : (0:ℝ) < ((2*Real.pi)^N)⁻¹ * CN + C0 + 1 := by
      have h1 : (0:ℝ) ≤ ((2*Real.pi)^N)⁻¹ * CN :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) N)) hN
      linarith
    positivity
  · intro d t hd ht0 ht1
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + t), Real.rpow_natCast]
    have hle2 : 1 + t ≤ 2 := by linarith
    have hpow : (1 + t)^N ≤ (2:ℝ)^N := pow_le_pow_left₀ (by linarith) hle2 N
    have hinv : ((2:ℝ)^N)⁻¹ ≤ ((1 + t)^N)⁻¹ := inv_anti₀ (pow_pos (by linarith) N) hpow
    have hX : C0 ≤ ((2*Real.pi)^N)⁻¹ * CN + C0 + 1 := by
      have h1 : (0:ℝ) ≤ ((2*Real.pi)^N)⁻¹ * CN :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) N)) hN
      linarith
    have hXnn : (0:ℝ) ≤ ((2*Real.pi)^N)⁻¹ * CN + C0 + 1 := by linarith
    have haux : (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d * ((2:ℝ)^N)⁻¹
        = 4 * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d := by
      have h2Nne : (2:ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
    have hstep : 4 * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d
        ≤ (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d * ((1 + t)^N)⁻¹ := by
      have hfac : (0:ℝ) ≤ (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d := by
        apply mul_nonneg _ hd.le
        exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) N)) hXnn
      have h3 := mul_le_mul_of_nonneg_left hinv hfac
      rwa [haux] at h3
    have hfinal : 4 * C0 * d ≤ 4 * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d := by
      nlinarith [hd, hX]
    linarith
  · intro d t hd ht1
    have htpos : 0 < t := by linarith
    rw [Real.rpow_neg (le_of_lt htpos), Real.rpow_natCast,
        Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + t), Real.rpow_natCast]
    have hle : (1+t)^N ≤ (2:ℝ)^N * t^N := by
      calc (1+t)^N ≤ (2*t)^N := pow_le_pow_left₀ (by linarith) (by linarith) N
        _ = (2:ℝ)^N * t^N := mul_pow 2 t N
    have hinv : ((2:ℝ)^N)⁻¹ * (t^N)⁻¹ ≤ ((1+t)^N)⁻¹ := by
      have h := inv_anti₀ (pow_pos (by linarith : (0:ℝ) < 1+t) N) hle
      rwa [mul_inv] at h
    have hXnn : (0:ℝ) ≤ ((2*Real.pi)^N)⁻¹ * CN + C0 + 1 := by
      have h1 : (0:ℝ) ≤ ((2*Real.pi)^N)⁻¹ * CN :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) N)) hN
      linarith
    have hfac : (0:ℝ) ≤ (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d := by
      apply mul_nonneg _ hd.le
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) N)) hXnn
    have hstep : (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d
          * (((2:ℝ)^N)⁻¹ * (t^N)⁻¹)
        ≤ (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d * ((1+t)^N)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hfac
    have haux2 : (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d
          * (((2:ℝ)^N)⁻¹ * (t^N)⁻¹)
        = 4 * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d * (t^N)⁻¹ := by
      have h2Nne : (2:ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
      have htne : t ≠ 0 := ne_of_gt htpos
      field_simp
    have hle' : ((2*Real.pi)^N)⁻¹ * CN ≤ ((2*Real.pi)^N)⁻¹ * CN + C0 + 1 := by linarith
    have hlow : 4 * ((2*Real.pi)^N)⁻¹ * CN * d * (t^N)⁻¹ ≤
        4 * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d * (t^N)⁻¹ := by
      have h1 : ((2*Real.pi)^N)⁻¹ * CN * d ≤ (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d :=
        mul_le_mul_of_nonneg_right hle' hd.le
      have h2 : (0:ℝ) ≤ (t^N)⁻¹ := by positivity
      nlinarith [h1, h2]
    calc 4 * ((2*Real.pi)^N)⁻¹ * CN * d * (t^N)⁻¹
        ≤ 4 * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1) * d * (t^N)⁻¹ := hlow
      _ = (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d
            * (((2:ℝ)^N)⁻¹ * (t^N)⁻¹) := haux2.symm
      _ ≤ (4 * (2:ℝ)^N * (((2*Real.pi)^N)⁻¹ * CN + C0 + 1)) * d * ((1+t)^N)⁻¹ := hstep

/-! ## 5. The main estimate -/

theorem annulusKernel_size (b : ℤ → ℝ → ℂ) (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b) (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ m z, ‖FourierTransform.fourierInv (b m) z‖ ≤ C * (2 : ℝ) ^ (-m) * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(N : ℝ)) := by
  obtain ⟨C0, hC0nn, hC0⟩ := hb.2 0
  obtain ⟨CN, hCNnn, hCN⟩ := hb.2 N
  obtain ⟨C, hCpos, hcase1, hcase2⟩ := annulusK_pack N C0 CN hC0nn hCNnn
  refine ⟨C, hCpos, ?_⟩
  intro m z
  set d : ℝ := (2 : ℝ) ^ (-m) with hd
  have hdpos : 0 < d := by rw [hd]; exact zpow_pos (by norm_num : (0:ℝ) < 2) (-m)
  set t : ℝ := d * |z| with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg hdpos.le (abs_nonneg z)
  have hrw : (1 + t) ^ (-(N : ℝ)) = ((1 + t) ^ N)⁻¹ := by
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + t), Real.rpow_natCast]
  rw [hrw]
  by_cases ht1 : t ≤ 1
  · have hint0 : ∫ x, ‖b m x‖ ≤ C0 * (4 * d) := by
      have h := annulusK_integral_iteratedDeriv_le b hb hsmooth m 0 C0 (fun ξ => hC0 m ξ)
      simpa [← hd] using h
    have hbnd : ‖FourierTransform.fourierInv (b m) z‖ ≤ C0 * (4 * d) :=
      (annulusK_fourierInv_le_integral (b m) z).trans hint0
    have hc1 := hcase1 d t hdpos ht0 ht1
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + t), Real.rpow_natCast] at hc1
    calc ‖FourierTransform.fourierInv (b m) z‖ ≤ C0 * (4 * d) := hbnd
      _ = 4 * C0 * d := by ring
      _ ≤ C * d * ((1 + t)^N)⁻¹ := hc1
  · have hz : z ≠ 0 := by
      intro h
      have ht0' : t = 0 := by rw [ht, h, abs_zero, mul_zero]
      have : (1:ℝ) < t := not_le.mp ht1
      linarith
    have hintN : ∫ x, ‖iteratedDeriv N (b m) x‖ ≤ CN * (2 : ℝ) ^ (m * N) * (4 * d) := by
      have h := annulusK_integral_iteratedDeriv_le b hb hsmooth m N CN (fun ξ => hCN m ξ)
      simpa [← hd] using h
    have hdec := annulusK_fourierInv_iteratedDeriv_le (b m) (hsmooth m)
      (fun n => annulusK_integrable b hb hsmooth m n) N hz
    have hnonneg : (0:ℝ) ≤ ((2 * Real.pi * |z|) ^ N)⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (abs_nonneg z)) N)
    have hbnd : ‖FourierTransform.fourierInv (b m) z‖
        ≤ ((2 * Real.pi * |z|) ^ N)⁻¹ * (CN * (2 : ℝ) ^ (m * N) * (4 * d)) :=
      hdec.trans (mul_le_mul_of_nonneg_left hintN hnonneg)
    have hident : ((2 * Real.pi * |z|) ^ N)⁻¹ * (CN * (2 : ℝ) ^ (m * N) * (4 * d))
        = 4 * ((2 * Real.pi) ^ N)⁻¹ * CN * d * (t ^ N)⁻¹ := by
      set A : ℝ := (2 : ℝ) ^ m with hA
      have hApos : 0 < A := by rw [hA]; exact zpow_pos (by norm_num : (0:ℝ) < 2) m
      have hAd : d * A = 1 := by
        rw [hd, hA, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
            show -m + m = (0 : ℤ) by ring, zpow_zero]
      have hAN : (2 : ℝ) ^ (m * N) = A ^ N := by
        rw [hA]; rw [zpow_mul, zpow_natCast]
      have hzA : |z| = A * t := by
        have h1 : A * t = |z| := by rw [ht, ← mul_assoc, mul_comm A d, hAd, one_mul]
        exact h1.symm
      rw [hAN, hzA, mul_pow, mul_pow, mul_inv, mul_inv]
      have hAne : A ≠ 0 := ne_of_gt hApos
      have htne : t ≠ 0 := ne_of_gt (mul_pos hdpos (abs_pos.mpr hz))
      field_simp
      ring
    have hc2 := hcase2 d t hdpos (le_of_lt (not_le.mp ht1))
    rw [Real.rpow_neg (le_of_lt (by linarith : (0:ℝ) < t)), Real.rpow_natCast,
        Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + t), Real.rpow_natCast] at hc2
    calc ‖FourierTransform.fourierInv (b m) z‖
        ≤ ((2 * Real.pi * |z|) ^ N)⁻¹ * (CN * (2 : ℝ) ^ (m * N) * (4 * d)) := hbnd
      _ = 4 * ((2 * Real.pi) ^ N)⁻¹ * CN * d * (t ^ N)⁻¹ := hident
      _ ≤ C * d * ((1 + t)^N)⁻¹ := hc2

end Work.BourgainPlan.Maximal
