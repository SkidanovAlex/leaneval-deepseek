import Mathlib
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.Gfun_sq_integral_ge_diag
import Submission.Work.GM.Affine.Gfun_sq_ge_center
import Submission.Work.GM.Affine.smoothed_psiSmooth_fourier

/-!
# `Work.GM.Affine.Gfun_sq_ge_coherence` (GM §9: the honest affine sum, coherence form)

The honest affine sum of GM §9 region II is

`Gfun C₀ T M₂ f u = Σ_{m₂,m₂' ∈ R2 M₂} Σ_{|j| ≤ ⌊2C₀M₂⌋} f̃((m₂u + j)/m₂')`,
`f̃ = smoothed psiSmooth T f`.

Here we prove the *coherence* lower bound: for `C₀ ≥ 1` there is `c = C₀/128 > 0` with

`c * M₂^6 * (∫ f)² ≤ ∫ u, (Gfun C₀ T M₂ f u)²`

for all `T ≥ 1`, `M₂ ≥ 1` and all continuous non-negative `f` supported in `[1/C₀, C₀]`.

The mechanism is the *first moment* of `Gfun` together with Cauchy–Schwarz:

* `∫ Gfun = (Σ_{m₂,m₂',j} m₂'/m₂) · ∫ f̃` and each ratio `m₂'/m₂ ≥ 1/2`, while
  `|R2 M₂| ≥ M₂/2` and `2⌊2C₀M₂⌋+1 ≥ 2C₀M₂`; hence `∫ Gfun ≥ (C₀M₂³/4) ∫ f̃ = (C₀M₂³/4) ∫ f`.
* `Gfun` is continuous, non-negative, and supported in the `C₀`-dependent interval
  `[-(2C₀+1), 4C₀+1]` of length `6C₀+2 ≤ 8C₀`; hence `(∫ Gfun)² ≤ 8C₀ ∫ (Gfun)²`.

Combining: `(C₀/128) M₂^6 (∫f)² ≤ ∫ (Gfun)²`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## 1. The smoothing preserves the integral at *every* scale `T > 0`

`smoothed_properties` proves `∫ (smoothed ψ T f) = ∫ f` only under `2C₀ ≤ T`; the identity in
fact holds for every `T > 0`, since `x ↦ T ψ (T x)` still has total mass `1`. -/

theorem smoothed_integral_eq {ψ f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ1 : ∫ x, ψ x = 1) (hf : Integrable f) :
    ∫ u, smoothed ψ T f u = ∫ u, f u := by
  set φ : ℝ → ℝ := fun x => T * ψ (T * x) with hφdef
  have hφc : Continuous φ := by
    rw [hφdef]; fun_prop
  have hψTcs : HasCompactSupport (fun x : ℝ => ψ (T * x)) :=
    hψcs.comp_homeomorph (Homeomorph.mulLeft₀ T hT.ne')
  have hφcs : HasCompactSupport φ := by
    rw [hφdef]
    exact hψTcs.mul_left (f := fun _ : ℝ => T)
  have hφint : Integrable φ := hφc.integrable_of_hasCompactSupport hφcs
  have hφ1 : ∫ x, φ x = 1 := by
    rw [hφdef, integral_const_mul,
      MeasureTheory.Measure.integral_comp_mul_left (g := ψ) (a := T),
      abs_of_pos (inv_pos.mpr hT), hψ1, smul_eq_mul, mul_one]
    field_simp
  calc ∫ u, smoothed ψ T f u
      = ∫ u, MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        rw [smoothed, MeasureTheory.convolution_lsmul_swap]
        simp only [smul_eq_mul, hφdef]
        rw [show (∫ t, T * ψ (T * (u - t)) * f t) = T * ∫ t, ψ (T * (u - t)) * f t by
          rw [← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t; ring]
    _ = (ContinuousLinearMap.lsmul ℝ ℝ (∫ x, φ x)) (∫ x, f x) :=
        MeasureTheory.integral_convolution (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
          (ContinuousLinearMap.lsmul ℝ ℝ) hφint hf
    _ = ∫ x, f x := by rw [hφ1]; simp

/-! ## 2. The support of `Gfun` is contained in a fixed `C₀`-dependent interval -/

theorem Gfun_supp_subset {C₀ T M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 1 ≤ T) (hM₂ : 1 ≤ M₂)
    {f : ℝ → ℝ} (hsupp : SuppHyp C₀ f) :
    ∀ u, Gfun C₀ T M₂ f u ≠ 0 → u ∈ Set.Icc (-(2 * C₀ + 1)) (4 * C₀ + 1) := by
  have hTpos : 0 < T := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hC₀pos : 0 < C₀ := by linarith
  intro u hu
  rw [Gfun] at hu
  obtain ⟨m₂, hm₂, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  obtain ⟨m₂', hm₂', hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨j, hj, hne''⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have h2pos : 0 < (m₂ : ℝ) := R2_pos hM₂pos hm₂
  have h2'pos : 0 < (m₂' : ℝ) := R2_pos hM₂pos hm₂'
  have h2'le : (m₂' : ℝ) ≤ 2 * M₂ := R2_le hm₂'
  have h2gt : M₂ < (m₂ : ℝ) := (Finset.mem_filter.mp hm₂).2
  have hjabs : |(j : ℝ)| ≤ 2 * C₀ * M₂ := by
    rw [Finset.mem_Icc] at hj
    have h1 : -((⌊2 * C₀ * M₂⌋ : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have h2 : (j : ℝ) ≤ ((⌊2 * C₀ * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast hj.2
    have h3 : ((⌊2 * C₀ * M₂⌋ : ℤ) : ℝ) ≤ 2 * C₀ * M₂ := Int.floor_le _
    linarith [abs_le.mpr ⟨h1, h2⟩]
  set v : ℝ := ((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ) with hv
  have hvmem : v ∈ Set.Icc (1 / C₀ - 1 / (4 * T)) (C₀ + 1 / (4 * T)) :=
    smoothed_supp_sharp hTpos hsupp v hne''
  have hne2 : (m₂ : ℝ) ≠ 0 := ne_of_gt h2pos
  have hne2' : (m₂' : ℝ) ≠ 0 := ne_of_gt h2'pos
  have hkey : u * (m₂ : ℝ) = v * (m₂' : ℝ) - (j : ℝ) := by
    rw [hv, div_mul_cancel₀ _ hne2']
    ring
  have hquarter : 1 / (4 * T) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * T) (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hupper : u * (m₂ : ℝ) ≤ 4 * C₀ * M₂ + M₂ / 2 := by
    have hvup : v ≤ C₀ + 1 / 4 := by linarith [hvmem.2, hquarter]
    have h1 : v * (m₂' : ℝ) ≤ (C₀ + 1 / 4) * (2 * M₂) := by
      calc v * (m₂' : ℝ) ≤ (C₀ + 1 / 4) * (m₂' : ℝ) :=
            mul_le_mul_of_nonneg_right hvup h2'pos.le
        _ ≤ (C₀ + 1 / 4) * (2 * M₂) := mul_le_mul_of_nonneg_left h2'le (by linarith)
    have h2 : -(j : ℝ) ≤ 2 * C₀ * M₂ := by linarith [neg_le_abs (j : ℝ), hjabs]
    linarith [hkey, h1, h2]
  have hlower : -M₂ / 2 - 2 * C₀ * M₂ ≤ u * (m₂ : ℝ) := by
    have hvlow : -1 / 4 ≤ v := by
      have h : (0 : ℝ) ≤ 1 / C₀ := by positivity
      linarith [hvmem.1, hquarter]
    have h1 : (-1 / 4) * (m₂' : ℝ) ≤ v * (m₂' : ℝ) :=
      mul_le_mul_of_nonneg_right hvlow h2'pos.le
    have h2 : (j : ℝ) ≤ 2 * C₀ * M₂ := by linarith [le_abs_self (j : ℝ), hjabs]
    have h3 : -M₂ / 2 ≤ (-1 / 4) * (m₂' : ℝ) := by nlinarith [h2'le]
    linarith [hkey, h1, h2, h3]
  constructor
  · have h4 : -(2 * C₀ + 1) * (m₂ : ℝ) < -(2 * C₀ + 1) * M₂ :=
      mul_lt_mul_of_neg_left h2gt (by linarith)
    have h : -(2 * C₀ + 1) * (m₂ : ℝ) ≤ u * (m₂ : ℝ) := by linarith [h4, hlower]
    exact le_of_mul_le_mul_right h h2pos
  · have h4 : (4 * C₀ + 1) * M₂ < (4 * C₀ + 1) * (m₂ : ℝ) :=
      mul_lt_mul_of_pos_left h2gt (by linarith)
    have h : u * (m₂ : ℝ) ≤ (4 * C₀ + 1) * (m₂ : ℝ) := by linarith [hupper, h4]
    exact le_of_mul_le_mul_right h h2pos

/-! ## 3. The first moment of `Gfun` -/

theorem Gfun_integral_ge_smoothed {C₀ T M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 0 < T) (hM₂ : 1 ≤ M₂)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) :
    (C₀ * M₂ ^ 3 / 4) * (∫ u, smoothed psiSmooth T f u) ≤ ∫ u, Gfun C₀ T M₂ f u := by
  have hM₂pos : (0 : ℝ) < M₂ := lt_of_lt_of_le zero_lt_one hM₂
  obtain ⟨hFcont0, hFcs0, -⟩ := smoothed_psiSmooth_fourier hT hf hcs
  set F : ℝ → ℝ := smoothed psiSmooth T f with hFdef
  have hFcont : Continuous F := by simpa only [hFdef] using hFcont0
  have hFcs : HasCompactSupport F := by simpa only [hFdef] using hFcs0
  have hFnn : ∀ u, 0 ≤ F u := by
    intro u
    rw [hFdef]
    exact smoothed_psiSmooth_nonneg hT hfnn u
  set n : ℤ := ⌊2 * C₀ * M₂⌋ with hn_def
  set J : Finset ℤ := Finset.Icc (-n) n with hJdef
  have hGfun_eq : ∀ u, Gfun C₀ T M₂ f u
      = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
          F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) := by
    intro u
    rw [Gfun]
  have hterm_int : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂, ∀ j ∈ J,
      Integrable (fun u : ℝ => F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) :=
    fun m₂ hm₂ m₂' hm₂' j _ =>
      integrable_affine hFcont hFcs (ne_of_gt (R2_pos hM₂pos hm₂))
        (ne_of_gt (R2_pos hM₂pos hm₂'))
  have hterm_val : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂, ∀ j ∈ J,
      (∫ u, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)))
        = ((m₂' : ℝ) / (m₂ : ℝ)) * ∫ u, F u := by
    intro m₂ hm₂ m₂' hm₂' j _
    have h := integral_affine_eq (f := F) (c := (m₂ : ℝ)) (d := (m₂' : ℝ)) (e := (j : ℝ))
      (ne_of_gt (R2_pos hM₂pos hm₂)) (R2_pos hM₂pos hm₂')
    rw [h, abs_of_pos (R2_pos hM₂pos hm₂)]
  have hGint : ∫ u, Gfun C₀ T M₂ f u
      = (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ))) * ∫ u, F u := by
    have hsumfac : (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
          ((m₂' : ℝ) / (m₂ : ℝ)) * ∫ u, F u)
        = (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)))
          * ∫ u, F u := by
      simp only [Finset.sum_mul]
    rw [show (∫ u, Gfun C₀ T M₂ f u)
        = ∫ u, ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
            F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact hGfun_eq u]
    rw [← hsumfac]
    rw [MeasureTheory.integral_finsetSum _ (fun m₂ hm₂ =>
      integrable_finsetSum _ (fun m₂' hm₂' =>
        integrable_finsetSum _ (fun j hj => hterm_int m₂ hm₂ m₂' hm₂' j hj)))]
    apply Finset.sum_congr rfl; intro m₂ hm₂
    rw [MeasureTheory.integral_finsetSum _ (fun m₂' hm₂' =>
      integrable_finsetSum _ (fun j hj => hterm_int m₂ hm₂ m₂' hm₂' j hj))]
    apply Finset.sum_congr rfl; intro m₂' hm₂'
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hterm_int m₂ hm₂ m₂' hm₂' j hj)]
    apply Finset.sum_congr rfl; intro j hj
    exact hterm_val m₂ hm₂ m₂' hm₂' j hj
  -- the coefficient of `∫ F`
  have hcoef : (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) ^ 2 * ((J.card : ℕ) : ℝ)
      ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)) := by
    have hterm : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂, ∀ j ∈ J,
        (1 / 2 : ℝ) ≤ ((m₂' : ℝ) / (m₂ : ℝ)) := by
      intro m₂ hm₂ m₂' hm₂' j _
      have h1 : M₂ < (m₂' : ℝ) := (Finset.mem_filter.mp hm₂').2
      have h2 : (m₂ : ℝ) ≤ 2 * M₂ := R2_le hm₂
      have h3 : 0 < (m₂ : ℝ) := R2_pos hM₂pos hm₂
      rw [le_div_iff₀ h3]
      linarith
    calc (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) ^ 2 * ((J.card : ℕ) : ℝ)
        = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, (1 / 2 : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)) :=
          Finset.sum_le_sum fun m₂ hm₂ => Finset.sum_le_sum fun m₂' hm₂' =>
            Finset.sum_le_sum fun j hj => hterm m₂ hm₂ m₂' hm₂' j hj
  have hJcard : 2 * C₀ * M₂ ≤ ((J.card : ℕ) : ℝ) := by
    have hnn : (0 : ℤ) ≤ n := by
      rw [hn_def]
      exact Int.floor_nonneg.mpr (by nlinarith)
    have hc : ((J.card : ℕ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by
      have h : (J.card : ℤ) = 2 * n + 1 := by
        rw [hJdef, Int.card_Icc]
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n + 1 - -n)]
        ring
      exact_mod_cast h
    rw [hc]
    have h1 : 2 * C₀ * M₂ - 1 < (n : ℝ) := by
      have hfloor := Int.sub_one_lt_floor (2 * C₀ * M₂)
      rw [hn_def]
      exact hfloor
    have h2 : (1 : ℝ) ≤ 2 * C₀ * M₂ := by nlinarith
    push_cast
    linarith
  have hkey : C₀ * M₂ ^ 3 / 4
      ≤ (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) ^ 2 * ((J.card : ℕ) : ℝ) := by
    have hR2card : M₂ / 2 ≤ ((R2 M₂).card : ℝ) := R2_card_ge hM₂
    have hstep : (M₂ / 2) ^ 2 * (2 * C₀ * M₂) * (1 / 2 : ℝ)
        ≤ ((R2 M₂).card : ℝ) ^ 2 * ((J.card : ℕ) : ℝ) * (1 / 2 : ℝ) := by
      have ha : (0 : ℝ) ≤ M₂ / 2 := by positivity
      have hb : (M₂ / 2) ^ 2 ≤ ((R2 M₂).card : ℝ) ^ 2 := pow_le_pow_left₀ ha hR2card 2
      have hc : (0 : ℝ) ≤ 2 * C₀ * M₂ := by positivity
      have he : (0 : ℝ) ≤ ((R2 M₂).card : ℝ) ^ 2 := by positivity
      calc (M₂ / 2) ^ 2 * (2 * C₀ * M₂) * (1 / 2 : ℝ)
          ≤ ((R2 M₂).card : ℝ) ^ 2 * (2 * C₀ * M₂) * (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hc) (by norm_num)
        _ ≤ ((R2 M₂).card : ℝ) ^ 2 * ((J.card : ℕ) : ℝ) * (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJcard he) (by norm_num)
    have hval : (M₂ / 2) ^ 2 * (2 * C₀ * M₂) * (1 / 2 : ℝ) = C₀ * M₂ ^ 3 / 4 := by ring
    linarith [hstep, hval]
  have hcoef' : C₀ * M₂ ^ 3 / 4
      ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)) := le_trans hkey hcoef
  have hVnn : 0 ≤ ∫ u, F u := integral_nonneg hFnn
  rw [hGint]
  exact mul_le_mul_of_nonneg_right hcoef' hVnn

/-! ## 4. Coherence -/

theorem Gfun_sq_ge_coherence {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {T M₂ : ℝ}, 1 ≤ T → 1 ≤ M₂ → ∀ {f : ℝ → ℝ}, Continuous f → (∀ u, 0 ≤ f u) →
        SuppHyp C₀ f →
        c * M₂ ^ 6 * (∫ u, f u) ^ 2 ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := by
  refine ⟨C₀ / 128, by positivity, ?_⟩
  intro T M₂ hT hM₂ f hf hfnn hsupp
  have hC₀pos : 0 < C₀ := by linarith
  have hTpos : 0 < T := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hfcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  obtain ⟨hsmcont, _hsmcs, -⟩ := smoothed_psiSmooth_fourier hTpos hf hfcs
  have hIfnn : 0 ≤ ∫ u, f u := integral_nonneg hfnn
  -- the smoothing preserves the integral
  have hψc : Continuous psiSmooth := psiSmooth_contDiff.continuous
  have hψcs : HasCompactSupport psiSmooth :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1) 1) isCompact_Icc
      (fun x hx => psiSmooth_support hx)
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hfcs
  have hsmass : ∫ u, smoothed psiSmooth T f u = ∫ u, f u :=
    smoothed_integral_eq hTpos hψc hψcs psiSmooth_integral hfint
  -- lower bound for the first moment of `Gfun`
  have hlow : (C₀ * M₂ ^ 3 / 4) * (∫ u, f u) ≤ ∫ u, Gfun C₀ T M₂ f u := by
    rw [← hsmass]
    exact Gfun_integral_ge_smoothed hC₀ hTpos hM₂ hf hfcs hfnn
  have hLnn : 0 ≤ (C₀ * M₂ ^ 3 / 4) * (∫ u, f u) :=
    mul_nonneg (by positivity) hIfnn
  -- continuity, non-negativity and support of `Gfun`
  have hGfun_eq : ∀ u, Gfun C₀ T M₂ f u
      = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
          smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) := by
    intro u; rw [Gfun]
  have hGcont : Continuous (fun u : ℝ => Gfun C₀ T M₂ f u) := by
    rw [show (fun u : ℝ => Gfun C₀ T M₂ f u) = fun u : ℝ =>
        ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
          smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from funext hGfun_eq]
    refine continuous_finsetSum _ (fun m₂ _ => continuous_finsetSum _ (fun m₂' _ =>
      continuous_finsetSum _ (fun j _ => ?_)))
    exact hsmcont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _)
  have hGnn : ∀ u, 0 ≤ Gfun C₀ T M₂ f u := by
    intro u
    rw [hGfun_eq u]
    exact Finset.sum_nonneg fun m₂ _ => Finset.sum_nonneg fun m₂' _ =>
      Finset.sum_nonneg fun j _ => smoothed_psiSmooth_nonneg hTpos hfnn _
  have hsuppG := Gfun_supp_subset hC₀ hT hM₂ hsupp
  have hab : -(2 * C₀ + 1) < 4 * C₀ + 1 := by linarith
  have hCS := sq_integral_le_width hGcont hGnn (a := -(2 * C₀ + 1)) (b := 4 * C₀ + 1)
    hab hsuppG
  set W : ℝ := ∫ u, (Gfun C₀ T M₂ f u) ^ 2 with hW
  have hWnn : 0 ≤ W := integral_nonneg fun u => sq_nonneg _
  have hCS' : (∫ u, Gfun C₀ T M₂ f u) ^ 2 ≤ (8 * C₀) * W := by
    refine le_trans hCS ?_
    exact mul_le_mul_of_nonneg_right (by linarith : (4 * C₀ + 1) - (-(2 * C₀ + 1)) ≤ 8 * C₀) hWnn
  have hsq : ((C₀ * M₂ ^ 3 / 4) * (∫ u, f u)) ^ 2 ≤ (∫ u, Gfun C₀ T M₂ f u) ^ 2 :=
    pow_le_pow_left₀ hLnn hlow 2
  have hA : ((C₀ * M₂ ^ 3 / 4) * (∫ u, f u)) ^ 2
      = (C₀ ^ 2 * M₂ ^ 6 / 16) * (∫ u, f u) ^ 2 := by ring
  have hstep : (C₀ ^ 2 * M₂ ^ 6 / 16) * (∫ u, f u) ^ 2 ≤ (8 * C₀) * W := by
    rw [← hA]
    exact le_trans hsq hCS'
  have hmul : ((C₀ / 128) * M₂ ^ 6 * (∫ u, f u) ^ 2) * (8 * C₀) ≤ W * (8 * C₀) := by
    have heq : ((C₀ / 128) * M₂ ^ 6 * (∫ u, f u) ^ 2) * (8 * C₀)
        = (C₀ ^ 2 * M₂ ^ 6 / 16) * (∫ u, f u) ^ 2 := by ring
    rw [heq, mul_comm W]
    exact hstep
  have h8 : (0 : ℝ) < 8 * C₀ := by positivity
  have hfin := le_of_mul_le_mul_right hmul h8
  exact hfin

end

end Work.GM.Affine
