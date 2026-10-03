import Mathlib
import Submission.Work.FIArea7.AngFourier
import Submission.Work.FIArea7.angFourierCoeff_le
import Submission.Work.FIArea7.vanishing_and_support
import Submission.Work.FIArea5.S16.fourier_truncation

namespace Work.FIArea7

open MeasureTheory intervalIntegral Filter
open scoped Topology

noncomputable section

/-- The exponential `e^{iℓα}` appearing in the truncated Fourier series has modulus `1`. -/
lemma angTrunc_norm_exp (ℓ : ℤ) (α : ℝ) :
    ‖Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- Evaluation of the `2π`-periodic lift of `w` at a point of `[0, 2π]`, using that `w`
vanishes at the endpoints. -/
lemma angTrunc_liftIoc_eval (w : ℝ → ℂ) (h0 : w 0 = 0) (h2π : w (2 * Real.pi) = 0)
    (α : ℝ) (hα : 0 ≤ α) (hα2 : α ≤ 2 * Real.pi) :
    (AddCircle.liftIoc (2 * Real.pi) 0 w) (α : AddCircle (2 * Real.pi)) = w α := by
  rcases eq_or_lt_of_le hα with h | h
  · subst h
    rw [show ((0 : ℝ) : AddCircle (2 * Real.pi)) =
        ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) from by
      rw [AddCircle.coe_period, AddCircle.coe_zero]]
    rw [AddCircle.liftIoc_coe_apply
      (show (2 * Real.pi : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) from
        ⟨by positivity, by linarith [Real.pi_pos]⟩)]
    rw [h2π, h0]
  · rw [AddCircle.liftIoc_coe_apply (show α ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) from
      ⟨h, by linarith⟩)]

/-- The Fourier coefficients of the `2π`-periodic lift of `w` are the angular Fourier
coefficients of `w`. -/
lemma angTrunc_fourierCoeff_lift (w : ℝ → ℂ) (ℓ : ℤ) :
    fourierCoeff (AddCircle.liftIoc (2 * Real.pi) 0 w) ℓ = angFourierCoeff w ℓ := by
  rw [angFourierCoeff]
  rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, Complex.real_smul]
  rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) from by push_cast; ring]
  apply congrArg (fun z => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
  apply intervalIntegral.integral_congr
  intro x _
  simp only [fourier_coe_apply, smul_eq_mul, zero_add, sub_zero]
  rw [show (2 * ↑Real.pi * Complex.I * ↑(-ℓ) * ↑x / ↑(2 * Real.pi))
        = -(Complex.I * (ℓ : ℂ) * ↑x) from by push_cast; field_simp]
  ring

/-- A `C²` function supported in `[0, 2πθ]` vanishes at `0` (by continuity). -/
lemma angTrunc_zero_at_zero (w : ℝ → ℂ) (θ : ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ α, w α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) : w 0 = 0 := by
  have hw0 : ∀ α, α < 0 → w α = 0 := (vanishing_and_support w θ hsupp).1
  have hclosed : IsClosed (w ⁻¹' {0}) := isClosed_singleton.preimage hw.continuous
  have hsub : Set.Iio (0:ℝ) ⊆ w ⁻¹' {0} := fun x hx => hw0 x hx
  have hcl : closure (Set.Iio (0:ℝ)) ⊆ w ⁻¹' {0} := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Iio] at hcl
  exact hcl (le_refl (0:ℝ))

/-- A `C²` function supported in `[0, 2πθ]` (`θ ≤ 1`) vanishes at `2π`. -/
lemma angTrunc_zero_at_two_pi (w : ℝ → ℂ) (θ : ℝ) (hθ1 : θ ≤ 1) (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ α, w α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) : w (2 * Real.pi) = 0 := by
  have hwA : ∀ α, 2 * Real.pi * θ < α → w α = 0 := (vanishing_and_support w θ hsupp).2.1
  have h2πθ_le : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [hθ1, Real.pi_pos]
  have hclosed : IsClosed (w ⁻¹' {0}) := isClosed_singleton.preimage hw.continuous
  have hsub : Set.Ioi (2 * Real.pi * θ) ⊆ w ⁻¹' {0} := fun x hx => hwA x hx
  have hcl : closure (Set.Ioi (2 * Real.pi * θ)) ⊆ w ⁻¹' {0} := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioi] at hcl
  exact hcl h2πθ_le

/-- ***FI* (16.27)**: the truncation of the Fourier series of the angular mollifier.

Let `w : ℝ → ℂ` be `C²`, bounded by `1`, supported in `[0, 2πθ]` (`0 < θ ≤ 1`) with the §7
derivative bounds `‖w^{(j)}‖ ≤ C θ^{-j}` for `j ≤ 2`, and let
`angFourierCoeff w ℓ = (1/2π)∫₀^{2π} w(α)e^{-iℓα}dα`.  Then for `α ∈ [0, 2π]` and `L ≥ 1`

  `‖w α − Σ_{|ℓ|≤L} angFourierCoeff w ℓ · e^{iℓα}‖ ≤ C' · θ⁻¹ · log(L+2) / L`,

the classical Dirichlet-kernel bound for a Lipschitz function (the `log L` is there because the
bound is pointwise).  The restriction `α ∈ [0,2π]` is essential: the partial sums are `2π`-periodic
while `w` is not.  Multiplying the bound by the `≍ θ²N` lattice points of the polar box gives the
summed error `O(L^{-1}N)` of *FI* (16.27) used by the bridge of §17. -/
theorem angTrunc_le (C : ℝ) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (w : ℝ → ℂ) (θ : ℝ) (L : ℕ) (α : ℝ),
        0 < θ → θ ≤ 1 → ContDiff ℝ 2 w →
        (∀ α, ‖w α‖ ≤ 1) →
        (∀ α, w α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
        (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ, ‖iteratedDeriv j w α‖ ≤ C * θ ^ (-(j : ℝ))) →
        1 ≤ L → α ∈ Set.Icc 0 (2 * Real.pi) →
        ‖w α - ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
            Work.FIArea7.angFourierCoeff w ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))‖
          ≤ C' * (θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ)) := by
  obtain ⟨K, hKpos, hK⟩ := angFourierCoeff_le C hC
  refine ⟨16 * K, by positivity, ?_⟩
  intro w θ L α hθ hθ1 hw hbdd hsupp hder hL hα
  have hα0 : 0 ≤ α := hα.1
  have hα2π : α ≤ 2 * Real.pi := hα.2
  have hw0 : w 0 = 0 := angTrunc_zero_at_zero w θ hw hsupp
  have hw2π : w (2 * Real.pi) = 0 := angTrunc_zero_at_two_pi w θ hθ1 hw hsupp
  -- The `2π`-periodic lift of `w`, and its Fourier coefficients.
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIoc (2 * Real.pi) 0 w,
     AddCircle.liftIoc_zero_continuous (by rw [hw0, hw2π]) hw.continuous.continuousOn⟩
  have hFcoeff : ∀ ℓ : ℤ, fourierCoeff (⇑F) ℓ = angFourierCoeff w ℓ := by
    intro ℓ; exact angTrunc_fourierCoeff_lift w ℓ
  have hcb : ∀ ℓ : ℤ, ‖angFourierCoeff w ℓ‖ ≤ K * θ * (1 + (θ * (ℓ:ℝ))^2)⁻¹ := by
    intro ℓ
    have h := hK w θ ℓ hθ hθ1 hw hbdd hsupp hder
    rwa [div_eq_mul_inv, ← mul_pow] at h
  have hsummable : Summable (fun ℓ : ℤ => K * θ * (1 + (θ*(ℓ:ℝ))^2)⁻¹) :=
    (Work.FIArea5.S16.int_summ θ hθ).mul_left _
  have hsumC : Summable (fun ℓ : ℤ => angFourierCoeff w ℓ) :=
    Summable.of_norm_bounded hsummable hcb
  have hsumF : Summable (fun ℓ : ℤ => fourierCoeff (⇑F) ℓ) :=
    hsumC.congr (fun ℓ => (hFcoeff ℓ).symm)
  -- Pointwise Fourier inversion at `α` (the coefficients are summable).
  have hpt := has_pointwise_sum_fourier_series_of_summable hsumF
  set T : ℤ → ℂ := fun ℓ => angFourierCoeff w ℓ *
      Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)) with hT
  have hFα : F (α : AddCircle (2 * Real.pi)) = w α := angTrunc_liftIoc_eval w hw0 hw2π α hα0 hα2π
  have hptT : HasSum T (w α) := by
    have h0 := hpt (α : AddCircle (2 * Real.pi))
    rw [hFα] at h0
    refine h0.congr_fun (fun i => ?_)
    show angFourierCoeff w i * Complex.exp (Complex.I * (i:ℂ) * (α:ℂ))
      = fourierCoeff (⇑F) i • fourier i (α : AddCircle (2 * Real.pi))
    rw [hFcoeff i, fourier_coe_apply, smul_eq_mul]
    congr 1
    rw [show (2 * ↑Real.pi * Complex.I * ↑i * ↑α / ↑(2 * Real.pi)) = Complex.I * (i:ℂ) * ↑α
        from by push_cast; field_simp]
  have hsymm : HasSum T (w α) (SummationFilter.symmetricIcc ℤ) :=
    hptT.mono_left (SummationFilter.symmetricIcc ℤ).le_atTop
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), T n) atTop (𝓝 (w α)) :=
    SummationFilter.hasSum_symmetricIcc_iff.mp hsymm
  have hlim : Tendsto (fun N : ℕ => ‖(∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), T n)
        - ∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), T ℓ‖) atTop
      (𝓝 ‖w α - ∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), T ℓ‖) :=
    (htend.sub_const _).norm
  -- The tail bound, for every truncation point `N ≥ L`.
  have key : ∀ N : ℕ, L ≤ N →
      ‖(∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), T n) - ∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), T ℓ‖
        ≤ 4 * K / (θ * (L:ℝ)) := by
    intro N hN
    have hsub : Finset.Icc (-(L:ℤ)) (L:ℤ) ⊆ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
      intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
    rw [show (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), T n) - (∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), T ℓ)
        = ∑ ℓ ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)) \ (Finset.Icc (-(L:ℤ)) (L:ℤ)), T ℓ from by
      rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]]
    refine (norm_sum_le _ _).trans ?_
    have hstep1 : ∑ ℓ ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)) \ (Finset.Icc (-(L:ℤ)) (L:ℤ)), ‖T ℓ‖
        ≤ ∑ ℓ ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)) \ (Finset.Icc (-(L:ℤ)) (L:ℤ)),
            K * θ * (1 + (θ*(ℓ:ℝ))^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro ℓ _
      rw [hT]; simp only
      rw [norm_mul, angTrunc_norm_exp, mul_one]
      exact hcb ℓ
    refine hstep1.trans ?_
    have hEven : Function.Even (fun ℓ : ℤ => K * θ * (1 + (θ * (ℓ:ℝ))^2)⁻¹) := by
      intro ℓ
      show K * θ * (1 + (θ * ((-ℓ : ℤ):ℝ))^2)⁻¹ = K * θ * (1 + (θ*(ℓ:ℝ))^2)⁻¹
      rw [show (θ * ((-ℓ:ℤ):ℝ)) = -(θ*(ℓ:ℝ)) from by push_cast; ring, neg_sq]
    have hnn : ∀ ℓ : ℤ, 0 ≤ K * θ * (1 + (θ*(ℓ:ℝ))^2)⁻¹ := fun ℓ => by positivity
    refine (Work.FIArea5.S16.annulus_le L N
      (fun ℓ : ℤ => K*θ*(1+(θ*(ℓ:ℝ))^2)⁻¹) hEven hnn).trans ?_
    have hb := Work.FIArea5.S16.sum_Ioo_bound L N θ hθ hL
    have hcast : ∀ n : ℕ, (1 + (θ * ((n:ℤ):ℝ))^2)⁻¹ = (1 + (θ * (n:ℝ))^2)⁻¹ := by
      intro n; norm_num
    have hsum_eq : ∑ n ∈ Finset.Ioo L (N+1), K * θ * (1 + (θ * ((n:ℤ):ℝ))^2)⁻¹
        = ∑ n ∈ Finset.Ioo L (N+1), K * θ * (1 + (θ * (n:ℝ))^2)⁻¹ := by
      apply Finset.sum_congr rfl; intro x _; rw [hcast x]
    rw [hsum_eq]
    have hS : ∑ n ∈ Finset.Ioo L (N+1), K * θ * (1 + (θ * (n:ℝ))^2)⁻¹
        ≤ K * θ * (2 / (θ^2 * (L:ℝ))) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    calc 2 * ∑ n ∈ Finset.Ioo L (N+1), K * θ * (1 + (θ * (n:ℝ))^2)⁻¹
        ≤ 2 * (K * θ * (2 / (θ^2 * (L:ℝ)))) := mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = 4 * K / (θ * (L:ℝ)) := by field_simp; ring
  have hmain : ‖w α - ∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), T ℓ‖ ≤ 4 * K / (θ * (L:ℝ)) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop L] with N hN
    exact key N hN
  -- Arithmetic: `4K/(θL) ≤ 16K · θ⁻¹ log(L+2)/L`.
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hlog : (1:ℝ)/4 ≤ Real.log ((L:ℝ)+2) := by
    have hL1 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    have hl23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have h3 : (3:ℝ) ≤ (L:ℝ)+2 := by linarith
    have hl3 : Real.log 3 ≤ Real.log ((L:ℝ)+2) := Real.log_le_log (by norm_num) h3
    linarith [Real.log_two_gt_d9]
  have hlog4 : (1:ℝ) ≤ 4 * Real.log ((L:ℝ)+2) := by linarith [hlog]
  have hθL : 0 < θ * (L:ℝ) := mul_pos hθ hLpos
  calc ‖w α - ∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), T ℓ‖ ≤ 4 * K / (θ * (L:ℝ)) := hmain
    _ ≤ 16 * K * (θ⁻¹ * Real.log ((L:ℝ) + 2) / (L:ℝ)) := by
        rw [show 16 * K * (θ⁻¹ * Real.log ((L:ℝ)+2) / (L:ℝ))
            = 16 * K * Real.log ((L:ℝ)+2) / (θ * (L:ℝ)) from by field_simp]
        rw [div_le_div_iff₀ hθL hθL]
        rw [show (16:ℝ) * K * Real.log ((L:ℝ)+2) * (θ * (L:ℝ))
            = 4 * K * (θ * (L:ℝ)) * (4 * Real.log ((L:ℝ)+2)) from by ring]
        exact le_mul_of_one_le_right (by positivity) hlog4

end

end Work.FIArea7
