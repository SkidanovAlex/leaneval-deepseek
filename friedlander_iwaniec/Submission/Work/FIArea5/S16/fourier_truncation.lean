import Mathlib
import Submission.Work.FIArea6.fourier_coeff_decay
import Submission.Work.FIArea5.S16.fourierCoeff_decay_cMoll

namespace Work.FIArea5.S16

open MeasureTheory intervalIntegral Filter
open scoped Topology

noncomputable section

instance instFactTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The `ℓ`-th complex Fourier coefficient of `q` over the period `[0, 2π]`. -/
def fcoef (q : ℝ → ℝ) (ℓ : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ β in (0 : ℝ)..(2 * Real.pi), (q β : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * β)

/-- The exponential factor `exp (i ℓ x)` has norm `1`. -/
lemma norm_exp_int' (ℓ : ℤ) (α : ℝ) :
    ‖Complex.exp ((ℓ : ℂ) * Complex.I * α)‖ = 1 := by
  rw [show (ℓ : ℂ) * Complex.I * α = (((ℓ : ℝ) * α : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **(16.26)** in the constants of the statement: bound on a single Fourier coefficient. -/
lemma fcoef_bound (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) (ℓ : ℤ) :
    ‖fcoef q ℓ‖ ≤ (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) := by
  have h := fourierCoeff_decay_cMoll q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 ℓ
  rw [fcoef, norm_mul]
  rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) from by push_cast; ring]
  rw [show ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) from by
    rw [show ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = |((1 / (2 * Real.pi) : ℝ))| from by simp]
    exact abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

lemma nat_summ (θ : ℝ) (hθ : 0 < θ) :
    Summable (fun n : ℕ => (1 + (θ * n) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hbase
    simpa using this
  have hcmp : Summable (fun n : ℕ => (1 + (θ * ((n : ℝ) + 1)) ^ 2)⁻¹) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℕ => ((θ * ((n : ℝ) + 1)) ^ 2)⁻¹)
    · intro n; positivity
    · intro n
      exact (inv_le_inv₀ (by positivity : (0 : ℝ) < 1 + (θ * ((n : ℝ) + 1)) ^ 2)
        (by positivity : (0 : ℝ) < (θ * ((n : ℝ) + 1)) ^ 2)).mpr
        (by linarith [sq_nonneg (θ * ((n : ℝ) + 1))])
    · have heq : (fun n : ℕ => ((θ * ((n : ℝ) + 1)) ^ 2)⁻¹)
          = (fun n : ℕ => (1 / θ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
        funext n; rw [mul_pow]; field_simp
      rw [heq]; exact hshift.mul_left _
  exact (summable_nat_add_iff (f := fun n : ℕ => (1 + (θ * n) ^ 2)⁻¹) 1).mp
    (by simpa [Nat.cast_add, Nat.cast_one, mul_add] using hcmp)

lemma int_summ (θ : ℝ) (hθ : 0 < θ) :
    Summable (fun ℓ : ℤ => (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) := by
  apply Summable.of_nat_of_neg
  · simpa using nat_summ θ hθ
  · have h := nat_summ θ hθ
    simpa using h

lemma fcoef_summable (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) :
    Summable (fcoef q) := by
  apply Summable.of_norm_bounded
    (g := fun ℓ : ℤ => (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹))
  · exact ((int_summ θ hθ).mul_left (10000000 * θ)).mul_left (1 / (2 * Real.pi))
  · intro ℓ; exact fcoef_bound q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 ℓ

/-- Evaluation of the periodic extension of `q` at a point of `[0, 2π]`. -/
lemma liftIoc_eval (q : ℝ → ℝ) (hq0 : q 0 = 0) (hq2π : q (2 * Real.pi) = 0)
    (α : ℝ) (hα : 0 ≤ α) (hα2 : α ≤ 2 * Real.pi) :
    (AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ)))
        (α : AddCircle (2 * Real.pi)) = (q α : ℂ) := by
  rcases eq_or_lt_of_le hα with h | h
  · subst h
    rw [show ((0 : ℝ) : AddCircle (2 * Real.pi)) =
        ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) from by
      rw [AddCircle.coe_period, AddCircle.coe_zero]]
    rw [AddCircle.liftIoc_coe_apply (show (2 * Real.pi : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) from
      ⟨by positivity, by linarith [Real.pi_pos]⟩)]
    rw [hq2π, hq0]
  · rw [AddCircle.liftIoc_coe_apply (show α ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) from
      ⟨h, by linarith⟩)]

/-- Tail bound: the sum of an even, nonnegative weight over the annulus `L < |ℓ| ≤ N`
is at most twice the sum over `L < n ≤ N`. -/
lemma annulus_le (L N : ℕ) (G : ℤ → ℝ) (hG : Function.Even G) (hGnn : ∀ ℓ, 0 ≤ G ℓ) :
    ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), G ℓ
      ≤ 2 * ∑ n ∈ Finset.Ioo L (N + 1), G (n : ℤ) := by
  set H : ℤ → ℝ := fun ℓ => if (L : ℤ) < |ℓ| then G ℓ else 0 with hH
  have hHeven : Function.Even H := by
    intro ℓ; simp only [hH, abs_neg, hG ℓ]
  have hHnn : ∀ ℓ, 0 ≤ H ℓ := by
    intro ℓ; simp only [hH]; split
    · exact hGnn ℓ
    · exact le_rfl
  have hsub : (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ))
      ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := Finset.sdiff_subset
  have hGH : ∀ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
      G ℓ = H ℓ := by
    intro ℓ hℓ
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hℓ
    obtain ⟨⟨_, _⟩, h3⟩ := hℓ
    simp only [hH]
    rw [if_pos]
    have h3' : ℓ < -(L : ℤ) ∨ (L : ℤ) < ℓ := by
      rw [not_and_or] at h3
      rcases h3 with h | h
      · left; omega
      · right; omega
    rw [lt_abs]
    rcases h3' with h | h
    · right; omega
    · left; exact h
  have hstep1 : ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), G ℓ
      = ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), H ℓ :=
    Finset.sum_congr rfl hGH
  have hstep2 : ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), H ℓ
      ≤ ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), H ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hHnn x)
  have hH0 : H 0 = 0 := by
    simp only [hH, abs_zero]
    rw [if_neg]; omega
  have hrange : ∑ m ∈ Finset.range (N + 1), H (m : ℤ) = ∑ n ∈ Finset.Ioo L (N + 1), G (n : ℤ) := by
    have hHm : ∀ m : ℕ, H (m : ℤ) = if L < m then G (m : ℤ) else 0 := by
      intro m
      simp only [hH]
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (m : ℤ))]
      by_cases hc : L < m
      · rw [if_pos hc, if_pos (Int.ofNat_lt.mpr hc)]
      · rw [if_neg hc, if_neg (fun h => hc (Int.ofNat_lt.mp h))]
    simp only [hHm]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  have hstep3 : ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), H ℓ
      = 2 * ∑ n ∈ Finset.Ioo L (N + 1), G (n : ℤ) := by
    rw [Finset.sum_Icc_of_even_eq_range hHeven N, hrange, hH0, sub_zero]
    rw [two_smul]
    ring
  calc ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), G ℓ
      = ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), H ℓ := hstep1
    _ ≤ ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), H ℓ := hstep2
    _ = 2 * ∑ n ∈ Finset.Ioo L (N + 1), G (n : ℤ) := hstep3

/-- Numerical bound for the tail of the weight `(1 + (θn)²)⁻¹`. -/
lemma sum_Ioo_bound (L N : ℕ) (θ : ℝ) (hθ : 0 < θ) (hL : 1 ≤ L) :
    ∑ n ∈ Finset.Ioo L (N + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹ ≤ 2 / (θ ^ 2 * L) := by
  have hcmp : ∀ n ∈ Finset.Ioo L (N + 1),
      (1 + (θ * (n : ℝ)) ^ 2)⁻¹ ≤ (1 / θ ^ 2) * ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      rw [Finset.mem_Ioo] at hn
      have : 0 < n := by omega
      exact_mod_cast this
    have hres : (1 / θ ^ 2) * ((n : ℝ) ^ 2)⁻¹ = ((θ * (n : ℝ)) ^ 2)⁻¹ := by
      rw [mul_pow]; field_simp
    rw [hres]
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < 1 + (θ * (n : ℝ)) ^ 2)
      (by positivity : (0 : ℝ) < (θ * (n : ℝ)) ^ 2)).mpr
      (by linarith [sq_nonneg (θ * (n : ℝ))])
  have h1 : ∑ n ∈ Finset.Ioo L (N + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹
      ≤ (1 / θ ^ 2) * ∑ n ∈ Finset.Ioo L (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
    calc ∑ n ∈ Finset.Ioo L (N + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹
        ≤ ∑ n ∈ Finset.Ioo L (N + 1), (1 / θ ^ 2) * ((n : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hcmp
      _ = (1 / θ ^ 2) * ∑ n ∈ Finset.Ioo L (N + 1), ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
  have h2 : ∑ n ∈ Finset.Ioo L (N + 1), ((n : ℝ) ^ 2)⁻¹ ≤ 2 / ((L : ℝ) + 1) := by
    simpa using sum_Ioo_inv_sq_le (α := ℝ) L (N + 1)
  have h3 : (1 / θ ^ 2) * (2 / ((L : ℝ) + 1)) ≤ 2 / (θ ^ 2 * (L : ℝ)) := by
    rw [show (1 / θ ^ 2) * (2 / ((L : ℝ) + 1)) = 2 / (θ ^ 2 * ((L : ℝ) + 1)) from by
      field_simp]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < θ ^ 2 * ((L : ℝ) + 1))
      (by positivity : (0 : ℝ) < θ ^ 2 * (L : ℝ))]
    nlinarith [sq_nonneg θ, hθ.le, hL]
  calc ∑ n ∈ Finset.Ioo L (N + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹
      ≤ (1 / θ ^ 2) * ∑ n ∈ Finset.Ioo L (N + 1), ((n : ℝ) ^ 2)⁻¹ := h1
    _ ≤ (1 / θ ^ 2) * (2 / ((L : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 / (θ ^ 2 * L) := h3

theorem fourier_truncation (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2)
    (L : ℕ) (hL : 1 ≤ L) (α : ℝ) (hα : 0 ≤ α) (hα2 : α ≤ 2 * Real.pi * θ) :
    ‖(q α : ℂ) - ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        ((1 / (2 * Real.pi) : ℂ) * ∫ β in (0 : ℝ)..(2 * Real.pi),
            (q β : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * β))
          * Complex.exp ((ℓ : ℂ) * Complex.I * α)‖
      ≤ 20000000 / (θ * L) := by
  have h2πθ : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [hθ, hθ1, Real.pi_pos]
  have hα2π : α ≤ 2 * Real.pi := le_trans hα2 h2πθ
  obtain ⟨hv1, hv2, _, _, _, _⟩ := Work.FIArea6.q_vanish_support q θ hqC hqsupp
  have hq_0 : q 0 = 0 := hv1 0 le_rfl
  have hq_2π : q (2 * Real.pi) = 0 := hv2 (2 * Real.pi) h2πθ
  -- the periodic extension of `q`
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ)),
      AddCircle.liftIoc_zero_continuous (by simp [hq_0, hq_2π])
        (Complex.continuous_ofReal.comp hqC.continuous).continuousOn⟩
  have hFcoeff : ∀ ℓ : ℤ, fourierCoeff (⇑F) ℓ = fcoef q ℓ := by
    intro ℓ
    rw [fcoef]
    show fourierCoeff (AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ))) ℓ = _
    rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
    simp only [zero_add, sub_zero, Complex.real_smul]
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) from by push_cast; ring]
    apply congrArg (fun z => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
    apply intervalIntegral.integral_congr
    intro x _
    simp only [fourier_coe_apply, smul_eq_mul, zero_add, sub_zero]
    rw [show (2 * ↑Real.pi * Complex.I * ↑(-ℓ) * ↑x / ↑(2 * Real.pi))
        = -(ℓ : ℂ) * Complex.I * ↑x from by push_cast; field_simp]
    ring
  have hFsumm : Summable (fun ℓ : ℤ => fourierCoeff (⇑F) ℓ) := by
    have h := fcoef_summable q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2
    exact h.congr (fun ℓ => (hFcoeff ℓ).symm)
  have hFx : F ((α : ℝ) : AddCircle (2 * Real.pi)) = (q α : ℂ) := by
    show (AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ)))
        ((α : ℝ) : AddCircle (2 * Real.pi)) = (q α : ℂ)
    exact liftIoc_eval q hq_0 hq_2π α hα hα2π
  set T : ℤ → ℂ := fun ℓ => fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I * α) with hT
  have hpt : HasSum (fun i => fourierCoeff (⇑F) i • fourier i ((α : ℝ) : AddCircle (2 * Real.pi)))
      (F ((α : ℝ) : AddCircle (2 * Real.pi))) :=
    has_pointwise_sum_fourier_series_of_summable hFsumm _
  have hpt1 : HasSum T (q α : ℂ) := by
    rw [hFx] at hpt
    refine hpt.congr_fun (fun i => ?_)
    show fcoef q i * Complex.exp ((i : ℂ) * Complex.I * α)
      = fourierCoeff (⇑F) i • fourier i ((α : ℝ) : AddCircle (2 * Real.pi))
    rw [hFcoeff i, fourier_coe_apply, smul_eq_mul]
    congr 1
    rw [show (2 * ↑Real.pi * Complex.I * ↑i * ↑α / ↑(2 * Real.pi))
        = (i : ℂ) * Complex.I * ↑α from by push_cast; field_simp]
  have hsym : HasSum T (q α : ℂ) (SummationFilter.symmetricIcc ℤ) :=
    hpt1.mono_left (SummationFilter.symmetricIcc ℤ).le_atTop
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), T n) atTop
      (𝓝 (q α : ℂ)) := SummationFilter.hasSum_symmetricIcc_iff.mp hsym
  have hlim : Tendsto
      (fun N : ℕ => ‖(∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), T n)
        - ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), T ℓ‖) atTop
      (𝓝 ‖(q α : ℂ) - ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), T ℓ‖) :=
    (htend.sub_const _).norm
  change ‖(q α : ℂ) - ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), T ℓ‖ ≤ 20000000 / (θ * L)
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop L] with N hN
  have hsub : Finset.Icc (-(L : ℤ)) (L : ℤ) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  rw [show (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), T n)
        - (∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), T ℓ)
      = ∑ ℓ ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)), T ℓ from by
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]]
  set A : ℝ := (1 / (2 * Real.pi)) * (10000000 * θ) with hAdef
  have hnormT : ∀ ℓ : ℤ, ‖T ℓ‖ ≤ A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ := by
    intro ℓ
    show ‖fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I * α)‖ ≤ A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
    rw [norm_mul, norm_exp_int' ℓ α, mul_one]
    calc ‖fcoef q ℓ‖
        ≤ (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) :=
          fcoef_bound q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 ℓ
      _ = A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ := by rw [hAdef]; ring
  have hGeven : Function.Even (fun ℓ : ℤ => A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) := by
    intro ℓ
    show A * (1 + (θ * ((-ℓ : ℤ) : ℝ)) ^ 2)⁻¹ = A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
    rw [show (θ * ((-ℓ : ℤ) : ℝ)) = -(θ * (ℓ : ℝ)) by push_cast; ring, neg_sq]
  have hGnn : ∀ ℓ : ℤ, 0 ≤ A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ := fun ℓ => by positivity
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun ℓ _ => hnormT ℓ)) ?_
  have hann := annulus_le L N (fun ℓ : ℤ => A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) hGeven hGnn
  have hann' : 2 * ∑ n ∈ Finset.Ioo L (N + 1), A * (1 + (θ * (((n : ℤ)) : ℝ)) ^ 2)⁻¹
      = 2 * ∑ n ∈ Finset.Ioo L (N + 1), A * (1 + (θ * (n : ℝ)) ^ 2)⁻¹ := by
    apply congrArg (fun z => 2 * z)
    apply Finset.sum_congr rfl
    intro n _
    norm_num
  rw [hann'] at hann
  refine le_trans hann ?_
  have hnum : ∑ n ∈ Finset.Ioo L (N + 1), A * (1 + (θ * (n : ℝ)) ^ 2)⁻¹
      ≤ A * (2 / (θ ^ 2 * L)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Ioo_bound L N θ hθ hL) (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_left hnum (by norm_num : (0 : ℝ) ≤ 2)) ?_
  rw [hAdef]
  rw [show 2 * ((1 / (2 * Real.pi)) * (10000000 * θ) * (2 / (θ ^ 2 * (L : ℝ))))
      = 20000000 / (Real.pi * θ * (L : ℝ)) from by field_simp; ring]
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : (0:ℕ) < L)
  have hθL : (0 : ℝ) < θ * (L : ℝ) := mul_pos hθ hL0
  refine div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 20000000) hθL ?_
  calc (θ * (L : ℝ)) = 1 * (θ * (L : ℝ)) := by ring
    _ ≤ Real.pi * (θ * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) hθL.le
    _ = Real.pi * θ * (L : ℝ) := by ring

end

end Work.FIArea5.S16
