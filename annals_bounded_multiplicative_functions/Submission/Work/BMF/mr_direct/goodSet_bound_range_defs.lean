import Mathlib
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.goodSet_E1_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary vocabulary for the range-generalised good-set bound

This file fixes the notation used by `Work.BMF.mr_direct.goodSet_bound_range`, together with
the elementary estimates about it:

* `winLo K X₁ j = X₁ e^{-(j+1)/K}` and `winHi K X₂ j = X₂ e^{-j/K}` are the two ends of the
  `j`-th Buchstab window of `mrDirect.remPolyR`;
* `winE b P Q K X₁ X₂ j` is the (weighted) coefficient energy of the `j`-th remainder
  polynomial over that window;
* `setIntegral_mono_of_le_on`, `setIntegral_le_intervalIntegral` are the two elementary
  set-integral comparison facts needed to pass from an integral over `u ⊆ [-S,S]` to an
  integral over `[-S,S]`;
* `winE_le_exp`, `winE_le_two` are the two estimates of `winE` by harmonic sums.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

noncomputable section

/-- Lower end of the `j`-th Buchstab window: `X₁ e^{-(j+1)/K}`. -/
def winLo (K X₁ : ℝ) (j : ℕ) : ℝ := X₁ * Real.exp (-((j : ℝ) + 1) / K)

/-- Upper end of the `j`-th Buchstab window: `X₂ e^{-j/K}`. -/
def winHi (K X₂ : ℝ) (j : ℕ) : ℝ := X₂ * Real.exp (-(j : ℝ) / K)

/-- Coefficient energy of `mrDirect.remPolyR b P Q K X₁ X₂ j` over its window. -/
def winE (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
    ‖b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ^ 2 / (m : ℝ) ^ 2

/-- `mrDirect.remPolyR` is the sum over `winLo`/`winHi`, by definition. -/
lemma remPolyR_eq_sum (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ) (t : ℝ) :
    Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t
      = ∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
          b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ *
            (m : ℂ) ^ (-(1 + Complex.I * t)) := rfl

/-- `mrDirect.remPolyR` is continuous in `t`. -/
lemma continuous_remPolyR (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ) (hX : 0 < X₁) :
    Continuous fun t : ℝ => Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t := by
  unfold Work.BMF.mrDirect.remPolyR
  refine continuous_finsetSum _ fun m hm => ?_
  have hm1 : 1 ≤ m := by
    have hmem := Finset.mem_Icc.mp hm
    have h1 : 1 ≤ ⌈X₁ * Real.exp (-((j : ℝ) + 1) / K)⌉₊ :=
      Nat.ceil_pos.mpr (mul_pos hX (Real.exp_pos _))
    omega
  exact Continuous.mul (Continuous.mul continuous_const continuous_const)
    (Work.BMF.mr_direct.continuous_cpow_neg_one_sub hm1)

/-- `winE` is nonnegative. -/
lemma winE_nonneg (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ) :
    0 ≤ winE b P Q K X₁ X₂ j := by
  rw [winE]
  exact Finset.sum_nonneg fun m _ => by positivity

/-! ### Two elementary set-integral comparison facts -/

/-- Monotonicity of the integral over a fixed (possibly non-measurable) set: it is enough to
know the pointwise inequality on `u` and that the larger of the two functions is integrable
on `u`. -/
lemma setIntegral_mono_of_le_on {u : Set ℝ} {f h : ℝ → ℝ}
    (hf : Measurable f) (hh : Measurable h)
    (hfi : IntegrableOn h u (volume : Measure ℝ))
    (h0 : ∀ x, 0 ≤ f x) (hle : ∀ x ∈ u, f x ≤ h x) :
    ∫ x in u, f x ≤ ∫ x in u, h x := by
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall h0) hfi ?_
  show ∀ᵐ x ∂(volume.restrict u : Measure ℝ), f x ≤ h x
  rw [ae_restrict_iff (measurableSet_le hf hh)]
  exact MeasureTheory.ae_of_all _ hle

/-- An integral over a subset of `[-S,S]` is at most the interval integral over `[-S,S]`,
for a nonnegative continuous integrand. -/
lemma setIntegral_le_intervalIntegral {u : Set ℝ} {h : ℝ → ℝ} {S : ℝ}
    (hS : 0 ≤ S) (hu : u ⊆ Set.Icc (-S) S) (hh : Continuous h)
    (hnn : ∀ x ∈ Set.Icc (-S) S, 0 ≤ h x) :
    ∫ x in u, h x ≤ ∫ x in (-S)..S, h x := by
  have hint : IntegrableOn h (Set.Icc (-S) S) (volume : Measure ℝ) :=
    hh.continuousOn.integrableOn_Icc
  have hnn' : (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[(volume : Measure ℝ).restrict (Set.Icc (-S) S)] h := by
    show ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Icc (-S) S)), (0 : ℝ) ≤ h x
    rw [ae_restrict_iff (measurableSet_le measurable_const hh.measurable)]
    exact MeasureTheory.ae_of_all _ hnn
  have h1 : ∫ x in u, h x ≤ ∫ x in Set.Icc (-S) S, h x :=
    setIntegral_mono_set hint hnn' (MeasureTheory.ae_of_all _ (fun x hx => hu hx))
  rw [intervalIntegral.integral_of_le (by linarith : -S ≤ S), integral_Icc_eq_integral_Ioc] at *
  exact h1

/-! ### Estimates of `winE` -/

/-- `winE` is at most the plain harmonic sum over its window. -/
lemma winE_le_inv_sq (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ) (hb : ∀ m, ‖b m‖ ≤ 1) :
    winE b P Q K X₁ X₂ j
      ≤ ∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j), (1 : ℝ) / (m : ℝ) ^ 2 := by
  rw [winE]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcoef : ‖b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ≤ 1 := by
    have hb1 : ‖b m‖ ≤ 1 := hb m
    have h2 : 1 ≤ Work.BMF.mrDirect.omegaCount P Q m + 1 := by omega
    have h3 : ‖((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ≤ 1 :=
      norm_inv_natCast_le_one h2
    calc ‖b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖
        = ‖b m‖ * ‖((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ :=
          norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hb1 h3 (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have h4 : ‖b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ^ 2 ≤ 1 := by
    have h5 := norm_nonneg (b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹)
    nlinarith [hcoef, h5]
  calc ‖b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹‖ ^ 2 / (m : ℝ) ^ 2
      ≤ 1 / (m : ℝ) ^ 2 := div_le_div_of_nonneg_right h4 (by positivity)
    _ = 1 / (m : ℝ) ^ 2 := rfl

/-- `winE` is at most `2 / winLo`, i.e. `2 e^{(j+1)/K}/X₁`. -/
lemma winE_le_exp (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 0 < X₁) :
    winE b P Q K X₁ X₂ j ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / X₁ := by
  have hA : 0 < winLo K X₁ j := mul_pos hX (Real.exp_pos _)
  have h1 := Work.BMF.mr_direct.natIcc_inv_sq_sum_le (winLo K X₁ j) (winHi K X₂ j) hA
  have h2 : 2 / winLo K X₁ j = 2 * Real.exp (((j : ℝ) + 1) / K) / X₁ := by
    rw [winLo]
    have he : Real.exp (-((j : ℝ) + 1) / K) = (Real.exp (((j : ℝ) + 1) / K))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [he]
    have hpos : (0 : ℝ) < Real.exp (((j : ℝ) + 1) / K) := Real.exp_pos _
    field_simp
  rw [← h2]
  exact le_trans (winE_le_inv_sq b P Q K X₁ X₂ j hb) h1

/-- `winE ≤ 2`, independently of all the parameters. -/
lemma winE_le_two (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 0 < X₁) :
    winE b P Q K X₁ X₂ j ≤ 2 := by
  have hA : 0 < winLo K X₁ j := mul_pos hX (Real.exp_pos _)
  have hc : 1 ≤ ⌈winLo K X₁ j⌉₊ := Nat.ceil_pos.mpr hA
  have h1 : (∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j), (1 : ℝ) / (m : ℝ) ^ 2)
      ≤ 2 := by
    have h2 := Work.BMF.mr_direct.sum_Icc_inv_sq_le ⌈winLo K X₁ j⌉₊ ⌊winHi K X₂ j⌋₊ hc
    have h3 : (2 : ℝ) / (⌈winLo K X₁ j⌉₊ : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hc : (0 : ℝ) < (⌈winLo K X₁ j⌉₊ : ℕ))]
      have h4 : (1 : ℝ) ≤ (⌈winLo K X₁ j⌉₊ : ℝ) := by exact_mod_cast hc
      linarith
    exact le_trans h2 h3
  exact le_trans (winE_le_inv_sq b P Q K X₁ X₂ j hb) h1

end

end Work.BMF.mr_direct
