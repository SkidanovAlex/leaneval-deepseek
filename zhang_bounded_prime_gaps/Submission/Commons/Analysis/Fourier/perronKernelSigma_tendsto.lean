import Mathlib
import Submission.Commons.Analysis.Fourier.perron_kernel_bound
noncomputable section

open Real Set Complex Filter intervalIntegral MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier


noncomputable def sigmaKernIntegrand (σ α : ℝ) (t : ℝ) : ℂ :=
  cexp (I * (↑α * ↑t)) / ((σ : ℂ) + I * ↑t)

noncomputable def unitKernIntegrand (β : ℝ) (u : ℝ) : ℂ :=
  cexp (I * (↑β * ↑u)) / ((1 : ℂ) + I * ↑u)

lemma sigma_den_ne_zero (σ t : ℝ) (hσ : σ ≠ 0) : ((σ : ℂ) + I * ↑t) ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have : σ = 0 := by simpa using hre
  exact hσ this

lemma unit_den_ne_zero (t : ℝ) : ((1 : ℂ) + I * ↑t) ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  norm_num at hre

lemma ofReal_inv_smul_den (σ t : ℝ) (hσ : σ ≠ 0) :
    ((1 : ℂ) + I * ↑(t / σ)) = ((↑(1 / σ : ℝ) : ℂ) * ((σ : ℂ) + I * ↑t)) := by
  apply Complex.ext <;> simp [Complex.ofReal_inv] <;> field_simp [hσ]

lemma sigma_eq_smul_unit_prod (σ α t : ℝ) (hσ : σ ≠ 0) :
    sigmaKernIntegrand σ α t = (((1 / σ : ℝ) : ℂ) * unitKernIntegrand (α * σ) (t / σ)) := by
  unfold sigmaKernIntegrand unitKernIntegrand
  have harg : (I * (↑α * ↑t : ℂ)) = I * ((↑(α * σ) * ↑(t / σ) : ℂ)) := by
    congr 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp [hσ]
  rw [harg]
  rw [ofReal_inv_smul_den σ t hσ]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ
  have hc' : ((↑(1 / σ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (one_div_ne_zero hσ)
  have hd2 : ((σ : ℂ) + I * ↑t) ≠ 0 := sigma_den_ne_zero σ t hσ
  field_simp [hc', hd2]

lemma sigma_eq_smul_unit (σ α t : ℝ) (hσ : σ ≠ 0) :
    sigmaKernIntegrand σ α t = (1 / σ : ℝ) • unitKernIntegrand (α * σ) (t / σ) := by
  rw [Algebra.smul_def]
  exact sigma_eq_smul_unit_prod σ α t hσ

lemma continuous_unitKernIntegrand (β : ℝ) : Continuous (unitKernIntegrand β) := by
  unfold unitKernIntegrand
  exact Continuous.div₀ (by fun_prop) (by fun_prop) (fun t => unit_den_ne_zero t)

lemma sigma_integral_eq_unit (R σ α : ℝ) (hσ : σ ≠ 0) :
    (∫ t in -R..R, sigmaKernIntegrand σ α t) =
      ∫ u in -(R / σ)..(R / σ), unitKernIntegrand (α * σ) u := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := -R) (b := R) (f := fun x : ℝ => x / σ) (f' := fun _ : ℝ => (1 / σ : ℝ))
    (g := unitKernIntegrand (α * σ))
    (h := by
      intro x hx
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id x).const_mul (1 / σ)))
    (h' := by fun_prop)
    (hg := continuous_unitKernIntegrand (α * σ))
  calc
    (∫ t in -R..R, sigmaKernIntegrand σ α t)
        = ∫ x in -R..R, (1 / σ : ℝ) • unitKernIntegrand (α * σ) (x / σ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change sigmaKernIntegrand σ α x = (1 / σ : ℝ) • unitKernIntegrand (α * σ) (x / σ)
          exact sigma_eq_smul_unit σ α x hσ
    _ = ∫ u in -(R / σ)..(R / σ), unitKernIntegrand (α * σ) u := by
          have h1 : (fun x : ℝ => (1 / σ : ℝ) • unitKernIntegrand (α * σ) (x / σ))
                = (fun x : ℝ => (1 / σ : ℝ) • ((unitKernIntegrand (α * σ)) ∘ (fun x : ℝ => x / σ)) x) := by
                funext x; rfl
          rw [h1]
          have hend : (-R / σ : ℝ) = -(R / σ) := by ring
          rw [← hend]
          exact hsub

lemma sigma_integral_eq_kern (R σ α : ℝ) (hσ : σ ≠ 0) :
    (∫ t in -R..R, sigmaKernIntegrand σ α t) = kern (R / σ) (α * σ) := by
  rw [sigma_integral_eq_unit R σ α hσ]
  unfold kern
  rfl

lemma tendsto_div_atTop_of_pos (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun R : ℝ => R / σ) atTop atTop := by
  have hσinv : 0 < 1 / σ := one_div_pos.mpr hσ
  have h := Filter.Tendsto.atTop_mul_const (r := 1 / σ) hσinv tendsto_id
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem perronKernelSigma_tendsto (σ α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0) :
    Filter.Tendsto
      (fun R : ℝ => (∫ (t : ℝ) in -R..R,
        Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t)))
      Filter.atTop
      (nhds (if 0 < α then 2 * ↑Real.pi * Complex.exp (-((σ : ℂ) * ↑α)) else 0)) := by
  change Tendsto (fun R : ℝ => ∫ t in -R..R, sigmaKernIntegrand σ α t) atTop
    (𝓝 (if 0 < α then 2 * ↑Real.pi * Complex.exp (-((σ : ℂ) * ↑α)) else 0))
  have hασ : α * σ ≠ 0 := mul_ne_zero hα (ne_of_gt hσ)
  have hkt := kern_tendsto_value (α * σ) hασ
  have hdiv : Tendsto (fun R : ℝ => R / σ) atTop atTop := tendsto_div_atTop_of_pos σ hσ
  have hcomp : Tendsto (fun R : ℝ => kern (R / σ) (α * σ)) atTop
      (𝓝 (if 0 < α * σ then (2 : ℂ) * ↑Real.pi * cexp (-(↑(α * σ) : ℂ)) else 0)) := hkt.comp hdiv
  have heq : (fun R : ℝ => ∫ t in -R..R, sigmaKernIntegrand σ α t)
      =ᶠ[atTop] fun R : ℝ => kern (R / σ) (α * σ) := by
    refine Eventually.of_forall (fun R => ?_)
    exact sigma_integral_eq_kern R σ α (ne_of_gt hσ)
  have hmain : Tendsto (fun R : ℝ => ∫ t in -R..R, sigmaKernIntegrand σ α t) atTop
      (𝓝 (if 0 < α * σ then (2 : ℂ) * ↑Real.pi * cexp (-(↑(α * σ) : ℂ)) else 0)) := by
    exact hcomp.congr' heq.symm
  convert hmain using 1
  · by_cases hpos : 0 < α
    · have hposβ : 0 < α * σ := mul_pos hpos hσ
      simp [hpos, hposβ]
      congr 1
      ring
    · have hneg : α < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hα
      have hnegβ : ¬ 0 < α * σ := by
        intro hb
        have hnon : α * σ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (le_of_lt hσ)
        exact (not_lt_of_ge hnon) hb
      simp [hpos, hnegβ]

end Commons.Analysis.Fourier
