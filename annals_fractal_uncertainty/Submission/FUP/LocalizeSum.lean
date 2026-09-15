import Submission.FUP.LocalizeAux

open MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The `ℓ`-modulation sum for the localisation estimate

Han–Schlag's proof of Corollary 4.2 (`cor:UPY`) from the single-scale estimate
(`lem:mainlem`) applies the single-scale estimate to the modulations
`f_ℓ(x) = e^{2πi⟨x,ℓ⟩}f(x)`, `ℓ ∈ (2ℤ)^d`, and sums the results over `ℓ`.  The sums that have to
be controlled are (`hsq` = squared `H^{-d}` norm, see `LocalizeAux`):

* `Σ_ℓ hsq(f_ℓ) ≤ C‖f‖²`   (`tsum_hsq_mod_le`),
* `Σ_ℓ hsq(1_Sf_ℓ) ≤ C hsq(1_Sf)`,
* the `L²(cube(-1,1)+ℓ)`-pieces of `𝓕f` tile `𝓕f`,

all with a constant depending only on `d`.
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The `ℓ`-vector `ℓ = 2m ∈ (2ℤ)^d`. -/
noncomputable def ellVec (m : Fin d → ℤ) : ℝᵈ := WithLp.toLp 2 (fun i => 2 * (m i : ℝ))

lemma ellVec_apply (m : Fin d → ℤ) (i : Fin d) : ellVec m i = 2 * (m i : ℝ) := by rw [ellVec]

/-- The modulation phase `x ↦ e^{2πi⟨x,ℓ⟩}` for `ℓ = 2m`. -/
noncomputable def modPhase (m : Fin d → ℤ) (x : ℝᵈ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x (ellVec m) : ℝ) : ℂ))

lemma modPhase_eq (m : Fin d → ℤ) (x : ℝᵈ) :
    modPhase m x = Complex.exp (2 * Real.pi * Complex.I *
      ((inner ℝ x (ellVec m) : ℝ) : ℂ)) := rfl

lemma norm_modPhase (m : Fin d → ℤ) (x : ℝᵈ) : ‖modPhase m x‖ = 1 := by
  rw [modPhase, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x (ellVec m) : ℝ) : ℂ)).re = 0 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x (ellVec m) : ℝ) : ℂ))
        = ((2 * Real.pi * (inner ℝ x (ellVec m) : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp
  rw [hre, Real.exp_zero]

lemma measurable_modPhase (m : Fin d → ℤ) : Measurable (modPhase m) := by
  rw [show modPhase m = fun x : ℝᵈ =>
      Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x (ellVec m) : ℝ) : ℂ)) from rfl]
  fun_prop

/-- The modulation `f_ℓ` of `f` by `ℓ = 2m`. -/
noncomputable def modFun (m : Fin d → ℤ) (f : ℝᵈ → ℂ) : ℝᵈ → ℂ :=
  fun x => modPhase m x * f x

lemma memLp_modFun {m : Fin d → ℤ} {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    MemLp (modFun m f) 2 (volume : Measure ℝᵈ) := by
  refine hf.of_le (((measurable_modPhase m).aestronglyMeasurable).mul hf.1) ?_
  filter_upwards with x
  rw [modFun, norm_mul, norm_modPhase, one_mul]

/-- **The Fourier transform of a modulation** is the translate of `𝓕f`: `𝓕(f_ℓ)(ξ) = 𝓕f(ξ-ℓ)`. -/
lemma fourier_modFun {m : Fin d → ℤ} {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    ((𝓕 ((memLp_modFun (m := m) hf).toLp (modFun m f)) : Lp ℂ 2 (volume : Measure ℝᵈ)) :
        ℝᵈ → ℂ) =ᵐ[volume]
      (fun ξ => ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - ellVec m)) := by
  have h := Commons.Analysis.Fourier.fourier_modulation_ae d (ellVec m) f hf
  obtain ⟨hf', heq⟩ := h
  have hcoe : (memLp_modFun (m := m) hf).toLp (modFun m f) = hf'.toLp _ := by congr 1
  rw [hcoe]
  exact heq

end Submission.FUP

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

lemma ellVec_eq (m : Fin d → ℤ) : ellVec m = (fun i => 2 * (m i : ℝ) : Fin d → ℝ) := by
  rw [ellVec]

/-- The translate of the `H^{-d}` weight: `∫ ⟨η+ℓ⟩^{-2d}‖F η‖² = ∫ ⟨ξ⟩^{-2d}‖F (ξ-ℓ)‖²`. -/
lemma integral_hweight_shift (F : ℝᵈ → ℂ) (m : Fin d → ℤ) :
    (∫ η, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ)) * ‖F η‖ ^ 2)
      = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F (ξ - ellVec m)‖ ^ 2 := by
  have hmp : MeasurePreserving (fun η : ℝᵈ => η + ellVec m)
      (volume : Measure ℝᵈ) (volume : Measure ℝᵈ) :=
    measurePreserving_add_right _ _
  have hemb : MeasurableEmbedding (fun η : ℝᵈ => η + ellVec m) :=
    (Homeomorph.addRight (ellVec m)).measurableEmbedding
  have h := hmp.integral_comp hemb
    (fun ξ : ℝᵈ => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F (ξ - ellVec m)‖ ^ 2)
  simp only [add_sub_cancel_right] at h
  exact h

/-- **The `ℓ`-modulation sum** (with the lattice bound `hC₀` as an explicit hypothesis, so that it
can be instantiated with `Commons.Analysis.Fourier.finset_bracket_lattice_le`).
For any finite set of modulations, the sum of the squared `H^{-d}` norms is bounded by `C₀` times
the squared `L²` norm of `f`. -/
theorem sum_hsq_mod_le (C₀ : ℝ)
    (hC₀ : ∀ (η : ℝᵈ) (s : Finset (Fin d → ℤ)),
      (∑ m ∈ s, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ))) ≤ C₀) :
    ∀ (f : ℝᵈ → ℂ) (hf : MemLp f 2 (volume : Measure ℝᵈ)) (S : Finset (Fin d → ℤ)),
      (∑ m ∈ S, hsq ((memLp_modFun (m := m) hf).toLp (modFun m f)))
        ≤ C₀ * ‖hf.toLp f‖ ^ 2 := by
  intro f hf S
  classical
  set F : ℝᵈ → ℂ := ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) with hF
  have hFmem : MemLp F 2 (volume : Measure ℝᵈ) := Lp.memLp _
  have hFint : Integrable (fun η => ‖F η‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).mp hFmem
  -- Step 1: each term is the integral of the shifted weight times `‖F‖²`
  have hterm : ∀ m : Fin d → ℤ,
      hsq ((memLp_modFun (m := m) hf).toLp (modFun m f))
        = ∫ η, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ)) * ‖F η‖ ^ 2 := by
    intro m
    rw [hsq, integral_hweight_shift F m]
    have hae := fourier_modFun (m := m) hf
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ, hF]
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  -- Step 2: interchange the finite sum with the integral
  have hint : ∀ m ∈ S, Integrable
      (fun η => (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ)) * ‖F η‖ ^ 2) volume := by
    intro m _
    refine Integrable.mono' hFint ?_ ?_
    · exact (measurable_hweight.comp (measurable_id.add measurable_const)).aestronglyMeasurable.mul
        (hFmem.aestronglyMeasurable.norm.pow 2)
    · filter_upwards with η
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (hweight_le_one _)
  calc (∑ m ∈ S, ∫ η, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ)) * ‖F η‖ ^ 2)
      = ∫ η, (∑ m ∈ S, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ)) * ‖F η‖ ^ 2) :=
        (MeasureTheory.integral_finsetSum S hint).symm
    _ ≤ ∫ η, C₀ * ‖F η‖ ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η =>
          Finset.sum_nonneg fun m _ => mul_nonneg (hweight_nonneg _) (sq_nonneg _))
          (hFint.const_mul C₀) (Filter.Eventually.of_forall fun η => ?_)
        change (∑ m ∈ S, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ)) * ‖F η‖ ^ 2) ≤ C₀ * ‖F η‖ ^ 2
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hC₀ η S) (sq_nonneg _)
    _ = C₀ * ‖hf.toLp f‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [← MeasureTheory.Lp.norm_fourier_eq (hf.toLp f), norm_sq_eq_integral (𝓕 (hf.toLp f))]

end Submission.FUP
