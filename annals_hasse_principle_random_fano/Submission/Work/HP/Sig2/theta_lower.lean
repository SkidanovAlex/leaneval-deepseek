import Mathlib
import Submission.Work.HP.Sig2.ThetaDefs
import Submission.Work.HP.Sig2.ThetaPoissonSetup
import Submission.Work.HP.Sig2.tsum_cos_lower
import Submission.Work.HP.Sig2.gaussian_poisson_zero
import Submission.Work.HP.Sig2.summable_gauss_quad
import Submission.Work.HP.Sig2.theta_eq_tsum_coords
import Submission.Work.HP.Sig2.rhoD_eq_tsum_coords

/-!
# Lower bound for the shifted theta function of a lattice

`Work.HP.Sig2.theta_lower`: for a discrete lattice `Λ ⊆ ι → ℝ`, `s > 0` and `t` in the real span
of `Λ`, `((2 - rhoD Λ s) / rhoD Λ s) * theta Λ s 0 ≤ theta Λ s t`.

The proof follows the shifted Poisson summation formula: writing `t = ∑ i, u i • latCoe Λ i` in a
`ℤ`-basis of `Λ`, with `G = latGram Λ` the Gram matrix of that basis, the Poisson summation
formula (`gaussian_poisson_zero`) gives
`theta Λ s t = (s^rank/√det G) Σ_{m ∈ ℤ^rank} exp(-π s² mᵀG⁻¹m) cos (2π (m·u))`, and the dual
coordinates `m ↦ ∑ i, (G⁻¹ *ᵥ m) i • latCoe Λ i` identify this with
`(theta Λ s 0 / rhoD Λ s) Σ_{w ∈ Λ*} exp(-π s² ‖w‖²) cos (2π ⟪w,t⟫)`; dropping every `cos` to
`-1` and noting that the `w = 0` term equals `1` gives the claim.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Work.HP.Sig2

open Work.HP
open ThetaPoisson

variable {ι : Type*} [Fintype ι]

/-! ## Elementary complex algebra -/

/-- Real part of `exp (x + 2π i y)`. -/
lemma re_exp_phase (x y : ℝ) :
    (Complex.exp ((x : ℂ) + 2 * Real.pi * Complex.I * (y : ℂ))).re
      = Real.exp x * Real.cos (2 * Real.pi * y) := by
  have hre : ((x : ℂ) + 2 * Real.pi * Complex.I * (y : ℂ)).re = x := by
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
  have him : ((x : ℂ) + 2 * Real.pi * Complex.I * (y : ℂ)).im = 2 * Real.pi * y := by
    simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
  rw [Complex.exp_re, hre, him]

/-- The real part of the phase `2π i y`. -/
lemma re_phase (y : ℝ) : (2 * Real.pi * Complex.I * (y : ℂ)).re = 0 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  norm_num

lemma ofReal_mul_re' (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-! ## The dual Gaussian weight -/

/-- The Gaussian weight `w ↦ exp(-π s² ‖w‖²)` on the dual lattice. -/
noncomputable def dualWeight (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) : dualLat Λ → ℝ :=
  fun w => Real.exp (-(Real.pi * s ^ 2) * rNorm ((w : ι → ℝ)) ^ 2)

theorem dualWeight_nonneg (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) (w : dualLat Λ) :
    0 ≤ dualWeight Λ s w := Real.exp_nonneg _

@[simp] theorem dualWeight_zero (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) :
    dualWeight Λ s 0 = 1 := by
  simp [dualWeight, rNorm]

theorem dualWeight_tsum (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) :
    (∑' w : dualLat Λ, dualWeight Λ s w) = rhoD Λ s := rfl

theorem dualWeight_apply (Λ : Submodule ℤ (ι → ℝ)) (s : ℝ) (w : dualLat Λ) :
    dualWeight Λ s w = Real.exp (-(Real.pi * s ^ 2) * rNorm ((w : ι → ℝ)) ^ 2) := rfl

/-! ## The final bounding step -/

/-- The final step of the proof of `theta_lower`: the Poisson identity
`theta Λ s t = (theta Λ s 0 / rhoD Λ s) * Σ_w exp(-π s² ‖w‖²) cos (2π ⟪w,t⟫)`
together with positivity of `theta Λ s 0` and summability of the dual weights implies the bound. -/
theorem theta_lower_of_cos (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) (t : ι → ℝ)
    (hsum : Summable (dualWeight Λ s)) (hρ : 0 < rhoD Λ s) (hθ : 0 < theta Λ s 0)
    (hident : theta Λ s t = (theta Λ s 0 / rhoD Λ s) *
      ∑' w : dualLat Λ, dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t)) :
    ((2 - rhoD Λ s) / rhoD Λ s) * theta Λ s 0 ≤ theta Λ s t := by
  have hbound := tsum_cos_lower (dualWeight Λ s)
    (fun w : dualLat Λ => Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t)) 0
    hsum (dualWeight_nonneg Λ s)
    (by rw [show ((0 : dualLat Λ) : ι → ℝ) = 0 from rfl]; simp [dotR])
    (fun w => Real.neg_one_le_cos _) (fun w => Real.cos_le_one _)
  rw [dualWeight_zero Λ s, dualWeight_tsum Λ s] at hbound
  have hbound' : 2 - rhoD Λ s ≤
      ∑' w : dualLat Λ, dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t) := by
    linarith
  rw [hident]
  have h1 : (0 : ℝ) ≤ theta Λ s 0 / rhoD Λ s := div_nonneg hθ.le hρ.le
  have h2 := mul_le_mul_of_nonneg_left hbound' h1
  have h3 : (theta Λ s 0 / rhoD Λ s) * (2 - rhoD Λ s)
      = ((2 - rhoD Λ s) / rhoD Λ s) * theta Λ s 0 := by ring
  rw [h3] at h2
  exact h2

/-! ## Summability of the Gaussian weights -/

/-- Summability of `n ↦ exp(-(π/s²) nᵀGn)` on the coordinate lattice. -/
theorem summable_gram_weight (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) :
    Summable (fun n : Idx Λ → ℤ => Real.exp (-(Real.pi / s ^ 2) *
      (∑ i, ∑ j, (n i : ℝ) * latGram Λ i j * (n j : ℝ)))) :=
  (summable_gauss_quad (latGram Λ) (latGram_posDef Λ)).2 (Real.pi / s ^ 2) (by positivity)

/-- Summability of `m ↦ exp(-π s² mᵀ G⁻¹ m)` on the coordinate lattice. -/
theorem summable_invGram_weight (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) :
    Summable (fun m : Idx Λ → ℤ => Real.exp (-(Real.pi * s ^ 2) *
      (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ)))) :=
  (summable_gauss_quad (latGram Λ)⁻¹ (latGram_posDef Λ).inv).2 (Real.pi * s ^ 2) (by positivity)

/-- The dual Gaussian weights are summable. -/
theorem summable_dual_weight (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) : Summable (dualWeight Λ s) := by
  rw [← (latDualEquiv Λ).summable_iff]
  have h2 : (dualWeight Λ s ∘ ⇑(latDualEquiv Λ)) = fun m : Idx Λ → ℤ =>
      Real.exp (-(Real.pi * s ^ 2) * (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) := by
    funext m
    simp only [Function.comp_apply, dualWeight, latDualEquiv_apply, rNorm_latDualMap_sq]
  rw [h2]
  exact summable_invGram_weight Λ s hs

/-- Positivity of `rhoD Λ s`. -/
theorem rhoD_pos (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s) :
    0 < rhoD Λ s := by
  have hsum := summable_invGram_weight Λ s hs
  have h1 := hsum.le_tsum (0 : Idx Λ → ℤ) (fun n _ => Real.exp_nonneg _)
  have h0 : Real.exp (-(Real.pi * s ^ 2) * (∑ i, ∑ j, ((0 : Idx Λ → ℤ) i : ℝ) *
      (latGram Λ)⁻¹ i j * ((0 : Idx Λ → ℤ) j : ℝ))) = 1 := by simp
  rw [h0] at h1
  rw [rhoD_eq_tsum_coords Λ s]
  linarith

/-- Positivity of `theta Λ s 0`. -/
theorem theta_zero_pos (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ] (s : ℝ) (hs : 0 < s) :
    0 < theta Λ s 0 := by
  have hu : latMap Λ (0 : Idx Λ → ℝ) = (0 : ι → ℝ) := map_zero _
  rw [theta_eq_tsum_coords Λ s (0 : ι → ℝ) (0 : Idx Λ → ℝ) hu]
  rw [show (∑' n : Idx Λ → ℤ, Real.exp (-(Real.pi / s ^ 2) *
        (∑ i, ∑ j, ((n i : ℝ) - (0 : Idx Λ → ℝ) i) * latGram Λ i j
          * ((n j : ℝ) - (0 : Idx Λ → ℝ) j))))
      = ∑' n : Idx Λ → ℤ, Real.exp (-(Real.pi / s ^ 2) *
          (∑ i, ∑ j, (n i : ℝ) * latGram Λ i j * (n j : ℝ))) from by
    refine tsum_congr fun n => congrArg (fun z : ℝ => Real.exp (-(Real.pi / s ^ 2) * z)) ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp]
  have hsum := summable_gram_weight Λ s hs
  have h1 := hsum.le_tsum (0 : Idx Λ → ℤ) (fun n _ => Real.exp_nonneg _)
  have h0 : Real.exp (-(Real.pi / s ^ 2) * (∑ i, ∑ j, ((0 : Idx Λ → ℤ) i : ℝ) *
      latGram Λ i j * ((0 : Idx Λ → ℤ) j : ℝ))) = 1 := by simp
  rw [h0] at h1
  linarith

/-! ## The shifted Poisson summation formula in coordinates -/

/-- The shifted Poisson summation formula for the theta function in coordinates (with shift
`i ↦ -(u i)`): exactly the `ℤ^κ` Gaussian Poisson summation of `gaussian_poisson_zero` for the
Gram matrix `latGram Λ`, with the left hand side written in terms of `(n - u)ᵀ G (n - u)`. -/
theorem gaussian_poisson_lat (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) (u : Idx Λ → ℝ) :
    (∑' n : Idx Λ → ℤ, Complex.exp (((-(Real.pi / s ^ 2) *
        (∑ i, ∑ j, ((n i : ℝ) - u i) * latGram Λ i j * ((n j : ℝ) - u j))) : ℝ)))
      = ((s : ℂ) ^ Fintype.card (Idx Λ) / ((Real.sqrt (latGram Λ).det : ℝ) : ℂ)) *
        ∑' m : Idx Λ → ℤ, Complex.exp (((-(Real.pi * s ^ 2) *
            (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) : ℝ)
          + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * (fun i => -(u i)) j) : ℝ)) := by
  have hP := gaussian_poisson_zero (latGram Λ) (latGram_posDef Λ) s hs (fun i => -(u i))
  have hL : (∑' n : Idx Λ → ℤ, Complex.exp (((-(Real.pi / s ^ 2) *
        (∑ i, ∑ j, ((n i : ℝ) - u i) * latGram Λ i j * ((n j : ℝ) - u j))) : ℝ)))
      = (∑' n : Idx Λ → ℤ, Complex.exp (((-(Real.pi / s ^ 2) *
          (∑ i, ∑ j, ((n i : ℝ) + (fun i => -(u i)) i) * latGram Λ i j
            * ((n j : ℝ) + (fun i => -(u i)) j))) : ℝ))) := by
    refine tsum_congr fun n => congrArg Complex.exp (congrArg (fun z : ℝ => (z : ℂ)) ?_)
    refine congrArg (fun z : ℝ => -(Real.pi / s ^ 2) * z) ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [sub_eq_add_neg, Pi.neg_apply]
  rw [hL]
  exact hP

/-- The shifted Poisson summation formula in `cos` form: for every `u : ℝ^κ`,
`theta Λ s (∑ i, u i • latCoe Λ i) = (s^κ/√det G) Σ_m exp(-π s² mᵀG⁻¹m) cos (2π (m·u))`. -/
theorem theta_eq_poisson_cos (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) (u : Idx Λ → ℝ) :
    theta Λ s (latMap Λ u) = (s ^ Fintype.card (Idx Λ) / Real.sqrt (latGram Λ).det) *
      ∑' m : Idx Λ → ℤ, Real.exp (-(Real.pi * s ^ 2) *
        (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) *
        Real.cos (2 * Real.pi * (∑ j, (m j : ℝ) * u j)) := by
  have hP := gaussian_poisson_lat Λ s hs u
  have hL : (theta Λ s (latMap Λ u) : ℂ) = ∑' n : Idx Λ → ℤ, Complex.exp
      (((-(Real.pi / s ^ 2) * (∑ i, ∑ j, ((n i : ℝ) - u i) * latGram Λ i j
        * ((n j : ℝ) - u j))) : ℝ)) := by
    rw [theta_eq_tsum_coords Λ s (latMap Λ u) u rfl, Complex.ofReal_tsum]
    exact tsum_congr fun n => Complex.ofReal_exp _
  have hK : ((s : ℂ) ^ Fintype.card (Idx Λ) / ((Real.sqrt (latGram Λ).det : ℝ) : ℂ))
      = (((s ^ Fintype.card (Idx Λ) / Real.sqrt (latGram Λ).det : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_div]
  have hsumC : Summable (fun m : Idx Λ → ℤ => Complex.exp
      (((-(Real.pi * s ^ 2) * (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) : ℝ)
        + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * (fun i => -(u i)) j) : ℝ))) := by
    refine Summable.of_norm_bounded
      (f := fun m : Idx Λ → ℤ => Complex.exp
        (((-(Real.pi * s ^ 2) * (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) : ℝ)
          + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * (fun i => -(u i)) j) : ℝ)))
      (g := fun m : Idx Λ → ℤ => Real.exp (-(Real.pi * s ^ 2) *
        (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))))
      (summable_invGram_weight Λ s hs) ?_
    intro m
    rw [Complex.norm_exp, Complex.add_re, Complex.ofReal_re, re_phase, add_zero]
  have hmain : theta Λ s (latMap Λ u)
      = (s ^ Fintype.card (Idx Λ) / Real.sqrt (latGram Λ).det) *
        (∑' m : Idx Λ → ℤ, (Complex.exp (((-(Real.pi * s ^ 2) *
            (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) : ℝ)
          + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * (fun i => -(u i)) j) : ℝ))).re) := by
    have h := congrArg Complex.re (hL.trans hP)
    rw [Complex.ofReal_re, hK, ofReal_mul_re', Complex.re_tsum hsumC] at h
    exact h
  have hterms : (∑' m : Idx Λ → ℤ, (Complex.exp (((-(Real.pi * s ^ 2) *
            (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) : ℝ)
          + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * (fun i => -(u i)) j) : ℝ))).re)
      = ∑' m : Idx Λ → ℤ, Real.exp (-(Real.pi * s ^ 2) *
          (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) *
          Real.cos (2 * Real.pi * (∑ j, (m j : ℝ) * u j)) := by
    refine tsum_congr fun m => ?_
    rw [re_exp_phase]
    have hph : (∑ j, (m j : ℝ) * (fun i => -(u i)) j) = -(∑ j, (m j : ℝ) * u j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.neg_apply]; ring
    rw [hph,
      show 2 * Real.pi * (-(∑ j, (m j : ℝ) * u j)) = -(2 * Real.pi * (∑ j, (m j : ℝ) * u j))
        from by ring,
      Real.cos_neg]
  rw [hmain, hterms]

/-- The shifted Poisson summation formula in dual-lattice form: for `t` in the real span of `Λ`,
`theta Λ s t = (theta Λ s 0 / rhoD Λ s) Σ_{w ∈ Λ*} exp(-π s² ‖w‖²) cos (2π ⟪w,t⟫)`. -/
theorem theta_cos_identity (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) (t : ι → ℝ) (u : Idx Λ → ℝ) (hu : latMap Λ u = t) :
    theta Λ s t = (theta Λ s 0 / rhoD Λ s) *
      ∑' w : dualLat Λ, dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t) := by
  have hgen := theta_eq_poisson_cos Λ s hs u
  have h0 := theta_eq_poisson_cos Λ s hs (0 : Idx Λ → ℝ)
  rw [map_zero] at h0
  have hZ : (∑' m : Idx Λ → ℤ, Real.exp (-(Real.pi * s ^ 2) *
      (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ)))) = rhoD Λ s :=
    (rhoD_eq_tsum_coords Λ s).symm
  have hzero : theta Λ s 0 = (s ^ Fintype.card (Idx Λ) / Real.sqrt (latGram Λ).det) *
      (∑' m : Idx Λ → ℤ, Real.exp (-(Real.pi * s ^ 2) *
        (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ)))) := by
    rw [h0]
    congr 1
    refine tsum_congr fun m => ?_
    rw [show (2 * Real.pi * (∑ j, (m j : ℝ) * (0 : Idx Λ → ℝ) j)) = 0 from by simp,
      Real.cos_zero, mul_one]
  have hdual : (∑' m : Idx Λ → ℤ, Real.exp (-(Real.pi * s ^ 2) *
        (∑ i, ∑ j, (m i : ℝ) * (latGram Λ)⁻¹ i j * (m j : ℝ))) *
        Real.cos (2 * Real.pi * (∑ j, (m j : ℝ) * u j)))
      = ∑' w : dualLat Λ, dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t) := by
    rw [← Equiv.tsum_eq (latDualEquiv Λ) (fun w : dualLat Λ =>
      dualWeight Λ s w * Real.cos (2 * Real.pi * dotR ((w : ι → ℝ)) t))]
    refine tsum_congr fun m => ?_
    rw [dualWeight_apply, latDualEquiv_apply, rNorm_latDualMap_sq, ← hu,
      dotR_latDualMap_latMap Λ m u]
  rw [← hu, hgen, hdual, hzero, hZ, ← hu]
  have hρne : rhoD Λ s ≠ 0 := ne_of_gt (rhoD_pos Λ s hs)
  field_simp

/-- Lower bound for the shifted theta function of a lattice: for `s > 0` and `t` in the real span
of `Λ`, `((2 - rhoD Λ s)/rhoD Λ s) * theta Λ s 0 ≤ theta Λ s t`.  Follows from the shifted Poisson
summation formula by taking real parts and using `Re (exp (-2πi ⟨w,t⟩)) ≥ -1`. -/
theorem theta_lower {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (hs : 0 < s) (t : ι → ℝ) (ht : t ∈ Submodule.span ℝ (Λ : Set (ι → ℝ))) :
    ((2 - rhoD Λ s) / rhoD Λ s) * theta Λ s 0 ≤ theta Λ s t := by
  obtain ⟨u, hu⟩ : ∃ u : Idx Λ → ℝ, latMap Λ u = t :=
    LinearMap.mem_range.mp ((mem_range_latMap Λ).mpr ht)
  exact theta_lower_of_cos Λ s hs t (summable_dual_weight Λ s hs) (rhoD_pos Λ s hs)
    (theta_zero_pos Λ s hs) (theta_cos_identity Λ s hs t u hu)

end Work.HP.Sig2
