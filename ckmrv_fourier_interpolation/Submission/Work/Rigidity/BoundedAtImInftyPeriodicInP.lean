/-
# Boundedness at `i∞` for `h`-periodic functions of moderate growth

`Work.Rigidity.boundedAtImInfty_of_periodic_inP` proves that a function `F ∈ 𝒫 = InP` which is
periodic of period **`1`** is bounded at the cusp `i∞`.  Here we deduce the general case: the
period may be an arbitrary real number `h > 0`.

The reduction is by the positive-real dilation `τ ↦ ⟨h, hh⟩ • τ` of the upper half plane
(`UpperHalfPlane.posRealAction`), which multiplies the coordinate by `h`:

  `G τ = F (⟨h, hh⟩ • τ)`.

Since `h • (1 +ᵥ τ) = h +ᵥ (h • τ)` in coordinates, `G` has period `1`, so it falls under the
period-`1` theorem; and `G ∈ 𝒫` because dilation by `h > 0` scales `im τ` and `‖τ‖` by the fixed
constant `h`.  Finally `F = G ∘ (⟨h⁻¹, ·⟩ • ·)` and dilation preserves the filter `atImInfty`, so
boundedness of `G` transfers back to `F`.
-/
import Mathlib
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP

noncomputable section

open UpperHalfPlane Filter Topology
open scoped Topology Manifold

namespace Work.Rigidity

theorem BoundedAtImInftyPeriodicInP {h : ℝ} (hh : 0 < h) {F : UpperHalfPlane → ℂ}
    (hP : Work.Kernels.InP F) (hper : ∀ τ : UpperHalfPlane, F ((h : ℝ) +ᵥ τ) = F τ) :
    UpperHalfPlane.IsBoundedAtImInfty F := by
  -- The dilated function, of period `1`.
  set G : UpperHalfPlane → ℂ :=
    fun τ => F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • τ) with hGdef
  -- Periodicity with period `1`, using `h • (1 +ᵥ τ) = h +ᵥ (h • τ)`.
  have hGper : ∀ τ : UpperHalfPlane, G ((1 : ℝ) +ᵥ τ) = G τ := by
    intro τ
    have hs : (⟨h, hh⟩ : {x : ℝ // 0 < x}) • ((1 : ℝ) +ᵥ τ)
        = h +ᵥ ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • τ) := by
      rw [UpperHalfPlane.ext_iff]
      simp only [UpperHalfPlane.coe_pos_real_smul, UpperHalfPlane.coe_vadd, Complex.real_smul]
      push_cast
      ring
    rw [hGdef]
    change F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • ((1 : ℝ) +ᵥ τ))
      = F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • τ)
    rw [hs, hper]
  -- Holomorphy of the dilation, via the lift `τ ↦ F (h • τ) ∘ ofComplex = (F ∘ ofComplex) ∘ (h·)`.
  have hGmdiff : MDiff (fun τ : UpperHalfPlane => F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • τ)) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hf : DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff).mp hP.1
    have hg : DifferentiableOn ℂ (fun z : ℂ => (h : ℂ) * z) {z : ℂ | 0 < z.im} := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℂ => (h : ℂ) * z) {z : ℂ | 0 < z.im}
        {z : ℂ | 0 < z.im} := by
      intro z hz
      have hz' : 0 < z.im := hz
      change 0 < ((h : ℂ) * z).im
      rw [show ((h : ℂ) * z).im = h * z.im by simp [Complex.mul_im]]
      exact mul_pos hh hz'
    have hcomp : DifferentiableOn ℂ ((F ∘ UpperHalfPlane.ofComplex) ∘ (fun z : ℂ => (h : ℂ) * z))
        {z : ℂ | 0 < z.im} := hf.comp hg hmaps
    refine hcomp.congr ?_
    intro z hz
    have hz' : 0 < z.im := hz
    have hstep : (⟨h, hh⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.ofComplex z
        = UpperHalfPlane.ofComplex ((h : ℂ) * z) := by
      rw [UpperHalfPlane.ext_iff]
      rw [UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos
        (by rw [show ((h:ℂ)*z).im = h*z.im by simp [Complex.mul_im]]; exact mul_pos hh hz')]
    show ((fun τ : UpperHalfPlane => F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • τ))
        ∘ UpperHalfPlane.ofComplex) z
        = ((F ∘ UpperHalfPlane.ofComplex) ∘ (fun z : ℂ => (h : ℂ) * z)) z
    show F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.ofComplex z)
        = F (UpperHalfPlane.ofComplex ((h : ℂ) * z))
    rw [hstep]
  -- Moderate growth of the dilation: `im (h • τ) = h * im τ`, `‖h • τ‖ = h * ‖τ‖`.
  have hGmg : Work.Kernels.ModerateGrowthOn Set.univ
      (fun τ : UpperHalfPlane => F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • τ)) := by
    obtain ⟨α, β, γ, hα, hβ, hγ, hb⟩ := hP.2
    refine ⟨α * max ((h⁻¹) ^ β) (h ^ γ), β, γ, by positivity, hβ, hγ, fun τ _ => ?_⟩
    have hτim : ((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ).im = h * τ.im :=
      UpperHalfPlane.pos_real_im _ _
    have hnorm : ‖(((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ : UpperHalfPlane) : ℂ)‖
        = h * ‖(τ : ℂ)‖ := by
      rw [UpperHalfPlane.coe_pos_real_smul, Complex.real_smul, norm_mul]
      congr 1
      simp [abs_of_pos hh]
    have h1 : (((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ).im)⁻¹ ^ β
        ≤ max ((h⁻¹) ^ β) (h ^ γ) * (τ.im)⁻¹ ^ β := by
      rw [hτim, mul_inv, Real.mul_rpow (inv_nonneg.mpr hh.le) (inv_nonneg.mpr τ.im_pos.le)]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (inv_nonneg.mpr τ.im_pos.le) _)
    have h2 : ‖(((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ : UpperHalfPlane) : ℂ)‖ ^ γ
        ≤ max ((h⁻¹) ^ β) (h ^ γ) * ‖(τ : ℂ)‖ ^ γ := by
      rw [hnorm, Real.mul_rpow hh.le (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)
    calc ‖F ((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ)‖
        ≤ α * ((((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ).im)⁻¹ ^ β
            + ‖(((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ : UpperHalfPlane) : ℂ)‖ ^ γ) :=
          hb _ (Set.mem_univ _)
      _ ≤ α * (max ((h⁻¹) ^ β) (h ^ γ) * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ)) := by
          apply mul_le_mul_of_nonneg_left _ hα
          calc ((((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ).im)⁻¹ ^ β
                + ‖(((⟨h,hh⟩ : {x : ℝ // 0 < x}) • τ : UpperHalfPlane) : ℂ)‖ ^ γ)
              ≤ max ((h⁻¹) ^ β) (h ^ γ) * (τ.im)⁻¹ ^ β
                + max ((h⁻¹) ^ β) (h ^ γ) * ‖(τ : ℂ)‖ ^ γ := add_le_add h1 h2
            _ = max ((h⁻¹) ^ β) (h ^ γ) * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ) := by ring
      _ = α * max ((h⁻¹) ^ β) (h ^ γ) * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ) := by ring
  have hGP : Work.Kernels.InP G := by rw [hGdef]; exact ⟨hGmdiff, hGmg⟩
  -- Apply the period-`1` theorem.
  have hbddG : UpperHalfPlane.IsBoundedAtImInfty G :=
    Work.Rigidity.boundedAtImInfty_of_periodic_inP hGP hGper
  -- Transfer the bound back along the inverse dilation `⟨h⁻¹, ·⟩ • ·`.
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbddG ⊢
  obtain ⟨M, A, hMA⟩ := hbddG
  refine ⟨M, h * A, fun τ hτ => ?_⟩
  set σ : UpperHalfPlane := (⟨h⁻¹, inv_pos.mpr hh⟩ : {x : ℝ // 0 < x}) • τ with hσ
  have hσim : σ.im = h⁻¹ * τ.im := by rw [hσ]; exact UpperHalfPlane.pos_real_im _ _
  have hAσ : A ≤ σ.im := by
    rw [hσim]
    have hle := mul_le_mul_of_nonneg_left hτ (inv_pos.mpr hh).le
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hh), one_mul] at hle
  have hGσ : G σ = F τ := by
    rw [hGdef]
    change F ((⟨h, hh⟩ : {x : ℝ // 0 < x}) • σ) = F τ
    congr 1
    rw [hσ, ← mul_smul]
    have : (⟨h, hh⟩ : {x : ℝ // 0 < x}) * ⟨h⁻¹, inv_pos.mpr hh⟩ = 1 := by
      ext; simp [mul_inv_cancel₀ (ne_of_gt hh)]
    rw [this, one_smul]
  have := hMA σ hAσ
  rwa [hGσ] at this

end Work.Rigidity
