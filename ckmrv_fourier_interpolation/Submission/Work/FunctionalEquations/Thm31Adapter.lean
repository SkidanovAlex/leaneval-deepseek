import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Kernels.Theorem31
import Submission.Work.RadialSpace.contDiff_comp_norm_omega

/-!
# Adapter: CKMRV Theorem 3.1 hypotheses `⇒` a `FunctionalEquationSolution`

`Work.Kernels.SatisfiesThm31 d k₀ F Ft` encodes the hypotheses (1)--(5) of CKMRV
Theorem 3.1 for a pair of *radial* profiles `F, Ft : ℍ → ℝ → ℂ`, whereas
`Work.FE.FunctionalEquationSolution d` states the same hypotheses (i)--(v) for
functions `ℂ → ℝ^d → ℂ` on the full upper half plane and Euclidean space.

This file bridges the two: the radial profile is lifted to Euclidean space by
`x ↦ F τ ‖x‖` (extended by `0` off the upper half plane), and every field of
`FunctionalEquationSolution` is transported across the lift.

The only analytic input is that an *even analytic* function `g : ℝ → ℂ` gives an
analytic function `x ↦ g ‖x‖` on `ℝ^d`; this is
`Work.RadialSpace.contDiff_comp_norm_omega` (`C^ω = analytic`, since in this
Mathlib `⊤ : ℕ∞ω` is `ω`).

## Main result

* `Work.FunctionalEquations.Thm31Adapter`
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane Manifold

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The radial lift `x ↦ g ‖x‖` of a one-variable function to `ℝ^d`. -/
def radialLift (g : ℝ → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ := fun x => g ‖x‖

@[simp] lemma radialLift_apply (g : ℝ → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    radialLift g x = g ‖x‖ := rfl

/-- A family of radial profiles, extended to all of `ℂ` by `0` off the upper half plane. -/
def extFun (F : ℍ → ℝ → ℂ) (τ : ℂ) : EuclideanSpace ℝ (Fin d) → ℂ :=
  if h : 0 < τ.im then radialLift (d := d) (F ⟨τ, h⟩) else 0

lemma extFun_of_pos {F : ℍ → ℝ → ℂ} {τ : ℂ} (hτ : 0 < τ.im) :
    extFun (d := d) F τ = radialLift (d := d) (F ⟨τ, hτ⟩) := by
  rw [extFun]; exact dif_pos hτ

lemma radial_extFun (F : ℍ → ℝ → ℂ) (τ : ℂ) : Radial (extFun (d := d) F τ) := by
  rw [extFun]
  by_cases h : 0 < τ.im
  · rw [dif_pos h]; exact fun x y hy => by simp only [radialLift_apply, hy]
  · rw [dif_neg h]; exact fun _ _ _ => rfl

/-- The radial derivative of the lift is the iterated derivative of the profile. -/
lemma radialDeriv_extFun (F : ℍ → ℝ → ℂ) (heF : ∀ τ : ℍ, Function.Even (F τ))
    {τ : ℂ} (hτ : 0 < τ.im) (ℓ : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    radialDeriv ℓ (extFun (d := d) F τ) x = iteratedDeriv ℓ (F ⟨τ, hτ⟩) ‖x‖ := by
  have hfun : (fun r : ℝ => radialLift (d := d) (F ⟨τ, hτ⟩) (realIncl (n := d) r)) =
      F ⟨τ, hτ⟩ := by
    funext r
    rw [radialLift_apply, Work.Sampling.realIncl_norm]
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr]; exact heF ⟨τ, hτ⟩ r
  rw [extFun_of_pos hτ]
  show iteratedDeriv ℓ (fun r : ℝ => radialLift (d := d) (F ⟨τ, hτ⟩) (realIncl (n := d) r)) ‖x‖
      = iteratedDeriv ℓ (F ⟨τ, hτ⟩) ‖x‖
  rw [hfun]

/-- Holomorphy in `τ` of the radial profile lifts to holomorphy of the lift. -/
lemma differentiableOn_extFun (F : ℍ → ℝ → ℂ) (hF : ∀ r : ℝ, MDiff (fun τ : ℍ => F τ r))
    (x : EuclideanSpace ℝ (Fin d)) :
    DifferentiableOn ℂ (fun τ : ℂ => extFun (d := d) F τ x) {z | 0 < z.im} := by
  have h := (UpperHalfPlane.mdifferentiable_iff).mp (hF ‖x‖)
  refine h.congr fun z hz => ?_
  show extFun (d := d) F z x = F (UpperHalfPlane.ofComplex z) ‖x‖
  rw [extFun_of_pos hz, radialLift_apply]
  exact (UpperHalfPlane.comp_ofComplex_of_im_pos (fun τ : ℍ => F τ ‖x‖) z hz).symm

/-- For even `d` the complex power `(i/τ)^(d/2)` of `slashFactor` equals the natural power. -/
lemma slashFactor_eq_of_even (hd : Even d) (τ : ℂ) :
    slashFactor d τ = (Complex.I / τ) ^ (d / 2) := by
  obtain ⟨k, hk⟩ := hd
  rw [slashFactor]
  have hdk : d / 2 = k := by omega
  have hcast : (d : ℂ) / 2 = ((d / 2 : ℕ) : ℂ) := by
    rw [hdk, hk]; push_cast; ring
  rw [hcast, Complex.cpow_natCast]

/-- Smoothness (analyticity) of the radial profile lifts to the lift on `ℝ^d`. -/
lemma contDiff_extFun (F : ℍ → ℝ → ℂ) (hF : ∀ τ : ℍ, ContDiff ℝ ⊤ (F τ))
    (heF : ∀ τ : ℍ, Function.Even (F τ)) (τ : ℂ) :
    ContDiff ℝ ⊤ (extFun (d := d) F τ) := by
  rw [extFun]
  by_cases h : 0 < τ.im
  · rw [dif_pos h]
    exact Work.RadialSpace.contDiff_comp_norm_omega (hF ⟨τ, h⟩) (heF ⟨τ, h⟩)
  · rw [dif_neg h]
    exact contDiff_const

theorem Thm31Adapter {d k₀ : ℕ} [NeZero d] (hd : Even d) (F Ft : ℍ → ℝ → ℂ)
    (h : Work.Kernels.SatisfiesThm31 d k₀ F Ft)
    (hsF : ∀ τ : ℍ, ContDiff ℝ ⊤ (F τ)) (hsFt : ∀ τ : ℍ, ContDiff ℝ ⊤ (Ft τ))
    (heF : ∀ τ : ℍ, Function.Even (F τ)) (heFt : ∀ τ : ℍ, Function.Even (Ft τ)) :
    Nonempty (FunctionalEquationSolution d) := by
  rcases h with ⟨hhol1, hhol2, hgrowth1, hgrowth2, hunif, hrec1, hrec2, hfe⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact extFun (d := d) F
  · exact extFun (d := d) Ft
  · exact fun x => differentiableOn_extFun F hhol1 x
  · exact fun x => differentiableOn_extFun Ft hhol2 x
  · exact fun τ => contDiff_extFun F hsF heF τ
  · exact fun τ => contDiff_extFun Ft hsFt heFt τ
  · exact fun τ => radial_extFun F τ
  · exact fun τ => radial_extFun Ft τ
  · intro k ℓ
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hb⟩ := hgrowth1 k ℓ
    refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
    intro τ x hτ
    rw [radialDeriv_extFun F heF hτ ℓ x]
    simpa using hb ⟨τ, hτ⟩ ‖x‖
  · intro k ℓ
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hb⟩ := hgrowth2 k ℓ
    refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
    intro τ x hτ
    rw [radialDeriv_extFun Ft heFt hτ ℓ x]
    simpa using hb ⟨τ, hτ⟩ ‖x‖
  · obtain ⟨α, β, hα, hβ, hb⟩ := hunif
    refine ⟨α, β, hα, hβ, fun τ x hτ h1 h2 => ?_⟩
    rw [extFun_of_pos (F := F) (τ := τ) hτ, radialLift_apply]
    calc ‖F ⟨τ, hτ⟩ ‖x‖‖ ≤ max ‖F ⟨τ, hτ⟩ ‖x‖‖ ‖Ft ⟨τ, hτ⟩ ‖x‖‖ := le_max_left _ _
      _ ≤ α * ((⟨τ, hτ⟩ : ℍ).im) ^ (-β) := hb ⟨τ, hτ⟩ ‖x‖
            (by rw [UpperHalfPlane.mk_re]; exact h1) (by rw [UpperHalfPlane.mk_re]; exact h2)
      _ = α * τ.im ^ (-β) := by rw [UpperHalfPlane.mk_im]
  · obtain ⟨α, β, hα, hβ, hb⟩ := hunif
    refine ⟨α, β, hα, hβ, fun τ x hτ h1 h2 => ?_⟩
    rw [extFun_of_pos (F := Ft) (τ := τ) hτ, radialLift_apply]
    calc ‖Ft ⟨τ, hτ⟩ ‖x‖‖ ≤ max ‖F ⟨τ, hτ⟩ ‖x‖‖ ‖Ft ⟨τ, hτ⟩ ‖x‖‖ := le_max_right _ _
      _ ≤ α * ((⟨τ, hτ⟩ : ℍ).im) ^ (-β) := hb ⟨τ, hτ⟩ ‖x‖
            (by rw [UpperHalfPlane.mk_re]; exact h1) (by rw [UpperHalfPlane.mk_re]; exact h2)
      _ = α * τ.im ^ (-β) := by rw [UpperHalfPlane.mk_im]
  · intro τ x hτ
    have hτ2 : 0 < (τ + 2).im := by simpa using hτ
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    rw [extFun_of_pos (F := F) (τ := τ + 2) hτ2,
        extFun_of_pos (F := F) (τ := τ + 1) hτ1, extFun_of_pos (F := F) (τ := τ) hτ]
    simp only [radialLift_apply]
    have hv2 : ((2 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 2, hτ2⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    have hv1 : ((1 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 1, hτ1⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    rw [← hv2, ← hv1]
    exact hrec1 ⟨τ, hτ⟩ ‖x‖
  · intro τ x hτ
    have hτ2 : 0 < (τ + 2).im := by simpa using hτ
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    rw [extFun_of_pos (F := Ft) (τ := τ + 2) hτ2,
        extFun_of_pos (F := Ft) (τ := τ + 1) hτ1, extFun_of_pos (F := Ft) (τ := τ) hτ]
    simp only [radialLift_apply]
    have hv2 : ((2 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 2, hτ2⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    have hv1 : ((1 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 1, hτ1⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    rw [← hv2, ← hv1]
    exact hrec2 ⟨τ, hτ⟩ ‖x‖
  · intro τ x hτ
    have hS : ((ModularGroup.S • (⟨τ, hτ⟩ : ℍ) : ℍ) : ℂ) = -1/τ := by
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk, inv_neg,
          div_eq_mul_inv, neg_one_mul]
    have hneg : 0 < (-1/τ).im := by rw [← hS]; exact UpperHalfPlane.im_pos _
    have hSe : (⟨-1/τ, hneg⟩ : ℍ) = ModularGroup.S • (⟨τ, hτ⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_mk]; exact hS.symm
    rw [extFun_of_pos (F := F) (τ := τ) hτ, extFun_of_pos (F := Ft) hneg,
        radialLift_apply, radialLift_apply]
    have hslash : slashFactor d τ = (Complex.I / (((⟨τ, hτ⟩ : ℍ)) : ℂ)) ^ (d / 2) := by
      rw [slashFactor_eq_of_even (d := d) hd τ, UpperHalfPlane.coe_mk]
    have hgauss : gaussianFun d τ x = Work.Kernels.gaussTerm ⟨τ, hτ⟩ ‖x‖ := by
      simp only [gaussianFun, Work.Kernels.gaussTerm, Complex.ofReal_pow]
    rw [hslash, hSe, hgauss]
    exact hfe ⟨τ, hτ⟩ ‖x‖

end

end Work.FunctionalEquations
