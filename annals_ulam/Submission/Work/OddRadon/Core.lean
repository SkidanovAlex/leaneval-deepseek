import Mathlib
import Submission.Commons.Analysis.Radon.sphericalRadon_rot
import Submission.Commons.Analysis.Radon.radial_reduction_of_radonOver
import Submission.Work.Analysis.Radon.SphericalRadon

/-!
# The spherical Radon transform — definitions (`Work.OddRadon`, part 1)

Chapter of the spherical-Radon transform used by the odd-dimensional case of Ryabogin's
theorem (Annals **195** (2022), Step 3).

## Conventions fixed here

* `sphereArea m` is the **surface area** of the unit sphere `S^m ⊆ ℝ^{m+1}`, i.e. the total mass
  of the rotation-invariant surface measure `Measure.toSphere volume`.
  (It is *not* the Lebesgue measure of `S^m` as a subset of `ℝ^{m+1}`, which vanishes.)
* `sphericalRadon d g ξ` is `∫ ω, g ω` over the unit sphere of the orthogonal complement
  `(ℝ ∙ ξ)ᗮ ⊆ ℝ^d`, with respect to the surface measure on that sphere.  Equivalently it is the
  integral of `g` over the "equator" `S^{d-1} ∩ ξ^⊥`.  It is invariant under `ξ ↦ c • ξ`
  (`c ≠ 0`); at `ξ = 0` the complement degenerates to all of `ℝ^d`, so every statement below
  assumes `ξ ≠ 0` (usually `‖ξ‖ = 1`).
* `radonProfile d γ c` is the one-variable reduction: it is `sphericalRadon d (γ ∘ (· 0)) ξ`
  whenever `ξ` is a unit vector with `√(1 - (ξ 0)^2) = c`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **Surface area of the unit sphere** `S^m ⊆ ℝ^{m+1}`: the total mass of the
rotation-invariant surface measure.  `sphereArea 0 = 2`, `sphereArea 1 = 2π`, `sphereArea 2 = 4π`. -/
def sphereArea (m : ℕ) : ℝ :=
  ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere).real Set.univ

/-- The spherical Radon transform of `g` at `ξ`: the integral of `g` over the equator
`S^{d-1} ∩ ξ^⊥ = S((ℝ ∙ ξ)ᗮ)`, with respect to the rotation-invariant surface measure. -/
def sphericalRadon (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ ω : Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1, g ((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d))
    ∂(MeasureTheory.Measure.toSphere (volume : Measure (ℝ ∙ ξ)ᗮ))

/-- The one-variable profile form of the spherical Radon transform. -/
def radonProfile (d : ℕ) (γ : ℝ → ℝ) (c : ℝ) : ℝ :=
  sphereArea (d - 3) * ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * s)

/-- The first standard basis vector of `ℝ^d`. -/
def e0 (d : ℕ) [NeZero d] : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) 1

/-- The paper's normal direction `ξ(α) = (sin α, 0, …, 0, -cos α)`. -/
def radonXi (d : ℕ) (α : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm fun i : Fin d =>
    if (i : ℕ) = 0 then Real.sin α else if (i : ℕ) = d - 1 then -Real.cos α else 0

@[simp] lemma radonXi_apply (d : ℕ) (α : ℝ) (i : Fin d) :
    (radonXi d α) i = if (i : ℕ) = 0 then Real.sin α
      else if (i : ℕ) = d - 1 then -Real.cos α else 0 := rfl

@[simp] lemma e0_apply (d : ℕ) [NeZero d] (i : Fin d) :
    (e0 d) i = if i = (0 : Fin d) then 1 else 0 := by simp [e0]

lemma e0_norm (d : ℕ) [NeZero d] : ‖e0 d‖ = 1 := by simp [e0]

/-- The first coordinate is the pairing against `e0`. -/
lemma inner_e0 (d : ℕ) [NeZero d] (x : EuclideanSpace ℝ (Fin d)) : ⟪x, e0 d⟫ = x 0 := by
  rw [e0, EuclideanSpace.inner_single_right]
  simp

/-- `sphericalRadon` in terms of the library's `radonOver` (definitional). -/
lemma sphericalRadon_eq_radonOver (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d g ξ = Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ) g := rfl

/-- **Integrability on the equator of a continuous integrand.** -/
lemma integrable_sphere_radon (d : ℕ) [NeZero d] {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) (ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω : Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1 =>
        g ((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d)))
      (MeasureTheory.Measure.toSphere (volume : Measure (ℝ ∙ ξ)ᗮ)) := by
  have hcont : Continuous fun ω : Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1 =>
      g ((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d)) :=
    hg.comp (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.of_bound hcont.aestronglyMeasurable (max C 0) ?_
  filter_upwards with ω
  exact (hC ω (Set.mem_univ ω)).trans (le_max_left _ _)

/-- **The Radon transform is additive** (on continuous integrands, where the integral is the
honest one). -/
theorem sphericalRadon_add (d : ℕ) [NeZero d] {g₁ g₂ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun x => g₁ x + g₂ x) ξ
      = sphericalRadon d g₁ ξ + sphericalRadon d g₂ ξ := by
  simp only [sphericalRadon]
  rw [integral_add]
  · exact integrable_sphere_radon d h₁ ξ
  · exact integrable_sphere_radon d h₂ ξ

/-- **The Radon transform is homogeneous** (unconditionally: the Bochner integral is
homogeneous even when the integrand is not integrable). -/
theorem sphericalRadon_const_mul (d : ℕ) [NeZero d] (c : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun x => c * g x) ξ = c * sphericalRadon d g ξ := by
  simp only [sphericalRadon]
  rw [integral_const_mul]

@[simp] theorem sphericalRadon_zero (d : ℕ) [NeZero d] (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun _ => (0 : ℝ)) ξ = 0 := by
  simp [sphericalRadon]

theorem sphericalRadon_neg (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun x => - g x) ξ = - sphericalRadon d g ξ := by
  have := sphericalRadon_const_mul d (-1) g ξ
  simpa using this

theorem sphericalRadon_sub (d : ℕ) [NeZero d] {g₁ g₂ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun x => g₁ x - g₂ x) ξ
      = sphericalRadon d g₁ ξ - sphericalRadon d g₂ ξ := by
  simp only [sphericalRadon]
  rw [integral_sub]
  · exact integrable_sphere_radon d h₁ ξ
  · exact integrable_sphere_radon d h₂ ξ

/-- **The Radon transform kills odd functions.**  If `g (-x) = - g x` then `𝓡 g ξ = 0` for
every `ξ`.  This is the analytic content of the paper's condition `𝓡(w_j ρ_K^d)(ξ) = 0`. -/
theorem sphericalRadon_odd (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ∀ x, g (-x) = - g x) (ξ : EuclideanSpace ℝ (Fin d)) : sphericalRadon d g ξ = 0 := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => g (-x)) = fun x => - g x := funext hg
  have hstep : Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ) (fun x => - g x)
      = - Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ) g := by
    rw [Commons.Analysis.Radon.radonOver, Commons.Analysis.Radon.radonOver, ← integral_neg]
  have key : Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ) g
      = - Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ) g :=
    (Commons.Analysis.Radon.radonOver_neg ((ℝ ∙ ξ)ᗮ) g).symm.trans
      ((congrArg (Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ)) hfun).trans hstep)
  have hzero : Commons.Analysis.Radon.radonOver ((ℝ ∙ ξ)ᗮ) g = 0 := by linarith [key]
  simpa [sphericalRadon_eq_radonOver] using hzero

/-- The Radon transform is even in `ξ`: `ξ` and `-ξ` span the same line, hence have the same
equator. -/
theorem sphericalRadon_neg_arg (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) : sphericalRadon d g (-ξ) = sphericalRadon d g ξ := by
  rw [sphericalRadon_eq_radonOver, sphericalRadon_eq_radonOver]
  exact Commons.Analysis.Radon.radonOver_congr (Commons.Analysis.Radon.orthogonal_span_neg ξ) g

/-- The Radon transform is invariant under rescaling of `ξ` by a nonzero scalar (the equator
only depends on the line spanned by `ξ`). -/
theorem sphericalRadon_smul_arg (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ)
    {c : ℝ} (hc : c ≠ 0) (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d g (c • ξ) = sphericalRadon d g ξ := by
  have h : (ℝ ∙ (c • ξ))ᗮ = (ℝ ∙ ξ)ᗮ := by
    rw [Submodule.span_singleton_smul_eq (R := ℝ) (isUnit_iff_ne_zero.mpr hc) ξ]
  rw [sphericalRadon_eq_radonOver, sphericalRadon_eq_radonOver]
  exact Commons.Analysis.Radon.radonOver_congr h g

/-- **Rotation covariance of the Radon transform.**
`𝓡 (g ∘ L) ξ = 𝓡 g (L ξ)` for every linear isometry equivalence `L` of `ℝ^d`.

Warning (see `README.md`): the *naive* form `𝓡 (g ∘ L) (L ξ) = 𝓡 g ξ` — with `L` applied to `ξ`
rather than to the point at which `𝓡 g` is evaluated — is **false**; see
`Work.OddRadon.not_naive_covariance`.  The correct statement, and the one the paper uses, is
the covariance below, together with `sphericalRadon_isometry_invariant`. -/
theorem sphericalRadon_comp_isometry (d : ℕ) [NeZero d]
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun x => g (L x)) ξ = sphericalRadon d g (L ξ) := by
  have hspan : Submodule.map (L.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) (ℝ ∙ ξ)
      = ℝ ∙ L ξ := by
    rw [Submodule.map_span, Set.image_singleton]
    simp [LinearIsometryEquiv.coe_toLinearEquiv]
  have hK : Submodule.map (L.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) ((ℝ ∙ ξ)ᗮ)
      = (ℝ ∙ (L ξ))ᗮ := by
    rw [Submodule.map_orthogonal_equiv (ℝ ∙ ξ) L, hspan]
  let e : ((ℝ ∙ ξ)ᗮ) ≃ₗᵢ[ℝ] ((ℝ ∙ (L ξ))ᗮ) :=
    { L.toLinearEquiv.ofSubmodules ((ℝ ∙ ξ)ᗮ) ((ℝ ∙ (L ξ))ᗮ) hK with
      norm_map' := fun x => by
        simp [LinearEquiv.ofSubmodules_apply, LinearIsometryEquiv.coe_toLinearEquiv] }
  have he_coe : ∀ x : ((ℝ ∙ ξ)ᗮ),
      ((e x : ((ℝ ∙ (L ξ))ᗮ)) : EuclideanSpace ℝ (Fin d))
        = L ((x : ((ℝ ∙ ξ)ᗮ)) : EuclideanSpace ℝ (Fin d)) := by
    intro x
    change (((L.toLinearEquiv.ofSubmodules ((ℝ ∙ ξ)ᗮ) ((ℝ ∙ (L ξ))ᗮ) hK) x :
      ((ℝ ∙ (L ξ))ᗮ)) : EuclideanSpace ℝ (Fin d))
        = L ((x : ((ℝ ∙ ξ)ᗮ)) : EuclideanSpace ℝ (Fin d))
    rw [LinearEquiv.ofSubmodules_apply]
    rfl
  have hmp := Commons.Analysis.Radon.sphereCongr_measurePreserving e
  have hint := hmp.integral_comp'
    (fun y : Metric.sphere (0 : ((ℝ ∙ (L ξ))ᗮ)) 1 =>
      g ((y : ((ℝ ∙ (L ξ))ᗮ)) : EuclideanSpace ℝ (Fin d)))
  simp only [sphericalRadon]
  rw [← hint]
  apply integral_congr_ae
  filter_upwards with x
  show g (L ((x : ((ℝ ∙ ξ)ᗮ)) : EuclideanSpace ℝ (Fin d)))
    = g (((e x : ((ℝ ∙ (L ξ))ᗮ)) : EuclideanSpace ℝ (Fin d)))
  rw [he_coe x]

/-- **`𝓡 g` is invariant under an isometry leaving `g` invariant** (the paper's "the spherical
Radon transform commutes with rotations"). -/
theorem sphericalRadon_isometry_invariant (d : ℕ) [NeZero d]
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ∀ x, g (L x) = g x)
    (ξ : EuclideanSpace ℝ (Fin d)) : sphericalRadon d g (L ξ) = sphericalRadon d g ξ := by
  rw [← sphericalRadon_comp_isometry d L g ξ]
  exact congrArg (fun g' => sphericalRadon d g' ξ) (funext hg)

/-- The covariance form with the inverse: `𝓡 (g ∘ L) (L⁻¹ ξ) = 𝓡 g ξ`. -/
theorem sphericalRadon_comp_isometry_inv (d : ℕ) [NeZero d]
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    sphericalRadon d (fun x => g (L x)) (L.symm ξ) = sphericalRadon d g ξ := by
  rw [sphericalRadon_comp_isometry d L g (L.symm ξ), LinearIsometryEquiv.apply_symm_apply]

end Work.OddRadon
