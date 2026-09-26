/-
# Holomorphy in `τ` of the CKMRV contour integral

This file transfers the general parametric-integral engine of
`Work.Asymptotics.ParamIntegral` to the CKMRV objects of `Work.Kernels`:

* `Work.Asymptotics.differentiableOn_cotransform` : holomorphy of
  `τ ↦ ∫_0^∞ K(τ,it)e^{-πr²t}dt` on an open set of `ℂ` on which the integrand is dominated;
* `Work.Asymptotics.mdifferentiableAt_kernelTransform` : the same statement for
  `τ ↦ Work.Kernels.kernelTransform K τ r` on `ℍ`, which is clause (1) of
  `Work.Kernels.SatisfiesThm31`.

The two analytic hypotheses are exactly the ones that the concrete kernel estimates must supply:

* a *dominator* `bound`, integrable on `(0,∞)`, for the contour integrand on the open set; its
  construction from Theorem 4.9(4) is `Work.Asymptotics.divisor_bound` /
  `Work.Asymptotics.norm_Kfun_le_of_divisor`;
* holomorphy of `τ ↦ K(τ,it)` on the open set for a.e. `t`, which holds whenever the contour
  carries no pole of `K` — see `Work.Asymptotics.Obstruction` for the precise obstruction and
  `Work.Asymptotics.ContourClean`.

**Warning (the naive statement is false).**  `MDiff (fun τ : ℍ => Fgen K τ r)` is *not* a
theorem about the literal `Work.Kernels.kernelTransform`: for every `τ` on one of the
`SL(2,ℤ)`-translates of the imaginary axis (for instance every `τ = 1 + it`, `t > 0`) the
integrand has a non-removable pole on the contour, so `kernelTransform` takes the junk value `0`
there.  See `Work.Asymptotics.Obstruction`.
-/
import Mathlib
import Submission.Work.Asymptotics.Basic
import Submission.Work.Asymptotics.ParamIntegral
import Submission.Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology Manifold

namespace Work.Asymptotics

/-- **Holomorphy of the contour integral on an open set of `ℂ`.**  If `U` is open, `bound` is an
integrable dominator for the contour integrand on `U`, and for a.e. `t` the function
`τ ↦ K(τ,it)e^{-πr²t}` is holomorphic on `U`, then `τ ↦ ∫_0^∞ K(τ,it)e^{-πr²t}dt` is holomorphic
on `U`.

The measurability hypothesis (needed for the Bochner integral) is discharged internally by
`Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn`, so only the two analytic
inputs remain. -/
theorem differentiableOn_cotransform {K : ℍ → ℍ → ℂ} {r : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (bound : ℝ → ℝ) (hbint : IntegrableOn bound (Set.Ioi (0 : ℝ)))
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖contourIntegrand K r z t‖ ≤ bound t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => contourIntegrand K r z' t) z)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => contourIntegrand K r z t)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (cotransform K r) U :=
  differentiableOn_integral_Ioi hU bound hbint hbb hdiff hmeas
    (fun z hz => aeStronglyMeasurable_deriv_of_differentiableOn hU hmeas hdiff z hz)

/-- The `sin²` prefactor of the transform is holomorphic, so the same statement holds for
`transformC`. -/
theorem differentiableOn_transformC {K : ℍ → ℍ → ℂ} {r : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (bound : ℝ → ℝ) (hbint : IntegrableOn bound (Set.Ioi (0 : ℝ)))
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖contourIntegrand K r z t‖ ≤ bound t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => contourIntegrand K r z' t) z)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => contourIntegrand K r z t)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (transformC K r) U :=
  (differentiableOn_const (c := sinSq r)).mul (differentiableOn_cotransform hU bound hbint hbb hdiff hmeas)

/-- **Holomorphy in `τ` of the CKMRV transform (clause (1) of `SatisfiesThm31`).**  If the
contour integrand is dominated on a neighbourhood of `τ₀` and is holomorphic in `τ` there for
a.e. `t`, then `τ ↦ Work.Kernels.kernelTransform K τ r` is complex differentiable at `τ₀`. -/
theorem mdifferentiableAt_kernelTransform {K : ℍ → ℍ → ℂ} {r : ℝ} {τ₀ : ℍ} {U : Set ℂ}
    (hU : IsOpen U) (hτ₀ : (τ₀ : ℂ) ∈ U) (_hsub : U ⊆ {z : ℂ | 0 < z.im})
    (bound : ℝ → ℝ) (hbint : IntegrableOn bound (Set.Ioi (0 : ℝ)))
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖contourIntegrand K r z t‖ ≤ bound t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => contourIntegrand K r z' t) z)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => contourIntegrand K r z t)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.kernelTransform K τ r) τ₀ := by
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have hOn : DifferentiableOn ℂ (transformC K r) U :=
    differentiableOn_transformC hU bound hbint hbb hdiff hmeas
  have hAt : DifferentiableAt ℂ (transformC K r) (τ₀ : ℂ) :=
    hOn.differentiableAt (hU.mem_nhds hτ₀)
  refine hAt.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos] with z hz
  have hcoe : (UpperHalfPlane.ofComplex z : ℍ) = ⟨z, hz⟩ :=
    UpperHalfPlane.ofComplex_apply_of_im_pos hz
  show (fun τ : ℍ => Work.Kernels.kernelTransform K τ r)
      (UpperHalfPlane.ofComplex z) = transformC K r z
  rw [hcoe, transformC_eq_kernelTransform K r hz]

/-- The same statement for the generating function `F = gaussTerm + kernelTransform` (the
`gaussTerm` term being entire). -/
theorem mdifferentiableAt_Fgen {K : ℍ → ℍ → ℂ} {r : ℝ} {τ₀ : ℍ} {U : Set ℂ}
    (hU : IsOpen U) (hτ₀ : (τ₀ : ℂ) ∈ U) (hsub : U ⊆ {z : ℂ | 0 < z.im})
    (bound : ℝ → ℝ) (hbint : IntegrableOn bound (Set.Ioi (0 : ℝ)))
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖contourIntegrand K r z t‖ ≤ bound t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => contourIntegrand K r z' t) z)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => contourIntegrand K r z t)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.Fgen K τ r) τ₀ := by
  have h1 := mdifferentiableAt_kernelTransform hU hτ₀ hsub bound hbint hbb hdiff hmeas
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.gaussTerm τ r) τ₀ := by
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    have heq : (fun z : ℂ => Work.Kernels.gaussTerm (UpperHalfPlane.ofComplex z) r)
        =ᶠ[𝓝 (τ₀ : ℂ)]
          (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z * (r : ℂ) ^ 2)) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos] with z hz
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      simp only [Work.Kernels.gaussTerm]
    exact (by fun_prop : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z * (r : ℂ) ^ 2))
        (τ₀ : ℂ)).congr_of_eventuallyEq heq
  have hfun_eq : (fun τ : ℍ => Work.Kernels.gaussTerm τ r + Work.Kernels.kernelTransform K τ r)
      = ((fun τ : ℍ => Work.Kernels.gaussTerm τ r)
          + fun τ : ℍ => Work.Kernels.kernelTransform K τ r) := by
    funext τ; rfl
  show MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
    (fun τ : ℍ => Work.Kernels.gaussTerm τ r + Work.Kernels.kernelTransform K τ r) τ₀
  rw [hfun_eq]
  exact h2.add h1

/-! ## The packaged analytic input

The two hypotheses of `mdifferentiableAt_kernelTransform` are what the concrete kernel estimates
must provide, point by point.  We package them once and for all: `GoodAt K r τ₀` says that the
contour integrand of `K` at parameter `r` is dominated near `τ₀` and is holomorphic in `τ` there
for a.e. `t`.  Proving `GoodAt` for the CKMRV kernels is the content of CKMRV Lemma 4.12 and
the `q`-expansion analysis of Section 4.4 of the paper; the reduction of `GoodAt` to a *bound*
on `K` along the contour and the *cleanliness* of the contour is
`Work.Asymptotics.goodAt_of_contour_bound` (below) and
`Work.Asymptotics.Obstruction` (for why cleanliness cannot be dropped). -/

/-- The analytic input needed at a point. -/
def GoodAt (K : ℍ → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) : Prop :=
  ∃ U ∈ 𝓝 (τ₀ : ℂ), U ⊆ {z : ℂ | 0 < z.im} ∧ ∃ bound : ℝ → ℝ,
    IntegrableOn bound (Set.Ioi (0 : ℝ)) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖contourIntegrand K r z t‖ ≤ bound t) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => contourIntegrand K r z' t) z) ∧
    (∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => contourIntegrand K r z t)
      (volume.restrict (Set.Ioi (0 : ℝ))))

/-- `GoodAt` gives holomorphy of the transform at `τ₀`. -/
theorem mdifferentiableAt_kernelTransform_of_goodAt {K : ℍ → ℍ → ℂ} {r : ℝ} {τ₀ : ℍ}
    (h : GoodAt K r τ₀) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.kernelTransform K τ r) τ₀ := by
  obtain ⟨U, hUne, hsub, bound, hbint, hbb, hdiff, hmeas⟩ := h
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 hUne
  have hR' : (0:ℝ) < R := hR
  refine mdifferentiableAt_kernelTransform Metric.isOpen_ball (Metric.mem_ball_self hR')
    (fun z hz => hsub (hRU hz)) bound hbint ?_ ?_ ?_
  · exact hbb.mono fun t ht z hz => ht z (hRU hz)
  · exact hdiff.mono fun t ht z hz => ht z (hRU hz)
  · intro z hz; exact hmeas z (hRU hz)

/-- `GoodAt` gives holomorphy of `Fgen` at `τ₀`. -/
theorem mdifferentiableAt_Fgen_of_goodAt {K : ℍ → ℍ → ℂ} {r : ℝ} {τ₀ : ℍ}
    (h : GoodAt K r τ₀) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Work.Kernels.Fgen K τ r) τ₀ := by
  obtain ⟨U, hUne, hsub, bound, hbint, hbb, hdiff, hmeas⟩ := h
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 hUne
  have hR' : (0:ℝ) < R := hR
  refine mdifferentiableAt_Fgen Metric.isOpen_ball (Metric.mem_ball_self hR')
    (fun z hz => hsub (hRU hz)) bound hbint ?_ ?_ ?_
  · exact hbb.mono fun t ht z hz => ht z (hRU hz)
  · exact hdiff.mono fun t ht z hz => ht z (hRU hz)
  · intro z hz; exact hmeas z (hRU hz)

/-- A *bound on the kernel along the contour*, uniform in `τ` over a ball, together with the
holomorphy of `τ ↦ K(τ,it)` for a.e. `t` (which holds whenever the contour is pole-free),
produces `GoodAt`.  This is the shape in which CKMRV Lemma 4.12 is used. -/
theorem goodAt_of_contour_bound {K : ℍ → ℍ → ℂ} {r : ℝ} {τ₀ : ℍ} {R : ℝ} (hR : 0 < R)
    (hsub : ∀ z : ℂ, dist z (τ₀ : ℂ) < R → 0 < z.im)
    (bound : ℝ → ℝ) (hbint : IntegrableOn bound (Set.Ioi (0 : ℝ)))
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z : ℂ, dist z (τ₀ : ℂ) < R →
      ‖contourIntegrand K r z t‖ ≤ bound t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z : ℂ, dist z (τ₀ : ℂ) < R →
      DifferentiableAt ℂ (fun z' => contourIntegrand K r z' t) z)
    (hmeas : ∀ z : ℂ, dist z (τ₀ : ℂ) < R →
      AEStronglyMeasurable (fun t : ℝ => contourIntegrand K r z t)
        (volume.restrict (Set.Ioi (0 : ℝ)))) :
    GoodAt K r τ₀ :=
  ⟨Metric.ball (τ₀ : ℂ) R, Metric.ball_mem_nhds _ hR, hsub, bound, hbint,
    hbb.mono fun t ht z hz => ht z (by simpa [Metric.mem_ball] using hz),
    hdiff.mono fun t ht z hz => ht z (by simpa [Metric.mem_ball] using hz),
    fun z hz => hmeas z (by simpa [Metric.mem_ball] using hz)⟩

end Work.Asymptotics
