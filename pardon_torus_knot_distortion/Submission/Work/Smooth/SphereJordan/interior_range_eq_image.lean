import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.disc_image_open_of_injective
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_isSimpleClosedCurve
import Submission.Work.Smooth.SphereJordan.OpenImageAux
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## Two auxiliary lemmas

The first lemma records that the finite part `ℂ` of the Riemann sphere is open, so that the
interior of the (image of a) subset of the finite part is computed in `ℂ`.  The second is the
*planar* invariance-of-domain statement of `interior_closure_V_eq.lean`: for an injective
continuous `f : 𝔻 → ℂ`, the interior of the image of the closed disc is the image of the open disc.
-/

/-- The interior of `coe '' A` in the Riemann sphere is `coe '' interior A`. -/
theorem interior_image_coe (A : Set ℂ) :
    interior ((↑) '' A : Set RiemannSphere) = (↑) '' interior A := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := interior_subset hy
    refine ⟨a, ?_, rfl⟩
    have hsub : ((↑) ⁻¹' (interior ((↑) '' A : Set RiemannSphere)) : Set ℂ) ⊆ A := by
      intro b hb
      obtain ⟨b', hb'A, hbb'⟩ := interior_subset hb
      have h : b' = b := OnePoint.coe_injective hbb'
      rw [h] at hb'A
      exact hb'A
    have hopen : IsOpen ((↑) ⁻¹' (interior ((↑) '' A : Set RiemannSphere)) : Set ℂ) :=
      isOpen_interior.preimage OnePoint.continuous_coe
    exact interior_maximal hsub hopen hy
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact interior_maximal (Set.image_mono interior_subset)
      (OnePoint.isOpenEmbedding_coe.isOpenMap (interior A) isOpen_interior) ⟨a, ha, rfl⟩

/-- **Invariance of domain at the boundary for an embedded disc in the plane**: the interior of the
image of the closed unit disc under an injective continuous map is the image of the open disc. -/
theorem interior_range_eq_openImage_plane {f : C(Disc, ℂ)} (hf : Function.Injective f) :
    interior (Set.range f) = openImage f := by
  apply Set.Subset.antisymm
  · rintro y hy
    obtain ⟨z, rfl⟩ := interior_subset hy
    refine ⟨z, ?_, rfl⟩
    by_contra hzlt
    have hznorm : ‖(z : ℂ)‖ = 1 := by
      have hle : ‖(z : ℂ)‖ ≤ 1 := by
        have h := z.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      exact le_antisymm hle (not_lt.mp hzlt)
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior (f z) hy
    have hball : Metric.ball (f z) ε ⊆ Set.range f := hεsub.trans interior_subset
    have hcne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; linarith
    let F : C(Disc, ℂ) := ⟨fun w => f z + ((ε / 2 : ℝ) : ℂ) * (w : ℂ), by fun_prop⟩
    have hFapply : ∀ w : Disc, F w = f z + ((ε / 2 : ℝ) : ℂ) * (w : ℂ) := fun w => rfl
    have hFinj : Function.Injective F := by
      intro a b hab
      rw [hFapply a, hFapply b] at hab
      have h2 : ((ε / 2 : ℝ) : ℂ) * (a : ℂ) = ((ε / 2 : ℝ) : ℂ) * (b : ℂ) :=
        add_left_cancel hab
      exact Subtype.ext (mul_left_cancel₀ hcne h2)
    have hFsub : Set.range F ⊆ Set.range f := by
      rintro p ⟨w, rfl⟩
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, hFapply w]
      have h1 : f z + ((ε / 2 : ℝ) : ℂ) * (w : ℂ) - f z = ((ε / 2 : ℝ) : ℂ) * (w : ℂ) := by
        ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
      have hw : ‖(w : ℂ)‖ ≤ 1 := by
        have h := w.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      nlinarith
    obtain ⟨g, hge, hginj⟩ := exists_lift_of_range_subset hf hFinj hFsub
    have hg0 : g 0 = z := by
      apply hf
      rw [hge 0, hFapply 0]
      simp
    let g' : C(Disc, ℂ) := ⟨fun w => ((g w : Disc) : ℂ), continuous_subtype_val.comp g.continuous⟩
    have hg'apply : ∀ w : Disc, g' w = ((g w : Disc) : ℂ) := fun w => rfl
    have hg'inj : Function.Injective g' := by
      intro a b hab
      rw [hg'apply a, hg'apply b] at hab
      exact hginj (Subtype.ext hab)
    have hmem := mem_interior_image_of_norm_lt_one g' hg'inj (0 : Disc) (by simp)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_interior (g' 0) hmem
    have hnormg0 : ‖g' 0‖ = 1 := by
      rw [hg'apply 0, hg0]; exact hznorm
    set q : ℂ := ((1 + ρ / 2 : ℝ) : ℂ) * (g' 0) with hqdef
    have hqball : q ∈ Metric.ball (g' 0) ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : q - g' 0 = ((ρ / 2 : ℝ) : ℂ) * (g' 0) := by
        rw [hqdef]; push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hnormg0,
        mul_one]
      linarith
    have hqle : ‖q‖ ≤ 1 := by
      obtain ⟨s, hs, hsq⟩ := interior_subset (hρsub hqball)
      rw [← hsq, hg'apply s]
      have h := (g s).2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hqnorm : ‖q‖ = 1 + ρ / 2 := by
      rw [hqdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + ρ / 2), hnormg0, mul_one]
    linarith
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact interior_mono (by rintro _ ⟨w, hw, rfl⟩; exact ⟨w, rfl⟩)
      (mem_interior_image_of_norm_lt_one f hf z hz)

/-! ## The target -/

theorem interior_range_eq_image {f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere)} (hf : Function.Injective f) : interior (Set.range f) = f '' {z : Work.Smooth.SphereJordan.Disc | ‖(z : ℂ)‖ < 1} := by
  obtain ⟨c, hc⟩ := exists_coe_notMem_range (f := f) hf
  -- the Möbius homeomorphism `M (x) = (x - c)⁻¹`, sending `c` to `∞`
  let M : RiemannSphere ≃ₜ RiemannSphere :=
    (Homeomorph.onePointCongr (Homeomorph.addRight (-c))).trans invHomeomorph
  have hMc : M (c : RiemannSphere) = infty := by
    show invHomeomorph
      ((Homeomorph.onePointCongr (Homeomorph.addRight (-c))) (c : RiemannSphere)) = infty
    have h1 : (Homeomorph.onePointCongr (Homeomorph.addRight (-c))) (c : RiemannSphere)
        = ((0 : ℂ) : RiemannSphere) := by
      show Homeomorph.onePointCongr (Homeomorph.addRight (-c)) (OnePoint.some c)
        = OnePoint.some 0
      simp [Homeomorph.onePointCongr]
    rw [h1, invHomeomorph_coe_zero]
  let g : C(Disc, RiemannSphere) := ⟨fun z => M (f z), M.continuous.comp f.continuous⟩
  have hg_apply : ∀ z, g z = M (f z) := fun z => rfl
  have hg_ne : ∀ z, g z ≠ infty := by
    intro z hz
    have h2 : M (f z) = M (c : RiemannSphere) := by rw [← hg_apply z, hz, hMc]
    exact hc ⟨z, M.injective h2⟩
  -- read `g` as a map into `ℂ` (it misses `∞`)
  set gfun : Disc → ℂ := fun z => Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg_ne z))
    with hgfun
  have hgfun_spec : ∀ z, ((gfun z : ℂ) : RiemannSphere) = g z := fun z =>
    Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hg_ne z))
  have hcont' : Continuous gfun := by
    rw [Topology.IsInducing.continuous_iff OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing]
    have h1 : ((↑) : ℂ → RiemannSphere) ∘ gfun = ⇑g := funext hgfun_spec
    rw [h1]; exact g.continuous
  let g' : C(Disc, ℂ) := ⟨gfun, hcont'⟩
  have hcoe_g' : ∀ z, ((g' z : ℂ) : RiemannSphere) = g z := hgfun_spec
  have hg'_inj : Function.Injective g' := by
    intro x y hxy
    have h1 : g x = g y := by rw [← hcoe_g' x, ← hcoe_g' y, hxy]
    exact hf (M.injective h1)
  -- the range of `g` and the image of the open disc
  have hrg : Set.range g = (↑) '' Set.range g' := by
    ext x; constructor
    · rintro ⟨z, rfl⟩
      exact ⟨g' z, ⟨z, rfl⟩, hcoe_g' z⟩
    · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (hcoe_g' z).symm⟩
  have hgO : g '' {z : Disc | ‖(z : ℂ)‖ < 1}
      = (↑) '' (g' '' {z : Disc | ‖(z : ℂ)‖ < 1}) := by
    ext x; constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g' z, ⟨z, hz, rfl⟩, hcoe_g' z⟩
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, (hcoe_g' z).symm⟩
  -- the spherical statement for the disc avoiding `∞`
  have hgoal_g : interior (Set.range g) = g '' {z : Disc | ‖(z : ℂ)‖ < 1} := by
    rw [hrg, hgO, interior_image_coe,
      interior_range_eq_openImage_plane (f := g') hg'_inj]
    simp only [openImage]
  -- transfer back along `M`
  have hrgM : Set.range g = M '' Set.range f := by
    rw [show ⇑g = (M : RiemannSphere → RiemannSphere) ∘ ⇑f from rfl]
    exact Set.range_comp (⇑M) (⇑f)
  have hMfO : M '' (f '' {z : Disc | ‖(z : ℂ)‖ < 1})
      = g '' {z : Disc | ‖(z : ℂ)‖ < 1} := by
    rw [← Set.image_comp]
    rfl
  have heq : M '' interior (Set.range f)
      = M '' (f '' {z : Disc | ‖(z : ℂ)‖ < 1}) := by
    rw [Homeomorph.image_interior M (Set.range f), ← hrgM, hgoal_g, hMfO]
  have hcancel : ∀ A : Set RiemannSphere, M.symm '' (M '' A) = A := by
    intro A
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
      rw [M.symm_apply_apply] at hyx
      rwa [← hyx]
    · intro hx
      exact ⟨M x, ⟨x, hx, rfl⟩, M.symm_apply_apply x⟩
  calc interior (Set.range f) = M.symm '' (M '' interior (Set.range f)) := (hcancel _).symm
    _ = M.symm '' (M '' (f '' {z : Disc | ‖(z : ℂ)‖ < 1})) := by rw [heq]
    _ = f '' {z : Disc | ‖(z : ℂ)‖ < 1} := hcancel _

end

end Work.Smooth.SphereJordan
