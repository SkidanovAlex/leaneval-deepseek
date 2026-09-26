import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.PCopy.Setup
import Submission.Work.Smooth.SphereJordan.OpenImageAux
import Submission.Work.Smooth.SphereJordan.openImage_isOpen
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI

namespace Work.Smooth.SphereJordan

/-!
# The interior of the closure of the bounded side is the bounded side

For a plane Schoenflies datum `S` of a closed plane curve `γ` (the bounded side `S.V`, the spanning
embedding `S.e : 𝔻 → ℂ` whose image is `closure S.V`), the interior of `closure S.V` is `S.V`.

The content is *invariance of domain at the boundary of the disc*: for an injective continuous map
`f : 𝔻 → ℂ`, the interior of `range f` is exactly the image of the open disc.  Indeed, using
`S.range_e` and `plane_schoenflies_openDisc_eq` the goal rewrites to that statement for `f = S.e`.

The proof of the disc statement combines two results already in the chapter:

* `mem_interior_image_of_norm_lt_one` (in `OpenImageAux`) — invariance of domain *at interior
  points*: the image of the open disc is open;
* `exists_lift_of_range_subset` (in `DiscSpansAPI`) — a map into the image of an embedded disc
  lifts through it.

If a boundary point `f z`, `‖z‖ = 1`, lay in the interior of `range f`, then a small disc around
`f z` would be contained in `range f`; lifting the map `w ↦ f z + (ε/2)·w` through `f` would produce
an injective continuous `g : 𝔻 → 𝔻` with `g 0 = z ∈ ∂𝔻`.  But the image of the open disc under `g`
is open in `ℂ` (invariance of domain at the interior point `0`) and lies in `𝔻`, while it contains
`g 0` of norm `1`: a neighbourhood of `g 0` would be contained in the closed unit disc, which is
impossible.
-/

/-- **Invariance of domain at the boundary for an embedded disc**: the interior of the image of the
closed unit disc under an injective continuous map is the image of the open disc. -/
theorem pcinterior_range_eq_openImage {f : C(Disc, ℂ)} (hf : Function.Injective f) :
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

/-- The interior of the closure of the bounded side of a plane Schoenflies datum is the bounded
side itself. -/
theorem pcinterior_closure_V_eq {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    interior (closure S.V) = S.V := by
  rw [← S.range_e, pcinterior_range_eq_openImage S.inj]
  exact Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S

end Work.Smooth.SphereJordan
