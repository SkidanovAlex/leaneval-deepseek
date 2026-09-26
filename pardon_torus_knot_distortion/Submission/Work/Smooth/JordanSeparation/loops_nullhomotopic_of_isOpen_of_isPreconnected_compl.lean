import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_approximation
import Submission.Work.Smooth.JordanSeparation.loopIn_nullhomotopic
import Submission.Work.Smooth.JordanSeparation.sphere_reduction_of_plane_crux
import Submission.Work.Smooth.JordanSeparation.simplyConnectedSpace_onePoint_complex
import Submission.Work.Smooth.SphereJordan.jordanCurve_twoComponents

/-!
# Loops in an open subset of the Riemann sphere with connected complement

The main result of this file is
`Work.Smooth.JordanSeparation.loops_nullhomotopic_of_isOpen_of_isPreconnected_compl`: every loop in
an open set `D ⊆ S²` whose complement `Dᶜ` is preconnected is null-homotopic in `D`.

The proof has three layers:

* the **lattice-walk approximation** `lwalk_approximation`: a loop in an open `U ⊆ ℂ` is homotopic
  in `↥U` to a conjugate of the realization of a closed lattice walk whose trace lies in `U`;
* the **peel** `lwalk_nullhomotopic`: such a lattice-walk loop is null-homotopic, which gives the
  plane crux `plane_loops_of_approx` (loops in an open `U ⊆ ℂ` with preconnected complement in the
  sphere are null-homotopic);
* the **sphere reduction** `sphere_reduction_of_plane_crux`, which transports the plane crux to
  the Riemann sphere along a Möbius homeomorphism sending a point of `Dᶜ` to `∞`.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- **The plane crux.**  A loop in an open `U ⊆ ℂ` whose complement in the Riemann sphere is
preconnected is null-homotopic in `U`. -/
private theorem plane_crux_loops {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    {x : ℂ} (hx : x ∈ U) (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    Path.Homotopic γ (Path.refl _) := by
  refine plane_loops_of_approx ?_ hUo hpre hx γ
  intro U' hUo' x' hx' γ'
  exact lwalk_approximation hUo' hx' γ'

/-- **The plane crux for a closed, preconnected and unbounded set `F`.**  The one-point
compactification of `F` is a continuum of the sphere, so the complement of `F` has preconnected
one-point compactification. -/
private theorem plane_loops_compl_closed_unbounded (F : Set ℂ) (hFc : IsClosed F)
    (hFp : IsPreconnected F) (hFu : ∀ R : ℝ, ∃ z ∈ F, R ≤ ‖z‖) {x : ℂ} (hx : x ∉ F)
    (γ : Path (⟨x, hx⟩ : ↥Fᶜ) (⟨x, hx⟩ : ↥Fᶜ)) : Path.Homotopic γ (Path.refl _) := by
  have hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' F ∪ {OnePoint.infty}) := by
    refine IsPreconnected.subset_closure
      (hFp.image _ OnePoint.continuous_coe.continuousOn) subset_union_left ?_
    intro z hz
    rcases hz with hz | hz
    · exact subset_closure hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Work.Smooth.SphereJordan.infty_mem_closure_coe_image hFu
  have hpre' : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' (Fᶜ)ᶜ ∪ {OnePoint.infty}) := by
    rw [compl_compl F]; exact hpre
  exact plane_crux_loops hFc.isOpen_compl hpre' hx γ

/-- **Every loop in an open subset of the Riemann sphere with preconnected complement is
null-homotopic in that subset.**  Equivalently: every complementary domain of a continuum in `S²`
is simply connected. -/
theorem loops_nullhomotopic_of_isOpen_of_isPreconnected_compl {D : Set (OnePoint ℂ)}
    (hDo : IsOpen D) (hDc : IsPreconnected Dᶜ) {x : OnePoint ℂ} (hx : x ∈ D)
    (γ : Path (⟨x, hx⟩ : ↥D) (⟨x, hx⟩ : ↥D)) : Path.Homotopic γ (Path.refl _) := by
  have hplane : ∀ (F : Set ℂ), IsClosed F → IsPreconnected F →
      (∀ R : ℝ, ∃ z ∈ F, R ≤ ‖z‖) →
      ∀ {x : ℂ} (hx : x ∉ F), ∀ γ : Path (⟨x, hx⟩ : ↥Fᶜ) (⟨x, hx⟩ : ↥Fᶜ),
        Path.Homotopic γ (Path.refl _) :=
    fun F hFc hFp hFu x hx γ => plane_loops_compl_closed_unbounded F hFc hFp hFu hx γ
  have hKc : IsCompact (Dᶜ) := hDo.isClosed_compl.isCompact
  have hxK : x ∈ (Dᶜ)ᶜ := (compl_compl D).symm ▸ hx
  let e : ↥D ≃ₜ ↥((Dᶜ)ᶜ) := Homeomorph.setCongr (compl_compl D).symm
  have hred : Path.Homotopic (γ.map e.continuous_toFun) (Path.refl (e ⟨x, hx⟩)) :=
    sphere_reduction_of_plane_crux hplane simplyConnectedSpace_onePoint_complex (Dᶜ) hKc hDc hxK
      (γ.map e.continuous_toFun)
  exact path_homotopic_of_homeomorph e γ hred

end

end Work.Smooth.JordanSeparation
