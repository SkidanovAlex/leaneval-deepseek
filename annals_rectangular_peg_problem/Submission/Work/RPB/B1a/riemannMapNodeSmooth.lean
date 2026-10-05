import Mathlib
import Submission.Work.RPB.B1a.RiemannMapNodeSmooth
import Submission.Work.RPB.B1a.riemannMap_exists
import Submission.Work.RPB.B1a.caratheodory_boundary_of_smooth

/-!
# `Work.RPB.B1a.riemannMapNodeSmooth`: node N6 in its smooth-boundary form

Assembly of the smooth-boundary node `Work.RPB.B1a.RiemannMapNodeSmooth` from the two halves that
`Submission/Work/RPB/B1a/` proves:

* `Work.RPB.B1a.riemannMap_exists` — the Riemann map `Φ₀` of the bounded domain `D` with connected
  complement (the ported Riemann-mapping result `Submission.Work.RPB.Port.RMT.Main`, inverted and
  normalised at the origin);
* `Work.RPB.B1a.caratheodory_boundary_of_smooth` — Carathéodory's boundary correspondence in the
  smooth case, giving the continuous injective extension to the closed disc and the continuous
  reparametrisation of the boundary values.

Everything else is bookkeeping: differentiability of the extension on the open disc, the image, the
boundary map into `Set.range v`, and `deriv Φ 0 = a` by eventual equality at the origin.
-/

open Complex Set Metric Filter Topology
open scoped ContDiff Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

theorem riemannMapNodeSmooth : RiemannMapNodeSmooth := by
  intro v hv D hDo hDc hDb hDcc hDfr
  -- The Riemann map of `D` onto the disc, normalised at the origin.
  obtain ⟨f, hfd, hfinj, hfim, a, ha, hfa⟩ := riemannMap_exists D hDo hDc hDb hDcc
  -- `frontier D = closure D \ interior D`.
  have hDfr' : closure D \ interior D = Set.range v := by
    rw [closure_sdiff_interior]; exact hDfr
  -- Carathéodory's boundary correspondence in the smooth case.
  obtain ⟨Φ, hΦc, hΦeq, hΦi, σ, _hσ, hσeq⟩ :=
    caratheodory_boundary_of_smooth v hv D hDo hDc hDb hDfr' f hfd hfinj hfim
  refine ⟨Φ, hΦc, ?_, hΦi, ?_, ?_, a, ha, ?_⟩
  · -- the extension is holomorphic on the open disc
    exact hfd.congr (fun z hz => hΦeq hz)
  · -- and still maps the disc onto `D`
    rw [← hfim]
    exact Set.image_congr (fun z hz => hΦeq hz)
  · -- the circle is mapped into the curve
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    obtain ⟨θ, _hθ, hθ⟩ := Complex.norm_eq_one_iff'.mp hz
    rw [← hθ]
    exact ⟨σ θ, (hσeq θ).symm⟩
  · -- the normalisation survives
    have hev : Φ =ᶠ[𝓝 (0 : ℂ)] f :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 one_pos) (fun z hz => hΦeq hz)
    exact hev.deriv_eq.trans hfa

end Work.RPB.B1a
