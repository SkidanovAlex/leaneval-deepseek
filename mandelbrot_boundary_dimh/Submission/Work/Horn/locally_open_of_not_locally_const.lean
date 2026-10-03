import Mathlib
import Submission.Work.Horn.germF0_base

namespace Work.Horn

open Set Metric Filter

/-- A holomorphic function on an open set which is not locally constant at `z` is locally open at
`z` (open mapping for a non-constant analytic function on a ball around `z`). -/
theorem locally_open_of_not_locally_const {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) {z : ℂ} (hz : z ∈ D)
    (h : ¬ (∀ᶠ w in nhds z, f w = f z)) :
    ∀ U ∈ nhds z, f '' U ∈ nhds (f z) := by
  -- `f` is analytic at `z` since it is holomorphic on an open set containing `z`.
  have hz' : AnalyticAt ℂ f z := hf.analyticAt (hD.mem_nhds hz)
  -- The local open mapping theorem: either `f` is eventually constant at `z`, or
  -- `nhds (f z) ≤ map f (nhds z)`.
  have hle : nhds (f z) ≤ map f (nhds z) :=
    (AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux hz').resolve_left h
  -- Translate `nhds (f z) ≤ map f (nhds z)` into the image-of-neighbourhood form: for every
  -- `U ∈ nhds z` we have `f ⁻¹' (f '' U) ∈ nhds z`, hence `f '' U ∈ map f (nhds z)`, hence
  -- `f '' U ∈ nhds (f z)`.
  intro U hU
  exact hle (mem_map.mpr (mem_of_superset hU (subset_preimage_image f U)))

end Work.Horn
