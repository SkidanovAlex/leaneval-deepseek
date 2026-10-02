/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# `Work.LandLeaves.periodicRaysLand` — periodic rays of the tricorn land

Milnor, *Dynamics in one complex variable*, Theorem 18.1 (Douady–Hubbard): if the filled Julia
set of `T_c` is connected, then every periodic dynamic ray lands at a periodic point.  Here `c`
ranges over the mandelbar `M*`, where `T_c` has a genuine Böttcher coordinate on the escaping
set (`Work.LandLeaves.bottcherInverse`).

## The argument

Let `φ = dynPhiOf c` and let `θ` be periodic of period `k` (`angDouble^[k] θ = θ`).  The
accumulation set

`A := Work.Landing.rayAccum c φ θ`

of the dynamic ray `R_c(θ)` is, by `Work.LandLeaves.isPreconnected_rayAccum`, a nonempty compact
*connected* subset of the Julia set, and by `Work.LandLeaves.rayAccum_iterate_image` it is
invariant under `F := (T_c)^[k]`, which maps the ray to itself with `F (Z r) = Z (r ^ (2^k))`
along the parametrisation `Z r := φ⁻¹ (r • e^{2πiθ})` of the ray.

Koebe's quarter theorem, applied to the univalent inverse Böttcher coordinate
(`Work.LandLeaves.bead_bound`, with `Work.LandLeaves.koebeQuarter` as the analytic input), shows
that the *consecutive beads* `Z ([r ^ (1/M), r])` of the ray have Euclidean diameter tending to
`0` as `r → 1⁺` (`M = 2^k`).  Hence if `a = lim Z (r_j)` with `r_j → 1⁺` then

`F a = lim F (Z (r_j ^ (1/M))) = lim Z (r_j) = a`,

i.e. every point of `A` is fixed by `F`
(`Work.LandLeaves.rayAccum_subset_fixp`).  A preconnected set of fixed points of the polynomial
iterate `(Tsq c)^[k] = (T_c)^[2k]` is a subsingleton
(`Work.LandLeaves.preconnected_fixp_subsingleton`), so `A` is a single point: the ray lands.

## Provenance

* `Work.LandLeaves.bottcherInverse` — Böttcher coordinate and inverse (proved).
* `Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher` — injectivity/surjectivity (proved).
* `Work.LandLeaves.isPreconnected_rayAccum` — connectedness of the accumulation set.
* `Work.LandLeaves.rayAccum_subset_fixp` — the geometric heart (Koebe + beads).
* `Work.LandLeaves.preconnected_fixp_subsingleton` — the final dynamical step.
* `Work.LandLeaves.rayAccum_nonempty` + the surjectivity half of the Böttcher homeomorphism.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Reductions
import Submission.Work.LandLeaves.rayAccum_nonempty
import Submission.Work.Bottcher.All
import Submission.Work.SeedDyn.Main
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.LandLeaves.isPreconnected_rayAccum
import Submission.Work.LandLeaves.rayAccum_periodic
import Submission.Work.LandLeaves.rayAccum_subset_fixp
import Submission.Work.LandLeaves.preconnected_fixp_subsingleton

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter
open Metric

namespace Work.LandLeaves

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet)

/-- **Every periodic dynamic ray of `T_c` lands**, for `c` in the mandelbar (Milnor 18.1). -/
theorem periodicRaysLand (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    Work.Landing.PeriodicRaysLand c := by
  intro θ hθ
  obtain ⟨k, hk, hper⟩ := hθ
  have hφ : IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    (Work.SeedDyn.isDynBottcherHomeo hc).1
  -- the accumulation set is preconnected and every point of it is fixed by `(T_c)^[k]`
  have hpre := Work.LandLeaves.isPreconnected_rayAccum (φ := Work.ParamRays.dynPhiOf c) hφ θ
  have hfix := Work.LandLeaves.rayAccum_subset_fixp c hc hk hper
  have hsub : (Work.Landing.rayAccum c (Work.ParamRays.dynPhiOf c) θ).Subsingleton := by
    refine Work.LandLeaves.preconnected_fixp_subsingleton c k hk hpre ?_
    intro z hz
    have h1 : (Tantibar c)^[k] z = z := hfix z hz
    have h2 : (Tantibar c)^[2 * k] z = (Work.Landing.Tsq c)^[k] z := by
      rw [Function.iterate_mul, Work.Landing.Family.tantibar_iterate_two_eq_tsq]
    have h3 : (Tantibar c)^[2 * k] z = z := by
      rw [Nat.mul_comm 2 k, Function.iterate_mul]
      exact (show Function.IsFixedPt ((Tantibar c)^[k]) z from h1).iterate 2
    rw [← h2, h3]
  -- nonemptiness of the accumulation set
  have hray : Work.Landing.RaysNearCircle c (Work.ParamRays.dynPhiOf c) := by
    intro ϑ ρ hρ
    have hnorm : ‖(((ρ : ℝ) : ℂ)) * Work.Landing.rayDirection ϑ‖ = ρ := by
      rw [norm_mul, Work.Landing.Rays.norm_rayDirection, mul_one,
        show ‖((ρ : ℝ) : ℂ)‖ = |ρ| from by simp, abs_of_pos (by linarith : (0 : ℝ) < ρ)]
    obtain ⟨z, hz, hzw⟩ :=
      (Work.SeedDyn.isDynBottcherHomeo hc).2.2 (((ρ : ℝ) : ℂ) * Work.Landing.rayDirection ϑ)
        (by rw [hnorm]; exact hρ)
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · rw [hzw]
      exact ⟨ρ, hρ, rfl⟩
    · rw [hzw, hnorm]
  obtain ⟨y, hy⟩ := Work.LandLeaves.rayAccum_nonempty hφ hray θ
  refine ⟨y, Work.ParamRays.dynPhiOf c, hφ, ?_⟩
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨hy, fun z hz => hsub hz hy⟩

end

end Work.LandLeaves
