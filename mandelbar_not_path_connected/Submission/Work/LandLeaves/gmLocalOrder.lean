/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# A cheaper route to the cyclic-order preservation of the angle map

`Work.LandLeaves.ccBet_angDouble_of_typeSet` (the "no crossing" input of the finiteness of the
type of a repelling periodic point, Goldberg–Milnor II Lemma 2.2) is proved here along a route
that avoids the *case analysis* (`long`/`hard`) and the *sign computation* of
`Work.LandLeaves.ccBet_angDouble_of_hard_case`.

The observation is that the only planar input needed is

> the local cyclic order of the ray tails at `y` agrees with the cyclic order of their angles
> **up to one global reversal**,

while the actual sign — which is what the lollipop/Böttcher-chart computation in
`NOTES_ccBet_v2_geometric_core.md` computes — is irrelevant, because

* the holomorphic second return map `τ = (T_c)^[2k]` is **injective on a small ball** `B(y,r)`
  (it is a local biholomorphism, multiplier `≠ 0`), and it maps the tail of `R_θ` to the tail of
  `R_{σθ}`; hence it preserves the local cyclic order of the tails, and
* `LocalOrder` below depends only on the `ccBet` class of the triple, up to the global reversal
  (a statement about three pairwise disjoint arcs from `y` to `∞`),

so that a single `ε ∈ {±1}` satisfies `LocalOrder u v w ↔ ccBet (ε ∘ (u,v,w))`, and `ε` cancels
in the final argument (see the assembly at the end of the file).

The predicate `LocalOrder` reads the local order off the *arguments of the ray points* as the
level tends to `1`: `arg (rayPt θ t - y)` is the direction in which `R_θ` meets the circle
`|z - y| = |rayPt θ t - y|`, and for `t` close to `1` those directions are in the local cyclic
order of the tails.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.LandLeaves

open scoped Topology

variable {c : ℂ} {φ : ℂ → ℂ}

/-- **The local cyclic order of the ray tails at their landing point.**

`LocalOrder hN y u v w` says: for the levels `t > 1` close enough to `1`, the *directions* of the
ray points `rayPt u t`, `rayPt v t`, `rayPt w t` as seen from `y` are in the counterclockwise
cyclic order `u, v, w` — i.e. the blackboard-cyclic order of the three curve germs at `y` is
`R_u, R_v, R_w`.  The arguments are divided by `2 * π` so that they are measured in *turns*,
matching `ccBet`, which is a betweenness relation on `ℝ / ℤ`.  (For a ray that does not land at
`y` this is simply false; for `θ ∈ K` the three germs do have a well-defined cyclic order and the
predicate does express it.) -/
def LocalOrder (hN : Work.EL.DynB c φ) (y : ℂ) (u v w : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[>] (1 : ℝ),
    ccBet (Complex.arg (Work.EL.rayPt hN u t - y) / (2 * Real.pi))
          (Complex.arg (Work.EL.rayPt hN v t - y) / (2 * Real.pi))
          (Complex.arg (Work.EL.rayPt hN w t - y) / (2 * Real.pi))

/-- The second-return angle map `σ = (angDouble)^[2k]` sends the type of `y` into itself. -/
theorem rayAccum_angDouble_singleton' {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {θ : ℝ} (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] θ) = {y} := by
  obtain ⟨hper, -⟩ := hrep
  have h2k : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] y = y := by
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hper.2, hper.2]
  rw [Work.Landing.rayAccum_iterate hφ θ (2 * k), h, Set.image_singleton, h2k]

end Work.LandLeaves
