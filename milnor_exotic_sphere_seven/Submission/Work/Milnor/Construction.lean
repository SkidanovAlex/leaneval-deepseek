import Mathlib
import Submission.Work.Milnor.QuatSphere
import Submission.Work.Glue.Basic
import Submission.Work.Glue.glued_isManifold
import Submission.Work.Quaternion.clutch_smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Milnor's construction of an exotic 7-sphere: the manifold `M_k`

Milnor (*On manifolds homeomorphic to the 7-sphere*, Ann. of Math. **64** (1956), 399–405)
constructs, for each integer `k`, the smooth 7-manifold
`M_k = (D⁴ × S³) ∪_f (D⁴ × S³)`,
where the two copies of the disc bundle `D⁴ × S³` are glued along their common boundary
`∂(D⁴ × S³) = S³ × S³` by the diffeomorphism `f(x, y) = (x, x^k * y * x⁻¹)` (unit quaternions).

This file sets up the *glueing data* as an instance of `Submission.Glue.Data`: instead of glueing
two manifolds with boundary, we cut each `D⁴ × S³` into an open *core* and an open *collar* and
glue the open collar pieces to a third open "double collar" piece.  Concretely, the manifold is
covered by the three open subsets

* `core = {‖x‖ < 3/4} × S³` (a copy for each of the two disc bundles),
* `collar = {1/4 < ‖x‖ < 3/4} × S³` (the double collar, whose parametrisation carries the twist
  `A(x) = x^k * · * x⁻¹` on its outer half),

with the identifications

* `glue₁ : {1/2 < ‖x‖ < 3/4} × S³ → {1/4 < ‖x‖ < 1/2} × S³`, `(X, y) ↦ (X - (1/4)X/‖X‖, y)`,
* `glue₂ : {1/2 < ‖x‖ < 3/4} × S³ → {1/2 < ‖x‖ < 3/4} × S³`, `(X, y) ↦ (X, A(X/‖X‖)⁻¹ y)`.

The second map carries the twist, which is precisely what makes the resulting smooth structure
exotic.

## Status

* the ambient manifold, the pieces and the glueing maps are defined here;
* `Submission.Glue.Data` (with its `ChartedSpace`/`IsManifold` instances) is available, so the
  remaining work is to turn `glue₁`, `glue₂` into `Data`s and to iterate the glueing;
* the two remaining mathematical inputs (that the resulting manifold is *homeomorphic* to `S⁷`,
  via a Morse function with two critical points and Reeb's theorem, and that it is *not*
  diffeomorphic to `S⁷`, via Milnor's `λ`-invariant) are **not** formalised here; they are the
  subject of subsequent work.

## Roadmap

1. `Work.Milnor.glue1_diffeomorph`, `Work.Milnor.glue2_diffeomorph` (delegated): `glue₁` and
   `glue₂ k` are diffeomorphisms of the open pieces.
2. `Work.Milnor.data_first_gluing` (delegated): package `glue₁` as the `Submission.Glue.Data`
   identifying the annulus of the first core with `collarInner`; then `Glue.Data.Glued`
   (with `Work.Glue.glued_isManifold`) is the first glued manifold `M₁`.
3. The second gluing identifies the annulus of a second copy of `core` with the image of the
   annulus inside `M₁`, using the *inverse* of `glue₂ k` (the twist).  Iterating
   `Work.Glue.glued_isManifold` yields a smooth `7`-manifold `M_k` modelled on
   `(𝓡 4).prod (𝓡 3)`.
4. `Work.Model.prod_transfer` (delegated, proved) turns this into a `ChartedSpace
   (EuclideanSpace ℝ (Fin 7))` together with `IsManifold (𝓡 7) ∞ M_k`, i.e. the first four
   conjuncts of `Submission.milnor_exotic_sphere_seven`.
5. Remaining (not started): `M_k ≃ₜ S⁷` (Milnor's Morse function with two critical points +
   Reeb's theorem) and `IsEmpty (M_k ≃ₘ⟮𝓡 7, 𝓡 7⟯ S⁷)` (Milnor's `λ`-invariant, i.e.
   Hirzebruch's signature theorem in dimension `8` and Pontryagin classes).
-/

open scoped Manifold ContDiff Topology
open Metric (sphere)
open TopologicalSpace Set

namespace Submission.Milnor

noncomputable section

/-- The ambient manifold `ℝ⁴ × S³` in which the pieces of Milnor's `M_k` live. -/
abbrev MSpace : Type := EuclideanSpace ℝ (Fin 4) × QS3

/-- The "core" `{‖x‖ < 3/4} × S³`: the inner part of one of the two disc bundles. -/
def core : Opens MSpace where
  carrier := {p : MSpace | ‖p.1‖ < 3/4}
  is_open' := isOpen_lt continuous_fst.norm continuous_const

/-- The "double collar" `{1/4 < ‖x‖ < 3/4} × S³`, which represents the region of `M_k` around the
seam where the two copies of `D⁴ × S³` are glued.  Its inner half `{1/4 < ‖x‖ < 1/2}` is attached
to the first core, its outer half `{1/2 < ‖x‖ < 3/4}` to the second core, with the twist. -/
def collar : Opens MSpace where
  carrier := {p : MSpace | 1/4 < ‖p.1‖ ∧ ‖p.1‖ < 3/4}
  is_open' := (isOpen_lt continuous_const continuous_fst.norm).inter
    (isOpen_lt continuous_fst.norm continuous_const)

/-- The gluing region inside a core: `{1/2 < ‖x‖ < 3/4} × S³`. -/
def annulus : Opens MSpace where
  carrier := {p : MSpace | 1/2 < ‖p.1‖ ∧ ‖p.1‖ < 3/4}
  is_open' := (isOpen_lt continuous_const continuous_fst.norm).inter
    (isOpen_lt continuous_fst.norm continuous_const)

/-- The inner half of the collar: `{1/4 < ‖x‖ < 1/2} × S³`, the image of the first gluing map. -/
def collarInner : Opens MSpace where
  carrier := {p : MSpace | 1/4 < ‖p.1‖ ∧ ‖p.1‖ < 1/2}
  is_open' := (isOpen_lt continuous_const continuous_fst.norm).inter
    (isOpen_lt continuous_fst.norm continuous_const)

/-- The unit quaternion in the direction of a nonzero vector `x : ℝ⁴`, where `ℝ⁴` is identified
with the quaternions by `Quaternion.linearIsometryEquivTuple`.  For `x = 0` we return `1`
(junk value, never used). -/
def unitDir (x : EuclideanSpace ℝ (Fin 4)) : QS3 :=
  if h : x = 0 then ⟨1, by rw [Metric.mem_sphere, dist_zero_right, norm_one]⟩
  else ⟨Quaternion.linearIsometryEquivTuple.symm x * (‖x‖ : ℝ)⁻¹, by
    have hnorm : ‖Quaternion.linearIsometryEquivTuple.symm x‖ = ‖x‖ :=
      Quaternion.linearIsometryEquivTuple.symm.norm_map x
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, Quaternion.norm_coe, norm_inv, norm_norm,
      hnorm]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr h)⟩

/-- The first gluing map: the outer annulus of a core is identified with the inner half of the
collar, by the affine radial rescaling `‖x‖ ↦ ‖x‖ - 1/4` (no twist). -/
def glue₁ (p : MSpace) : MSpace :=
  (((‖p.1‖ - 1/4) / ‖p.1‖) • p.1, p.2)

/-- The second gluing map: the outer annulus of the second core is identified with the outer half
of the collar (which is `annulus` itself, as a subset), with the quaternionic twist
`y ↦ A(x)⁻¹ y = x^{-k} y x`.  So `glue₂ k` is a self-map of the annulus. -/
def glue₂ (k : ℤ) (p : MSpace) : MSpace :=
  (p.1, clutch (-k) (unitDir p.1, p.2))

end

end Submission.Milnor
