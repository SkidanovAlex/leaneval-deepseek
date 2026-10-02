import Mathlib
import Submission.Work.PTGeometric.RegionManifoldNC

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the defining function of the source region of the null-bordism

`Work.PTGeometric.SourceRegionPhiProp k Z U` is the **whole** geometric content of the source
construction's `Φ`: a `C^∞` function on the half-space `A = EuclideanHalfSpace ((8+k)+1)` whose
sublevel set `{Φ ≤ 0}` is a compact neighbourhood of the closed set `Z` (the zero set of the
null-homotopy, `W₀ = H ⁻¹' core`), contained in the prescribed open set `U` (a small neighbourhood of
`Z` avoiding `H ⁻¹' {t₀}`), whose zero set meets `Z` only on `∂A`, and which is a submersion at every
zero and *one-sided* at the boundary zeros (the `hone` condition of the region-charting theorem:
at a boundary zero the differential of `Φ` is a strictly negative multiple of the differential of the
zeroth coordinate).

## Construction (the design that makes every clause provable)

The hard clause is the submersivity at the zeros (`hsub`): the region is a manifold with boundary only
if `0` is a *regular* value of `Φ` in the interior.  A naive `Φ = ρ - c` fails both this and the
boundary condition.  The construction below makes `hsub` a **parametric Sard** statement:

* let `ω : A → [0, ∞)` be the smooth Urysohn function of `Z` with `ω = 0` exactly on `Z`, `ω ≥ 1` off
  `U` and off a compact set (this is `Work.PTGeometric.exists_sourceDefiningFunction`);
* let `θ : ℝ → ℝ` be smooth with `θ (0) = θ' (0) = 0`, `θ < 0` on `(0, a)`, `θ (a) = θ' (a) = 0`,
  `θ > 0` on `(a, ∞)` and `θ (1) > 1` (e.g. `θ s = c * s ^ 2 * (s - a) ^ 3` for suitable `c`, `a`);
* let `h : ℝ → ℝ` be smooth with `h 0 = 0`, `h' 0 < 0`, `h ≤ 0` on `[0, 1]`, `h ≥ -1`,
  `h(t)/t → ∞` (e.g. `h t = t * (t - 1) * (1 + (t - 1) * Real.smoothTransition (t - 1))`);
* put `Φ₀ x = θ (ω x) + h (x 0)` and `χ x = (x 0) ^ 2`.  Then `χ ≥ 0`, `χ = 0` exactly on `∂A`, and
  the *parametric* family `Φ_t x = Φ₀ x - t * χ x` has, for almost every `t`, all its interior zeros
  regular — this is exactly `volume_badSet_eq_zero_euclid` applied to `G := Φ₀` (extended to the
  ambient Euclidean space along `ω`, or applied with the open-set variant on the interior), whose
  conclusion is that the set of *bad* `t` is Lebesgue-null;
* choose `t > 0` outside that null set and small enough that the remaining (open) conditions hold;
  then `Φ := Φ_t` satisfies every clause, because

  - at a boundary zero `x` (`x 0 = 0`) one has `Φ x = θ (ω x)`, so `ω x ∈ {0, a}` and `θ' (ω x) = 0`
    forces `mfderiv Φ x = h' (0) • mfderiv (fun y => y.1 0) x` (the tangential part dies), which is
    both `hone` (with `c = h' (0) < 0`) and `hsub`;
  - `Z ⊆ {Φ ≤ 0}` because on `Z` one has `ω = 0` and `x 0 < 1`, and `Z ∩ {Φ = 0} ⊆ ∂A` because
    `h (x 0) = t * (x 0) ^ 2 ≥ 0` forces `x 0 = 0` there;
  - `{Φ ≤ 0} ⊆ {ω < 1} ⊆ U`: on `{Φ ≤ 0}` one has `θ (ω x) ≤ -h (x 0) + t * (x 0) ^ 2`; from
    `h (x 0) - t * (x 0) ^ 2 ≤ -θ_min` the coordinate `x 0` is bounded (`h` is superlinear), and then
    `θ (ω x) ≤ 1 + t * X ^ 2`, so `ω x ≤ s < 1` provided `θ (1) > 1 + t * X ^ 2`;
  - `IsCompact {Φ ≤ 0}`: closed, and contained in the bounded set `{x 0 ≤ X} ∩ {ω < 1} ⊆ U` whose
    closure is compact.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The defining-function residual of the source region.**  See the file header for the
construction. -/
def SourceRegionPhiProp (k : ℕ) (Z U : Set (EuclideanHalfSpace ((8 + k) + 1))) : Prop :=
  ∃ Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ,
    ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
    Z ⊆ {x | Φ x ≤ 0} ∧
    {x | Φ x ≤ 0} ⊆ U ∧
    IsCompact {x | Φ x ≤ 0} ∧
    (Z ∩ {x | Φ x = 0} ⊆ {x | x.1 0 = 0}) ∧
    (∀ x : EuclideanHalfSpace ((8 + k) + 1), Φ x = 0 →
      IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ x) ∧
    (∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (EuclideanHalfSpace ((8 + k) + 1)), Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph (EuclideanHalfSpace ((8 + k) + 1))
            (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace ((8 + k) + 1)) ∧
        x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔
          y ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (EuclideanHalfSpace ((8 + k) + 1))) ∧
        mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
            (modelWithCornersSelf ℝ ℝ) Φ x
          = c • mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              (modelWithCornersSelf ℝ ℝ)
              (fun y : EuclideanHalfSpace ((8 + k) + 1) => (e y).1 0) x)

end

end Work.PTGeometric
