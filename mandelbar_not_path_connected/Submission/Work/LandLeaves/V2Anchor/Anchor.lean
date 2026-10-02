import Mathlib
import Submission.Work.LandLeaves.V2Anchor.Tail
import Submission.Work.LandLeaves.V2Anchor.Cluster
import Submission.Work.LandLeaves.V2Anchor.ClusterAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A periodic dynamic ray landing at a repelling periodic point (clash-free assembly)

This file assembles the *anchor* of the landing theory — the statement that a repelling periodic
point `y` which is the landing point of some dynamic ray is the landing point of a *periodic* one
— out of the clash-free chain in `Submission/Work/LandLeaves/V2Anchor/`:

* `Work.LandLeaves.V2Anchor.exists_backward_orbit_tail` : from a landing ray at `y` one gets a
  *backward orbit* `θ` of the `4^k`-tupling map together with a geometric tail bound: the `m`-th
  fundamental bead of the ray of `θ n` (`n ≥ m`) lies in `B(y, κ^m r)`;
* `Work.LandLeaves.V2Anchor.cluster_rayAccum_eq_singleton` : hence every tail-cluster point `x` of
  the sequence `n ↦ Int.fract (θ n)` is an angle whose ray accumulates exactly at `y`;
* `Work.LandLeaves.V2Anchor.exists_periodicAngle_of_backward_orbit_cluster` : the closed
  tail-cluster set is then `σ`-invariant (`σ = angDouble^[2k]`), `σ`-surjective, and `σ` is
  injective modulo `1` on it (by `Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq` plus the
  previous point), so it is finite by
  `Work.LandLeaves.finite_of_closedInCircle_invariant_injective` and contains a periodic point.

The result is the input of the finiteness of the type of `y` and hence of the closedness of the
type (`Work.LandLeaves.rayAccum_subset_of_limit_alt`).
-/

namespace Work.LandLeaves.V2Anchor

noncomputable section

open Classical Filter Set
open scoped Topology

variable {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}

/-- The `d`-tupling map of the circle does not see the representative of an angle modulo `1`:
`fract (d * fract x) = fract (d * x)` for a natural number `d`. -/
theorem fract_mul_natCast_fract (a : ℕ) (x : ℝ) :
    Int.fract ((a : ℝ) * Int.fract x) = Int.fract ((a : ℝ) * x) := by
  refine Int.fract_eq_fract.mpr ⟨-(a * ⌊x⌋), ?_⟩
  have h : x - Int.fract x = ((⌊x⌋ : ℤ) : ℝ) := by
    have := Int.self_sub_fract (a := x)
    linarith
  push_cast
  rw [← h]
  ring

/-- The backward-orbit relation `4^k * θ (n+1) = θ n + m` for the *raw* angles `θ n` implies the
backward-orbit relation `β n = angDouble^[2k] (β (n+1))` for the normalised angles
`β n = Int.fract (θ n)`. -/
theorem fract_backward (hk : 0 < k) {θ : ℕ → ℝ}
    (hmod : ∀ n : ℕ, ∃ m : ℤ, (4 : ℝ) ^ k * θ (n + 1) = θ n + m) (n : ℕ) :
    Int.fract (θ n) = (Work.Landing.angDouble)^[2 * k] (Int.fract (θ (n + 1))) := by
  obtain ⟨m, hm⟩ := hmod n
  rw [Work.LandLeaves.angDouble_iterate_two_mul hk]
  have hcast : (((4 ^ k : ℕ)) : ℝ) = (4 : ℝ) ^ k := by push_cast; ring
  have h1 : Int.fract ((4 : ℝ) ^ k * Int.fract (θ (n + 1)))
      = Int.fract ((4 : ℝ) ^ k * θ (n + 1)) := by
    have h := fract_mul_natCast_fract (4 ^ k) (θ (n + 1))
    rwa [hcast] at h
  rw [h1, hm, Int.fract_add_intCast]

/-- **A periodic dynamic ray lands at every repelling periodic point which is the landing point of
some ray.**  If the accumulation set of the ray at the angle `θ₀` is the singleton `{y}` for a
repelling periodic point `y` of odd period `k`, then there is an angle `t` whose ray accumulates
exactly at `y` and whose class modulo `1` is periodic of period `2 * k * q` (`q > 0`) under angle
doubling. -/
theorem periodicTypeAngle_of_landingRay {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (h : ∃ θ : ℝ, Work.Landing.rayAccum c φ θ = {y}) :
    ∃ q : ℕ, 0 < q ∧ ∃ t : ℝ,
      Work.Landing.PeriodicAngle (Int.fract t) (2 * k * q) ∧
      Work.Landing.rayAccum c φ t = {y} := by
  classical
  have hk : 0 < k := hrep.1.1
  obtain ⟨θ₀, hθ₀⟩ := h
  -- the dynamical Nakane data of the Böttcher coordinate
  have hN : Work.EL.DynB c φ := dynBNakane hφ
  have hL : Work.EL.LandsN hN θ₀ y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ θ₀ y).mpr ⟨φ, hφ, hθ₀⟩
  -- the backward orbit of `θ₀` under the `4^k`-tupling map, with the geometric tail bound
  obtain ⟨r, κ, r₀, hr, hκ0, hκ1, hr₀, θ, _hθ0, hmod, htail⟩ :=
    exists_backward_orbit_tail hφ hN hrep hL
  -- every tail-cluster point of the normalised angles is an angle landing at `y`
  refine exists_periodicAngle_of_backward_orbit_cluster (β := fun n => Int.fract (θ n)) hφ hrep
    (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) (fun n => fract_backward hk hmod n) ?_
  intro x hx
  exact cluster_rayAccum_eq_singleton hφ hN hk hr hκ0 hκ1 hr₀ htail hx

end

end Work.LandLeaves.V2Anchor
