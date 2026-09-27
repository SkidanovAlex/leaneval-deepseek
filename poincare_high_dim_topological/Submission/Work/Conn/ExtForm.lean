import Submission.Work.PL.Defs
import Submission.Work.Conn.Main
import Submission.Work.Conn.Extend.exists_continuousMap_ball_of_homotopic_const
import Submission.Work.Conn.HomotopyInvariance.nullhomotopic_iff_of_homotopyEquiv
import Submission.Work.Conn.Contractible.nullhomotopic_of_contractible

/-!
# Connectivity in the extension form `PL.ExtOverDisc`

The blueprint's consumers (`Geo/Radial`, `Engulf`) want connectivity in the form
`PL.ExtOverDisc X j` : every map `𝕊ʲ → X` extends over the closed ball `𝔻ʲ⁺¹`.

This file provides

* `Work.Conn.extOverDisc_iff` : `PL.ExtOverDisc X j ↔ ∀ f : C(𝕊ʲ, X), f.Nullhomotopic`
  (a null-homotopy of `𝕊ʲ → X` is exactly a map on the cone `𝔻ʲ⁺¹`, and the ball is contractible);
* `Work.Conn.extOverDisc_sphere` : `∀ j < n, PL.ExtOverDisc 𝕊ⁿ j`, i.e. `πⱼ(𝕊ⁿ) = 0`;
* `Work.Conn.forall_extOverDisc_sphere` : the `j ≤ n - 2` form,
* `Work.Conn.extOverDisc_of_homotopyEquiv_sphere` : the same for a space homotopy equivalent to `𝕊ⁿ`;
* `Work.Conn.extOverDisc_of_contractible` : the same for a contractible space.
-/

open Metric (sphere closedBall)
open ContinuousMap

namespace Work.Conn

/-- A map whose domain is contractible is null-homotopic. -/
theorem nullhomotopic_of_contractible_domain {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace X] (f : C(X, Y)) : f.Nullhomotopic := by
  have h := (id_nullhomotopic X).comp_right f
  simpa using h

/-- A map out of `𝕊ʲ` extends over `𝔻ʲ⁺¹` if and only if it is null-homotopic: a null-homotopy is
a map on the cone on `𝕊ʲ`, and the cone on `𝕊ʲ` is the ball, which is contractible. -/
theorem extOverDisc_iff {X : Type*} [TopologicalSpace X] (j : ℕ) :
    PL.ExtOverDisc X j ↔ ∀ f : C(Sph j, X), f.Nullhomotopic := by
  constructor
  · intro h f
    obtain ⟨g, hg⟩ := h f
    haveI : ContractibleSpace (Ball (j + 1)) :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1).contractibleSpace
        ⟨0, mem_Ball_iff.mpr (by norm_num)⟩
    have hgn : g.Nullhomotopic := nullhomotopic_of_contractible_domain g
    have hf : f = g.comp (SphToBall j) := by
      ext x
      exact (hg x).symm
    rw [hf]
    exact hgn.comp_left (SphToBall j)
  · intro h f
    obtain ⟨y₀, hy₀⟩ := h f
    obtain ⟨g, hg⟩ := Extend.exists_continuousMap_ball_of_homotopic_const f y₀ hy₀
    refine ⟨g, fun x => ?_⟩
    have h1 : g (SphToBall j x) = f x := congrArg (fun m : C(Sph j, X) => m x) hg
    convert h1 using 2
    exact Subtype.ext rfl

/-- **`πⱼ(𝕊ⁿ) = 0` for `j < n`**, in the extension form used by the blueprint. -/
theorem extOverDisc_sphere {n j : ℕ} (hj : j < n) : PL.ExtOverDisc (Sph n) j :=
  (extOverDisc_iff j).mpr fun f => nullhomotopic_sphere_of_lt hj f

/-- `πⱼ(𝕊ⁿ) = 0` for all `j ≤ n - 2`, in the form `Geo/Radial` consumes. -/
theorem forall_extOverDisc_sphere {n : ℕ} (hn : 2 ≤ n) : ∀ j ≤ n - 2, PL.ExtOverDisc (Sph n) j :=
  fun j hj => extOverDisc_sphere (by omega)

/-- `πⱼ(𝕊ⁿ) = 0` for all `j < n`, as a function of `j`. -/
theorem forall_lt_extOverDisc_sphere (n : ℕ) : ∀ j < n, PL.ExtOverDisc (Sph n) j :=
  fun _ hj => extOverDisc_sphere hj

/-- **Connectivity of a space homotopy equivalent to `𝕊ⁿ`**: `πⱼ = 0` for `j < n`, in the
extension form. -/
theorem extOverDisc_of_homotopyEquiv_sphere {M : Type*} [TopologicalSpace M] {n j : ℕ}
    (hj : j < n) (e : M ≃ₕ Sph n) : PL.ExtOverDisc M j :=
  (extOverDisc_iff j).mpr fun f =>
    (HomotopyInvariance.nullhomotopic_iff_of_homotopyEquiv e f).mpr
      (nullhomotopic_sphere_of_lt hj (e.toFun.comp f))

/-- A space homeomorphic to `𝕊ⁿ` has `πⱼ = 0` for `j < n`. -/
theorem extOverDisc_of_homeomorph_sphere {M : Type*} [TopologicalSpace M] {n j : ℕ}
    (hj : j < n) (e : M ≃ₜ Sph n) : PL.ExtOverDisc M j :=
  extOverDisc_of_homotopyEquiv_sphere hj e.toHomotopyEquiv

/-- A contractible space has `πⱼ = 0` for every `j` (in particular an open cell has the
connectivity needed by the engulfing theorem). -/
theorem extOverDisc_of_contractible {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (j : ℕ) : PL.ExtOverDisc X j :=
  (extOverDisc_iff j).mpr fun f => Contractible.nullhomotopic_of_contractible f

/-- An open cell `W ≃ₜ ℝⁿ` has `πⱼ = 0` for every `j`. -/
theorem extOverDisc_of_homeomorph_euclidean {X : Type*} [TopologicalSpace X] {n : ℕ}
    (e : X ≃ₜ EuclideanSpace ℝ (Fin n)) (j : ℕ) : PL.ExtOverDisc X j := by
  haveI : ContractibleSpace (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    convex_univ.contractibleSpace ⟨0, Set.mem_univ _⟩
  haveI : ContractibleSpace (EuclideanSpace ℝ (Fin n)) :=
    (Homeomorph.Set.univ _).symm.toHomotopyEquiv.contractibleSpace
  haveI : ContractibleSpace X := e.toHomotopyEquiv.contractibleSpace
  exact extOverDisc_of_contractible j

/-- The `ExtOverDisc` form of an open cell of `PL`. -/
theorem extOverDisc_of_isOpenCell {M : Type*} [TopologicalSpace M] {n : ℕ} {W : Set M}
    (hW : PL.IsOpenCell n W) (j : ℕ) : PL.ExtOverDisc W j := by
  obtain ⟨_, ⟨e⟩⟩ := hW
  exact extOverDisc_of_homeomorph_euclidean e j

/-- `πⱼ(𝕊ⁿ⁻¹) = 0` for `j ≤ n - 2`, in the form in which `Geo/Radial` (`G8`, `annulus_conn`)
consumes it: the sphere is written as `sphere (0 : E n) 1` rather than `Sph (n - 1)`. -/
theorem forall_extOverDisc_sphere_prev {n : ℕ} (hn : 2 ≤ n) :
    ∀ j ≤ n - 2, PL.ExtOverDisc (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) j := by
  rcases n with _ | m
  · omega
  · exact fun j hj => forall_lt_extOverDisc_sphere m j (by omega)

end Work.Conn
