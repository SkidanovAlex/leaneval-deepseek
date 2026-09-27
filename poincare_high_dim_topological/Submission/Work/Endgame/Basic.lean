import Mathlib
import Submission.Work.Endgame.Defs

/-!
# Endgame: homeomorphisms built from a puncture and the one-point compactification

This file contains the homeomorphisms (= "definitions") of the endgame chapter; the
propositional API about them lives in the sibling modules
(`Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph` and friends).

Given `h : ({p}ᶜ : Set M) ≃ₜ ℝⁿ` with `M` compact Hausdorff, we get

* `homeomorphOnePointOfComplHomeomorph p h : M ≃ₜ OnePoint ℝⁿ` (`M` *is* the one-point
  compactification of `ℝⁿ`),
* `homeomorphSphereOfComplHomeomorph p h : M ≃ₜ 𝕊ⁿ`.

Also, any homeomorphism `e : X ≃ₜ Y` restricts to
`homeomorphComplSingleton e p : ({p}ᶜ : Set X) ≃ₜ ({e p}ᶜ : Set Y)`.
-/

open Metric (sphere)
open Set Filter Topology
open scoped OnePoint

namespace Work.Endgame

universe u

variable {M : Type*}

/-- A homeomorphism `e : X ≃ₜ Y` restricts to a homeomorphism between the complements of any
point `p : X` and its image `e p`. -/
noncomputable def homeomorphComplSingleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X) : ({p}ᶜ : Set X) ≃ₜ ({e p}ᶜ : Set Y) where
  toFun x := ⟨e x.1, by
    rintro (h : e x.1 = e p)
    exact x.2 (e.injective h)⟩
  invFun y := ⟨e.symm y.1, by
    rintro (h : e.symm y.1 = p)
    refine y.2 ?_
    have h' := congrArg e h
    rwa [e.apply_symm_apply y.1] at h'⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- If the complement of `p : M` in a compact Hausdorff space is homeomorphic to `ℝⁿ`, then `M`
is (homeomorphic to) the one-point compactification of `ℝⁿ`. -/
noncomputable def homeomorphOnePointOfComplHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M) (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin n)) :=
  (onePointComplHomeomorph p).symm.trans h.onePointCongr

/-- The one-point compactification of `ℝⁿ` is `𝕊ⁿ`, so a space homeomorphic to it is a sphere. -/
noncomputable def homeomorphSphereOfHomeomorphOnePoint {n : ℕ} {M : Type*} [TopologicalSpace M]
    (h : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin n))) :
    M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  h.trans (onePointEuclideanHomeomorphSphere n)

/-- **Main endgame homeomorphism.** A compact Hausdorff space whose puncture is `ℝⁿ` is `𝕊ⁿ`. -/
noncomputable def homeomorphSphereOfComplHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M) (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (homeomorphOnePointOfComplHomeomorph p h).trans (onePointEuclideanHomeomorphSphere n)

/-- **Main endgame homeomorphism, general model space.** A compact Hausdorff space whose puncture
is an `n`-dimensional normed real vector space is `𝕊ⁿ`. -/
noncomputable def homeomorphSphereOfComplHomeomorphOfFinrank {n : ℕ} {M V : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (p : M) (hV : Module.finrank ℝ V = n)
    (h : ({p}ᶜ : Set M) ≃ₜ V) :
    M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ((onePointComplHomeomorph p).symm.trans h.onePointCongr).trans
    (onePointEquivSphereOfFinrankEq (by rw [hV]; simp))

end Work.Endgame
