/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The rational cohomology of the spheres

The degree-shift isomorphism `H^{m+1}(S^{n+1}; ℚ) ≅ H^m(S^n; ℚ)` (`sphere_shift`, assembled in
`Submission.Work.Sphere.Suspension`) together with the three base cases
`H¹(S¹) ≅ ℚ` (`Work.Sphere.CircleH1`), `H¹(S^{n+2}) = 0` (`Work.Sphere.H_one_sph_succ`) and the
cohomology of `S⁰` (`Work.Sphere.H_sph_zero`) give the values of the cohomology of the spheres:

* `H^n(S^n; ℚ) ≅ ℚ` for `n ≥ 1` (`sphere_top`),
* `H^k(S^n; ℚ) = 0` for `0 < k`, `k ≠ n` (`sphere_subsingleton`),
* `H⁰(S^n; ℚ) ≅ ℚ` for `n ≥ 1` (`sphere_H0`).
-/
import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Sphere.H_one_sph_succ
import Submission.Work.Sphere.H_sph_zero
import Submission.Work.Sphere.CircleH1
import Submission.Work.Sphere.pathConnected_sph
import Submission.Work.Cohomology.H_zero_connected

namespace Work.Sphere

open Submission.Cohomology Submission.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- **The degree shift of the sphere.**  For `m ≥ 1` there is an isomorphism
`H^{m+1}(S^{n+1}; ℚ) ≅ H^m(S^n; ℚ)`, obtained by the Mayer–Vietoris collapse of the two-cap cover
of `S^{n+1}` and the homotopy equivalence of the doubly punctured sphere with `S^n`. -/
theorem sphere_shift (n m : ℕ) (hm : 1 ≤ m) :
    Nonempty (H (singSph (n+1)) ℚ (m+1) ≃ₗ[ℚ] H (singSph n) ℚ m) :=
  ⟨(smallSphereIso n (m+1)).symm.trans ((mvSphere n m hm).trans
    ((capCIso n m).trans ((capPrimeIso n m).trans
      ((dpSpaceIso n m).trans (dpSphereIso n m)))))⟩

/-- The cohomology of `S^n` is `ℚ` in degree `n`, for `n ≥ 1`. -/
theorem sphere_top (n : ℕ) (hn : 1 ≤ n) : Nonempty (H (singSph n) ℚ n ≃ₗ[ℚ] ℚ) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        exact CircleH1
      · obtain ⟨e⟩ := sphere_shift n n hnpos
        obtain ⟨e₂⟩ := ih (by omega)
        exact ⟨e.trans e₂⟩

/-- `Subsingleton` transfers across an isomorphism of cohomology groups. -/
theorem subsingleton_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (h : Subsingleton W) : Subsingleton V :=
  ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-- The cohomology of `S^n` vanishes in positive degrees different from `n`. -/
theorem sphere_subsingleton (n k : ℕ) (hk : 0 < k) (hkn : k ≠ n) :
    Subsingleton (H (singSph n) ℚ k) := by
  revert k
  induction n with
  | zero => intro k hk _; exact H_sph_zero.1 k hk
  | succ n ih =>
      intro k hk hkn
      rcases k with _ | m
      · omega
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- `k = 1`: `H¹(S^{n+1}) = 0`, which forces `n ≥ 1`
        subst hm0
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact H_one_sph_succ n'
      · -- `k ≥ 2`: shift a degree down
        obtain ⟨e⟩ := sphere_shift n m hmpos
        exact subsingleton_of_linearEquiv e (ih m (by omega) (by omega))

/-- The degree `0` cohomology of `S^n` is `ℚ` for `n ≥ 1`. -/
theorem sphere_H0 (n : ℕ) (hn : 1 ≤ n) : Nonempty (H (singSph n) ℚ 0 ≃ₗ[ℚ] ℚ) := by
  haveI : PathConnectedSpace (Sph n) := pathConnected_sph n hn
  exact Work.Cohomology.H_zero_connected (Sph n)

/-- The cohomology of `S^n` in the top degree `n` is `ℚ` (for `n ≥ 1`). -/
theorem sphere_top' (n : ℕ) (hn : 1 ≤ n) : Nonempty (H (singSph n) ℚ n ≃ₗ[ℚ] ℚ) :=
  sphere_top n hn

end

end Work.Sphere
