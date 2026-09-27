import Mathlib
import Submission.Work.Drive.ppParity.Defs

/-!
# Surjectivity of a linear map restricted to a coordinate hyperplane is an open condition

`Work.Drive.ppParity.surjective_domRestrict_open`: if `L : ℝ^{m+1} → ℝ^m` is surjective when
restricted to the *closed* subspace `{v | v i = 0}` (a hyperplane), then so is `L + S` for every
`S` with `‖S‖` small enough.

This is the quantitative form of "surjectivity is an open condition" for linear maps.  The proof is
the standard one, in the finite-dimensional setting so that no Banach open mapping theorem is
needed:

* `K := ker (proj i)` is the hyperplane; `hL` is exactly the surjectivity of `L|_K`;
* since `Tgt m = ℝ^m` is a vector space (`Module.Projective ℝ _`), `L|_K` has a *linear* right
  inverse `R : ℝ^m →ₗ K`, i.e. `L (R w) = w` for all `w`;
* `ℝ^m` is finite dimensional, so `R` is automatically continuous; let `Rc : ℝ^m →L ℝ^{m+1}` be it
  (`Rc w ∈ K`, `L (Rc w) = w`);
* for `‖S‖ < ε := (1 + ‖Rc‖)⁻¹` the operator `T := S ∘ Rc : ℝ^m → ℝ^m` has `‖T‖ ≤ ‖S‖ ‖Rc‖ < 1`,
  so `1 + T` is a unit of the Banach algebra `ℝ^m →L ℝ^m` (Neumann series,
  `isUnit_one_sub_of_norm_lt_one`), hence surjective;
* finally `(L + S) (Rc y) = L (Rc y) + S (Rc y) = y + T y = (1 + T) y = w` for `y` with
  `(1 + T) y = w`, and `Rc y ∈ K`.

This is the "small perturbations do not destroy regularity" step used by the pair-Sard machinery of
the transport (`Work.Drive.PPRegAt`).
-/

namespace Work.Drive.ppParity

set_option synthInstance.maxHeartbeats 200000 in
theorem surjective_domRestrict_open {m : ℕ} (i : Fin (m + 1))
    (L : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m)
    (hL : Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} => L v.1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m, ‖S‖ < ε →
      Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} => (L + S) v.1) := by
  classical
  -- The hyperplane `{v | v i = 0}` as a submodule.
  let K : Submodule ℝ (Work.Drive.Amb m) := LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) i)
  have hsub : ∀ (v : Work.Drive.Amb m), v ∈ K ↔ v i = 0 := fun v => Iff.rfl
  -- `hL` is the surjectivity of `L` restricted to `K`.
  have hsurj : Function.Surjective ((L.comp K.subtypeL) : K → Work.Drive.Tgt m) := by
    intro w
    obtain ⟨v, hv⟩ := hL w
    refine ⟨⟨v.1, (hsub v.1).2 v.2⟩, ?_⟩
    simpa using hv
  -- A *linear* right inverse of `L|_K`, which exists because `ℝ^m` is projective.
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective
    ((L.comp K.subtypeL).toLinearMap) (LinearMap.range_eq_top.2 hsurj)
  have hRw : ∀ w : Work.Drive.Tgt m, L ((R w : K) : Work.Drive.Amb m) = w := by
    intro w
    have h := congrArg (fun f : Work.Drive.Tgt m →ₗ[ℝ] Work.Drive.Tgt m => f w) hR
    simpa using h
  -- `R` viewed in the ambient space, and its continuity (finite dimension).
  let R2 : Work.Drive.Tgt m →ₗ[ℝ] Work.Drive.Amb m := K.subtype.comp R
  let Rc : Work.Drive.Tgt m →L[ℝ] Work.Drive.Amb m := R2.toContinuousLinearMap
  have hRc : ∀ w, L (Rc w) = w := by
    intro w
    have hv : Rc w = ((R w : K) : Work.Drive.Amb m) := rfl
    rw [hv, hRw w]
  have hRcK : ∀ w, (Rc w) i = 0 := by
    intro w
    have hv : Rc w = ((R w : K) : Work.Drive.Amb m) := rfl
    rw [hv]
    exact (hsub _).1 (R w).2
  refine ⟨(1 + ‖Rc‖)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro S hS
  -- The perturbation, seen through the right inverse, is a small operator.
  have hST : ‖S.comp Rc‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le S Rc) ?_
    rcases eq_or_lt_of_le (norm_nonneg Rc) with h0 | h0
    · rw [← h0, mul_zero]; norm_num
    · have h3 : (1 + ‖Rc‖)⁻¹ * ‖Rc‖ < 1 := by
        have hb : (0 : ℝ) < 1 + ‖Rc‖ := by positivity
        have h4 := mul_lt_mul_of_pos_left (by linarith : ‖Rc‖ < 1 + ‖Rc‖) (inv_pos.mpr hb)
        rwa [inv_mul_cancel₀ (ne_of_gt hb)] at h4
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hS h0) h3.le
  -- Hence `1 + S ∘ Rc` is invertible.
  have hunit : IsUnit (1 + S.comp Rc) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -(S.comp Rc)) (by simpa using hST)
    simpa [sub_neg_eq_add] using h
  obtain ⟨u, hu⟩ := hunit
  intro w
  have hsurjT : ∃ y, (1 + S.comp Rc) y = w := by
    refine ⟨(u.inv : Work.Drive.Tgt m →L[ℝ] Work.Drive.Tgt m) w, ?_⟩
    have h1 : ((1 + S.comp Rc) * (u.inv : Work.Drive.Tgt m →L[ℝ] Work.Drive.Tgt m) = 1) := by
      rw [← hu]; exact Units.mul_inv u
    have h := congrArg (fun f : Work.Drive.Tgt m →L[ℝ] Work.Drive.Tgt m => f w) h1
    simpa [mul_apply_eq_comp] using h
  obtain ⟨y, hy⟩ := hsurjT
  refine ⟨⟨Rc y, hRcK y⟩, ?_⟩
  have hy' : y + (S.comp Rc) y = w := by simpa using hy
  show L (Rc y) + S (Rc y) = w
  rw [hRc y]
  exact hy'

end Work.Drive.ppParity
