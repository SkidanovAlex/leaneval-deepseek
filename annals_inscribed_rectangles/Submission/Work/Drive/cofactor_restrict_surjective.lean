import Mathlib
import Submission.Work.Drive.cofactorVec_apply_ne_zero
import Submission.Work.Drive.cofactorVec_ne_zero_of_surjective
import Submission.Work.Drive.ker_eq_span_cofactorVec

/-!
# The face criterion for a transversally cut-out zero set

`Submission/Work/Drive/cofactorVec_apply_ne_zero.lean` proves one half of the following criterion:
if the restriction of `T : ℝ^{m+1} → ℝ^m` to the coordinate hyperplane `{v | v i = 0}` is
surjective, then the `i`-th component of the cofactor vector `cofactorVec T` does not vanish.  This
file proves the converse, so that for *surjective* `T` the two conditions are equivalent:

> `T` restricted to the face `{v i = 0}` is surjective  ⟺  `cofactorVec T i ≠ 0`.

The point of the criterion is that it converts the third hypothesis of `Submission.Drive.ParityProp`
(“the zero set of `F` meets every face of the box transversally”) into a condition on a *single
scalar*: for a zero `x`, the tangential direction of the zero set (spanned by the cofactor vector of
`fderiv ℝ F x`, which is the kernel direction) must not be tangent to the face, i.e. its `i`-th
component must be nonzero.  This is the form in which the face hypothesis of
`Work.Drive.even_ncard_loopMeet_add_solidMeet` and `Work.Drive.even_ncard_loopEnd_add_side_add_tau`
is meant to be verified (see `Submission/Work/Drive/INTERSECTION_THEORY_STATUS.md`).
-/

namespace Work.Drive

open Submission.Drive

noncomputable section

/-- The `i`-th coordinate functional on the ambient space `ℝ^{m+1}`. -/
def coordLin {m : ℕ} (i : Fin (m + 1)) : Amb m →ₗ[ℝ] ℝ where
  toFun v := v i
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] lemma coordLin_apply {m : ℕ} (i : Fin (m + 1)) (v : Amb m) : coordLin i v = v i := rfl

lemma coordLin_ne_zero {m : ℕ} (i : Fin (m + 1)) : coordLin (m := m) i ≠ 0 := by
  intro h
  have hval : coordLin (m := m) i (EuclideanSpace.single i 1) = 1 := by simp
  rw [h] at hval
  simp at hval

/-- **The face criterion.**  For a surjective linear map `T : ℝ^{m+1} → ℝ^m`, the restriction of `T`
to the coordinate hyperplane `{v | v i = 0}` is surjective if and only if the `i`-th component of
the cofactor vector of `T` is nonzero.

The kernel of `T` is one-dimensional, spanned by `cofactorVec T` (`ker_eq_span_cofactorVec`).  The
restriction to the hyperplane is surjective iff the hyperplane surjects onto the quotient by the
kernel, iff the kernel is not contained in the hyperplane, iff `cofactorVec T` has nonzero `i`-th
coordinate. -/
theorem surjective_domRestrict_iff_cofactorVec_ne_zero {m : ℕ} (T : Amb m →L[ℝ] Tgt m)
    (hT : Function.Surjective T) (i : Fin (m + 1)) :
    Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1) ↔ cofactorVec T i ≠ 0 := by
  refine ⟨cofactorVec_apply_ne_zero T i, fun hne => ?_⟩
  set K : Submodule ℝ (Amb m) := LinearMap.ker (coordLin (m := m) i) with hK
  have hfinK : Module.finrank ℝ K = Module.finrank ℝ (Tgt m) := by
    have h1 : Module.finrank ℝ (LinearMap.ker (coordLin (m := m) i)) + 1 = m + 1 := by
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := coordLin (m := m) i)
        (coordLin_ne_zero i)
      rwa [finrank_euclideanSpace_fin] at h
    have h2 : Module.finrank ℝ K + 1 = m + 1 := by rw [hK]; exact h1
    rw [finrank_euclideanSpace_fin]
    omega
  set T' : K →ₗ[ℝ] Tgt m := (T : Amb m →ₗ[ℝ] Tgt m).domRestrict K with hT'
  have hinj : Function.Injective T' := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    have hTu : T u.1 = 0 := by
      have h0 : T' u = 0 := hu
      simpa [hT', LinearMap.domRestrict_apply] using h0
    have hspan : u.1 ∈ Submodule.span ℝ {cofactorVec T} := by
      rw [← ker_eq_span_cofactorVec T hT]
      exact hTu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
    have hcoord : c * cofactorVec T i = 0 := by
      have h0 : u.1 i = 0 := u.2
      rw [← hc] at h0
      simpa using h0
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hcoord with h | h
      · exact h
      · exact absurd h hne
    have hmem : (u : Amb m) = 0 := by rw [← hc, hc0, zero_smul]
    exact Subtype.ext hmem
  have hsurj : Function.Surjective T' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinK).mp hinj
  intro w
  obtain ⟨u, hu⟩ := hsurj w
  exact ⟨⟨u.1, u.2⟩, hu⟩

/-- **The cofactor vector and any non-zero kernel vector have the same vanishing coordinates.**

For a surjective `T : ℝ^{m+1} → ℝ^m` the kernel is one-dimensional, spanned by `cofactorVec T`, so
every non-zero `k` with `T k = 0` is a non-zero multiple of `cofactorVec T`; in particular `k` and
`cofactorVec T` vanish in exactly the same coordinates.  This is how the face criterion is applied to
a *computable* kernel direction (for instance the direction of the intersection 1-manifold of two
chains) instead of to the cofactor vector itself. -/
theorem cofactorVec_apply_ne_zero_iff {m : ℕ} (T : Amb m →L[ℝ] Tgt m)
    (hT : Function.Surjective T) {k : Amb m} (hk : T k = 0) (hne : k ≠ 0) (i : Fin (m + 1)) :
    cofactorVec T i ≠ 0 ↔ k i ≠ 0 := by
  have hmem : k ∈ Submodule.span ℝ {cofactorVec T} := by
    rw [← ker_eq_span_cofactorVec T hT]
    exact hk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcne : c ≠ 0 := by
    intro h0
    exact hne (by rw [← hc, h0, zero_smul])
  rw [← hc, PiLp.smul_apply, smul_eq_mul, mul_ne_zero_iff]
  exact ⟨fun h => ⟨hcne, h⟩, fun h => h.2⟩

end

end Work.Drive
