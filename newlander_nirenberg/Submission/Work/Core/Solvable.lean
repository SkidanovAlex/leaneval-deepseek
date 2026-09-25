import Submission.Work.Core.Std

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

variable {n : ℕ}

/-- **The analytic input of the Newlander–Nirenberg theorem**, in the sharp form needed for the
chart: the (linear!) `∂̄`-equation for the standard coordinate functions has a solution on a
neighbourhood of `x`, and the resulting corrected coordinates still have invertible differentials.

Concretely: there is an open `V ∋ x`, `V ⊆ U`, and functions `v j` smooth on `V` with

* `∂̄_J v_j = (i/2)·(dz_j ∘ (J - Jstd))` on `V` (the right hand side is exactly `∂̄_J z_j`, the
  obstruction to the coordinate function `z_j` itself being holomorphic), and
* the corrected coordinates `z_j - v_j` have invertible differentials on `V`.

This is the local solvability of the `∂̄`-equation of an integrable almost complex structure
(with a loss of one derivative, obtained from the Cauchy-kernel estimates on a small polydisc);
it is the single missing analytic ingredient of the development. -/
def DbarSolvable {n : ℕ} (J : E n → E n →L[ℝ] E n) (U : Set (E n)) (x : E n)
    (T : E n ≃L[ℝ] F n) : Prop :=
  ∃ V : Set (E n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
    ∃ v : Fin n → E n → ℂ, (∀ j, ContDiffOn ℝ ∞ (v j) V) ∧
      (∀ j, ∀ y ∈ V, dbar J (v j) y
        = (Complex.I / 2) • ((fderiv ℝ (zcoord T j) y).comp (J y - stdOf T y))) ∧
      (∀ y ∈ V, Function.Bijective
        (fderiv ℝ (fun y : E n => fun j => zcoord T j y - v j y) y))

/-- **`DbarSolvable` implies the analytic core**.  If the `∂̄`-equation above is solvable near
`x`, then the corrected coordinates `z_j - v_j` are `J`-holomorphic with invertible
differentials, which is the conclusion of `nn_core`. -/
theorem nn_core_of_dbar {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n}
    {x : E n} {T : E n ≃L[ℝ] F n} (h : DbarSolvable J U x T) :
    ∃ V : Set (E n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ u : Fin n → E n → ℂ, (∀ j, ContDiffOn ℝ ∞ (u j) V) ∧
      (∀ j, ∀ y ∈ V, ∀ v : E n,
        fderiv ℝ (u j) y (J y v) = Complex.I * fderiv ℝ (u j) y v) ∧
      (∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y)) := by
  obtain ⟨V, hV, hxV, hVU, v, hv, hveq, hvinv⟩ := h
  refine ⟨V, hV, hxV, hVU, (fun j y => zcoord T j y - v j y), ?_, ?_, ?_⟩
  · intro j
    exact (contDiff_zcoord T j).contDiffOn.sub (hv j)
  · intro j y hy w
    have hd : dbar J (fun y : E n => zcoord T j y - v j y) y = 0 := by
      have hz : DifferentiableAt ℝ (zcoord T j) y :=
        ((contDiff_zcoord T j).differentiable (by simp)).differentiableAt
      have hvy : DifferentiableAt ℝ (v j) y :=
        ((hv j).contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
      rw [dbar_sub J _ _ y hz hvy, dbar_linearization T J (zcoord T j) y]
      have hzero : dbar (stdOf T) (zcoord T j) y = 0 := by
        rw [dbar_eq_zero_iff]
        intro w
        exact zcoord_hol T j y w
      rw [hzero, hveq j y hy, zero_add, sub_self]
    exact ((dbar_eq_zero_iff J (fun y : E n => zcoord T j y - v j y) y).mp hd) w
  · intro y hy
    exact hvinv y hy

/-- In the flat (standard) case the analytic input is trivially satisfied: the coordinate
functions themselves are already holomorphic, so the correction `v` is zero. -/
theorem dbar_solvable_std {U : Set (E n)} (hU : IsOpen U) {x : E n} (hx : x ∈ U)
    (T : E n ≃L[ℝ] F n) : DbarSolvable (stdOf T) U x T := by
  refine ⟨U, hU, hx, subset_refl U, (fun _ _ => 0), ?_, ?_, ?_⟩
  · intro j
    exact contDiffOn_const
  · intro j y hy
    rw [dbar_const]
    ext w
    simp
  · intro y hy
    simpa using bijective_fderiv_zcoord_tuple T y

end Submission
