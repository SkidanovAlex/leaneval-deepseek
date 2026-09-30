/-
# The frame `(σ̂_v, frame2, frame3)` is orthonormal

The cusp charts of `Work.Cusp.Basic` use the frame `(frame1 v, frame2 v, frame3 v)` of the UHS
horizontal space `ℝ³`:

* `frame1 v = σ̂_v`, the unit vector along the slope `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}`;
* `frame2 v`, the unit vector along `κ_{v,2} − proj_{σ_v} κ_{v,2}`;
* `frame3 v = κ̂_{v,3}`, the unit vector along `κ_{v,3}`.

Since the lattice basis `(κ_{v,1}, κ_{v,2}, κ_{v,3})` is orthogonal (`kappa` in `Data.lean`), the
three vectors form an orthonormal frame, and this is what the polar chart needs: the `w`-coordinates
`(⟪y, frame2 v⟫, ⟪y, frame3 v⟫)` are orthonormal coordinates on `σ_v^⊥`.

The only geometric input is the concrete integral data `kappa`, `slopeB`, `slopeC`; it is consumed by
case analysis on `v : Fin 5` plus `norm_num`.  The algebraic steps (orthogonal projection, unit
normalisation) are abstract inner-product-space manipulations.

The vector `gnum v = ⟪σ_v,σ_v⟫ • κ_{v,2} − ⟪κ_{v,2},σ_v⟫ • σ_v` is `⟪σ_v,σ_v⟫` times
`frame2aux v`; it has *integral* coordinates, so its non-vanishing (which is what makes `frame2` a
unit vector) can be decided numerically without ever handling the irrational `‖σ_v‖`.  For every
`v` the relevant coordinate of `gnum v` is nonzero: `(0,420,-2)`, `(420,0,-2)`, `(0,-2,420)`,
`(0,420,-2)`, `(0,-16,1696)` for `v = 0,…,4`.
-/
import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### The concrete lattice data -/

/-- `⟪σ_v, σ_v⟫ ≠ 0`, i.e. the slope is a nonzero vector (both are decided by the integral data). -/
private lemma slope_inner_self_ne_zero (v : Fin 5) : inner ℝ (slope v) (slope v) ≠ 0 := by
  fin_cases v <;>
    simp only [slope, slopeB, slopeC, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three] <;>
    norm_num

/-- `⟪κ_{v,3}, κ_{v,3}⟫ ≠ 0`. -/
private lemma lam3_inner_self_ne_zero (v : Fin 5) : inner ℝ (lam3 v) (lam3 v) ≠ 0 := by
  fin_cases v <;>
    simp only [lam3, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three] <;>
    norm_num

/-- The lattice basis is orthogonal: `κ_{v,2} ⊥ κ_{v,3}`. -/
private lemma lam2_orth_lam3 (v : Fin 5) : inner ℝ (lam2 v) (lam3 v) = 0 := by
  fin_cases v <;>
    simp only [lam2, lam3, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three] <;>
    norm_num

/-- `σ_v ⊥ κ_{v,3}` (the slope lies in the `κ_{v,1}κ_{v,2}`-plane, `c_v = 0`). -/
private lemma slope_orth_lam3 (v : Fin 5) : inner ℝ (slope v) (lam3 v) = 0 := by
  fin_cases v <;>
    simp only [slope, slopeB, slopeC, lam3, kv, kappa, PiLp.inner_apply, Fin.sum_univ_three] <;>
    norm_num

private lemma slope_ne_zero (v : Fin 5) : slope v ≠ 0 :=
  (inner_self_ne_zero (𝕜 := ℝ) (x := slope v)).mp (slope_inner_self_ne_zero v)

private lemma lam3_ne_zero (v : Fin 5) : lam3 v ≠ 0 :=
  (inner_self_ne_zero (𝕜 := ℝ) (x := lam3 v)).mp (lam3_inner_self_ne_zero v)

/-! ### Non-vanishing of `frame2aux`

`frame2aux v` is the orthogonal projection of `κ_{v,2}` to `σ_v^⊥`; it is nonzero because `κ_{v,2}`
is not parallel to `σ_v`.  Clearing the denominator `⟪σ_v,σ_v⟫` leaves the vector `gnum v` with
integral coordinates. -/

/-- `⟪σ_v,σ_v⟫ • frame2aux v`, a vector with integral coordinates. -/
private def gnum (v : Fin 5) : E3 :=
  inner ℝ (slope v) (slope v) • lam2 v - inner ℝ (lam2 v) (slope v) • slope v

private lemma gnum_ne_zero (v : Fin 5) : gnum v ≠ 0 := by
  rw [← inner_self_ne_zero (𝕜 := ℝ) (x := gnum v)]
  fin_cases v <;>
    simp only [gnum, slope, slopeB, slopeC, lam2, kv, kappa, PiLp.inner_apply,
      Fin.sum_univ_three] <;>
    norm_num

private lemma frame2aux_smul_gnum (v : Fin 5) :
    inner ℝ (slope v) (slope v) • frame2aux v = gnum v := by
  rw [frame2aux, gnum, smul_sub, smul_smul, ← real_inner_self_eq_norm_sq (slope v),
    mul_div_cancel₀ _ (slope_inner_self_ne_zero v)]

private lemma frame2aux_ne_zero (v : Fin 5) : frame2aux v ≠ 0 := by
  intro h
  exact gnum_ne_zero v (by rw [← frame2aux_smul_gnum v, h, smul_zero])

/-! ### Orthogonality of the frame -/

private lemma inner_slope_frame2aux (v : Fin 5) : inner ℝ (slope v) (frame2aux v) = 0 := by
  rw [frame2aux, inner_sub_right, real_inner_smul_right, ← real_inner_self_eq_norm_sq (slope v),
    div_mul_cancel₀ _ (slope_inner_self_ne_zero v), real_inner_comm (slope v) (lam2 v), sub_self]

private lemma inner_lam3_frame2aux (v : Fin 5) : inner ℝ (lam3 v) (frame2aux v) = 0 := by
  rw [frame2aux, inner_sub_right, real_inner_smul_right,
    real_inner_comm (lam2 v) (lam3 v), real_inner_comm (slope v) (lam3 v),
    lam2_orth_lam3 v, slope_orth_lam3 v, mul_zero, sub_zero]

theorem frame_orthonormal (v : Fin 5) :
    inner ℝ (frame1 v) (frame2 v) = 0 ∧ inner ℝ (frame1 v) (frame3 v) = 0 ∧
      inner ℝ (frame2 v) (frame3 v) = 0 ∧
      ‖frame1 v‖ = 1 ∧ ‖frame2 v‖ = 1 ∧ ‖frame3 v‖ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame1, frame2, real_inner_smul_left, real_inner_smul_right, inner_slope_frame2aux v]
    ring
  · rw [frame1, frame3, real_inner_smul_left, real_inner_smul_right, slope_orth_lam3 v]
    ring
  · rw [frame2, frame3, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (lam3 v) (frame2aux v), inner_lam3_frame2aux v]
    ring
  · rw [frame1]
    exact norm_smul_inv_norm (slope_ne_zero v)
  · rw [frame2]
    exact norm_smul_inv_norm (frame2aux_ne_zero v)
  · rw [frame3]
    exact norm_smul_inv_norm (lam3_ne_zero v)

end Work.Cusp
