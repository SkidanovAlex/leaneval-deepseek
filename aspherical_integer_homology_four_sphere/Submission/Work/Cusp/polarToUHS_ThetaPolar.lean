/-
# On the collar the polar chart is the UHS (outer) chart, through `polarToUHS`

`polarToUHS v : (r,θ,w₁,w₂) ↦ (x,s)` is the isometry of `Basic` between the polar (warped
metric) coordinates of the `v`-th filling piece and the upper half space coordinates of the cusp:
`x = (‖σ_v‖/2π)·θ·σ̂_v + w₁·frame2 v + w₂·frame3 v` and `s = e^{R₀−r}`.

This file proves the round trip that is needed to glue the charts across the junction layer
`‖p‖∞ = 1/2` of the collar: for every point of the collar, `1/2 ≤ ‖p‖∞ ≤ 1`, the UHS point
`ThetaOuter v p y` of the outer chart is the image of the polar point `ThetaPolar v p y` under
`polarToUHS v`,

  `polarToUHS v (ThetaPolar v p y) = ThetaOuter v p y`.

The two charts use the *same* height, by construction of `collarHeight` — the radial coordinate of
the collar is `r = R₀ − log s` with `s = collarS v p y` (`exp_radial_collar`) — so the whole content
is in the horizontal `x`-coordinate `ℝ³`:

* `(‖σ_v‖/2π) · thetaAng v p y · σ̂_v = u(p)·σ_v + (⟪cuspY v y, σ_v⟫/‖σ_v‖²)·σ_v`, because
  `thetaAng v p y = 2π u(p) + 2π ⟪cuspY v y, σ_v⟫/‖σ_v‖²` and `‖σ_v‖ σ̂_v = σ_v`;
* the remaining part `(⟪y, frame2 v⟫)·frame2 v + (⟪y, frame3 v⟫)·frame3 v` of the `w`-coordinates
  completes the projection to the full `cuspY v y = y₂λ₂ + y₃λ₃`, because `(σ̂_v, frame2 v, frame3 v)`
  is an orthonormal frame of `ℝ³` (`frame_orthonormal`), i.e. it reconstructs every vector from its
  inner products with its members.

The second point is the only non-concrete ingredient, and it is proved abstractly for an arbitrary
orthonormal *triple* of `E3` (the dimension count `3 = 3` enters through `finrank_euclideanSpace`),
so that the concrete lattice data is never unfolded here.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.frame_orthonormal
import Submission.Work.Cusp.exp_radial_collar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### Reconstructing a vector of `ℝ³` from an orthonormal triple -/

/-- **An orthonormal triple of `E3 = ℝ³` reconstructs every vector from its inner products.**  The
family `e` is linearly independent (`Orthonormal.linearIndependent`) and lives in the
three-dimensional space `E3` (`finrank_euclideanSpace`), hence spans it; writing `z` in that span and
reading off the coefficients with `orthonormal_iff_ite` gives
`z = ∑ i, ⟪z, e i⟫ • e i`. -/
lemma orthonormal_fin3_sum_inner_smul (e : Fin 3 → E3) (h : Orthonormal ℝ e) (z : E3) :
    (∑ i, inner ℝ z (e i) • e i) = z := by
  have hli : LinearIndependent ℝ e := h.linearIndependent
  have hspan : Submodule.span ℝ (Set.range e) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, finrank_euclideanSpace, Fintype.card_fin]
  have hz : z ∈ Submodule.span ℝ (Set.range e) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
  have hite : ∀ i j : Fin 3, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp h
  have hkey : ∀ j, inner ℝ (∑ i, c i • e i) (e j) = c j := by
    intro j
    rw [show inner ℝ (∑ i, c i • e i) (e j) = ∑ i, c i * inner ℝ (e i) (e j) from ?_]
    · simp only [hite]
      rw [Fin.sum_univ_three]
      fin_cases j <;> simp
    · rw [sum_inner]
      exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_smul_left])
  have key : ∀ j, c j = inner ℝ z (e j) := by
    intro j; rw [← hc]; exact (hkey j).symm
  rw [← hc]
  exact Finset.sum_congr rfl (fun i _ => by rw [hkey i, key i])

/-- **The frame `(σ̂_v, frame2 v, frame3 v)` reconstructs every vector of `ℝ³`** from the inner
products with its three members: it is an orthonormal triple (`frame_orthonormal`). -/
lemma frame_expansion (v : Fin 5) (z : E3) :
    inner ℝ z (frame1 v) • frame1 v + inner ℝ z (frame2 v) • frame2 v
      + inner ℝ z (frame3 v) • frame3 v = z := by
  have horth : Orthonormal ℝ (fun i : Fin 3 => (![frame1 v, frame2 v, frame3 v] : Fin 3 → E3) i) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [frame_orthonormal v, real_inner_comm]
  have h := orthonormal_fin3_sum_inner_smul _ horth z
  rw [Fin.sum_univ_three] at h
  simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

/-! ### The slope and its unit vector -/

/-- `‖σ_v‖ • σ̂_v = σ_v`: `frame1 v = σ̂_v` is the unit vector along the slope. -/
lemma frame1_smul_norm (v : Fin 5) : ‖slope v‖ • frame1 v = slope v := by
  rw [frame1, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (slope_ne_zero v)), one_smul]

/-- Scaling the unit vector `σ̂_v` by `‖σ_v‖ · c` gives `c • σ_v`. -/
lemma smul_frame1 (v : Fin 5) (c : ℝ) : (‖slope v‖ * c) • frame1 v = c • slope v := by
  rw [mul_comm (‖slope v‖) c, mul_smul, frame1_smul_norm]

/-- **The orthogonal projection of `z` on the span of `σ_v`, in the orthonormal frame.**  The
projection `(⟪z,σ_v⟫/‖σ_v‖²) • σ_v` is `⟪z,σ̂_v⟫ • σ̂_v`, the `σ̂`-component of `z` in the
orthonormal frame `(σ̂_v, frame2 v, frame3 v)`. -/
lemma inner_slope_smul (v : Fin 5) (z : E3) :
    (inner ℝ z (slope v) / ‖slope v‖ ^ 2) • slope v = inner ℝ z (frame1 v) • frame1 v := by
  have hn : ‖slope v‖ ≠ 0 := norm_ne_zero_iff.mpr (slope_ne_zero v)
  rw [frame1, real_inner_smul_right, smul_smul]
  congr 1
  field_simp

/-! ### The horizontal part of the round trip -/

/-- **The horizontal `x`-coordinate of `polarToUHS v` at a point of the polar chart is the cusp
coordinate `cuspX v (u p) y`.**  Expanding `thetaAng` and using `‖σ_v‖ σ̂_v = σ_v` turns the angle
term into `u(p)·σ_v` plus the orthogonal projection of `cuspY v y` on `σ_v`; by
`frame_expansion` the latter together with the two `w`-terms reconstructs the whole vector
`cuspY v y = y₂λ₂ + y₃λ₃`. -/
lemma polarToUHS_horizontal (v : Fin 5) (p y : E2) :
    (‖slope v‖ / (2 * π) * thetaAng v p y) • frame1 v
      + wOf v y 0 • frame2 v + wOf v y 1 • frame3 v = cuspX v (u p) y := by
  have hn : ‖slope v‖ ≠ 0 := norm_ne_zero_iff.mpr (slope_ne_zero v)
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  -- the scalar prefactor of `σ̂_v`: the two `2π`-terms of `thetaAng`
  have hscalar : ‖slope v‖ / (2 * π) * thetaAng v p y
      = ‖slope v‖ * u p + ‖slope v‖ * (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2) := by
    rw [thetaAng]
    field_simp
  rw [hscalar, add_smul, smul_frame1 v (u p),
    smul_frame1 v (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2)]
  -- the map part of the projection is `⟪cuspY,σ̂_v⟫ • σ̂_v`
  rw [inner_slope_smul v (cuspY v y)]
  rw [show wOf v y 0 = inner ℝ (cuspY v y) (frame2 v) from rfl,
    show wOf v y 1 = inner ℝ (cuspY v y) (frame3 v) from rfl]
  -- regroup and reconstruct `cuspY v y` from the orthonormal frame
  rw [show ((u p • slope v + inner ℝ (cuspY v y) (frame1 v) • frame1 v)
        + inner ℝ (cuspY v y) (frame2 v) • frame2 v) + inner ℝ (cuspY v y) (frame3 v) • frame3 v
      = u p • slope v + (inner ℝ (cuspY v y) (frame1 v) • frame1 v
        + inner ℝ (cuspY v y) (frame2 v) • frame2 v
        + inner ℝ (cuspY v y) (frame3 v) • frame3 v) by abel]
  rw [frame_expansion v (cuspY v y)]
  rfl

/-- **The round trip of the collar charts.**  On the collar `1/2 ≤ ‖p‖∞ ≤ 1` the UHS point
`ThetaOuter v p y` is the image under `polarToUHS v` of the polar point `ThetaPolar v p y`: the
fourth coordinate agrees by `exp_radial_collar` (the height of the collar is `s = e^{R₀−r}`, and
the junction layer `‖p‖∞ = 1/2` is handled by the agreement `s_J = e^{R₀−r_J}` of the two
branches), and the first three coordinates agree by `polarToUHS_horizontal`. -/
theorem polarToUHS_ThetaPolar (v : Fin 5) (p y : E2) (h1 : 1/2 ≤ nrm p) (h2 : nrm p ≤ 1) :
    polarToUHS v (ThetaPolar v p y) = ThetaOuter v p y := by
  have hx := polarToUHS_horizontal v p y
  have hs := exp_radial_collar v p y h1
  have e0 : polarToUHS v (ThetaPolar v p y) 0 = ThetaOuter v p y 0 := by
    rw [show polarToUHS v (ThetaPolar v p y) 0 =
      ((‖slope v‖ / (2 * π) * thetaAng v p y) • frame1 v + wOf v y 0 • frame2 v
        + wOf v y 1 • frame3 v) 0 from rfl,
      show ThetaOuter v p y 0 = (cuspX v (u p) y) 0 from rfl]
    exact congrArg (fun w : E3 => w.ofLp 0) hx
  have e1 : polarToUHS v (ThetaPolar v p y) 1 = ThetaOuter v p y 1 := by
    rw [show polarToUHS v (ThetaPolar v p y) 1 =
      ((‖slope v‖ / (2 * π) * thetaAng v p y) • frame1 v + wOf v y 0 • frame2 v
        + wOf v y 1 • frame3 v) 1 from rfl,
      show ThetaOuter v p y 1 = (cuspX v (u p) y) 1 from rfl]
    exact congrArg (fun w : E3 => w.ofLp 1) hx
  have e2 : polarToUHS v (ThetaPolar v p y) 2 = ThetaOuter v p y 2 := by
    rw [show polarToUHS v (ThetaPolar v p y) 2 =
      ((‖slope v‖ / (2 * π) * thetaAng v p y) • frame1 v + wOf v y 0 • frame2 v
        + wOf v y 1 • frame3 v) 2 from rfl,
      show ThetaOuter v p y 2 = (cuspX v (u p) y) 2 from rfl]
    exact congrArg (fun w : E3 => w.ofLp 2) hx
  have e3 : polarToUHS v (ThetaPolar v p y) 3 = ThetaOuter v p y 3 := by
    rw [show polarToUHS v (ThetaPolar v p y) 3 = Real.exp (R0 - radial v p y) from rfl,
      show ThetaOuter v p y 3 = collarS v p y from rfl]
    exact hs
  ext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

end Work.Cusp
