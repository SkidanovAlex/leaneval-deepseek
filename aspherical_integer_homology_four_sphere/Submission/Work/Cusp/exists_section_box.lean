import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.wOf_add
import Submission.Work.Cusp.wDet_ne_zero
import Submission.Work.Cusp.ThetaPolar_injOn
import Submission.Work.Cusp.invY_wOf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A local section of the `w`-coordinates `wOf v`

`wOf v y` is the pair `(⟪cuspY v y, frame2 v⟫, ⟪cuspY v y, frame3 v⟫)` of coordinates of the
`σ^⊥`-component of the cusp coordinate `y₂λ₂ + y₃λ₃` in the orthonormal frame `(frame2, frame3)`.
It is the linear isomorphism of `Basic.wOf` (with inverse `Basic.invY` and nonzero determinant
`wDet v ≠ 0`), so that `y ↦ wOf v y` descends to a *local* homeomorphism `(ℝ/ℤ)² → (ℝ/ℤ)²`.

The statement proved here makes the word "local" effective: around *any* point `wOf v y` there is
an open set `W` whose preimage under `wOf v` meets every `ℤ²`-coset in at most one point.  In
other words, on `W` the coordinates `w` determine the class of `y` modulo `ℤ²` — that is what makes
the charts `Θ_v` (which are functions of `(p, y)` with `y`-dependence only through `wOf v y`,
`thetaAng` and hence `Θ_v` being `ℤ²`-periodic in `y`) honest charts of `W_v`.

## The argument

`wOf v` is (defeq to) the linear map `invYLin v` composed with the explicit `2 × 2` matrix
`G = (⟪λ_i, e_j⟫)`; more precisely `Basic.invY v` is the explicit inverse `H` of `wOf v`
(`invY_wOf`), and `invYLin v` is that same explicit formula packaged as a `ℝ`-linear map.  Since
`E2 = ℝ²` is finite dimensional, `H` is continuous, so `SemilinearMapClass.bound_of_continuous`
provides a constant `C > 0` with `‖H w‖ ≤ C ‖w‖` for all `w`.  Taking

`W = Metric.ball (wOf v y) (1 / (2 (C + 1)))`

gives the result: if `wOf v y'` and `wOf v y''` both lie in `W`, then
`‖y' - y''‖ = ‖H (wOf v y' - wOf v y'')‖ ≤ C ‖wOf v y' - wOf v y''‖ < C / (C + 1) < 1`,
while `y' - y''` is a vector of the integer lattice `ℤ²` as soon as `y'` and `y''` have the same
image in `(ℝ/ℤ)²`; the only element of `ℤ²` of norm `< 1` is `0`.
-/

noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `Basic.invY v` written as an explicit `ℝ`-linear map: the inverse of the matrix
`G = (⟪λ_i, e_j⟫)` (whose determinant is `wDet v`), given by the adjugate. -/
def invYLin (v : Fin 5) : E2 →ₗ[ℝ] E2 where
  toFun := fun w =>
    (wDet v)⁻¹ • !₂[⟪lam3 v, frame3 v⟫_ℝ * w 0 - ⟪lam3 v, frame2 v⟫_ℝ * w 1,
                            -(⟪lam2 v, frame3 v⟫_ℝ * w 0) + ⟪lam2 v, frame2 v⟫_ℝ * w 1]
  map_add' := by intro a b; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro c a; ext i; fin_cases i <;> simp <;> ring

/-- The formula defining `invYLin` is literally the formula defining `Basic.invY`. -/
theorem invYLin_apply (v : Fin 5) (w : E2) : invYLin v w = invY v w := rfl

/-- `invYLin v` inverts `wOf v`. -/
theorem invYLin_wOf (v : Fin 5) (y : E2) : invYLin v (wOf v y) = y := invY_wOf v y

/-- If two reals have the same image in `ℝ/ℤ` then their difference is an integer. -/
theorem sub_eq_intCast_of_addCircle_eq {a b : ℝ}
    (h : (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ))) : ∃ n : ℤ, a - b = n := by
  have h0 : ((a - b : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  exact ⟨n, by simpa using hn.symm⟩

/-- **A local section of `wOf v`.**  Every point `wOf v y` has an open neighbourhood `W` on which
the `w`-coordinates determine the class of the cusp coordinate modulo `ℤ²`: two points `y'`, `y''`
whose `w`-images lie in `W` and which agree in `(ℝ/ℤ)²` are equal. -/
theorem exists_section_box (v : Fin 5) (y : E2) :
    ∃ W : Set E2, IsOpen W ∧ wOf v y ∈ W ∧
      ∀ y' y'' : E2, wOf v y' ∈ W → wOf v y'' ∈ W →
        (∀ i, ((y' i : ℝ) : AddCircle (1 : ℝ)) = ((y'' i : ℝ) : AddCircle (1 : ℝ))) →
        y' = y'' := by
  -- `invYLin v` is a linear map on the finite dimensional space `ℝ²`, hence bounded.
  obtain ⟨C, hCpos, hC⟩ := SemilinearMapClass.bound_of_continuous (invYLin v)
    (LinearMap.continuous_of_finiteDimensional (invYLin v))
  have hC1pos : (0 : ℝ) < C + 1 := by linarith
  have hrpos : (0 : ℝ) < 1 / (2 * (C + 1)) := by positivity
  refine ⟨Metric.ball (wOf v y) (1 / (2 * (C + 1))), Metric.isOpen_ball, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_self]; exact hrpos
  · intro y' y'' hy' hy'' hmod
    rw [Metric.mem_ball, dist_eq_norm] at hy' hy''
    -- the two `w`-values are close to `wOf v y`, hence to each other
    have htri : ‖wOf v y' - wOf v y''‖ < 2 * (1 / (2 * (C + 1))) := by
      have hsplit : (wOf v y' - wOf v y) + (wOf v y - wOf v y'') = wOf v y' - wOf v y'' := by
        abel
      have ht : ‖wOf v y' - wOf v y''‖
          ≤ ‖wOf v y' - wOf v y‖ + ‖wOf v y - wOf v y''‖ := by
        rw [← hsplit]; exact norm_add_le _ _
      rw [norm_sub_rev (wOf v y) (wOf v y'')] at ht
      have h2 : ‖wOf v y' - wOf v y‖ + ‖wOf v y'' - wOf v y‖
          < 2 * (1 / (2 * (C + 1))) := by
        rw [show 2 * (1 / (2 * (C + 1)))
              = 1 / (2 * (C + 1)) + 1 / (2 * (C + 1)) from by ring]
        exact add_lt_add hy' hy''
      linarith
    have h1 : invYLin v (wOf v y') = y' := invY_wOf v y'
    have h2 : invYLin v (wOf v y'') = y'' := invY_wOf v y''
    have hkey : y' - y'' = invYLin v (wOf v y' - wOf v y'') := by
      rw [map_sub, h1, h2]
    -- `‖y' - y''‖ ≤ C ‖wOf v y' - wOf v y''‖ < C / (C + 1) < 1`
    have hnorm : ‖y' - y''‖ < 1 := by
      rw [hkey]
      have hC2 : C * (2 * (1 / (2 * (C + 1)))) < 1 := by
        have heq : C * (2 * (1 / (2 * (C + 1)))) = C / (C + 1) := by field_simp
        rw [heq]
        rw [div_lt_one hC1pos]
        linarith
      exact lt_trans (lt_of_le_of_lt (hC _) (mul_lt_mul_of_pos_left htri hCpos)) hC2
    -- `y' - y''` is an integer vector of norm `< 1`, hence zero
    ext i
    have hlt : |y' i - y'' i| < 1 := by
      simpa using lt_of_le_of_lt (PiLp.norm_apply_le (y' - y'') i) hnorm
    obtain ⟨n, hn⟩ := sub_eq_intCast_of_addCircle_eq (hmod i)
    have hn0 : n = 0 := by
      have h3 : (n : ℝ) < 1 := by rw [← hn]; exact (abs_lt.mp hlt).2
      have h4 : -(1 : ℝ) < (n : ℝ) := by rw [← hn]; exact (abs_lt.mp hlt).1
      have h5 : n < 1 := by exact_mod_cast h3
      have h6 : -1 < n := by exact_mod_cast h4
      omega
    have hzero : y' i - y'' i = 0 := by rw [hn, hn0]; norm_num
    exact sub_eq_zero.mp hzero

end Work.Cusp
