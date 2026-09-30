import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.kv_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of the cusp coordinate map `(u, y) ↦ u σ_v + y₂ λ₂ + y₃ λ₃`

The map `cuspX v u y = u • slope v + cuspY v y` sends the pair of coordinates
`(u, y₂, y₃) ∈ ℝ × ℝ²` to the cusp coordinate `x = u σ_v + y₂ λ₂ + y₃ λ₃ ∈ ℝ³`.  Since
`(σ_v, λ₂, λ₃) = (κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}, κ_{v,2}, κ_{v,3})` is a basis of `ℝ³`
(the three `κ_{v,i}` being mutually orthogonal and nonzero), this map is a linear isomorphism
`ℝ³ → ℝ³`, in particular injective.

The proof extracts the `u` coordinate by pairing with the dual functional `⟪κ_{v,1}, ·⟫` (which
annihilates `κ_{v,2}, κ_{v,3}` and gives `‖κ_{v,1}‖²` on `σ_v`), then extracts `y₂, y₃` by pairing
`cuspY` with `⟪κ_{v,2}, ·⟫` and `⟪κ_{v,3}, ·⟫`.
-/

noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### Orthogonality of the cusp lattice vectors

The three vectors `κ_{v,1}, κ_{v,2}, κ_{v,3}` of the `v`-th cusp are pairwise orthogonal. -/

/-- `κ_{v,1} ⊥ κ_{v,2}`. -/
theorem kv_inner_01 (v : Fin 5) : inner ℝ (kv v 0) (kv v 1) = 0 := by
  fin_cases v <;>
    · simp only [kv, kappa, PiLp.inner_apply, Fin.sum_univ_three]
      norm_num

/-- `κ_{v,1} ⊥ κ_{v,3}`. -/
theorem kv_inner_02 (v : Fin 5) : inner ℝ (kv v 0) (kv v 2) = 0 := by
  fin_cases v <;>
    · simp only [kv, kappa, PiLp.inner_apply, Fin.sum_univ_three]
      norm_num

/-- `κ_{v,2} ⊥ κ_{v,3}`. -/
theorem kv_inner_12 (v : Fin 5) : inner ℝ (kv v 1) (kv v 2) = 0 := by
  fin_cases v <;>
    · simp only [kv, kappa, PiLp.inner_apply, Fin.sum_univ_three]
      norm_num

/-- `κ_{v,2} ⊥ κ_{v,1}` (the symmetric form, needed for `inner_kv2_cuspY`). -/
theorem kv_inner_21 (v : Fin 5) : inner ℝ (kv v 2) (kv v 1) = 0 := by
  rw [real_inner_comm]; exact kv_inner_12 v

/-! ### Pairing `cuspY` and `slope` with the lattice vectors -/

/-- `⟪κ_{v,1}, cuspY_v y⟫ = 0`: `κ_{v,1}` is orthogonal to `cuspY_v y = y₂ κ_{v,2} + y₃ κ_{v,3}`. -/
theorem inner_kv0_cuspY (v : Fin 5) (y : E2) : inner ℝ (kv v 0) (cuspY v y) = 0 := by
  simp only [cuspY, lam2, lam3]
  rw [inner_add_right, inner_smul_right, inner_smul_right, kv_inner_01 v, kv_inner_02 v]
  ring

/-- `⟪κ_{v,i}, cuspY_v y⟫` recovers the `κ_{v,i}` coordinate of `cuspY_v y`
(`i = 2, 3`), using that `(κ_{v,i})` is orthogonal. -/
theorem inner_kv1_cuspY (v : Fin 5) (y : E2) :
    inner ℝ (kv v 1) (cuspY v y) = y 0 * ‖kv v 1‖ ^ 2 := by
  simp only [cuspY, lam2, lam3]
  rw [inner_add_right, inner_smul_right, inner_smul_right, kv_inner_12 v,
    real_inner_self_eq_norm_sq]
  ring

/-- `⟪κ_{v,3}, cuspY_v y⟫ = y₃ ‖κ_{v,3}‖²`. -/
theorem inner_kv2_cuspY (v : Fin 5) (y : E2) :
    inner ℝ (kv v 2) (cuspY v y) = y 1 * ‖kv v 2‖ ^ 2 := by
  simp only [cuspY, lam2, lam3]
  rw [inner_add_right, inner_smul_right, inner_smul_right, kv_inner_21 v,
    real_inner_self_eq_norm_sq]
  ring

/-- `⟪κ_{v,1}, σ_v⟫ = ‖κ_{v,1}‖²`: `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` and `κ_{v,1}` is
orthogonal to the other two. -/
theorem inner_kv0_slope (v : Fin 5) : inner ℝ (kv v 0) (slope v) = ‖kv v 0‖ ^ 2 := by
  simp only [slope]
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    kv_inner_01 v, kv_inner_02 v, real_inner_self_eq_norm_sq]
  ring

/-! ### Injectivity -/

/-- The cusp coordinate map `(u, y) ↦ u σ_v + y₂ λ₂ + y₃ λ₃` is injective: `(σ_v, λ₂, λ₃)` is a
basis of `ℝ³` because `(κ_{v,1}, κ_{v,2}, κ_{v,3})` is an orthogonal basis and
`σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}`. -/
theorem cuspX_injOn (v : Fin 5) : Set.InjOn (fun z : ℝ × E2 => cuspX v z.1 z.2) Set.univ := by
  intro z1 _ z2 _ h
  obtain ⟨u1, y1⟩ := z1
  obtain ⟨u2, y2⟩ := z2
  -- extract the `u` coordinate by pairing with `κ_{v,1}`
  have hu : u1 = u2 := by
    have hh : inner ℝ (kv v 0) (u1 • slope v + cuspY v y1) =
        inner ℝ (kv v 0) (u2 • slope v + cuspY v y2) := by
      have := congrArg (fun x : E3 => inner ℝ (kv v 0) x) h
      simpa only [cuspX] using this
    simp only [inner_add_right, inner_smul_right, inner_kv0_cuspY, inner_kv0_slope,
      add_zero] at hh
    exact mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (kv_ne_zero v 0))) hh
  -- extract `y₂, y₃` by pairing `cuspY` with `κ_{v,2}` and `κ_{v,3}`
  have hy : y1 = y2 := by
    have hc : cuspY v y1 = cuspY v y2 := by
      have hh := h
      rw [hu] at hh
      simp only [cuspX] at hh
      exact add_left_cancel hh
    have h0 : y1 0 = y2 0 := by
      have hh : inner ℝ (kv v 1) (cuspY v y1) = inner ℝ (kv v 1) (cuspY v y2) := by rw [hc]
      rw [inner_kv1_cuspY, inner_kv1_cuspY] at hh
      exact mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (kv_ne_zero v 1))) hh
    have h1 : y1 1 = y2 1 := by
      have hh : inner ℝ (kv v 2) (cuspY v y1) = inner ℝ (kv v 2) (cuspY v y2) := by rw [hc]
      rw [inner_kv2_cuspY, inner_kv2_cuspY] at hh
      exact mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (kv_ne_zero v 2))) hh
    exact PiLp.ext (fun i => by fin_cases i <;> assumption)
  rw [hu, hy]

end Work.Cusp
