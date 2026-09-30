/-
# The `w`-coordinates of an integer torus displacement are bounded away from `0`

A lemma for the fiber computations of the junction coordinate inclusion: the displacement vector
`jlVec v n m = (0, 2π(n + ⟪cuspY v μ(m), σ_v⟫/‖σ_v‖²), (wOf v μ(m))₀, (wOf v μ(m))₁)`
(`Work.RTOwed.jLat`) has its last two components `wOf v (jLreal m)` bounded below away from the
origin whenever `m ≠ 0`: the square sum is at least `10⁻⁶`.

The reason is that the `w`-matrix `G_v = (⟪λ_i, frame_j⟫) = wOf v` is diagonal in the data at hand
(`⟪λ₃,frame₂⟫ = 0` and `⟪λ₂,frame₃⟫ = 0`, by orthogonality of the cusp lattice basis
`κ_{v,1} ⊥ κ_{v,2} ⊥ κ_{v,3}` and `σ_v ⊥ κ_{v,3}`), so that

`wOf v (jLreal m) = (⟪λ₂,frame₂⟫ · m₀, ⟪λ₃,frame₃⟫ · m₁)`,

and both diagonal entries are bounded below: `⟪λ₃,frame₃⟫² = ‖λ₃‖² ≥ 4`, while
`⟪λ₂,frame₂⟫² = ‖λ₂‖² − ⟪λ₂,σ_v⟫²/‖σ_v‖² = ‖κ_{v,2}‖²‖κ_{v,1}‖²/‖σ_v‖² = 4/44101` (cusps 1–4) or
`64/44948` (cusp 5), both `> 10⁻⁶`.  Since an integer `m_i ≠ 0` has `m_i² ≥ 1`, the bound follows.
-/
import Mathlib
import Submission.Work.RTOwed.jLat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.RTOWed

/-! ## Elementary numerical helper -/

/-- `(√n/k · (k/n) · k)² = k²/n` for `n > 0`: the normalisation that appears when squaring the
`σ^⊥`-coordinate of `κ_{v,2}`, which is `√n/k` times an integer multiple. -/
private lemma sqrt_div_mul_sq (n k : ℝ) (hn : 0 < n) :
    (Real.sqrt n / k * (k / n) * k) ^ 2 = k ^ 2 / n := by
  rw [show Real.sqrt n / k * (k / n) * k = k / Real.sqrt n by
    field_simp
    rw [Real.sq_sqrt hn.le]; ring]
  rw [div_pow, Real.sq_sqrt hn.le]

/-- An integer `m ≠ 0` has `m² ≥ 1`, hence `(m : ℝ)² ≥ 1`. -/
private lemma one_le_sq_of_ne_zero {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have : (1 : ℤ) ≤ m ^ 2 := by
    have hpos : (0 : ℤ) < m ^ 2 := by rwa [sq_pos_iff]
    omega
  exact_mod_cast this

/-! ## Orthogonality of the `w`-matrix -/

/-- `κ_{v,2} ⊥ frame3 v`: `frame3 v` is the unit vector along `κ_{v,3}`. -/
private lemma lam2_dot_frame3 (v : Fin 5) :
    inner ℝ (Work.Cusp.lam2 v) (Work.Cusp.frame3 v) = 0 := by
  fin_cases v <;>
    simp [Work.Cusp.frame3, Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
      PiLp.inner_apply, Fin.sum_univ_three]

/-- `κ_{v,3} ⊥ frame2 v`: `frame2 v` lies in the `(κ_{v,1},κ_{v,2},σ_v)`-plane, which is
orthogonal to `κ_{v,3}`. -/
private lemma lam3_dot_frame2 (v : Fin 5) :
    inner ℝ (Work.Cusp.lam3 v) (Work.Cusp.frame2 v) = 0 := by
  fin_cases v <;>
    simp [Work.Cusp.frame2, Work.Cusp.frame2aux, Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.slope,
      Work.Cusp.slopeB, Work.Cusp.slopeC, Work.Cusp.kv, Work.Cusp.kappa,
      PiLp.inner_apply, Fin.sum_univ_three, PiLp.norm_sq_eq_of_L2]

/-! ## Lower bounds for the diagonal entries -/

/-- `⟪κ_{v,2}, frame2 v⟫² ≥ 10⁻⁶` for every cusp: the exact value is
`‖κ_{v,2}‖²‖κ_{v,1}‖²/‖σ_v‖²`, which is `4/44101` (cusps 1–4) or `64/44948` (cusp 5). -/
private lemma lam2_frame2_sq_bound (v : Fin 5) :
    (1 : ℝ) / 10 ^ 6 ≤ (inner ℝ (Work.Cusp.lam2 v) (Work.Cusp.frame2 v)) ^ 2 := by
  fin_cases v <;>
    simp [Work.Cusp.frame2, Work.Cusp.frame2aux, Work.Cusp.lam2, Work.Cusp.slope,
      Work.Cusp.slopeB, Work.Cusp.slopeC, Work.Cusp.kv, Work.Cusp.kappa,
      PiLp.inner_apply, Fin.sum_univ_three, PiLp.norm_sq_eq_of_L2] <;>
    rw [PiLp.norm_eq_of_L2] <;> simp [Fin.sum_univ_three] <;> norm_num <;>
    rw [sqrt_div_mul_sq _ _ (by norm_num)] <;> norm_num

/-- `⟪κ_{v,3}, frame3 v⟫² = ‖κ_{v,3}‖² ≥ 4 ≥ 10⁻⁶` for every cusp. -/
private lemma lam3_frame3_sq_bound (v : Fin 5) :
    (1 : ℝ) / 10 ^ 6 ≤ (inner ℝ (Work.Cusp.lam3 v) (Work.Cusp.frame3 v)) ^ 2 := by
  fin_cases v <;>
    simp [Work.Cusp.frame3, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
      PiLp.inner_apply, Fin.sum_univ_three] <;>
    rw [PiLp.norm_eq_of_L2] <;> simp [Fin.sum_univ_three] <;> norm_num

/-! ## The two coordinates of `wOf v (jLreal M)` -/

/-- The first `w`-coordinate of an integer torus displacement: only the `κ_{v,2}`-component
survives, `⟪κ_{v,3}, frame2 v⟫ = 0`. -/
private lemma wOf_jLreal_zero (v : Fin 5) (M : Fin 2 → ℤ) :
    (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 0
      = inner ℝ (Work.Cusp.lam2 v) (Work.Cusp.frame2 v) * (M 0 : ℝ) := by
  simp [Work.Cusp.wOf, Work.Cusp.cuspY, real_inner_smul_left, inner_add_left, lam3_dot_frame2 v]
  ring_nf

/-- The second `w`-coordinate of an integer torus displacement: only the `κ_{v,3}`-component
survives, `⟪κ_{v,2}, frame3 v⟫ = 0`. -/
private lemma wOf_jLreal_one (v : Fin 5) (M : Fin 2 → ℤ) :
    (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 1
      = inner ℝ (Work.Cusp.lam3 v) (Work.Cusp.frame3 v) * (M 1 : ℝ) := by
  simp [Work.Cusp.wOf, Work.Cusp.cuspY, real_inner_smul_left, inner_add_left, lam2_dot_frame3 v]
  ring_nf

/-! ## The bound -/

theorem jlVec_wOf_sq_bound (v : Work.Space.Cusp) (M : Fin 2 → ℤ) (hM : M ≠ 0) :
    1 / 10 ^ 6 ≤ (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 0 ^ 2
      + (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 1 ^ 2 := by
  have h0 := wOf_jLreal_zero v M
  have h1 := wOf_jLreal_one v M
  have hle2 := lam2_frame2_sq_bound v
  have hle3 := lam3_frame3_sq_bound v
  rw [h0, h1]
  rcases eq_or_ne (M 1) 0 with hM1 | hM1
  · -- the second integer coordinate vanishes, so the first one is nonzero
    have hM0 : M 0 ≠ 0 := by
      intro h
      exact hM (by funext i; fin_cases i <;> simp [h, hM1])
    have hM0sq : (1 : ℝ) ≤ (M 0 : ℝ) ^ 2 := one_le_sq_of_ne_zero hM0
    rw [hM1]
    simp only [Int.cast_zero, mul_zero, sq, add_zero]
    nlinarith [hle2, hM0sq,
      sq_nonneg (inner ℝ (Work.Cusp.lam2 v) (Work.Cusp.frame2 v))]
  · -- the second integer coordinate is nonzero
    have hM1sq : (1 : ℝ) ≤ (M 1 : ℝ) ^ 2 := one_le_sq_of_ne_zero hM1
    nlinarith [hle3, hM1sq,
      sq_nonneg (inner ℝ (Work.Cusp.lam2 v) (Work.Cusp.frame2 v) * (M 0 : ℝ)),
      sq_nonneg (inner ℝ (Work.Cusp.lam3 v) (Work.Cusp.frame3 v))]

end Work.RTOWed
