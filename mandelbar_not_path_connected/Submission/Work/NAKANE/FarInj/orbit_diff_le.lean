/-
# Orbit separation for the two diagonal `pMap`-orbits

Fix a large `x` (`‖x‖ ≥ 256`) and a parameter `y` close to `x` (`‖y - x‖ ≤ ‖x‖/2`).
Writing `A_n = (pMap x)^[n] x` and `B_n = (pMap y)^[n] y`, the two orbits separate at most
like the relative error `‖x - y‖/‖x‖`, with a geometric factor `32^n` and weighted by the
sizes of the iterates:

`‖A_n - B_n‖ ≤ 32^n * (‖x - y‖ / ‖x‖) * (‖A_n‖ + ‖B_n‖)`.

(`Work.NAKANE.FarInj.orbit_diff_le`.)

The proof is a one-step induction.  Because `pMap c w = (w² + c̄)² + c` is monic of degree
four, the difference of two `pMap`-values is

`pMap x a - pMap y b = ((a - b)(a + b) + (x̄ - ȳ)) · (a² + b² + x̄ + ȳ) + (x - y)`,

so the one-step separation is controlled by `(‖a‖ + ‖b‖)(‖a‖² + ‖b‖² + ‖x‖ + ‖y‖)`, which is
`O(max(‖a‖,‖b‖)³)`.  Since one `pMap`-step at least *fourths* the norm
(`Work.NAKANE.FarInj.norm_pMap_ge`: `‖w‖⁴/2 ≤ ‖pMap c w‖`), the resulting geometric factor
`(‖a‖+‖b‖)(‖a‖²+‖b‖²+‖x‖+‖y‖)` is bounded by `32·(‖A_{n+1}‖ + ‖B_{n+1}‖)` — so the induction
closes with the constant `32`, and `32^n` times the sum of the norms at level `n` is exactly
the right bookkeeping.  The choice `32` (rather than the true growth) is for arithmetic
convenience; the underlying estimate is a factor `≤ 16` per step with plenty of slack.
-/
import Mathlib
import Submission.Work.NAKANE.FarInj.DiagFoundation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.FarInj

open scoped ComplexConjugate

open Work.Bottcher

/-! ## The one-step difference bound -/

/-- **Difference of two `pMap`-values.**  For arbitrary `x, y, a, b`,

`‖pMap x a - pMap y b‖ ≤ (‖a‖² + ‖b‖² + ‖x‖ + ‖y‖)·(‖a - b‖(‖a‖ + ‖b‖) + ‖x - y‖) + ‖x - y‖`.

This is the exact expansion
`pMap x a - pMap y b = ((a-b)(a+b) + (x̄ - ȳ))(a² + b² + x̄ + ȳ) + (x - y)`
followed by the triangle inequality. -/
lemma norm_pMap_sub_le (x y a b : ℂ) :
    ‖pMap x a - pMap y b‖
      ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖x‖ + ‖y‖) * (‖a - b‖ * (‖a‖ + ‖b‖) + ‖x - y‖) + ‖x - y‖ := by
  have hid : pMap x a - pMap y b
      = ((a - b) * (a + b) + (conj x - conj y)) * ((a ^ 2 + b ^ 2) + (conj x + conj y)) + (x - y) := by
    rw [pMap_apply, pMap_apply]; ring
  rw [hid]
  have hC : ‖(a ^ 2 + b ^ 2) + (conj x + conj y)‖ ≤ ‖a‖^2 + ‖b‖^2 + ‖x‖ + ‖y‖ := by
    have h1 : ‖(a^2 + b^2) + (conj x + conj y)‖ ≤ ‖a^2 + b^2‖ + ‖conj x + conj y‖ := norm_add_le _ _
    have h2 : ‖a^2 + b^2‖ ≤ ‖a^2‖ + ‖b^2‖ := norm_add_le _ _
    have h3 : ‖conj x + conj y‖ ≤ ‖conj x‖ + ‖conj y‖ := norm_add_le _ _
    rw [norm_pow, norm_pow] at h2
    rw [Complex.norm_conj, Complex.norm_conj] at h3
    linarith
  have hB : ‖(a - b) * (a + b) + (conj x - conj y)‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) + ‖x - y‖ := by
    have hconj : conj x - conj y = conj (x - y) := by rw [map_sub]
    rw [hconj]
    have h1 : ‖(a - b) * (a + b) + conj (x - y)‖ ≤ ‖(a - b) * (a + b)‖ + ‖conj (x - y)‖ := norm_add_le _ _
    rw [norm_mul, Complex.norm_conj] at h1
    nlinarith [h1, norm_add_le a b, norm_nonneg (a - b)]
  have hb0 : 0 ≤ ‖a - b‖ * (‖a‖ + ‖b‖) + ‖x - y‖ := by positivity
  have h1 : ‖((a - b) * (a + b) + (conj x - conj y)) * ((a ^ 2 + b ^ 2) + (conj x + conj y)) + (x - y)‖
      ≤ ‖(a - b) * (a + b) + (conj x - conj y)‖ * ‖(a ^ 2 + b ^ 2) + (conj x + conj y)‖ + ‖x - y‖ := by
    calc _ ≤ ‖((a - b) * (a + b) + (conj x - conj y)) * ((a^2 + b^2) + (conj x + conj y))‖ + ‖x - y‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul]
  have h2 : ‖(a - b) * (a + b) + (conj x - conj y)‖ * ‖(a ^ 2 + b ^ 2) + (conj x + conj y)‖ + ‖x - y‖
      ≤ (‖a - b‖ * (‖a‖ + ‖b‖) + ‖x - y‖) * (‖a‖^2 + ‖b‖^2 + ‖x‖ + ‖y‖) + ‖x - y‖ := by
    have h3 := mul_le_mul hB hC (by positivity) hb0
    linarith
  linarith

/-! ## The arithmetic of the induction step -/

/-- **Constant bookkeeping.**  For `u, v ≥ 16` and `nx ≤ u`, `ny ≤ v`,

`(u² + v² + nx + ny)(u + v)² + (u² + v² + nx + ny)(u + v) + (u + v) ≤ 16 (u⁴ + v⁴)`.

This is the numerical heart of the induction: the left-hand side is what one step of
separation costs, and `16(u⁴+v⁴) ≤ 32(‖A_{n+1}‖ + ‖B_{n+1}‖)` by the fourthing estimate. -/
lemma arith_master (u v nx ny : ℝ) (hu : 16 ≤ u) (hv : 16 ≤ v) (hnxu : nx ≤ u) (hnyv : ny ≤ v) :
    (u^2+v^2+nx+ny)*(u+v)^2 + (u^2+v^2+nx+ny)*(u+v) + (u+v) ≤ 16*(u^4+v^4) := by
  have h1 : (0:ℝ) ≤ u := by linarith
  have h2 : (0:ℝ) ≤ v := by linarith
  have hm0 : (0:ℝ) ≤ u + v := by linarith
  have L2 : (u+v)^2 ≤ 2*(u^2+v^2) := by nlinarith [sq_nonneg (u-v)]
  have L3 : (u^2+v^2)^2 ≤ 2*(u^4+v^4) := by nlinarith [sq_nonneg (u^2-v^2)]
  have L4 : (u^2+v^2)*(u+v) ≤ 2*(u^4+v^4) := by
    nlinarith [mul_nonneg hm0 (sq_nonneg (u-v)), sq_nonneg (u-v), h1, h2]
  have L6 : u+v ≤ u^2+v^2 := by
    nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ u-1), mul_nonneg h2 (by linarith : (0:ℝ) ≤ v-1)]
  have L7 : u^2+v^2 ≤ u^4+v^4 := by
    nlinarith [mul_nonneg (sq_nonneg u) (by nlinarith : (0:ℝ) ≤ u^2-1),
      mul_nonneg (sq_nonneg v) (by nlinarith : (0:ℝ) ≤ v^2-1)]
  have L1 : u^2+v^2+nx+ny ≤ (u^2+v^2)+(u+v) := by linarith
  nlinarith [L1, L2, L3, L4, L6, L7, h1, h2, sq_nonneg (u+v), mul_nonneg h1 h2]

/-- **The transfer lemma.**  Given a one-step boundary
`r' ≤ (u² + v² + nx + ny)(r(u+v) + δ) + δ`, the induction hypothesis `r ≤ e(u+v)`, the
matching estimate `δ ≤ e(u+v)` for the parameter increment, and the fourthing growth
estimate `(u⁴ + v⁴)/2 ≤ N` for the new orbit sizes, we get `r' ≤ 32 e N`. -/
lemma step_transfer (u v nx ny N r r' δ e : ℝ)
    (hu : 16 ≤ u) (hv : 16 ≤ v) (hnx0 : 0 ≤ nx) (hnxu : nx ≤ u) (hny0 : 0 ≤ ny) (hnyv : ny ≤ v)
    (hN : (u^4+v^4)/2 ≤ N)
    (he : 0 ≤ e) (hr : r ≤ e * (u+v)) (hδe : δ ≤ e * (u+v))
    (hstep : r' ≤ (u^2+v^2+nx+ny) * (r*(u+v) + δ) + δ) :
    r' ≤ 32 * e * N := by
  have harith : (u^2+v^2+nx+ny)*(u+v)^2 + (u^2+v^2+nx+ny)*(u+v) + (u+v) ≤ 32*N := by
    have := arith_master u v nx ny hu hv hnxu hnyv
    linarith
  have hS : 0 ≤ u+v := by linarith
  have hK : 0 ≤ u^2+v^2+nx+ny := by nlinarith [hu, hv, hnx0, hny0]
  have h1 : r * (u+v) ≤ e * (u+v) * (u+v) := mul_le_mul_of_nonneg_right hr hS
  have h2 : (u^2+v^2+nx+ny) * (r*(u+v)+δ) + δ
      ≤ e * ((u^2+v^2+nx+ny)*(u+v)^2 + (u^2+v^2+nx+ny)*(u+v) + (u+v)) := by
    nlinarith [h1, hδe, hK, hS, he]
  have h3 : e * ((u^2+v^2+nx+ny)*(u+v)^2 + (u^2+v^2+nx+ny)*(u+v) + (u+v)) ≤ e * (32*N) :=
    mul_le_mul_of_nonneg_left harith he
  linarith [hstep, h2, h3]

/-- **Normalising the parameter increment.**  If `δ ≥ 0`, `X > 0`, `X ≤ S` and `1 ≤ K` then
`δ ≤ K · (δ/X) · S`; applied with `δ = ‖x - y‖`, `X = ‖x‖`, `S = ‖A_n‖ + ‖B_n‖`,
`K = 32^n` this converts the `n = 0` bound `δ ≤ (δ/‖x‖)(‖x‖+‖y‖)` into the `e`-form used by
the induction. -/
lemma delta_le_mul (δ X S K : ℝ) (hδ : 0 ≤ δ) (hX : 0 < X) (hXS : X ≤ S) (hK : 1 ≤ K) :
    δ ≤ K * (δ / X) * S := by
  have h1 : δ = (δ / X) * X := by rw [div_mul_cancel₀ _ hX.ne']
  have h2 : (0:ℝ) ≤ δ / X := by positivity
  have hS : (0:ℝ) ≤ S := by linarith
  have h3 : δ ≤ (δ / X) * S := by
    calc δ = (δ / X) * X := h1
      _ ≤ (δ / X) * S := mul_le_mul_of_nonneg_left hXS h2
  have h4 : (0:ℝ) ≤ (δ / X) * S := mul_nonneg h2 hS
  have h5 : (δ / X) * S ≤ K * ((δ / X) * S) := by nlinarith [hK, h4]
  calc δ ≤ (δ / X) * S := h3
    _ ≤ K * ((δ / X) * S) := h5
    _ = K * (δ / X) * S := by ring

/-! ## The main lemma -/

/-- **Orbit separation for the two diagonal orbits.**  Let `‖x‖ ≥ 256` and `‖y - x‖ ≤ ‖x‖/2` (so the point `x` and the parameter `y` are comparable and close).  Then the `pMap x`-orbit of `x` and the `pMap y`-orbit of `y` separate at most like `32^n (‖x-y‖/‖x‖)` times the sum of norms of the two `n`-th iterates.  Here `pMap c w = (w^2 + conj c)^2 + c = T_c (T_c w)` is the holomorphic second iterate of the tricorn map.  The constant `32` is not optimal (the true growth is `4^n`) and is chosen for the convenience of the arithmetic. -/
lemma orbit_diff_le (x y : ℂ) (hA : 256 ≤ ‖x‖) (hδ : ‖y - x‖ ≤ ‖x‖ / 2) (n : ℕ) :
    ‖(Work.Bottcher.pMap x)^[n] x - (Work.Bottcher.pMap y)^[n] y‖
      ≤ 32 ^ n * (‖x - y‖ / ‖x‖)
          * (‖(Work.Bottcher.pMap x)^[n] x‖ + ‖(Work.Bottcher.pMap y)^[n] y‖) := by
  have hxpos : (0:ℝ) < ‖x‖ := by linarith
  have key : ∀ m : ℕ, ‖(pMap x)^[m] x - (pMap y)^[m] y‖
      ≤ 32 ^ m * (‖x - y‖ / ‖x‖) * (‖(pMap x)^[m] x‖ + ‖(pMap y)^[m] y‖) := by
    intro m
    induction m with
    | zero =>
      simp only [Function.iterate_zero_apply, pow_zero, one_mul]
      rw [div_mul_eq_mul_div, le_div_iff₀ hxpos]
      nlinarith [norm_nonneg y, norm_nonneg (x - y)]
    | succ m ih =>
      obtain ⟨hu16, hv16, hxu, hyv⟩ := orbit_bounds x y hA hδ m
      have hgA : ‖(pMap x)^[m] x‖^4/2 ≤ ‖pMap x ((pMap x)^[m] x)‖ :=
        (norm_pMap_ge x ((pMap x)^[m] x) hu16 (by linarith)).1
      have hgB : ‖(pMap y)^[m] y‖^4/2 ≤ ‖pMap y ((pMap y)^[m] y)‖ :=
        (norm_pMap_ge y ((pMap y)^[m] y) hv16 (by linarith)).1
      have hN : (‖(pMap x)^[m] x‖^4 + ‖(pMap y)^[m] y‖^4)/2
                ≤ ‖pMap x ((pMap x)^[m] x)‖ + ‖pMap y ((pMap y)^[m] y)‖ := by linarith
      have hstep := norm_pMap_sub_le x y ((pMap x)^[m] x) ((pMap y)^[m] y)
      have hr : ‖(pMap x)^[m] x - (pMap y)^[m] y‖
          ≤ (32^m * (‖x - y‖/‖x‖)) * (‖(pMap x)^[m] x‖ + ‖(pMap y)^[m] y‖) := ih
      have he : (0:ℝ) ≤ 32^m * (‖x - y‖/‖x‖) := by positivity
      have hδe : ‖x - y‖ ≤ (32^m * (‖x - y‖/‖x‖)) * (‖(pMap x)^[m] x‖ + ‖(pMap y)^[m] y‖) :=
        delta_le_mul _ _ _ _ (by positivity) hxpos (by linarith) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 32))
      have hmain := step_transfer ‖(pMap x)^[m] x‖ ‖(pMap y)^[m] y‖ ‖x‖ ‖y‖
          (‖pMap x ((pMap x)^[m] x)‖ + ‖pMap y ((pMap y)^[m] y)‖)
          ‖(pMap x)^[m] x - (pMap y)^[m] y‖
          ‖pMap x ((pMap x)^[m] x) - pMap y ((pMap y)^[m] y)‖
          ‖x - y‖ (32^m * (‖x - y‖/‖x‖))
          hu16 hv16 (norm_nonneg x) hxu (norm_nonneg y) hyv hN he hr hδe hstep
      have h1 : (pMap x)^[m.succ] x = pMap x ((pMap x)^[m] x) := Function.iterate_succ_apply' (pMap x) m x
      have h2 : (pMap y)^[m.succ] y = pMap y ((pMap y)^[m] y) := Function.iterate_succ_apply' (pMap y) m y
      rw [h1, h2]
      have hp : (32:ℝ) ^ m.succ = 32 ^ m * 32 := pow_succ 32 m
      have heq : 32 ^ m.succ * (‖x - y‖ / ‖x‖) * (‖pMap x ((pMap x)^[m] x)‖ + ‖pMap y ((pMap y)^[m] y)‖)
          = 32 * (32^m * (‖x - y‖/‖x‖)) * (‖pMap x ((pMap x)^[m] x)‖ + ‖pMap y ((pMap y)^[m] y)‖) := by
        rw [hp]; ring
      rw [heq]
      exact hmain
  exact key n

end Work.NAKANE.FarInj
