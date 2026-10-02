import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-! ## Elementary bounds for polynomial evaluation on the unit disc

We record two elementary facts used to bound the polynomials `Ppoly` and `Qpoly` near `0`:

* `norm_eval_le_sum_coeff`: on the closed unit disc, `‖p.eval w‖` is at most the sum of the
  norms of the coefficients of `p`;
* `norm_eval_le_divX`: if moreover `p.coeff 0 = 0`, i.e. `p` is divisible by `X`, then
  `‖p.eval w‖ ≤ K * ‖w‖` with `K` the sum of the norms of the coefficients of `p.divX`.

Together with the computation of the constant terms of `Ppoly` and `Qpoly`
(`coeff_zero_Ppoly`, `coeff_zero_Qpoly`) these give the requested bounds. -/

/-- On the closed unit disc, the evaluation of a polynomial over `ℂ` is bounded by the sum of the
norms of its coefficients. -/
theorem norm_eval_le_sum_coeff (p : Polynomial ℂ) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖p.eval w‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ := by
  rw [Polynomial.eval_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg w) hw)

/-- A polynomial over `ℂ` with vanishing constant term is `O(w)` on the closed unit disc. -/
theorem norm_eval_le_divX (p : Polynomial ℂ) (w : ℂ) (hw : ‖w‖ ≤ 1) (h0 : p.coeff 0 = 0) :
    ‖p.eval w‖ ≤ (∑ i ∈ Finset.range (p.divX.natDegree + 1), ‖p.divX.coeff i‖) * ‖w‖ := by
  have heval : p.eval w = w * p.divX.eval w := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add p]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, h0,
      add_zero]
  rw [heval, norm_mul]
  have hb := norm_eval_le_sum_coeff p.divX w hw
  calc ‖w‖ * ‖p.divX.eval w‖
      ≤ ‖w‖ * (∑ i ∈ Finset.range (p.divX.natDegree + 1), ‖p.divX.coeff i‖) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg w)
    _ = (∑ i ∈ Finset.range (p.divX.natDegree + 1), ‖p.divX.coeff i‖) * ‖w‖ := by ring

/-- The constant term of `Qpoly` is `1`. -/
theorem coeff_zero_Qpoly (m : ℕ) (hm : 2 ≤ m) (G : Polynomial ℂ) : (Qpoly m G).coeff 0 = 1 := by
  unfold Qpoly
  rw [PowerSeries.coeff_trunc]
  rw [ite_eq_left (by omega : 0 < m - 1)]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [PowerSeries.constantCoeff_inv]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [Polynomial.coeff_coe]
  simp [upoly]

/-- The constant term of `Ppoly` is `1/(m-1)`, so `Ppoly m G - C (1/(m-1))` is divisible by `X`. -/
theorem coeff_zero_Ppoly (m : ℕ) (hm : 2 ≤ m) (G : Polynomial ℂ) :
    (Ppoly m G).coeff 0 = 1 / (((m - 1 : ℕ) : ℂ)) := by
  unfold Ppoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [Polynomial.coeff_monomial, ite_eq_left rfl, coeff_zero_Qpoly m hm G]
    simp
  · intro j _ hj
    rw [Polynomial.coeff_monomial, ite_eq_right hj]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The polynomials `Ppoly` and `Qpoly` are close to their constant terms.**

There are constants `KP, KQ ≥ 0` with
`‖(Ppoly m G).eval w - 1/(m-1)‖ ≤ KP ‖w‖` and `‖(Qpoly m G).eval w - 1‖ ≤ KQ ‖w‖` for every
`‖w‖ ≤ 1`.

(Indeed `Ppoly m G - C (1/(m-1))` and `Qpoly m G - 1` are polynomials divisible by `X`, so on the
unit disc each is bounded by the sum of the norms of its coefficients times `‖w‖.) -/
theorem polyBoundsAux (m : ℕ) (hm : 2 ≤ m) (G : Polynomial ℂ) :
    (∃ KP : ℝ, 0 ≤ KP ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
        ‖(Ppoly m G).eval w - (1 / (((m - 1 : ℕ) : ℂ)))‖ ≤ KP * ‖w‖) ∧
    (∃ KQ : ℝ, 0 ≤ KQ ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ‖(Qpoly m G).eval w - 1‖ ≤ KQ * ‖w‖) := by
  constructor
  · refine ⟨∑ i ∈ Finset.range
        ((Ppoly m G - Polynomial.C (1 / (((m - 1 : ℕ) : ℂ)))).divX.natDegree + 1),
      ‖(Ppoly m G - Polynomial.C (1 / (((m - 1 : ℕ) : ℂ)))).divX.coeff i‖,
      Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
    intro w hw
    have h0 : (Ppoly m G - Polynomial.C (1 / (((m - 1 : ℕ) : ℂ)))).coeff 0 = 0 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_left rfl, coeff_zero_Ppoly m hm G, sub_self]
    have hb := norm_eval_le_divX (Ppoly m G - Polynomial.C (1 / (((m - 1 : ℕ) : ℂ)))) w hw h0
    rw [Polynomial.eval_sub, Polynomial.eval_C] at hb
    exact hb
  · refine ⟨∑ i ∈ Finset.range ((Qpoly m G - Polynomial.C 1).divX.natDegree + 1),
      ‖(Qpoly m G - Polynomial.C 1).divX.coeff i‖,
      Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
    intro w hw
    have h0 : (Qpoly m G - Polynomial.C (1 : ℂ)).coeff 0 = 0 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_left rfl, coeff_zero_Qpoly m hm G, sub_self]
    have hb := norm_eval_le_divX (Qpoly m G - Polynomial.C (1 : ℂ)) w hw h0
    rw [Polynomial.eval_sub, Polynomial.eval_C] at hb
    simpa using hb

end Work.FatouDeg.Petal
