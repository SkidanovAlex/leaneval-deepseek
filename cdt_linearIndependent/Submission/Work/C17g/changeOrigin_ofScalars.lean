import Mathlib

/-!
# Changing the origin of `ofScalars`

For a scalar series `∑ cₙ xⁿ`, the coefficients of the power series obtained by
expanding at the point `x` are the binomial transforms of the original
coefficients: the `k`-th coefficient evaluated on the constant vector `1` is

`∑' l, ((k + l).choose l) * c (k + l) * x ^ l`.

This is exactly `Work.C17g.changeOrigin_ofScalars`.
-/

namespace Work.C17g

open Finset

/-- Evaluation of a scalar formal multilinear series on an arbitrary vector. -/
private lemma ofScalars_apply_prod (c : ℕ → ℂ) (n : ℕ) (v : Fin n → ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ c n) v = c n * ∏ i, v i := by
  simp only [FormalMultilinearSeries.ofScalars]
  rw [smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    smul_eq_mul, ← List.prod_ofFn]

/-- A "piecewise constant" product over a `Finset`: picking `x` on `s` and `1` outside. -/
private lemma prod_piecewise_eq_pow (x : ℂ) (n : ℕ) (s : Finset (Fin n)) :
    ∏ i, s.piecewise (fun _ => x) (fun _ => (1 : ℂ)) i = x ^ s.card := by
  simp only [Finset.piecewise]
  rw [Finset.prod_ite_mem, Finset.prod_const, Finset.univ_inter]

/-- The `l`-th coefficient of the `k`-th `changeOriginSeries`, evaluated on the constant
vector `1`, is `(k+l).choose l * c (k+l) * x^l`. -/
private lemma changeOriginSeries_apply_eq (c : ℕ → ℂ) (x : ℂ) (k l : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ c).changeOriginSeries k l (fun _ => x)) (fun _ => (1 : ℂ))
      = ((k + l).choose l : ℂ) * c (k + l) * x ^ l := by
  rw [FormalMultilinearSeries.changeOriginSeries]
  rw [_root_.sum_apply]
  rw [_root_.sum_apply]
  simp only [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  trans ∑ s : {s : Finset (Fin (k + l)) // s.card = l}, c (k + l) * x ^ l
  · apply Finset.sum_congr rfl
    intro s _
    rw [ofScalars_apply_prod, prod_piecewise_eq_pow, s.2]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    ring

theorem changeOrigin_ofScalars (c : ℕ → ℂ) {x : ℂ} {k : ℕ}
    (hx : ‖x‖₊ < (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    HasSum (fun l : ℕ => ((k + l).choose l : ℂ) * c (k + l) * x ^ l)
      (((FormalMultilinearSeries.ofScalars ℂ c).changeOrigin x) k (fun _ => 1)) := by
  have hx' : x ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    rw [mem_eball_zero_iff]
    exact hx
  have hx'' : x ∈
      Metric.eball (0 : ℂ) ((FormalMultilinearSeries.ofScalars ℂ c).changeOriginSeries k).radius := by
    rw [mem_eball_zero_iff] at hx' ⊢
    exact lt_of_lt_of_le hx' (FormalMultilinearSeries.le_changeOriginSeries_radius _ k)
  have hAS : HasSum
      (fun l => ((FormalMultilinearSeries.ofScalars ℂ c).changeOriginSeries k l) (fun _ => x))
      (((FormalMultilinearSeries.ofScalars ℂ c).changeOriginSeries k).sum x) :=
    (FormalMultilinearSeries.hasSum _ hx'')
  have hAS2 := ContinuousMultilinearMap.hasSum_eval hAS (fun _ => (1 : ℂ))
  exact hAS2.congr_fun (fun l => (changeOriginSeries_apply_eq c x k l).symm)

end Work.C17g
