import Mathlib

namespace Work.NN.Core.TelTwoDF

open scoped NNReal ENNReal Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `l`-th term of `p.changeOriginSeries k`, applied to a constant vector `d`, is bounded by
the number of subsets of `Fin (k+l)` of cardinality `l` times `‖p (k+l)‖ ‖d‖^l`. -/
lemma norm_changeOriginSeries_apply_const_le_card (p : FormalMultilinearSeries 𝕜 E F) (d : E)
    (k l : ℕ) :
    ‖(p.changeOriginSeries k l) (fun _ => d)‖ ≤
      (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ) * (‖p (k + l)‖ * ‖d‖ ^ l) := by
  have h1 := p.nnnorm_changeOriginSeries_apply_le_tsum k l d
  have h1r : (‖(p.changeOriginSeries k l) (fun _ => d)‖₊ : ℝ) ≤
      ∑' _ : {s : Finset (Fin (k + l)) // s.card = l},
        ((‖p (k + l)‖₊ * ‖d‖₊ ^ l : ℝ≥0) : ℝ) := by
    rw [← NNReal.coe_tsum]
    exact NNReal.coe_le_coe.mpr h1
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1r
  simp only [NNReal.coe_mul, NNReal.coe_pow] at h1r
  exact h1r

/-- Consequently, that term is bounded by `2 ^ (k+l) * ‖p (k+l)‖ * ‖d‖ ^ l`. -/
lemma norm_changeOriginSeries_apply_const_le (p : FormalMultilinearSeries 𝕜 E F) (d : E)
    (k l : ℕ) :
    ‖(p.changeOriginSeries k l) (fun _ => d)‖ ≤ 2 ^ (k + l) * ‖p (k + l)‖ * ‖d‖ ^ l := by
  refine (norm_changeOriginSeries_apply_const_le_card p d k l).trans ?_
  have hcard : (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ) ≤ 2 ^ (k + l) := by
    exact_mod_cast (Fintype.card_subtype_le (fun s : Finset (Fin (k + l)) => s.card = l)).trans_eq
      (by rw [Fintype.card_finset, Fintype.card_fin])
  calc (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ) * (‖p (k + l)‖ * ‖d‖ ^ l)
      ≤ 2 ^ (k + l) * (‖p (k + l)‖ * ‖d‖ ^ l) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 ^ (k + l) * ‖p (k + l)‖ * ‖d‖ ^ l := by ring

/-- The change of origin coefficient bound, in the `C`, `r` form. -/
lemma norm_changeOriginSeries_apply_const_le_C (p : FormalMultilinearSeries 𝕜 E F) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hp : ∀ k : ℕ, ‖p k‖ ≤ C / r ^ k) {d : E} (hd : ‖d‖ ≤ r / 8)
    (k l : ℕ) :
    ‖(p.changeOriginSeries k l) (fun _ => d)‖ ≤ C / r ^ k * 2 ^ k * (1 / 4) ^ l := by
  refine (norm_changeOriginSeries_apply_const_le p d k l).trans ?_
  have hX : ‖p (k + l)‖ * ‖d‖ ^ l ≤ (C / r ^ (k + l)) * (r / 8) ^ l := by
    refine mul_le_mul (hp (k + l)) (pow_le_pow_left₀ (norm_nonneg d) hd l) (by positivity)
      (by positivity)
  calc 2 ^ (k + l) * ‖p (k + l)‖ * ‖d‖ ^ l
      = 2 ^ (k + l) * (‖p (k + l)‖ * ‖d‖ ^ l) := by ring
    _ ≤ 2 ^ (k + l) * ((C / r ^ (k + l)) * (r / 8) ^ l) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = C / r ^ k * 2 ^ k * (1 / 4) ^ l := by
        rw [pow_add, pow_add]
        have hr8 : (r / 8) ^ l = r ^ l * (1 / 8 : ℝ) ^ l := by
          rw [show r / 8 = r * (1 / 8) by ring, mul_pow]
        have h14 : (1 / 4 : ℝ) ^ l = 2 ^ l * (1 / 8) ^ l := by
          rw [show (1 / 4 : ℝ) = 2 * (1 / 8) by norm_num, mul_pow]
        rw [hr8, h14]
        field_simp

theorem changeOrigin_norm_le_of_bound {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F) {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hp : ∀ k : ℕ, ‖p k‖ ≤ C / r ^ k) {d : E} (hd : ‖d‖ ≤ r / 8) (k : ℕ) :
    ‖p.changeOrigin d k‖ ≤ 2 * C * (2 / r) ^ k := by
  set G : ℝ := C / r ^ k * 2 ^ k with hG
  have hGnn : 0 ≤ G := by rw [hG]; positivity
  have hgeo : Summable (fun l : ℕ => G * (1 / 4 : ℝ) ^ l) := by
    have h := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
    exact h.mul_left G
  have hbound : ∀ l, ‖(p.changeOriginSeries k l) (fun _ => d)‖ ≤ G * (1 / 4) ^ l := by
    intro l
    rw [hG]
    exact norm_changeOriginSeries_apply_const_le_C p hC hr hp hd k l
  have hsumm : Summable (fun l => ‖(p.changeOriginSeries k l) (fun _ => d)‖) :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => hbound l) hgeo
  have hrepr : p.changeOrigin d k = ∑' l, (p.changeOriginSeries k l) (fun _ => d) := rfl
  rw [hrepr]
  calc ‖∑' l, (p.changeOriginSeries k l) (fun _ => d)‖
      ≤ ∑' l, ‖(p.changeOriginSeries k l) (fun _ => d)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' l, G * (1 / 4) ^ l := Summable.tsum_le_tsum (fun l => hbound l) hsumm hgeo
    _ = G * (4 / 3) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)]
        norm_num
    _ ≤ 2 * C * (2 / r) ^ k := by
        have h2 : 2 * C * (2 / r) ^ k = G * 2 := by
          rw [hG, div_pow]
          ring
        rw [h2]
        nlinarith [hGnn]

end Work.NN.Core.TelTwoDF
