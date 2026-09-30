import Mathlib
import Submission.Work.BW.aligned_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Purely numerical core of `F_bound_wn_supported`.

Given a vector `t : Fin m → ℤ` carried on the Finset `J`, weights `hc ≥ 0` on `J`, and a
positive `d`, if every coordinate is bounded by
`(9 |J| d³)^{|J|} · (2π/d) · ∏_{i ∈ J.erase j} hc i`, then the weighted `ℓ¹`-norm
`wn (d · hc) t = ∑ i, |t i| · d · hc i` is bounded by `4π |J| (9 |J| d³)^{|J|} · ∏_{i ∈ J} hc i`.
The two constants are in fact equal: the factor `2π/d` together with the outer `d` and the
`2` in front of `wn` reproduces the `4π` on the right. -/
lemma F_bound_wn_supported_aux {m : ℕ} (J : Finset (Fin m)) (t : Fin m → ℤ)
    (hc : Fin m → ℝ) {d : ℝ} (hd : 0 < d) (hhc : ∀ j ∈ J, 0 ≤ hc j)
    (hsupp : ∀ i, i ∉ J → t i = 0)
    (ht : ∀ j ∈ J, |((t j : ℤ) : ℝ)| ≤
      (9 * (J.card : ℝ) * d ^ 3) ^ (J.card) * (2 * Real.pi / d) *
        ∏ i ∈ J.erase j, hc i) :
    2 * wn (fun i => d * hc i) t ≤
      4 * Real.pi * (J.card : ℝ) * (9 * (J.card : ℝ) * d ^ 3) ^ (J.card) *
        ∏ i ∈ J, hc i := by
  classical
  set A : ℝ := (9 * (J.card : ℝ) * d ^ 3) ^ (J.card) with hA
  -- The weighted norm only sees the support `J`.
  have hwn : wn (fun i => d * hc i) t = ∑ j ∈ J, |((t j : ℤ) : ℝ)| * (d * hc j) := by
    simp only [wn]
    exact (Finset.sum_subset (Finset.subset_univ J) (fun x _ hx => by simp [hsupp x hx])).symm
  -- Each coordinate contributes at most `A · 2π · ∏_{i ∈ J} hc i`.
  have hterm : ∀ j ∈ J,
      |((t j : ℤ) : ℝ)| * (d * hc j) ≤ A * (2 * Real.pi) * ∏ i ∈ J, hc i := by
    intro j hj
    have h1 := mul_le_mul_of_nonneg_right (ht j hj) (mul_nonneg hd.le (hhc j hj))
    have h2 : (A * (2 * Real.pi / d) * ∏ i ∈ J.erase j, hc i) * (d * hc j)
        = A * (2 * Real.pi) * ∏ i ∈ J, hc i := by
      rw [← Finset.prod_erase_mul J hc hj]
      field_simp
    exact h1.trans (le_of_eq h2)
  have hsum : ∑ j ∈ J, |((t j : ℤ) : ℝ)| * (d * hc j) ≤
      A * (2 * Real.pi) * (J.card : ℝ) * ∏ i ∈ J, hc i := by
    calc ∑ j ∈ J, |((t j : ℤ) : ℝ)| * (d * hc j)
        ≤ ∑ j ∈ J, A * (2 * Real.pi) * ∏ i ∈ J, hc i := Finset.sum_le_sum hterm
      _ = A * (2 * Real.pi) * (J.card : ℝ) * ∏ i ∈ J, hc i := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc 2 * wn (fun i => d * hc i) t
      = 2 * ∑ j ∈ J, |((t j : ℤ) : ℝ)| * (d * hc j) := by rw [hwn]
    _ ≤ 2 * (A * (2 * Real.pi) * (J.card : ℝ) * ∏ i ∈ J, hc i) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 4 * Real.pi * (J.card : ℝ) * A * ∏ i ∈ J, hc i := by ring

lemma F_bound_wn_supported {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (α : Fin m → K) (ℓ : Fin m → ℂ) (J : Finset (Fin m))
    (t : Fin m → ℤ) (hsupp : ∀ i, i ∉ J → t i = 0)
    (ht : ∀ j ∈ J, |((t j : ℤ) : ℝ)| ≤
      (9 * ((J.card : ℝ)) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (J.card) *
        (2 * Real.pi / (Module.finrank ℚ K : ℝ)) *
          ∏ i ∈ J.erase j, hmod (α i) (ℓ i)) :
    2 * wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) t ≤
      4 * Real.pi * ((J.card : ℝ)) * (9 * (J.card : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (J.card) *
        ∏ i ∈ J, hmod (α i) (ℓ i) := by
  have hd : 0 < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  refine F_bound_wn_supported_aux J t (fun i => hmod (α i) (ℓ i)) hd ?_ hsupp ht
  intro j _
  -- `h(α j) ≥ 1/d > 0`, since the number field degree is positive.
  exact le_of_lt (lt_of_lt_of_le (div_pos one_pos hd)
    (le_trans (le_max_right _ _) (le_max_right _ _)))

end Work.BW
