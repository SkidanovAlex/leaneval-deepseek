import Mathlib
import Submission.Work.HP.GradCount.ncard_spec_le

namespace Work.HP.BoundaryMain

/-- The absolute-value version of `Work.HP.GradCount.ncard_spec_le`: the box cut out by the
`n` affine interval constraints `|c k * u + A k| ≤ C` (`k ≠ j`) together with the single
"special" constraint `|c j * v + ∑_{i≠j} w i * c i + A j| ≤ C`, where now `u` and `v` are
merely required to be nonzero, has at most `(2C/|u| + 2)^n * (2C/|v| + 2)` integer points.

The sign of a nonzero `u` is absorbed into the coefficient vector: replacing `u` by `|u|` and
`A k` by `(u/|u|) * A k` (for `k ≠ j`) preserves `|c k * u + A k|`; likewise the sign of `v`
is absorbed into `w` and the constant term `A j`. This reduces the statement to
`ncard_spec_le`, which assumes `0 < u`, `0 < v`. -/
theorem spec_box_ncard_abs (n : ℕ) (j : Fin (n + 1)) (u v C : ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hC : 0 ≤ C) (w A : Fin (n + 1) → ℝ) :
    (({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * u + A k| ≤ C) ∧
        |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j| ≤ C} :
        Set (Fin (n + 1) → ℤ)).ncard : ℝ)
      ≤ (2 * C / |u| + 2) ^ n * (2 * C / |v| + 2) := by
  classical
  have hupos : (0 : ℝ) < |u| := abs_pos.mpr hu
  have hvpos : (0 : ℝ) < |v| := abs_pos.mpr hv
  set σu : ℝ := u / |u| with hσu
  set σv : ℝ := v / |v| with hσv
  have hσu_abs : |σu| = 1 := by rw [hσu, abs_div, abs_abs]; exact div_self (by positivity)
  have hσv_abs : |σv| = 1 := by rw [hσv, abs_div, abs_abs]; exact div_self (by positivity)
  have hσu_mul : σu * |u| = u := by rw [hσu]; exact div_mul_cancel₀ u (by positivity)
  have hσv_mul : σv * |v| = v := by rw [hσv]; exact div_mul_cancel₀ v (by positivity)
  have hσu_sq : σu * σu = 1 := by
    have h2 : σu * σu = |σu| ^ 2 := by rw [sq_abs]; ring
    rw [h2, hσu_abs]; norm_num
  have hσv_sq : σv * σv = 1 := by
    have h2 : σv * σv = |σv| ^ 2 := by rw [sq_abs]; ring
    rw [h2, hσv_abs]; norm_num
  set A2 : Fin (n + 1) → ℝ := fun k => if k = j then σv * A j else σu * A k with hA2
  set w2 : Fin (n + 1) → ℝ := fun i => σv * w i with hw2
  have hcoef : ∀ (c : Fin (n + 1) → ℤ) (k : Fin (n + 1)), k ≠ j →
      |(c k : ℝ) * u + A k| = |(c k : ℝ) * |u| + A2 k| := by
    intro c k hk
    have hA2k : A2 k = σu * A k := by rw [hA2]; simp only [ite_eq_right hk]
    rw [hA2k]
    have heq : (c k : ℝ) * u + A k = σu * ((c k : ℝ) * |u| + σu * A k) := by
      have h1 : σu * ((c k : ℝ) * |u| + σu * A k)
          = (c k : ℝ) * (σu * |u|) + (σu * σu) * A k := by ring
      rw [h1, hσu_mul, hσu_sq, one_mul]
    rw [heq, abs_mul, hσu_abs, one_mul]
  have hcoefj : ∀ c : Fin (n + 1) → ℤ,
      |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j|
      = |(c j : ℝ) * |v| + ∑ i ∈ Finset.univ.erase j, w2 i * (c i : ℝ) + A2 j| := by
    intro c
    have hA2j : A2 j = σv * A j := by rw [hA2]; simp only [ite_true]
    have hsum : ∑ i ∈ Finset.univ.erase j, w2 i * (c i : ℝ)
        = σv * ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) := by
      rw [hw2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi; ring
    rw [hA2j, hsum]
    have heq : (c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j
        = σv * ((c j : ℝ) * |v| + σv * ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + σv * A j) := by
      have h1 : σv * ((c j : ℝ) * |v| + σv * ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + σv * A j)
          = (c j : ℝ) * (σv * |v|) + (σv * σv) * (∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ)) + (σv * σv) * A j := by ring
      rw [h1, hσv_mul, hσv_sq, one_mul, one_mul]
    rw [heq, abs_mul, hσv_abs, one_mul]
  have hset : ({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * u + A k| ≤ C) ∧
        |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j| ≤ C} :
        Set (Fin (n + 1) → ℤ))
      = ({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * |u| + A2 k| ≤ C) ∧
        |(c j : ℝ) * |v| + ∑ i ∈ Finset.univ.erase j, w2 i * (c i : ℝ) + A2 j| ≤ C} :
        Set (Fin (n + 1) → ℤ)) := by
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => by rw [← hcoef c k hk]; exact h1 k hk, by rw [← hcoefj c]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => by rw [hcoef c k hk]; exact h1 k hk, by rw [hcoefj c]; exact h2⟩
  rw [hset]
  exact Work.HP.GradCount.ncard_spec_le n j |u| |v| C hupos hvpos hC w2 A2

end Work.HP.BoundaryMain
