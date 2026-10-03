import Mathlib
import Submission.Work.Analysis.Paraproduct.TensorNorm

namespace Work.Analysis.Paraproduct

open scoped BigOperators

/-- For a non-negative vector on a finite type and an exponent `r ≥ 2`, the finite `ℓ^r` norm is
bounded by the `ℓ²` norm.  Equivalently, `(∑ u_j^r)^{1/r} ≤ (∑ u_j²)^{1/2}`.

The proof writes `u_j^r = u_j^{r-2} · u_j²` and bounds `u_j^{r-2} ≤ S^{(r-2)/2}` for every `j`,
where `S = ∑ u_j²` and (as `j` ranges over a nonempty set of indices, or vacuously)
`u_j² ≤ S`.  Everything is carried out in `ℝ≥0`, where no sign conditions are needed. -/
private theorem lp_rpow_le_l2 {ι : Type*} [Fintype ι] {r : ℝ} (hr : (2:ℝ) ≤ r)
    (u : ι → NNReal) :
    (∑ j, u j ^ r) ^ (1 / r) ≤ (∑ j, u j ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
  have hr0 : 0 < r := by linarith
  have hw : 0 ≤ r - 2 := by linarith
  have hh : 0 ≤ (r - 2) / 2 := by linarith
  set S : NNReal := ∑ j, u j ^ (2:ℝ) with hSdef
  -- every term of the sum is bounded by the sum
  have hle : ∀ j, u j ^ (2:ℝ) ≤ S := by
    intro j
    have h := Finset.single_le_sum (f := fun k => u k ^ (2:ℝ)) (fun k _ => zero_le)
      (Finset.mem_univ j)
    simpa [hSdef] using h
  -- `u_j^{r-2} ≤ S^{(r-2)/2}`
  have hpow : ∀ j, u j ^ (r - 2) ≤ S ^ ((r - 2) / 2) := by
    intro j
    have h1 : u j ^ (r - 2) = (u j ^ (2:ℝ)) ^ ((r - 2) / 2) := by
      rw [← NNReal.rpow_mul]
      congr 1
      ring
    rw [h1]
    exact NNReal.rpow_le_rpow (hle j) hh
  -- hence `u_j^r = u_j^{r-2} u_j^2 ≤ S^{(r-2)/2} u_j^2`
  have hstep : ∀ j, u j ^ r ≤ S ^ ((r - 2) / 2) * u j ^ (2:ℝ) := by
    intro j
    have h2 : u j ^ r = u j ^ (r - 2) * u j ^ (2:ℝ) := by
      rw [← NNReal.rpow_add_of_nonneg (u j) hw (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hpow j) zero_le
  -- summing gives `∑ u_j^r ≤ S^{r/2}`
  have hsum : ∑ j, u j ^ r ≤ S ^ (r / 2) := by
    calc ∑ j, u j ^ r ≤ ∑ j, S ^ ((r - 2) / 2) * u j ^ (2:ℝ) :=
          Finset.sum_le_sum (fun j _ => hstep j)
      _ = S ^ ((r - 2) / 2) * S := by rw [hSdef, Finset.mul_sum]
      _ = S ^ ((r - 2) / 2) * S ^ (1:ℝ) := by rw [NNReal.rpow_one]
      _ = S ^ ((r - 2) / 2 + 1) :=
          (NNReal.rpow_add_of_nonneg S hh (by norm_num : (0:ℝ) ≤ 1)).symm
      _ = S ^ (r / 2) := by congr 1; ring
  calc (∑ j, u j ^ r) ^ (1 / r) ≤ (S ^ (r / 2)) ^ (1 / r) :=
        NNReal.rpow_le_rpow hsum (by positivity)
    _ = S ^ (1 / (2:ℝ)) := by
      rw [← NNReal.rpow_mul]
      rw [show r / 2 * (1 / r) = (r * (1 / r)) / 2 by ring, mul_one_div_cancel hr0.ne']

theorem WithLp_toLp_norm_mono {J : ℕ} {r : NNReal} (hr : (2 : NNReal) ≤ r) (x : Fin J → ℂ) :
    ‖WithLp.toLp r x‖ ≤ ‖WithLp.toLp (2 : NNReal) x‖ := by
  have hr1 : (1:NNReal) ≤ r := le_trans (by norm_num) hr
  have h1 : Fact (1 ≤ (r:ENNReal)) := ⟨by exact_mod_cast hr1⟩
  have h2 : Fact (1 ≤ ((2:NNReal):ENNReal)) := ⟨by norm_num⟩
  have key : ‖WithLp.toLp (r:ENNReal) x‖₊ ≤ ‖WithLp.toLp (2:NNReal) x‖₊ := by
    rw [PiLp.nnnorm_eq_sum (p := (r:ENNReal)) (by simp) (WithLp.toLp (r:ENNReal) x),
      PiLp.nnnorm_eq_sum (p := ((2:NNReal):ENNReal)) (by simp) (WithLp.toLp (2:NNReal) x)]
    push_cast
    exact lp_rpow_le_l2 (by exact_mod_cast hr) (fun j => ‖x j‖₊)
  exact_mod_cast key

end Work.Analysis.Paraproduct
