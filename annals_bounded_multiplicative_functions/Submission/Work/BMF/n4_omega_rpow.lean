import Mathlib
import Submission.Work.BMF.n4_omega_sqrt_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **`(2m)^{ω(q)}` is at most `q^{1/(2ℓ)}` for large `q`.**  For `ℓ ≥ 1` and `m ≥ 1` there is
`q₀` with `(2m)^{ω(q)} ≤ q^{1/(2ℓ)}` for all `q ≥ q₀`, where `ω(q) = q.primeFactors.card`.

This follows immediately from `Work.BMF.pow_omega_le_pow_aux` in this directory, which states
that for `j, m ≥ 1` there is `q₀` with `(2m)^{j·ω(q)} ≤ q` for all `q ≥ q₀`: take `j = 2ℓ ≥ 1`,
get `((2m)^{ω(q)})^{2ℓ} ≤ q`, and take the `(2ℓ)`-th root (monotonicity of `y ↦ y^{1/(2ℓ)}` on
`ℝ≥0`), using `(q^{1/(2ℓ)})^{2ℓ} = q` for `q ≥ 0`.) -/
lemma n4_omega_rpow (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (((2 * m : ℕ)) : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ ((1 : ℝ) / (2 * (ℓ : ℝ))) := by
  set A : ℝ := ((2 * m : ℕ) : ℝ) with hA
  have hA1 : (1 : ℝ) ≤ A := by rw [hA]; exact_mod_cast (show 1 ≤ 2 * m by omega)
  obtain ⟨q₀, hq₀⟩ := pow_omega_le_pow_aux m (2 * ℓ) hm (by omega)
  refine ⟨max q₀ 1, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hq
  have hqq : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hbig : A ^ ((2 * ℓ) * q.primeFactors.card) ≤ (q : ℝ) :=
    hq₀ q (le_trans (le_max_left _ _) hq)
  -- `((2m)^{ω})^{2ℓ} = (2m)^{2ℓ·ω} ≤ q`
  have key : (A ^ q.primeFactors.card) ^ (2 * ℓ) ≤ (q : ℝ) := by
    have : A ^ (q.primeFactors.card * (2 * ℓ)) ≤ (q : ℝ) := by
      rwa [mul_comm]
    rwa [pow_mul] at this
  -- `(q^{1/(2ℓ)})^{2ℓ} = q`
  have hrhs : ((q : ℝ) ^ ((1 : ℝ) / (2 * (ℓ : ℝ)))) ^ (2 * ℓ) = (q : ℝ) := by
    rw [← Real.rpow_natCast ((q : ℝ) ^ ((1 : ℝ) / (2 * (ℓ : ℝ)))) (2 * ℓ)]
    rw [← Real.rpow_mul hqq]
    have h1 : ((1 : ℝ) / (2 * (ℓ : ℝ))) * ((2 * ℓ : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [h1, Real.rpow_one]
  have hgoal : (A ^ q.primeFactors.card) ^ (2 * ℓ)
      ≤ ((q : ℝ) ^ ((1 : ℝ) / (2 * (ℓ : ℝ)))) ^ (2 * ℓ) := by
    rw [hrhs]; exact key
  exact (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hqq _)
    (by omega : (2 * ℓ) ≠ 0)).mp hgoal

end Work.BMF
