import Mathlib
import Submission.Work.Lattice.poissonBasics
import Submission.Work.Poisson.summable_intVec_zpow_neg

/-!
# Summability of a Schwartz function over the integer lattice `ℤⁿ`

A Schwartz function on `ℝⁿ` decays faster than any polynomial, hence its restriction to
the lattice `ℤⁿ` is summable.  This is the basic convergence input for the periodization
`∑_{v ∈ ℤⁿ} f (x + v)` appearing in the Poisson summation formula.

The decay input is Mathlib's `SchwartzMap.one_add_le_sup_seminorm_apply`, which bounds
`‖f x‖` by a constant times `(1 + ‖x‖) ^ (-N)` for any `N`.  The comparison series
`∑_{v ∈ ℤⁿ} (1 + ‖v‖) ^ (-N)` converges for `N > n`; that is
`Work.Poisson.summable_intVec_zpow_neg`, and it is stated for the integer vectors
`Work.Modular.intVec v : Fin n → ℝ` carrying the coordinate supremum norm.  Since the
coordinate supremum norm is dominated by the Euclidean (`ℓ²`) norm
(`PiLp.norm_apply_le`), the series with the Euclidean norm is summable as well.
-/

namespace Work.Lattice

open scoped SchwartzMap

/-- The Euclidean (`ℓ²`) norm dominates the coordinate supremum norm on `ℤⁿ`. -/
theorem norm_intVec_le_norm_intVecE {n : ℕ} (v : Fin n → ℤ) :
    ‖Work.Modular.intVec v‖ ≤ ‖Work.Modular.intVecE v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  simpa using PiLp.norm_apply_le (Work.Modular.intVecE v) i

/-- Comparison of negative integer powers: if `0 ≤ a ≤ b` then
`(1 + b) ^ (-N) ≤ (1 + a) ^ (-N)`. -/
theorem zpow_neg_le_zpow_neg_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) (N : ℕ) :
    (1 + b) ^ (-(N : ℤ)) ≤ (1 + a) ^ (-(N : ℤ)) := by
  have ha1 : 0 < 1 + a := by linarith
  have hb1 : 0 < 1 + b := by linarith
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
    inv_le_inv₀ (pow_pos hb1 N) (pow_pos ha1 N)]
  exact pow_le_pow_left₀ ha1.le (by linarith) N

theorem summable_schwartz_intVec {n : ℕ} (g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable fun v : Fin n → ℤ => g (WithLp.toLp 2 (Work.Lattice.intVecToReal v)) := by
  change Summable fun v : Fin n → ℤ => g (Work.Modular.intVecE v)
  -- The decay bound `‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(n+1))`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(((n + 1 : ℕ)) : ℤ)) := by
    refine ⟨2 ^ (n + 1) * ((Finset.Iic ((n + 1 : ℕ), 0)).sup
      fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, fun x => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := ((n + 1 : ℕ), 0)) (k := n + 1) (n := 0) le_rfl le_rfl g x
    rw [norm_iteratedFDeriv_zero] at h
    rw [zpow_neg, zpow_natCast, inv_eq_one_div, mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr (by rwa [mul_comm] at h)
  -- The comparison series on `ℤⁿ`, first with the supremum norm, then with the Euclidean one.
  have hsumm_sup : Summable fun v : Fin n → ℤ =>
      (1 + ‖Work.Modular.intVec v‖) ^ (-(((n + 1 : ℕ)) : ℤ)) :=
    Work.Poisson.summable_intVec_zpow_neg (ι := Fin n) (n + 1) (by simp)
  have hsumm : Summable fun v : Fin n → ℤ =>
      (1 + ‖Work.Modular.intVecE v‖) ^ (-(((n + 1 : ℕ)) : ℤ)) :=
    hsumm_sup.of_nonneg_of_le (fun v => zpow_nonneg (by positivity) _)
      (fun v => zpow_neg_le_zpow_neg_of_le (norm_nonneg _) (norm_intVec_le_norm_intVecE v) _)
  exact Summable.of_norm_bounded (hsumm.mul_left C) fun v => hC (Work.Modular.intVecE v)

end Work.Lattice
