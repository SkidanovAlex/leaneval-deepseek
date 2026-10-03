import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

/-- A `Λ`-lacunary sequence of nonnegative reals with `Λ > 1` and positive first term is
    unbounded: for every `M` all sufficiently late terms exceed `M`. -/
theorem unbounded_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {x : ℕ → NNReal} (hx0 : 0 < x 0)
    (hx : ∀ n, Λ * x n ≤ x (n + 1)) :
    ∀ M : NNReal, ∃ n : ℕ, ∀ m ≥ n, M ≤ x m := by
  have hx0ne : x 0 ≠ 0 := ne_of_gt hx0
  have hgeom : ∀ n, Λ ^ n * x 0 ≤ x n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc Λ ^ (k + 1) * x 0 = Λ * (Λ ^ k * x 0) := by ring
        _ ≤ Λ * x k := by
              exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ x (k + 1) := hx k
  have hmono : Monotone x := by
    apply monotone_nat_of_le_succ
    intro n
    calc x n = 1 * x n := by rw [one_mul]
      _ ≤ Λ * x n := mul_le_mul_of_nonneg_right hΛ.le (by positivity)
      _ ≤ x (n + 1) := hx n
  intro M
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (y := Λ) (M / x 0) hΛ
  refine ⟨n, fun m hm => ?_⟩
  have h1 : M ≤ Λ ^ n * x 0 := by
    have h2 : M / x 0 * x 0 ≤ Λ ^ n * x 0 :=
      mul_le_mul_of_nonneg_right hn.le (by positivity)
    rwa [div_mul_cancel₀ M hx0ne] at h2
  exact le_trans h1 (le_trans (hgeom n) (hmono hm))

end Commons.Analysis.Real