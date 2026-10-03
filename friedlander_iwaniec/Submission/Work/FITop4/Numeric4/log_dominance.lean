import Mathlib

namespace Work.FITop4.Numeric4

theorem log_dominance :
    (∀ C δ : ℝ, 0 ≤ C → 0 < δ → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (Real.log (x : ℝ)) ^ C ≤ (x : ℝ) ^ δ) ∧
    (∀ C : ℝ, 0 ≤ C → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (Real.log (x : ℝ)) ^ C ≤ Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2)) ∧
    (∀ C η : ℝ, 0 ≤ C → 0 < η → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (Real.log (x : ℝ)) ^ C ≤ Real.exp (η * Real.log (x : ℝ))) ∧
    (∀ D : ℝ, 0 ≤ D → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → D ≤ Real.log (x : ℝ)) ∧
    (∀ D : ℝ, 0 ≤ D → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → D ≤ Real.log (Real.log (x : ℝ))) := by
  -- (1) `(log x)^C ≤ x^δ` eventually: `log x ^ C = o(x ^ δ)` for `δ > 0`.
  have h1 : ∀ C δ : ℝ, 0 ≤ C → 0 < δ → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (Real.log (x : ℝ)) ^ C ≤ (x : ℝ) ^ δ := by
    intro C δ hC hδ
    have h : (fun x : ℝ => (Real.log x)^C) =o[Filter.atTop] (fun x => x^δ) :=
      _root_.isLittleO_log_rpow_rpow_atTop C hδ
    rw [Asymptotics.isLittleO_iff] at h
    have h1' : ∀ᶠ x : ℝ in Filter.atTop, ‖(Real.log x)^C‖ ≤ 1 * ‖x^δ‖ := h one_pos
    have h2' : ∀ᶠ n : ℕ in Filter.atTop, ‖(Real.log (n:ℝ))^C‖ ≤ 1 * ‖((n:ℝ))^δ‖ :=
      tendsto_natCast_atTop_atTop.eventually h1'
    have h3' : ∀ᶠ n : ℕ in Filter.atTop, 3 ≤ n :=
      Filter.eventually_atTop.2 ⟨3, fun b hb => hb⟩
    rw [Filter.eventually_atTop] at h2' h3'
    obtain ⟨a, ha⟩ := h2'
    obtain ⟨b, hb⟩ := h3'
    refine ⟨max a b, fun n hn => ?_⟩
    have := ha n (le_trans (le_max_left _ _) hn)
    simp only [one_mul] at this
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg n) C),
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ)] at this
    exact this
  -- (5) `D ≤ log (log x)` eventually (used for (2)).
  have h5 : ∀ D : ℝ, 0 ≤ D → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        D ≤ Real.log (Real.log (x : ℝ)) := by
    intro D hD
    obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (Real.exp D))
    refine ⟨max N 3, fun x hx => ?_⟩
    have hxN : N ≤ x := le_trans (le_max_left _ _) hx
    have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le (Real.exp_pos (Real.exp D)) hN
    have hlogN : Real.exp D ≤ Real.log (N:ℝ) := by
      rw [← Real.log_exp (Real.exp D)]
      exact Real.log_le_log (Real.exp_pos (Real.exp D)) hN
    have hlogNpos : 0 < Real.log (N:ℝ) := lt_of_lt_of_le (Real.exp_pos D) hlogN
    have hlogx : Real.log (N:ℝ) ≤ Real.log (x:ℝ) :=
      Real.log_le_log hNpos (Nat.cast_le.mpr hxN)
    have hDle : D ≤ Real.log (Real.log (N:ℝ)) := by
      rw [← Real.log_exp D]
      exact Real.log_le_log (Real.exp_pos D) hlogN
    have : Real.log (Real.log (N:ℝ)) ≤ Real.log (Real.log (x:ℝ)) :=
      Real.log_le_log hlogNpos hlogx
    linarith
  -- (4) `D ≤ log x` eventually.
  have h4 : ∀ D : ℝ, 0 ≤ D → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        D ≤ Real.log (x : ℝ) := by
    intro D hD
    obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp D)
    refine ⟨N, fun x hx => ?_⟩
    have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le (Real.exp_pos D) hN
    have hDle : D ≤ Real.log (N:ℝ) := by
      rw [← Real.log_exp D]
      exact Real.log_le_log (Real.exp_pos D) hN
    have hlogx : Real.log (N:ℝ) ≤ Real.log (x:ℝ) :=
      Real.log_le_log hNpos (Nat.cast_le.mpr hx)
    linarith
  -- (2) `(log x)^C ≤ exp((log log x)^2)`: take logs; `C ≤ log log x` eventually.
  have h2 : ∀ C : ℝ, 0 ≤ C → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (Real.log (x : ℝ)) ^ C ≤ Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := by
    intro C hC
    obtain ⟨a, ha⟩ := h5 C hC
    refine ⟨max a 3, fun x hx => ?_⟩
    have hxa : a ≤ x := le_trans (le_max_left _ _) hx
    have hxC : C ≤ Real.log (Real.log (x:ℝ)) := ha x hxa
    have hxpos : (0:ℝ) < Real.log (x:ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < x by omega)
    have hnn : 0 ≤ Real.log (Real.log (x:ℝ)) := le_trans hC hxC
    rw [Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hxC hnn
  -- (3) `(log x)^C ≤ exp(η log x) = x^η` is the special case `δ = η` of (1).
  have h3 : ∀ C η : ℝ, 0 ≤ C → 0 < η → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (Real.log (x : ℝ)) ^ C ≤ Real.exp (η * Real.log (x : ℝ)) := by
    intro C η hC hη
    obtain ⟨x0, hx0⟩ := h1 C η hC hη
    refine ⟨max x0 2, fun x hx => ?_⟩
    have hx1 : x0 ≤ x := le_trans (le_max_left _ _) hx
    have h := hx0 x hx1
    have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (show 0 < x by omega)
    have heq : (x:ℝ)^η = Real.exp (η * Real.log (x:ℝ)) := by
      rw [Real.rpow_def_of_pos hxpos, mul_comm]
    rw [heq] at h
    exact h
  exact ⟨h1, h2, h3, h4, h5⟩

end Work.FITop4.Numeric4
