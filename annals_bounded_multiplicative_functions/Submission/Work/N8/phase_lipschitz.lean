import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

namespace Work.N8

/-- Auxiliary: `Real.log` is `1/x`-Lipschitz on `[x, x+L]` (for `x > 0`, any `L`).
This is the mean-value theorem applied to `Real.log`, whose derivative `1/t` is at most
`1/x` on the interval. -/
lemma log_sub_abs_le {x L : ℝ} (hx : 0 < x) {a b : ℝ}
    (ha : a ∈ Set.Icc x (x + L)) (hb : b ∈ Set.Icc x (x + L)) :
    |Real.log a - Real.log b| ≤ (1 / x) * |a - b| := by
  have hs : Convex ℝ (Set.Icc x (x + L)) := convex_Icc _ _
  have hdiff : ∀ t ∈ Set.Icc x (x + L), DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le hx ht.1))
  have hbound : ∀ t ∈ Set.Icc x (x + L), ‖deriv Real.log t‖ ≤ 1 / x := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    simpa [one_div] using one_div_le_one_div_of_le hx ht.1
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hs hb ha
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

theorem phase_lipschitz {P γ : Polynomial ℝ} {T T₀ x L c₁ cT : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hTT : |T - T₀| ≤ cT * (x / L))
    (hd : ∀ t ∈ Set.Icc x (x + L),
        |deriv (fun s => P.eval s - T / (2 * Real.pi) * Real.log s - γ.eval s) t| ≤ c₁ / L) :
    ∀ a ∈ Set.Icc x (x + L), ∀ b ∈ Set.Icc x (x + L),
      |(T₀ * Real.log a - 2 * Real.pi * (P.eval a - γ.eval a))
        - (T₀ * Real.log b - 2 * Real.pi * (P.eval b - γ.eval b))| ≤ (2 * Real.pi * c₁ + cT) / L * |a - b| := by
  intro a ha b hb
  have hs : Convex ℝ (Set.Icc x (x + L)) := convex_Icc _ _
  -- `Real.log` Lipschitz bound
  have hlog : |Real.log a - Real.log b| ≤ (1 / x) * |a - b| :=
    log_sub_abs_le hx ha hb
  -- Lipschitz bound for the "phase" function `F s = P.eval s - T/(2π) log s - γ.eval s`
  have hF : |(P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
      - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b)| ≤ (c₁ / L) * |a - b| := by
    have hdiff : ∀ t ∈ Set.Icc x (x + L),
        DifferentiableAt ℝ (fun s => P.eval s - T / (2 * Real.pi) * Real.log s - γ.eval s) t := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx ht.1)
      have hlog' : DifferentiableAt ℝ (fun s => T / (2 * Real.pi) * Real.log s) t :=
        (Real.differentiableAt_log ht0).const_mul _
      exact (P.differentiableAt.sub hlog').sub γ.differentiableAt
    have hbound : ∀ t ∈ Set.Icc x (x + L),
        ‖deriv (fun s => P.eval s - T / (2 * Real.pi) * Real.log s - γ.eval s) t‖ ≤ c₁ / L := by
      intro t ht
      rw [Real.norm_eq_abs]
      exact hd t ht
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hs hb ha
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  -- Bound on the shift `T₀ - T`
  have hTx : |T₀ - T| * (1 / x) ≤ cT / L := by
    have hTT' : |T₀ - T| ≤ (cT / L) * x := by
      rw [abs_sub_comm]
      calc |T - T₀| ≤ cT * (x / L) := hTT
        _ = cT / L * x := by ring
    rw [mul_one_div]
    exact (div_le_iff₀ hx).mpr hTT'
  -- Identity rewriting the target expression through `F`
  have hid : ∀ s : ℝ, T₀ * Real.log s - 2 * Real.pi * (P.eval s - γ.eval s)
      = (T₀ - T) * Real.log s
        - 2 * Real.pi * (P.eval s - T / (2 * Real.pi) * Real.log s - γ.eval s) := fun s => by
    have key : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ T (by positivity)]
    rw [show 2 * Real.pi * (P.eval s - T / (2 * Real.pi) * Real.log s - γ.eval s)
          = 2 * Real.pi * P.eval s - (2 * Real.pi * (T / (2 * Real.pi))) * Real.log s
              - 2 * Real.pi * γ.eval s from by ring]
    rw [key]; ring
  have hEq : ((T₀ * Real.log a - 2 * Real.pi * (P.eval a - γ.eval a))
        - (T₀ * Real.log b - 2 * Real.pi * (P.eval b - γ.eval b)))
      = (T₀ - T) * (Real.log a - Real.log b)
        - 2 * Real.pi * ((P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
            - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b)) := by
    rw [hid a, hid b]; ring
  rw [hEq]
  calc |(T₀ - T) * (Real.log a - Real.log b)
          - 2 * Real.pi * ((P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
              - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b))|
      ≤ |(T₀ - T) * (Real.log a - Real.log b)|
          + |2 * Real.pi * ((P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
              - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b))| := by
        have := abs_sub_le ((T₀ - T) * (Real.log a - Real.log b)) 0
          (2 * Real.pi * ((P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
              - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b)))
        simpa using this
    _ = |T₀ - T| * |Real.log a - Real.log b|
          + 2 * Real.pi * |(P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
              - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b)| := by
        rw [abs_mul (T₀ - T) (Real.log a - Real.log b),
            abs_mul (2 * Real.pi) ((P.eval a - T / (2 * Real.pi) * Real.log a - γ.eval a)
              - (P.eval b - T / (2 * Real.pi) * Real.log b - γ.eval b)),
            abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    _ ≤ |T₀ - T| * ((1 / x) * |a - b|)
          + 2 * Real.pi * ((c₁ / L) * |a - b|) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hF (by positivity))
    _ = (|T₀ - T| * (1 / x) + 2 * Real.pi * (c₁ / L)) * |a - b| := by ring
    _ ≤ (cT / L + 2 * Real.pi * (c₁ / L)) * |a - b| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        linarith [hTx]
    _ = ((2 * Real.pi * c₁ + cT) / L) * |a - b| := by ring

end Work.N8
