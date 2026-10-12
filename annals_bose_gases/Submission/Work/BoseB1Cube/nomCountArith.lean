import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

theorem nomCountArith {μ a ℓ κ b C₀ C_A E n N R cP : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hC₀ : 0 ≤ C₀) (hC_A : 0 ≤ C_A) (hE : 0 ≤ E) (hN : 0 < N) (hcP : 0 ≤ cP)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hKl : μ * a * ℓ ^ 2 * κ ≤ 1)
    (hsmall : C₀ * E * κ * (1 + 2 * (μ * a * ℓ ^ 2) / b) ≤ 1 / 2)
    (h1 : μ * a * (n : ℝ) * N
        ≤ C₀ * (μ ^ 2 * a * ℓ ^ 3 * N + R + μ * a * cP))
    (h2 : R ≤ C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * (n : ℝ) * N)
    (h3 : (b / (2 * ℓ ^ 2)) * cP
        ≤ C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * (n : ℝ) * N) :
    (n : ℝ) ≤ 2 * C₀ * (1 + C_A * (1 + 2 / b)) * μ * ℓ ^ 3 := by
  have h2b : (0:ℝ) < 2 / b := by positivity
  have hμa : (0:ℝ) < μ * a := by positivity
  have hμaN : (0:ℝ) < μ * a * N := by positivity
  rcases le_or_gt n 0 with hn | hn
  · -- `n ≤ 0`: the right-hand side is nonnegative
    have hnn : (0:ℝ) ≤ 2 * C₀ * (1 + C_A * (1 + 2 / b)) * μ * ℓ ^ 3 := by positivity
    linarith
  · -- `0 < n`; multiply `hsmall` by the positive count `μ a N n`
    have hBn : (0:ℝ) < (μ * a * N) * n := by positivity
    have hb3 : (0:ℝ) ≤ 2 * ℓ ^ 2 / b := by positivity
    have hcancel : (2 * ℓ ^ 2 / b) * (b / (2 * ℓ ^ 2)) = 1 := by field_simp
    -- `h3` cleared of its divisor `b/(2ℓ²)`
    have h3b : cP ≤ (2 * ℓ ^ 2 / b) * (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N) := by
      have h := mul_le_mul_of_nonneg_left h3 hb3
      have heq : (2 * ℓ ^ 2 / b) * ((b / (2 * ℓ ^ 2)) * cP) = cP := by
        rw [← mul_assoc, hcancel, one_mul]
      rw [heq] at h
      exact h
    -- `h1` rearranged
    have hA : (μ * a * N) * n ≤ C₀ * (μ ^ 2 * a * ℓ ^ 3 * N + R + μ * a * cP) := by linarith [h1]
    -- the `R`-row and the `cP`-row combined
    have hRp : R + μ * a * cP
        ≤ (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N)
          * (1 + 2 * (μ * a * ℓ ^ 2) / b) := by
      have h := add_le_add h2 (mul_le_mul_of_nonneg_left h3b (le_of_lt hμa))
      have heq : (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N)
            * (1 + 2 * (μ * a * ℓ ^ 2) / b)
          = (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N)
            + μ * a * ((2 * ℓ ^ 2 / b)
                * (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N)) := by ring
      linarith [h, heq]
    have hA2 : C₀ * (μ ^ 2 * a * ℓ ^ 3 * N + R + μ * a * cP)
        ≤ C₀ * (μ ^ 2 * a * ℓ ^ 3 * N
            + (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N)
              * (1 + 2 * (μ * a * ℓ ^ 2) / b)) := by
      apply mul_le_mul_of_nonneg_left _ hC₀
      linarith [hRp]
    -- `κ (1 + 2 μ a ℓ²/b) ≤ 1 + 2/b` from `κ ≤ 1` and `μ a ℓ² κ ≤ 1`
    have hκ : κ * (1 + 2 * (μ * a * ℓ ^ 2) / b) ≤ 1 + 2 / b := by
      have h1' : κ ≤ 1 := hκ1
      have h2' : (2 * (μ * a * ℓ ^ 2) / b) * κ ≤ 2 / b := by
        have h := mul_le_mul_of_nonneg_right hKl (le_of_lt h2b)
        calc (2 * (μ * a * ℓ ^ 2) / b) * κ = (μ * a * ℓ ^ 2 * κ) * (2 / b) := by ring
          _ ≤ 1 * (2 / b) := h
          _ = 2 / b := by ring
      calc κ * (1 + 2 * (μ * a * ℓ ^ 2) / b) = κ + (2 * (μ * a * ℓ ^ 2) / b) * κ := by ring
        _ ≤ 1 + 2 / b := add_le_add h1' h2'
    have hCA' : C₀ * C_A * (κ * (1 + 2 * (μ * a * ℓ ^ 2) / b)) ≤ C₀ * C_A * (1 + 2 / b) :=
      mul_le_mul_of_nonneg_left hκ (mul_nonneg hC₀ hC_A)
    have hCAκ : (μ ^ 2 * a * ℓ ^ 3 * N) * (C₀ * C_A * (κ * (1 + 2 * (μ * a * ℓ ^ 2) / b)))
        ≤ (μ ^ 2 * a * ℓ ^ 3 * N) * (C₀ * C_A * (1 + 2 / b)) :=
      mul_le_mul_of_nonneg_left hCA' (by positivity)
    -- the `n`-coefficient is at most `1/2`
    have hQ : (C₀ * E * κ * (1 + 2 * (μ * a * ℓ ^ 2) / b)) * ((μ * a * N) * n)
        ≤ (1 / 2) * ((μ * a * N) * n) :=
      mul_le_mul_of_nonneg_right hsmall (le_of_lt hBn)
    have hfin : C₀ * (μ ^ 2 * a * ℓ ^ 3 * N
          + (C_A * (μ ^ 2 * a * ℓ ^ 3 * κ) * N + E * (μ * a * κ) * n * N)
            * (1 + 2 * (μ * a * ℓ ^ 2) / b))
        ≤ C₀ * μ ^ 2 * a * ℓ ^ 3 * N * (1 + C_A * (1 + 2 / b))
          + (1 / 2) * ((μ * a * N) * n) := by
      linarith [hCAκ, hQ]
    have hmain : (μ * a * N) * n
        ≤ (μ * a * N) * (C₀ * μ * ℓ ^ 3 * (1 + C_A * (1 + 2 / b)))
          + (1 / 2) * ((μ * a * N) * n) := by
      have h := le_trans hA (le_trans hA2 hfin)
      nlinarith [h]
    have hfin2 : (μ * a * N) * n
        ≤ (μ * a * N) * (2 * (C₀ * μ * ℓ ^ 3 * (1 + C_A * (1 + 2 / b)))) := by linarith [hmain]
    have hnb : n ≤ 2 * (C₀ * μ * ℓ ^ 3 * (1 + C_A * (1 + 2 / b))) :=
      (mul_le_mul_iff_right₀ hμaN).mp hfin2
    linarith [hnb]

end Work.BoseB1Cube
