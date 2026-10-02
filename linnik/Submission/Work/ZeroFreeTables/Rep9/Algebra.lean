/-
# ZeroFreeTables/Rep9/Algebra

The **algebraic endgame** of the repeated-zero (§9-diagonal) derivation of
`Engine.HBLemma9_1_rep`: from the inequality `(D)` that the §9 double-zero derivation
produces, and the side condition `cond913` at the diagonal, deduce the target
`ineq913 λ₁ λ₁ a K ε`.

Running HB §9 at the *double* zero `ρ₁` (the two points `σ+iγ₀`, `σ+iγ₁` of (9.1)
coincide, and the multiplicity `≥ 2` of `ρ₁` doubles the "near zero" terms) gives, with
`α = a + λ₁`, `x = α/a` and the constant `c` of the log-derivative input (HB Lemma 3.1
at `φ = 1/2`, i.e. `c = 1/4`),

`(D) :  0 ≤ (K²+K+½)·P₃(x) − (2K²+4K+3/2)·P₃(1) + α·c·(K²+3K+3/2)`,

whereas the target is

`(T) :  0 ≤ (K²+½)·(P₃(x) − P₃(1)) − 2K·P₃(1) + α·(K²+3K+3/2)/6 + α·ε`.

With `A'(x) = (K²+2K+1)·P₃(1) − K·P₃(x)` one has exactly

`(T) − (D) = A'(x) + α·(1/6 − c)·(K²+3K+3/2) + α·ε`.

`cond913` gives `x³ ≤ K₀+1` (`K₀ = Kond K`), and `P₃(y) ≤ (8/3)y³` for `y ≥ 1`, so
`A'(x) ≥ (8/3)·((K+1)² − K(K₀+1)) = (8/3)·slack₀` with
`slack₀ = K²+K+1−K·K₀ ≥ K`.  Hence for `c ≤ 1/6 + slack₀/(12K)` (satisfied by `c = 1/4`)

`(T) ≥ (D) + slack₀·((8/3) − α(K²+3K+3/2)/(12K)) + αε`.

If `α(K²+3K+3/2) < 32K` this is `≥ 0` using `(D) ≥ 0`; if `α(K²+3K+3/2)/6 ≥ 16K/3` then
`(T) ≥ 0` directly from `P₃(x) ≥ P₃(1) = 8/3`.  The two ranges cover everything.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Rep9

open Work.ZeroFreeTables

theorem P3R_one : P3R 1 = 8/3 := by norm_num [P3R]

/-- `P₃` is increasing on `[0,∞)`. -/
theorem P3R_mono {x y : ℝ} (hx0 : 0 ≤ x) (h : x ≤ y) : P3R x ≤ P3R y := by
  have hy0 : 0 ≤ y := le_trans hx0 h
  have h2 : x^2 ≤ y^2 := by nlinarith only [sq_nonneg (y - x), sq_nonneg (y + x), hy0, hx0, h]
  have h3 : x^3 ≤ y^3 := by nlinarith [sq_nonneg (y - x), hy0, hx0]
  simp only [P3R]
  linarith only [h, h2, h3]

/-- `P₃(y) ≤ (8/3)y³` for `y ≥ 1` (i.e. `1 + y ≤ 2y²`). -/
theorem P3R_le_cube {y : ℝ} (hy : 1 ≤ y) : P3R y ≤ (8/3) * y^3 := by
  have h : 1 + y ≤ 2*y^2 := by linarith only [sq_nonneg (y - 1), hy]
  have hmul : y * (1 + y) ≤ y * (2*y^2) := mul_le_mul_of_nonneg_left h (by linarith only [hy])
  simp only [P3R]
  linarith only [hmul]

/-- `K ≤ slack₀ = K²+K+1 − K·Kond K`. -/
theorem slack_ge {K : ℝ} (hK : 0 < K) : K ≤ K^2 + K + 1 - K * Kond K := by
  have hle : Kond K ≤ K + 3/(4*K) := min_le_left _ _
  have hle' : Kond K ≤ 4*K := min_le_right _ _
  by_cases h : (1/2 : ℝ) ≤ K
  · have hm : K * Kond K ≤ K * (K + 3/(4*K)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hK)
    have h2 : K * (K + 3/(4*K)) = K^2 + 3/4 := by field_simp
    linarith only [hm, h2]
  · have hm : K * Kond K ≤ K * (4*K) :=
      mul_le_mul_of_nonneg_left hle' (le_of_lt hK)
    nlinarith only [hm, h, hK]

/-- **The algebraic endgame.** -/
theorem ineq913_diag_of_derived {a K c ε lam : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hε : 0 < ε) (hlam : 0 ≤ lam)
    (hx3 : ((a + lam)/a)^3 ≤ Kond K + 1)
    (hc : c ≤ 1/6 + (K^2 + K + 1 - K * Kond K)/(12*K))
    (hD : 0 ≤ (K^2 + K + 1/2) * P3R ((a+lam)/a) - (2*K^2 + 4*K + 3/2) * P3R 1
            + (a+lam) * c * (K^2 + 3*K + 3/2)) :
    ineq913 lam lam a K ε := by
  set al := a + lam with hal
  set x := al/a with hx
  set c2 := K^2 + 3*K + 3/2 with hc2
  set S := K^2 + K + 1 - K * Kond K with hS
  have halpos : 0 < al := by rw [hal]; linarith only [ha, hlam]
  have hx1 : 1 ≤ x := by
    rw [hx, hal]; rw [le_div_iff₀ ha]; linarith only [hlam]
  have hx3' : x^3 ≤ Kond K + 1 := by rw [hx, hal] at hx3 ⊢; exact hx3
  have hc2pos : 0 < c2 := by rw [hc2]; positivity
  have hP1 : P3R 1 = 8/3 := P3R_one
  have hSnn : 0 ≤ S := by rw [hS]; linarith only [slack_ge hK, hK]
  -- A' ≥ (8/3)S
  have hP3cube : P3R x ≤ (8/3) * x^3 := P3R_le_cube hx1
  have hA' : (8/3) * S ≤ (K^2 + 2*K + 1) * P3R 1 - K * P3R x := by
    have h1 : K * P3R x ≤ K * ((8/3) * x^3) := mul_le_mul_of_nonneg_left hP3cube (le_of_lt hK)
    have h2 : (8/3) * x^3 ≤ (8/3) * (Kond K + 1) := by linarith only [hx3', hx3]
    have h3 : K * ((8/3) * x^3) ≤ K * ((8/3) * (Kond K + 1)) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hK)
    have h4 : (K^2 + 2*K + 1) * P3R 1 = (8/3) * (K^2 + 2*K + 1) := by rw [hP1]; ring
    have h5 : K * ((8/3) * (Kond K + 1)) = (8/3) * (K * Kond K + K) := by ring
    have h6 : (8/3) * S = (8/3) * (K^2 + 2*K + 1) - (8/3) * (K * Kond K + K) := by
      rw [hS]; ring
    linarith only [h1, h3, h4, h5, h6]
  have hD' : 0 ≤ (K^2 + K + 1/2) * P3R x - (2*K^2 + 4*K + 3/2) * P3R 1 + al*c*c2 := by
    rw [hx, hal, hc2]; exact hD
  have key : (K^2 + 1/2) * (P3R x - P3R 1) - 2*K*P3R 1 + al*((1/6)*c2) + al*ε
      = ((K^2 + K + 1/2) * P3R x - (2*K^2 + 4*K + 3/2) * P3R 1 + al*c*c2)
        + ((K^2 + 2*K + 1) * P3R 1 - K * P3R x) + al*(1/6 - c)*c2 + al*ε := by
    rw [hP1]; ring
  have hcore : 0 ≤ (K^2 + 1/2) * (P3R x - P3R 1) - 2*K*P3R 1 + al*((1/6)*c2) + al*ε := by
    rw [key]
    by_cases hcase : 16*K/3 ≤ al * ((1/6)*c2 + ε)
    · have hP3ge : P3R 1 ≤ P3R x := P3R_mono (by norm_num) hx1
      have h1 : 0 ≤ (K^2 + 1/2) * (P3R x - P3R 1) :=
        mul_nonneg (by positivity) (by linarith only [hP3ge])
      have h2 : 2*K*P3R 1 = 16*K/3 := by rw [hP1]; ring
      have h3 : al*((1/6)*c2) + al*ε = al*((1/6)*c2 + ε) := by ring
      linarith only [h1, h2, h3, hcase]
    · push Not at hcase
      have hsmall : al * c2 < 32*K := by
        have h6 : al * c2 ≤ al * (6 * ((1/6)*c2 + ε)) := by
          have h7 : c2 ≤ 6 * ((1/6)*c2 + ε) := by linarith only [hε]
          exact mul_le_mul_of_nonneg_left h7 (le_of_lt halpos)
        linarith only [h6, hcase]
      have hBC : -(al * S * c2 / (12*K)) ≤ al*(1/6 - c)*c2 := by
        have h1 : c - 1/6 ≤ S/(12*K) := by linarith only [hc]
        have h3 : (c - 1/6) * c2 ≤ (S/(12*K)) * c2 :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hc2pos)
        have h4 : (S/(12*K)) * c2 = S * c2 / (12*K) := by ring
        have h3' : (c - 1/6) * c2 ≤ S * c2 / (12*K) := by rw [← h4]; exact h3
        have h5 : al*(1/6 - c)*c2 = -(al * ((c - 1/6) * c2)) := by ring
        have h6 : al * ((c - 1/6) * c2) ≤ al * (S * c2 / (12*K)) :=
          mul_le_mul_of_nonneg_left h3' (le_of_lt halpos)
        have h7 : al * (S * c2 / (12*K)) = al * S * c2 / (12*K) := by ring
        rw [h5]
        linarith only [h6, h7]
      have hSC : 0 ≤ (8/3)*S - al * S * c2 / (12*K) := by
        have h5 : al*c2/(12*K) ≤ (8/3) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 12*K)]
          linarith only [hsmall]
        have h6 : al * S * c2 / (12*K) = S * (al*c2/(12*K)) := by ring
        rw [h6]
        have h7 : S * (al*c2/(12*K)) ≤ S * (8/3) := mul_le_mul_of_nonneg_left h5 hSnn
        linarith only [h7]
      have hEC : 0 ≤ al*ε := mul_nonneg (le_of_lt halpos) (le_of_lt hε)
      linarith only [hD', hA', hBC, hSC, hEC, hD]
  -- transport to the target
  have hlamne : a + lam ≠ 0 := by linarith only [ha, hlam]
  simp only [ineq913, p913, psi13]
  rw [show (a + lam) / (a + lam) = 1 by rw [div_self hlamne]]
  rw [← hal, ← hx, ← hc2]
  exact hcore

/-- **The side condition at the diagonal.**  `cond913 λ λ a K` says
`Kond K/(a+λ)³ + 1/(a+λ)³ ≥ 1/a³`, i.e. `((a+λ)/a)³ ≤ Kond K + 1`. -/
theorem cond913_cube_le {a K lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam)
    (h : cond913 lam lam a K) : ((a + lam)/a)^3 ≤ Kond K + 1 := by
  have hpos : 0 < a + lam := by linarith only [ha, hlam]
  have h3 : 0 < (a + lam)^3 := pow_pos hpos 3
  have ha3 : 0 < a^3 := pow_pos ha 3
  have hsum : (Kond K + 1)/(a+lam)^3 ≥ 1/a^3 := by
    have hh : Kond K/(a+lam)^3 + 1/(a+lam)^3 = (Kond K+1)/(a+lam)^3 := by ring
    rw [← hh]; exact h
  have key : (a+lam)^3 ≤ (Kond K+1) * a^3 := by
    have h2 : (1/a^3) * (a^3 * (a+lam)^3) ≤ ((Kond K+1)/(a+lam)^3) * (a^3*(a+lam)^3) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    have e1 : (1/a^3) * (a^3 * (a+lam)^3) = (a+lam)^3 := by field_simp
    have e2 : ((Kond K+1)/(a+lam)^3) * (a^3*(a+lam)^3) = (Kond K+1)*a^3 := by field_simp
    linarith only [h2, e1, e2]
  rw [div_pow, div_le_iff₀ ha3]
  linarith only [key]

end Work.ZeroFreeTables.Rep9
