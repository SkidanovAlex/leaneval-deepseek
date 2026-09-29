import Mathlib

namespace Work.TMC16Core.Assembly

/-- Final decay patch: under the arithmetic hypotheses coming from the
Avila–Jitomirskaya (`Ten Martini`) argument — `γ = 7L/10`, `1 ≤ g`,
`dZ ≤ 40 g`, `n ≤ dZ/g + 1`, `dZ ≤ n·g`, and `d - z + 1 ≤ dZ` with
`z ≤ qn/20 + 5`, `qn ≤ 5 d` — the exponential weight
`M · 2^n · exp(-γ · min(dZ - n, n·g))` is dominated by `exp(-(L/2) d)`.

The hypotheses `hz`, `hd5` together with `hdz` give `dZ ≥ 3d/4 - 4`, while
`hn1`, `h40` give `n ≤ 41`; then `γ · min(dZ - n, n g) ≥ γ (3d/4 - 4 - n)`,
and the exponent of the left-hand side is at most
`Ld/40 - 46γ - 41 log 2 + n log 2 - γ(3d/4 - 4 - n)`
`= -Ld/2 + γ(n-42) + (n-41) log 2 ≤ -Ld/2`. -/
theorem decay_patch_final {γ L M dZ d z qn g : ℝ} {n : ℕ}
    (hL : 0 < L) (hγ : γ = 7 * L / 10) (hM0 : 0 ≤ M) (hg : 1 ≤ g) (h40 : dZ ≤ 40 * g)
    (hn1 : (n : ℝ) ≤ dZ / g + 1) (hn2 : dZ ≤ (n : ℝ) * g)
    (hdz : d - z + 1 ≤ dZ) (hz : z ≤ qn / 20 + 5) (hd5 : qn ≤ 5 * d)
    (habs : M * Real.exp (5 * γ + 41 * (γ + Real.log 2)) ≤ Real.exp (L / 40 * d)) :
    M * (2 : ℝ) ^ n * Real.exp (-(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))
      ≤ Real.exp (-(L / 2) * d) := by
  have _ : (0 : ℝ) ≤ M := hM0
  have hγpos : 0 < γ := by rw [hγ]; linarith
  have hγnn : 0 ≤ γ := le_of_lt hγpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgpos : 0 < g := by linarith
  -- `n ≤ 41`
  have hn41 : (n : ℝ) ≤ 41 := by
    have h1 : dZ / g ≤ 40 := by rw [div_le_iff₀ hgpos]; linarith
    linarith
  -- `dZ ≥ 3d/4 - 4`
  have hdm : 3 * d / 4 - 4 ≤ dZ := by
    have h2 : qn / 20 ≤ d / 4 := by linarith
    linarith
  -- `3d/4 - 4 - n ≤ min (dZ - n) (n g)`
  have hmin : 3 * d / 4 - 4 - (n : ℝ) ≤ min (dZ - (n : ℝ)) ((n : ℝ) * g) := by
    apply le_min
    · linarith
    · have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  have hγm : γ * (3 * d / 4 - 4 - (n : ℝ)) ≤ γ * min (dZ - (n : ℝ)) ((n : ℝ) * g) :=
    mul_le_mul_of_nonneg_left hmin hγnn
  -- logarithmic bound on `M`
  have hMbound : M ≤ Real.exp (L / 40 * d - (5 * γ + 41 * (γ + Real.log 2))) := by
    have hpos : 0 < Real.exp (5 * γ + 41 * (γ + Real.log 2)) := Real.exp_pos _
    rw [Real.exp_sub]
    exact (le_div_iff₀ hpos).mpr habs
  -- rewrite `2 ^ n` as `exp (n log 2)`
  have hX : M * (2 : ℝ) ^ n * Real.exp (-(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))
      = M * Real.exp ((n : ℝ) * Real.log 2 + -(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) := by
    conv_lhs => rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul]
    rw [mul_assoc, ← Real.exp_add]
  rw [hX]
  have hstep : M * Real.exp ((n : ℝ) * Real.log 2
        + -(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))
      ≤ Real.exp (L / 40 * d - (5 * γ + 41 * (γ + Real.log 2)))
        * Real.exp ((n : ℝ) * Real.log 2
        + -(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) :=
    mul_le_mul_of_nonneg_right hMbound (Real.exp_pos _).le
  refine le_trans hstep ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hγm, hγ, hL, hn41, hlog2]

end Work.TMC16Core.Assembly
