import Mathlib
import Submission.Work.TMC16Core.Assembly.decay_patch_final

namespace Work.TMC16Core.Assembly

/-- Final resonance arithmetic (`TMC16`): given `γ ≥ 7L/10`, `Q ≥ 300`,
`Q ≤ 5d`, `1 ≤ g`, `dZ ≤ 40 g` and the ceiling hypotheses together with the
`dZ` lower bound `d - ((Q-1)/20 + 4) ≤ dZ`, there is an integer `n` with
`n ≤ dZ/g + 1`, `dZ ≤ n g`, and the exponential weight
`C (1+3Q) · 2^n · exp(-γ · min(dZ - n, n g))` is at most `exp(-(L/2) d)`.

The witness is `n = ⌈dZ/g⌉`.  From `Q ≤ 5d` and `Q ≥ 300` we get `d ≥ 60`,
hence `dZ ≥ 3d/4 - 4`; and `h40` with `n ≤ dZ/g + 1 ≤ 41` gives `n ≤ 41`.
Since `dZ ≤ n g` we also have `min (dZ - n) (n g) = dZ - n ≥ 3d/4 - 4 - n ≥ 0`,
so replacing `γ` by `γ₀ = 7L/10` in the exponent only decreases it.  Finally
`habs` bounds `M := C(1+3Q) ≤ exp(Ld/40 - (5γ₀ + 41(γ₀ + log 2)))`, and the
resulting exponent `Ld/40 - 46γ₀ - 41 log 2 + n log 2 - γ₀ min` is at most
`-Ld/2 + γ₀(n-42) + (n-41) log 2 ≤ -Ld/2`. -/
theorem res_final_arith {γ L C : ℝ} {Q : ℕ} {d : ℕ} {dZ g : ℝ}
    (hL : 0 < L) (hγ7 : 7 * L / 10 ≤ γ) (hC : 0 ≤ C) (hQ : 300 ≤ Q)
    (hd5 : (Q : ℝ) ≤ 5 * (d : ℝ))
    (hdZ0 : 0 ≤ dZ) (hg1 : 1 ≤ g) (h40 : dZ ≤ 40 * g)
    (hdz : (d : ℝ) - ((((Q - 1 : ℕ) : ℝ)) / 20 + 4) ≤ dZ)
    (habs : C * (1 + 3 * (Q : ℝ)) * Real.exp (5 * (7 * L / 10) + 41 * (7 * L / 10 + Real.log 2))
      ≤ Real.exp (L / 40 * (d : ℝ))) :
    ∃ n : ℕ, ((n : ℝ) ≤ dZ / g + 1 ∧ dZ ≤ (n : ℝ) * g) ∧
      C * (1 + 3 * (Q : ℝ)) * (2 : ℝ) ^ n *
        Real.exp (-(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) ≤ Real.exp (-(L / 2) * (d : ℝ)) := by
  have hgpos : 0 < g := by linarith
  -- `d ≥ 60` from `Q ≥ 300` and `Q ≤ 5d`
  have hd60 : (60 : ℝ) ≤ (d : ℝ) := by
    have h : (300 : ℝ) ≤ 5 * (d : ℝ) := le_trans (by exact_mod_cast hQ) hd5
    linarith
  set γ₀ : ℝ := 7 * L / 10 with hγ₀_def
  have hγ₀nn : 0 ≤ γ₀ := by rw [hγ₀_def]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set M : ℝ := C * (1 + 3 * (Q : ℝ)) with hM_def
  have hM0 : 0 ≤ M := by
    rw [hM_def]
    exact mul_nonneg hC (by positivity)
  -- the witness: `n = ⌈dZ / g⌉`
  set n : ℕ := ⌈dZ / g⌉₊ with hn_def
  have hcel : dZ / g ≤ (n : ℝ) := by rw [hn_def]; exact Nat.le_ceil _
  have hlt : (n : ℝ) < dZ / g + 1 := by
    rw [hn_def]; exact Nat.ceil_lt_add_one (div_nonneg hdZ0 hgpos.le)
  have hn1 : (n : ℝ) ≤ dZ / g + 1 := le_of_lt hlt
  have hn2 : dZ ≤ (n : ℝ) * g := (div_le_iff₀ hgpos).mp hcel
  have hdg40 : dZ / g ≤ 40 := by rw [div_le_iff₀ hgpos]; linarith
  have hn41 : (n : ℝ) ≤ 41 := by linarith
  -- `dZ ≥ 3d/4 - 4`
  have hQ20 : (((Q - 1 : ℕ) : ℝ)) / 20 ≤ (d : ℝ) / 4 := by
    have h1 : (((Q - 1 : ℕ) : ℝ)) ≤ (Q : ℝ) := Nat.cast_le.mpr (Nat.sub_le Q 1)
    linarith [hd5]
  have hdm : 3 * (d : ℝ) / 4 - 4 ≤ dZ := by linarith [hdz, hQ20]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- `min (dZ - n) (n g) = dZ - n`
  have hmin_eq : min (dZ - (n : ℝ)) ((n : ℝ) * g) = dZ - (n : ℝ) := by
    apply le_antisymm (min_le_left _ _)
    apply le_min le_rfl
    linarith [hn2, hnn]
  have hmin0 : 0 ≤ min (dZ - (n : ℝ)) ((n : ℝ) * g) := by
    rw [hmin_eq]; linarith [hdm, hn41, hd60]
  have hmin_lb : 3 * (d : ℝ) / 4 - 4 - (n : ℝ) ≤ min (dZ - (n : ℝ)) ((n : ℝ) * g) := by
    rw [hmin_eq]; linarith [hdm]
  -- exponential bound on `M` coming from `habs`
  have hMbound : M ≤ Real.exp (L / 40 * (d : ℝ) - (5 * γ₀ + 41 * (γ₀ + Real.log 2))) := by
    have hpos : 0 < Real.exp (5 * γ₀ + 41 * (γ₀ + Real.log 2)) := Real.exp_pos _
    rw [Real.exp_sub]
    exact (le_div_iff₀ hpos).mpr habs
  refine ⟨n, ⟨hn1, hn2⟩, ?_⟩
  -- rewrite `2^n` as `exp (n log 2)`
  have hX : M * (2 : ℝ) ^ n * Real.exp (-(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))
      = M * Real.exp ((n : ℝ) * Real.log 2 + -(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) := by
    conv_lhs => rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul]
    rw [mul_assoc, ← Real.exp_add]
  have hγm := mul_le_mul_of_nonneg_left hmin_lb hγ₀nn
  -- replace `γ` by `γ₀` in the exponential weight (using `min ≥ 0`)
  have hExpB : Real.exp ((n : ℝ) * Real.log 2 + -(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))
      ≤ Real.exp ((n : ℝ) * Real.log 2 + -(γ₀ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) := by
    apply Real.exp_le_exp.mpr
    have : γ₀ * min (dZ - (n : ℝ)) ((n : ℝ) * g) ≤ γ * min (dZ - (n : ℝ)) ((n : ℝ) * g) :=
      mul_le_mul_of_nonneg_right hγ7 hmin0
    linarith
  calc M * (2 : ℝ) ^ n * Real.exp (-(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))
      = M * Real.exp ((n : ℝ) * Real.log 2 + -(γ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) := hX
    _ ≤ Real.exp (L / 40 * (d : ℝ) - (5 * γ₀ + 41 * (γ₀ + Real.log 2)))
          * Real.exp ((n : ℝ) * Real.log 2 + -(γ₀ * min (dZ - (n : ℝ)) ((n : ℝ) * g))) :=
        mul_le_mul hMbound hExpB (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (L / 40 * (d : ℝ) - (5 * γ₀ + 41 * (γ₀ + Real.log 2))
          + ((n : ℝ) * Real.log 2 + -(γ₀ * min (dZ - (n : ℝ)) ((n : ℝ) * g)))) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(L / 2) * (d : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hγm, hγ₀_def, hn41, hlog2, hL]

end Work.TMC16Core.Assembly
