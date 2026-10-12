import Mathlib.Algebra.Order.Star.Real
import Submission.Work.MGroupInput.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- **FS's choice of the two-arm split, with a general window constant.**
For `μ > 0`, `β > 0` with `1 ≤ μβ`, every `Cn ≥ 2` and every `n : ℕ` there are
`m, n', n'' ∈ ℕ` with `n = m n' + n''`, `n'' < n'`, the window
`Cn μβ ≤ n' ≤ (Cn+1) μβ`, `n'' < (Cn+1) μβ`, and the density-level two-arm
inequality

  `(1/18)(n/β − μ)²/(1 + n/(βμ)) ≤ (1/4)(n''/β − μ)² + (1/18)μ(n − n'')/β`.

The split is `n' := ⌈Cn μβ⌉`, and for `n ≥ n'` one takes the Euclidean
division `n = (n / n')·n' + n % n'`; for `n < n'` one takes `m := 0`,
`n'' := n` and the boundary branch `sharp_branch_gain`. -/
theorem exists_two_arm_split_gen {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) (hμβ : 1 ≤ μ * β)
    {Cn : ℝ} (hCn : 2 ≤ Cn) (n : ℕ) :
    ∃ m n' n'', n = m * n' + n'' ∧ n'' < n' ∧
      Cn * μ * β ≤ (n' : ℝ) ∧ (n' : ℝ) ≤ (Cn + 1) * μ * β ∧
      (n'' : ℝ) < (Cn + 1) * μ * β ∧
      1 / 18 * (((n : ℝ) / β - μ) ^ 2 / (1 + (n : ℝ) / β / μ)) ≤
        1 / 4 * ((n'' : ℝ) / β - μ) ^ 2 + 1 / 18 * μ * (((n : ℝ) - (n'' : ℝ)) / β) := by
  have hApos : 0 < Cn * μ * β := by nlinarith [hCn, hμ, hβ]
  set N : ℕ := Nat.ceil (Cn * μ * β) with hNdef
  have hNge : Cn * μ * β ≤ (N : ℝ) := Nat.le_ceil _
  have hNpos : 0 < N := by
    have h : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hApos hNge
    exact_mod_cast h
  have hNup : (N : ℝ) ≤ (Cn + 1) * μ * β := by
    have h1 : (N : ℝ) < Cn * μ * β + 1 := Nat.ceil_lt_add_one (le_of_lt hApos)
    nlinarith [hμβ, h1]
  by_cases hn : n < N
  · -- boundary branch `m = 0`, `n'' = n`
    refine ⟨0, N, n, by simp, hn, hNge, hNup, ?_, ?_⟩
    · have hcast : (n : ℝ) < (N : ℝ) := by exact_mod_cast hn
      linarith
    · have ht0 : 0 ≤ (n : ℝ) / β := by positivity
      have h := Submission.BoseGases.sharp_branch_gain (μ := μ) (t := (n : ℝ) / β) hμ ht0
      simpa using h
  · -- interior branch: Euclidean division `n = (n / N)·N + n % N`
    have hNle : N ≤ n := le_of_not_gt hn
    refine ⟨n / N, N, n % N, ?_, Nat.mod_lt _ hNpos, hNge, hNup, ?_, ?_⟩
    · rw [mul_comm]
      exact (Nat.div_add_mod n N).symm
    · have hcast : ((n % N : ℕ) : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.mod_lt n hNpos
      linarith
    · rw [show ((n : ℝ) - (((n % N : ℕ)) : ℝ)) / β
            = (n : ℝ) / β - (((n % N : ℕ)) : ℝ) / β by ring]
      have hdiv1 : 1 ≤ n / N := (Nat.one_le_div_iff hNpos).mpr hNle
      have h2A : 2 * μ * β ≤ (N : ℝ) := by
        have h2 : 2 * μ * β ≤ Cn * μ * β := by
          nlinarith [mul_le_mul_of_nonneg_right hCn (le_of_lt hApos), hApos]
        exact le_trans h2 hNge
      have hNge2 : 2 * μ ≤ (N : ℝ) / β := by
        rw [le_div_iff₀ hβ]
        exact h2A
      have hcast : ((n : ℝ) - ((n % N : ℕ) : ℝ)) = ((n / N : ℕ) : ℝ) * (N : ℝ) := by
        have hnn : n - n % N = n / N * N := by
          have h := Nat.sub_eq_of_eq_add (Nat.div_add_mod n N).symm
          rwa [mul_comm] at h
        rw [← Nat.cast_sub (Nat.mod_le n N), hnn]
        push_cast
        ring
      have hs : 2 * μ ≤ (n : ℝ) / β - ((n % N : ℕ) : ℝ) / β := by
        have hs0 : 2 * μ ≤ ((n : ℝ) - ((n % N : ℕ) : ℝ)) / β := by
          rw [hcast]
          have h1 : (1 : ℝ) ≤ ((n / N : ℕ) : ℝ) := by exact_mod_cast hdiv1
          have h2 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
          calc 2 * μ ≤ (N : ℝ) / β := hNge2
            _ = 1 * ((N : ℝ) / β) := by ring
            _ ≤ ((n / N : ℕ) : ℝ) * ((N : ℝ) / β) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = ((n / N : ℕ) : ℝ) * (N : ℝ) / β := by ring
        rwa [show ((n : ℝ) - ((n % N : ℕ) : ℝ)) / β
              = (n : ℝ) / β - (((n % N : ℕ)) : ℝ) / β by ring] at hs0
      have ha0 : 0 ≤ ((n % N : ℕ) : ℝ) / β := by positivity
      have hat : ((n % N : ℕ) : ℝ) / β ≤ (n : ℝ) / β := by
        have h1 : ((n % N : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.mod_le n N
        exact div_le_div_of_nonneg_right h1 (le_of_lt hβ)
      exact Submission.BoseGases.two_arm_gain (μ := μ) (t := (n : ℝ) / β)
        (a := ((n % N : ℕ) : ℝ) / β) hμ ha0 hat hs

end Work.MGroupInput
