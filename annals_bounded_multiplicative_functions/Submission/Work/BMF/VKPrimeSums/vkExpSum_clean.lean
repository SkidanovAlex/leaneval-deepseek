import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.VKExpSum.weyl_small_lambda
import Submission.Work.BMF.VKF.deep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A clean instance of the Vinogradov–Korobov exponential-sum bound

`Work.BMF.VKExpSum C D` (the exponential-sum bound of Ford's Theorem 2) is assembled here from the
two *proved* halves of the deep route:

* `Work.BMF.VKExpSum.weyl_small_lambda` — the bounded range `log t ≤ (13/5) log N`;
* `Work.BMF.VKF.vkf_deep` — the deep range `(13/5) log N ≤ log t` together with `dK0 λ² ≤ log N`;

and the trivial range `log N ≤ dK0 λ²`, where the crude bound `‖Ssum N u t R‖ ≤ 2N` suffices.
-/

namespace Work.BMF.VKPrimeSums

open Finset

noncomputable section

/-- `Ssum` is the exponential sum of `Work.BMF.VKExpSum` (definitionally). -/
theorem vkExpSum_clean : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ Work.BMF.VKExpSum C D := by
  obtain ⟨Cw, Dw, hCw, hDw, hW⟩ := Work.BMF.VKExpSum.weyl_small_lambda
  have hDdpos : 0 < Work.BMF.VKF.dD := by
    unfold Work.BMF.VKF.dD; norm_num
  have hCdpos : 0 < Work.BMF.VKF.dC := by
    unfold Work.BMF.VKF.dC; exact Real.exp_pos _
  set D : ℝ := max Dw Work.BMF.VKF.dD with hDdef
  set C : ℝ := max (max Cw (3 * Work.BMF.VKF.dC))
      (3 * Real.exp (Work.BMF.VKF.dK0 / D)) with hCdef
  have hDpos : 0 < D := by rw [hDdef]; exact lt_max_of_lt_left hDw
  have hDwD : Dw ≤ D := by rw [hDdef]; exact le_max_left _ _
  have hDdD : Work.BMF.VKF.dD ≤ D := by rw [hDdef]; exact le_max_right _ _
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_max_iff.mpr (Or.inl (lt_max_iff.mpr (Or.inl hCw)))
  have hCwC : Cw ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCdC : 3 * Work.BMF.VKF.dC ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCtriv : 3 * Real.exp (Work.BMF.VKF.dK0 / D) ≤ C := by
    rw [hCdef]; exact le_max_right _ _
  refine ⟨C, D, hCpos, hDpos, ?_⟩
  intro N t hN2 hNt u hu0 hu1 R hR hR2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hlam2 : (0 : ℝ) < (Real.log t / Real.log N) ^ 2 := by positivity
  -- monotonicity in the constant of the saving
  have hmono : ∀ E : ℝ, 0 < E → E ≤ D →
      N ^ (1 - 1 / (E * (Real.log t / Real.log N) ^ 2))
        ≤ N ^ (1 - 1 / (D * (Real.log t / Real.log N) ^ 2)) := by
    intro E hE hED
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have h1 : 1 / (D * (Real.log t / Real.log N) ^ 2)
        ≤ 1 / (E * (Real.log t / Real.log N) ^ 2) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right hED hlam2.le)
    linarith
  change ‖Work.BMF.Ssum N u t R‖ ≤ C * N ^ (1 - 1 / (D * (Real.log t / Real.log N) ^ 2))
  by_cases hsmall : Real.log t ≤ (13 / 5 : ℝ) * Real.log N
  · refine le_trans (hW N t u R hN2 hNt hsmall hu0 hu1 hR hR2) ?_
    exact mul_le_mul hCwC (hmono Dw hDw hDwD) (by positivity) (by positivity)
  · have hlarge : (13 / 5 : ℝ) * Real.log N ≤ Real.log t := le_of_lt (lt_of_not_ge hsmall)
    by_cases hdeep : Work.BMF.VKF.dK0 * (Real.log t / Real.log N) ^ 2 ≤ Real.log N
    · refine le_trans (Work.BMF.VKF.vkf_deep N t u R hN2 hNt hlarge hdeep hu0 hu1 hR hR2) ?_
      exact mul_le_mul hCdC (hmono Work.BMF.VKF.dD hDdpos hDdD) (by positivity) (by positivity)
    · push_neg at hdeep
      -- the trivial range: the crude bound `‖Ssum‖ ≤ 2N`
      have hterm : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
          ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
        intro n _hn
        have hx : (0 : ℝ) < (n : ℝ) + u := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp
      have hcard : ‖Work.BMF.Ssum N u t R‖ ≤ 3 * N := by
        rw [Work.BMF.Ssum]
        calc ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
              ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
            ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
                ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
          _ = ((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℝ) := by
              rw [Finset.sum_congr rfl hterm]
              simp
          _ ≤ 3 * N := by
              have hsub : Finset.Ioc ⌊N⌋₊ ⌊R⌋₊ ⊆ Finset.range (⌊R⌋₊ + 1) := by
                intro x hx
                rw [Finset.mem_range]
                exact Nat.lt_succ_of_le (Finset.mem_Ioc.mp hx).2
              have h1 : (Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card ≤ ⌊R⌋₊ + 1 := by
                calc (Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card ≤ (Finset.range (⌊R⌋₊ + 1)).card :=
                      Finset.card_le_card hsub
                  _ = ⌊R⌋₊ + 1 := Finset.card_range _
              have h2 : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le (by linarith)
              have h3 : ((⌊R⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * N := by
                have h4 : ((⌊R⌋₊ + 1 : ℕ) : ℝ) = ((⌊R⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
                rw [h4]; linarith
              have h5 : ((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℝ) ≤ ((⌊R⌋₊ + 1 : ℕ) : ℝ) := by
                exact_mod_cast h1
              linarith
      -- `2 N ≤ C N^{1-a}` with `a = 1/(D λ²)`
      set a : ℝ := 1 / (D * (Real.log t / Real.log N) ^ 2) with hadef
      have hapos : 0 < a := by rw [hadef]; positivity
      have hNa : N ^ a ≤ Real.exp (Work.BMF.VKF.dK0 / D) := by
        rw [Real.rpow_def_of_pos hNpos a, hadef]
        apply Real.exp_le_exp.mpr
        have hstep : (1 / (D * (Real.log t / Real.log N) ^ 2)) * Real.log N
            ≤ (1 / (D * (Real.log t / Real.log N) ^ 2)) *
                (Work.BMF.VKF.dK0 * (Real.log t / Real.log N) ^ 2) :=
          mul_le_mul_of_nonneg_left hdeep.le (by positivity)
        have heq : (1 / (D * (Real.log t / Real.log N) ^ 2)) *
              (Work.BMF.VKF.dK0 * (Real.log t / Real.log N) ^ 2) = Work.BMF.VKF.dK0 / D := by
          have hne : (Real.log t / Real.log N) ^ 2 ≠ 0 := ne_of_gt hlam2
          have hDne : D ≠ 0 := ne_of_gt hDpos
          have hltne : Real.log t ≠ 0 := ne_of_gt hlogt
          field_simp
        linarith [hstep, heq]
      have hscale : 3 * N ≤ 3 * (N ^ (1 - a) * N ^ a) := by
        have h : N = N ^ (1 - a) * N ^ a := by
          rw [← Real.rpow_add hNpos]
          norm_num
        linarith [h]
      have hfin : 3 * (N ^ (1 - a) * N ^ a) ≤ C * N ^ (1 - a) := by
        have h5 : 3 * N ^ a ≤ C :=
          le_trans (mul_le_mul_of_nonneg_left hNa (by norm_num)) hCtriv
        have h6 : 0 ≤ N ^ (1 - a) := (Real.rpow_pos_of_pos hNpos _).le
        calc 3 * (N ^ (1 - a) * N ^ a) = (3 * N ^ a) * N ^ (1 - a) := by ring
          _ ≤ C * N ^ (1 - a) := mul_le_mul_of_nonneg_right h5 h6
      linarith [hcard, hscale, hfin]

end

end Work.BMF.VKPrimeSums
