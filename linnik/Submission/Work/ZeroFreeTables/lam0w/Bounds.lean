/-
# ZeroFreeTables/lam0w/Bounds — the uniform error bounds of the wide HB Lemma 8.3

* `abs_re_tsum_le`, `summable_parity`, `paritySumBound`: the uniform bound on the parity
  ("trivial zero") sums `∑_n Re (s + par + 2n)^{-k}`, `k = 2, 3`.
* `invSqSum_uniform`: the multiplicity-weighted inverse-square zero sum is `≪ log N`, with a
  constant uniform in the character (this is `P9.zeroSum_invSq_tsum` with the existential
  constant pulled outside the quantifier over `N, χ`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.trivSeriesBound
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive

open Complex DirichletCharacter
open scoped BigOperators
namespace Work.ZeroFreeTables.lam0w

lemma abs_re_tsum_le {f : ℕ → ℂ} (hf : Summable f) :
    |(∑' n, (f n).re)| ≤ ∑' n, ‖f n‖ := by
  rw [show (∑' n, (f n).re) = (∑' n, f n).re from (Complex.re_tsum hf).symm]
  exact le_trans (Complex.abs_re_le_norm _) (norm_tsum_le_tsum_norm hf.norm)

lemma summable_parity (par : ℕ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hseries : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (k + 1)) :=
    (summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ) ^ (k + 1)) 1).mpr
      ((Real.summable_one_div_nat_pow (p := k + 1)).mpr (by omega))
  have hbound : ∀ n : ℕ,
      ‖(1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnorm : (n : ℝ) + 1 ≤ ‖s + ((par + 2 * n : ℕ) : ℂ)‖ := by
      have hre : (s + ((par + 2 * n : ℕ) : ℂ)).re = s.re + ((par + 2 * n : ℕ) : ℝ) := by
        simp [Complex.add_re]
      have hpar : (0 : ℝ) ≤ (par : ℝ) := Nat.cast_nonneg par
      calc (n : ℝ) + 1 ≤ s.re + 2 * (n : ℝ) := by linarith
        _ ≤ s.re + ((par + 2 * n : ℕ) : ℝ) := by push_cast; linarith
        _ = (s + ((par + 2 * n : ℕ) : ℂ)).re := hre.symm
        _ ≤ ‖s + ((par + 2 * n : ℕ) : ℂ)‖ := Complex.re_le_norm _
    have hle : 1 / ‖s + ((par + 2 * n : ℕ) : ℂ)‖ ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hnpos hnorm
    calc ‖(1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)‖
        = ‖1 / (s + ((par + 2 * n : ℕ) : ℂ))‖ ^ (k + 1) := norm_pow _ _
      _ = (1 / ‖s + ((par + 2 * n : ℕ) : ℂ)‖) ^ (k + 1) := by rw [norm_div, norm_one]
      _ ≤ (1 / ((n : ℝ) + 1)) ^ (k + 1) := pow_le_pow_left₀ (by positivity) hle (k + 1)
      _ = 1 / ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
            rw [div_pow, one_pow, Nat.cast_add, Nat.cast_one]
  exact Summable.of_norm_bounded hseries hbound

theorem paritySumBound : ∃ Ct : ℝ, 0 < Ct ∧ ∀ (par : ℕ), par ≤ 1 → ∀ s : ℂ, 1 < s.re →
    |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ)))^2)).re| ≤ Ct ∧
    |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ)))^3)).re| ≤ Ct := by
  obtain ⟨Ct, hCt0, hCt⟩ := Work.ZeroFreeTables.P9.trivSeriesBound
  refine ⟨Ct, hCt0, fun par hpar s hs => ?_⟩
  have hs12 : (1:ℝ)/2 ≤ s.re := by linarith
  obtain ⟨hb2, hb3⟩ := hCt s hs12 par hpar
  refine ⟨?_, ?_⟩
  · exact le_trans (abs_re_tsum_le (by simpa using summable_parity par hs 1 (by norm_num))) hb2
  · exact le_trans (abs_re_tsum_le (by simpa using summable_parity par hs 2 (by norm_num))) hb3

/-- The multiplicity-weighted inverse-square zero sum, with a constant uniform in `N` and `χ`. -/
theorem invSqSum_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
      (s : ℂ),
      Work.ZeroFreeTables.P9.invSqSum N χ s
        ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count hcpos.le
  refine ⟨C, hCpos, ?_⟩
  intro N _ χ hχ hprim s
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg hN1
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfin : ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2))
        ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := by
    intro S
    refine hC (DirichletCharacter.completedLFunction χ) hΛan (Real.log (N : ℝ)) hlogN ?_ s S
    intro a ρ hρ
    exact hc χ hχ hprim a ρ hρ
  have hcongr : Work.ZeroFreeTables.P9.invSqSum N χ s
      = ∑' u : ℂ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2)) := by
    unfold Work.ZeroFreeTables.P9.invSqSum
    exact tsum_congr (fun u => by
      rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u])
  rw [hcongr]
  have hnn : ∀ u : ℂ, (0 : ℝ) ≤
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    have h1 : (0 : ℝ) ≤ 1 / (1 + ‖s - u‖ ^ 2) := by positivity
    positivity
  have hsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2))) := summable_of_sum_le hnn hfin
  calc (∑' u : ℂ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := hsumm.tsum_le_of_sum_le hfin
    _ = C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by ring

end Work.ZeroFreeTables.lam0w
