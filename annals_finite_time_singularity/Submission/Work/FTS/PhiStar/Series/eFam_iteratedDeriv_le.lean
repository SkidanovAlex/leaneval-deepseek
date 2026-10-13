/-
# `Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le`

Polynomial-in-`j` bounds for the iterated angular derivatives of the Dirichlet eigenfunctions
`eFam j θ = cos θ · gC (2j+1) (sin θ)` of `Lzero` on the *closed* interval `Iθ = [0, π/2]`.

**Statement.** For every derivative order `m` there is `C > 0` with
`|∂_θ^m (eFam j) θ| ≤ C · (j+1)^(4m+4)` for every `j` and every `θ ∈ Iθ`.

**Route.**  The trigonometric form of the Gegenbauer polynomial
(`FamLopAux.TrigGegen`, in the angle `ψ = π/2 - θ`, where `sin θ = cos ψ`)

    `gC n (cos ψ) = famTrig n ψ = Σ_{k ≤ n} famC k · famC (n-k) · cos ((2k-n) ψ)`,
      `famC k = (3/2)_k / k! ≥ 0`

turns `eFam j` into a finite sum of pure affine cosines,
`eFam j θ = cos θ · Σ_{k ≤ 2j+1} famC k famC (2j+1-k) cos ((2k-(2j+1))(π/2-θ))`.
Each summand is differentiated explicitly by `iteratedDeriv_cos_affine`
(`∂^l (cos (a·+c)) = a^l · cos (a· + c + l·π/2)`, hence bounded by `|a|^l` in absolute value),
the coefficients are nonnegative and sum to `famTrig n 0 = gC n 1 = (n+1)(n+2)/2`
(`gCAtOne`), and the Leibniz rule `iteratedDeriv_mul` for the outer factor `cos θ` (all of
whose iterated derivatives are bounded by `1`) gives the bound; finally `n = 2j+1` turns
`(n+1)^{m+2}` into `2^{m+2}(j+1)^{m+2}` and `m + 2 ≤ 4m + 4` closes the estimate.
-/
import Mathlib
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.FamLopAux.Defs
import Submission.Work.FTS.PhiStar.FamLopAux.TrigGegen
import Submission.Work.FTS.PhiStar.Series.Deleg.gCAtOne
import Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Trig

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Finset

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- Every iterated derivative of `Real.cos` is bounded by `1` in absolute value. -/
lemma abs_iteratedDeriv_cos_le_one (l : ℕ) (θ : ℝ) : |iteratedDeriv l Real.cos θ| ≤ 1 := by
  have h := congrFun (Work.FTS.PhiStar.FlatWAux.iteratedDeriv_cos_affine 1 0 l) θ
  have hfun : (fun θ : ℝ => Real.cos (1 * θ + 0)) = Real.cos := by funext x; simp
  rw [hfun] at h
  rw [h]
  simpa using Work.FTS.PhiStar.FlatWAux.abs_cos_le_one' (1 * θ + 0 + (l : ℝ) * (Real.pi / 2))

/-- **Derivative bound for the trigonometric Gegenbauer sum.**  For every `l`, `n` and `θ`, the
`l`-th derivative of `θ ↦ famTrig n (π/2 - θ)` is bounded by the total coefficient mass
`(n+1)(n+2)/2 = famTrig n 0` of `famTrig n`, times `(n+1)^l`. -/
lemma abs_iteratedDeriv_famTrig_sub (l n : ℕ) (θ : ℝ) :
    |iteratedDeriv l (fun θ : ℝ => Work.FTS.PhiStar.famTrig n (Real.pi / 2 - θ)) θ|
      ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) + 1) / 2) * ((n : ℝ) + 1) ^ l := by
  have hfun : (fun θ : ℝ => Work.FTS.PhiStar.famTrig n (Real.pi / 2 - θ))
      = fun θ : ℝ => ∑ k ∈ Finset.range (n + 1),
          (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
              * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
            * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
                + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)) := by
    funext θ'
    rw [Work.FTS.PhiStar.famTrig]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring_nf
  have hterm : ∀ k ∈ Finset.range (n + 1),
      |iteratedDeriv l (fun θ : ℝ => (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ|
        ≤ (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ))) * ((n : ℝ) + 1) ^ l := by
    intro k hk
    rw [iteratedDeriv_const_mul_field]
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Work.FTS.PhiStar.FlatWAux.famC_nonneg _)
      (Work.FTS.PhiStar.FlatWAux.famC_nonneg _))]
    have hcos : iteratedDeriv l (fun θ : ℝ => Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
            + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ
        = (-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) ^ l
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)
              + (l : ℝ) * (Real.pi / 2)) :=
      congrFun (Work.FTS.PhiStar.FlatWAux.iteratedDeriv_cos_affine
        (-(2 * ((k : ℕ) : ℝ) - (n : ℝ)))
        ((2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)) l) θ
    rw [hcos, abs_mul, abs_pow, abs_neg]
    have hk' : ((k : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have hknn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
    have hbk : |2 * ((k : ℕ) : ℝ) - (n : ℝ)| ≤ (n : ℝ) + 1 :=
      abs_le.mpr ⟨by linarith, by linarith [hk']⟩
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Work.FTS.PhiStar.FlatWAux.famC_nonneg _)
      (Work.FTS.PhiStar.FlatWAux.famC_nonneg _))
    calc |2 * ((k : ℕ) : ℝ) - (n : ℝ)| ^ l
          * |Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)
              + (l : ℝ) * (Real.pi / 2))|
        ≤ ((n : ℝ) + 1) ^ l * 1 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hbk l)
          (Work.FTS.PhiStar.FlatWAux.abs_cos_le_one' _) (abs_nonneg _) (by positivity)
      _ = ((n : ℝ) + 1) ^ l := mul_one _
  have hsum : (∑ k ∈ Finset.range (n + 1),
      Work.FTS.PhiStar.famC ((k : ℕ) : ℤ) * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
      = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
    have h1 : Work.FTS.PhiStar.famTrig n 0 = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
      have h := Work.FTS.PhiStar.FamLopAux.TrigGegen n 0
      rw [Real.cos_zero] at h
      rw [← h, Work.FTS.PhiStar.Series.Deleg.gCAtOne n]
    rw [← h1, Work.FTS.PhiStar.famTrig]
    apply Finset.sum_congr rfl
    intro k hk
    simp
  rw [hfun, iteratedDeriv_fun_sum (I := Finset.range (n + 1)) (x := θ)
    (by intro k hk; fun_prop)]
  calc |∑ k ∈ Finset.range (n + 1),
          iteratedDeriv l (fun θ : ℝ => (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ|
      ≤ ∑ k ∈ Finset.range (n + 1),
          |iteratedDeriv l (fun θ : ℝ => (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
          * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ))) * ((n : ℝ) + 1) ^ l :=
        Finset.sum_le_sum hterm
    _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) + 1) / 2) * ((n : ℝ) + 1) ^ l := by
        rw [← Finset.sum_mul, hsum]
        ring

/-- The bound of `eFam_iteratedDeriv_le` in the family index `n = 2j+1`: the analysis of
`abs_iteratedDeriv_famTrig_sub` plus the Leibniz rule in `cos θ` shows

    `|∂_θ^m (eFam j) θ| ≤ 2^m · (n+1)^{m+2}`,   `n = 2j+1`. -/
lemma eFam_iteratedDeriv_le_base (m j : ℕ) (θ : ℝ) :
    |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
      ≤ (2 : ℝ) ^ m * ((((2 * j + 1 : ℕ) : ℝ)) + 1) ^ (m + 2) := by
  have he : Work.FTS.PhiStar.Gegenbauer.eFam j
      = Real.cos * (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) := by
    funext θ'
    simp only [Pi.mul_apply]
    rw [Work.FTS.PhiStar.Gegenbauer.eFam, ← Real.cos_pi_div_two_sub θ',
      Work.FTS.PhiStar.FamLopAux.TrigGegen]
  have hG : ContDiffAt ℝ (m : ℕ∞)
      (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ := by
    rw [show (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ))
        = fun θ : ℝ => ∑ k ∈ Finset.range (2 * j + 1 + 1),
            (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
                * Work.FTS.PhiStar.famC (((2 * j + 1 : ℕ) : ℤ) - ((k : ℕ) : ℤ)))
              * Real.cos ((-(2 * ((k : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ))) * θ
                  + (2 * ((k : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) * (Real.pi / 2)) from ?_]
    · fun_prop
    · funext θ'
      rw [Work.FTS.PhiStar.famTrig]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring_nf
  rw [he, iteratedDeriv_mul (Real.contDiff_cos (n := (m : ℕ∞))).contDiffAt hG]
  set N : ℝ := ((2 * j + 1 : ℕ) : ℝ) + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN]
    have hcast : ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * ((j : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hFnn : (0 : ℝ) ≤ N * (N + 1) / 2 := by nlinarith [hN0]
  have hgoal : |∑ i ∈ Finset.range (m + 1), ↑(m.choose i) * iteratedDeriv i Real.cos θ
        * iteratedDeriv (m - i)
            (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ|
      ≤ (2 : ℝ) ^ m * (N * (N + 1) / 2 * N ^ m) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have step1 : ∑ i ∈ Finset.range (m + 1), |↑(m.choose i) * iteratedDeriv i Real.cos θ
          * iteratedDeriv (m - i)
              (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ|
        ≤ ∑ i ∈ Finset.range (m + 1),
            ↑(m.choose i) * (N * (N + 1) / 2 * N ^ (m - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
      have h1 := abs_iteratedDeriv_cos_le_one i θ
      have h2 := abs_iteratedDeriv_famTrig_sub (m - i) (2 * j + 1) θ
      calc ↑(m.choose i) * |iteratedDeriv i Real.cos θ|
            * |iteratedDeriv (m - i)
                (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ|
          ≤ ↑(m.choose i) * 1 * (N * (N + 1) / 2 * N ^ (m - i)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (m.choose i))) h2
              (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg (m.choose i)) zero_le_one)
        _ = ↑(m.choose i) * (N * (N + 1) / 2 * N ^ (m - i)) := by ring
    refine le_trans step1 ?_
    have step2 : ∑ i ∈ Finset.range (m + 1), ↑(m.choose i) * (N * (N + 1) / 2 * N ^ (m - i))
        ≤ ∑ i ∈ Finset.range (m + 1), ↑(m.choose i) * (N * (N + 1) / 2 * N ^ m) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle : N ^ (m - i) ≤ N ^ m := pow_le_pow_right₀ hN1 (Nat.sub_le m i)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hFnn) (Nat.cast_nonneg _)
    refine le_trans step2 ?_
    rw [← Finset.sum_mul]
    have hchoose : (∑ i ∈ Finset.range (m + 1), (↑(m.choose i) : ℝ)) = (2 : ℝ) ^ m := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
      norm_num
    rw [hchoose]
  refine le_trans hgoal ?_
  have hFN : N * (N + 1) / 2 * N ^ m ≤ N ^ (m + 2) := by
    have hle : N * (N + 1) / 2 ≤ N ^ 2 := by nlinarith [hN1]
    calc N * (N + 1) / 2 * N ^ m ≤ N ^ 2 * N ^ m :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hN0.le m)
      _ = N ^ (m + 2) := by rw [← pow_add, Nat.add_comm]
  calc (2 : ℝ) ^ m * (N * (N + 1) / 2 * N ^ m) ≤ (2 : ℝ) ^ m * N ^ (m + 2) :=
        mul_le_mul_of_nonneg_left hFN (by positivity)
    _ = (2 : ℝ) ^ m * ((((2 * j + 1 : ℕ) : ℝ)) + 1) ^ (m + 2) := by rw [hN]

theorem eFam_iteratedDeriv_le (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ C * ((j : ℝ) + 1) ^ (4 * m + 4) := by
  refine ⟨(2 : ℝ) ^ (2 * m + 2), by positivity, ?_⟩
  intro j θ hθ
  have hbase := eFam_iteratedDeriv_le_base m j θ
  refine le_trans hbase ?_
  have hcast : (((2 * j + 1 : ℕ) : ℝ)) + 1 = 2 * ((j : ℝ) + 1) := by push_cast; ring
  have hpow : (2 : ℝ) ^ m * 2 ^ (m + 2) = 2 ^ (2 * m + 2) := by
    rw [← pow_add, show m + (m + 2) = 2 * m + 2 from by omega]
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  calc (2 : ℝ) ^ m * ((((2 * j + 1 : ℕ) : ℝ)) + 1) ^ (m + 2)
      = 2 ^ m * (2 ^ (m + 2) * ((j : ℝ) + 1) ^ (m + 2)) := by rw [hcast, mul_pow]
    _ = 2 ^ (2 * m + 2) * ((j : ℝ) + 1) ^ (m + 2) := by rw [← mul_assoc, hpow]
    _ ≤ 2 ^ (2 * m + 2) * ((j : ℝ) + 1) ^ (4 * m + 4) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj1 (by omega)) (by positivity)

end Work.FTS.PhiStar.Series
