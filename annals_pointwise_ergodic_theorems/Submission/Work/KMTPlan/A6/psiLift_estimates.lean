import Mathlib

namespace Work.KMTPlan.A6

open MeasureTheory Filter Finset
open scoped ENNReal BigOperators Topology

/-!
## Estimates for the "lift" `t ↦ ψ (t + a n / R)` of a Schwartz function

This file proves `psiLift_estimates`: for a Schwartz function `ψ : ℝ → ℂ`, a finite family
`(d n)`, and real shifts `a n`, `b n`, the two-parameter family
`∑ n ∈ s, ψ (t + a n / R) * ψ (t + b n / R) * d n` is uniformly in `R` bounded by a constant
times `(1+|t|)⁻²`, its limit as `R → ∞` (uniformly in `t`) is `(ψ t)^2 ∑ n ∈ s, d n`, and the
limit function `t ↦ ‖ψ t‖^2 * ‖∑ n ∈ s, d n‖` is controlled both pointwise and by a
`min |t| |u|`-weighted Lipschitz bound.

The three analytic inputs are:
* `psiLift_decay_two`: Schwartz decay `‖ψ t‖ ≤ C / (1+|t|)^2`,
* `psiLift_lipschitz_aux`: global Lipschitz continuity of `ψ` (from the bounded derivative),
* `psiLift_shift_decay_aux`: the same decay, uniformly over bounded shifts of the argument.
-/

/-- Pointwise Schwartz decay with an explicit `(1 + |t|)⁻²` bound. -/
private theorem psiLift_decay_two (ψ : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖ψ t‖ ≤ B / (1 + |t|) ^ 2 := by
  refine ⟨max (2 ^ 2 * ((Finset.Iic ((2, 0) : ℕ × ℕ)).sup
      (fun m' => SchwartzMap.seminorm ℝ m'.1 m'.2) ψ)) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · intro t
    have hbound : (1 + |t|) ^ 2 * ‖ψ t‖ ≤
        2 ^ 2 * ((Finset.Iic ((2,0) : ℕ × ℕ)).sup
          (fun m' => SchwartzMap.seminorm ℝ m'.1 m'.2) ψ) := by
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := ((2,0) : ℕ × ℕ)) (k := 2) (n := 0) le_rfl le_rfl ψ t
      simpa using h
    have hle : (1 + |t|)^2 * ‖ψ t‖ ≤ max (2^2 * ((Finset.Iic ((2, 0) : ℕ × ℕ)).sup
        (fun m' => SchwartzMap.seminorm ℝ m'.1 m'.2) ψ)) 1 := hbound.trans (le_max_left _ _)
    exact (le_div_iff₀ (by positivity : (0:ℝ) < (1 + |t|)^2)).mpr (by rw [mul_comm]; exact hle)

/-- A Schwartz function on `ℝ` is globally Lipschitz, with constant the Schwartz seminorm of
its derivative. -/
private theorem psiLift_lipschitz_aux (ψ : SchwartzMap ℝ ℂ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, ‖ψ x - ψ y‖ ≤ L * |x - y| := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ ψ), by positivity, ?_⟩
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (f := (ψ : ℝ → ℂ)) (C := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ ψ))
    (fun z _ => ψ.differentiableAt) (fun z _ => ?_) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  · simpa [Real.norm_eq_abs] using h
  · have hz : deriv (ψ : ℝ → ℂ) z = (SchwartzMap.derivCLM ℝ ℂ ψ) z :=
      (SchwartzMap.derivCLM_apply ℝ ψ z).symm
    rw [hz]
    exact SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℂ ψ) z

/-- Uniform Schwartz decay for a translated argument: for `|α| ≤ M` the translate `ψ (· + α)`
is dominated by `C / (1 + |t|)^2` with `C` independent of `α`. -/
private theorem psiLift_shift_decay_aux (ψ : SchwartzMap ℝ ℂ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α t : ℝ), |α| ≤ M → ‖ψ (t + α)‖ ≤ C / (1 + |t|) ^ 2 := by
  obtain ⟨B, hBpos, hBdec⟩ := psiLift_decay_two ψ
  refine ⟨B * (1 + M)^2, by positivity, ?_⟩
  intro α t hα
  have h1 : ‖ψ (t + α)‖ ≤ B / (1 + |t + α|)^2 := hBdec (t + α)
  have hsq : (1 + |t|)^2 ≤ (1 + M)^2 * (1 + |t + α|)^2 := by
    have hle : 1 + |t| ≤ (1 + M) * (1 + |t + α|) := by
      have h2 : |t| ≤ |t + α| + |α| := by
        calc |t| = |(t + α) + (-α)| := by ring_nf
          _ ≤ |t + α| + |-α| := abs_add_le _ _
          _ = |t + α| + |α| := by rw [abs_neg]
      nlinarith [hM, abs_nonneg (t + α), h2, hα]
    calc (1 + |t|)^2 ≤ ((1 + M) * (1 + |t + α|))^2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = (1 + M)^2 * (1 + |t + α|)^2 := by rw [mul_pow]
  calc ‖ψ (t + α)‖ ≤ B / (1 + |t + α|)^2 := h1
    _ ≤ B * (1 + M)^2 / (1 + |t|)^2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc B * (1 + |t|)^2 ≤ B * ((1 + M)^2 * (1 + |t + α|)^2) :=
              mul_le_mul_of_nonneg_left hsq hBpos.le
          _ = B * (1 + M)^2 * (1 + |t + α|)^2 := by ring

theorem psiLift_estimates {ι : Type*} (s : Finset ι) (ψ : SchwartzMap ℝ ℂ) (d : ι → ℂ)
    (a b : ι → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ (R : ℕ) (t : ℝ), ‖∑ n ∈ s, ψ (t + a n / (R : ℝ)) * ψ (t + b n / (R : ℝ)) * d n‖
          ≤ A / (1 + |t|) ^ 2) ∧
      (∀ t : ℝ, |‖ψ t‖ ^ 2 * ‖∑ n ∈ s, d n‖| ≤ A / (1 + |t|) ^ 2) ∧
      (∀ t u : ℝ, |‖ψ t‖ ^ 2 * ‖∑ n ∈ s, d n‖ - ‖ψ u‖ ^ 2 * ‖∑ n ∈ s, d n‖|
          ≤ A / (1 + min |t| |u|) ^ 2 * |t - u|) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℝ,
        ‖(∑ n ∈ s, ψ (t + a n / (R : ℝ)) * ψ (t + b n / (R : ℝ)) * d n)
            - (ψ t) ^ 2 * (∑ n ∈ s, d n)‖ ≤ ε) := by
  set M : ℝ := ∑ n ∈ s, (|a n| + |b n|) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact Finset.sum_nonneg (fun n _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  obtain ⟨C, hCpos, hC⟩ := psiLift_shift_decay_aux ψ M hMnn
  have hCnn : 0 ≤ C := hCpos.le
  obtain ⟨L, hLnn, hLip⟩ := psiLift_lipschitz_aux ψ
  -- decay of `ψ` itself, and the resulting global bound
  have hdec : ∀ t : ℝ, ‖ψ t‖ ≤ C / (1 + |t|)^2 :=
    fun t => by simpa using hC 0 t (by simpa using hMnn)
  have hbdd : ∀ x : ℝ, ‖ψ x‖ ≤ C := by
    intro x
    have hx : 1 ≤ (1 + |x|)^2 := by nlinarith [abs_nonneg x]
    calc ‖ψ x‖ ≤ C / (1 + |x|)^2 := hdec x
      _ ≤ C := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+|x|)^2)]
          calc C = C * 1 := (mul_one C).symm
            _ ≤ C * (1 + |x|)^2 := mul_le_mul_of_nonneg_left hx hCnn
  -- abbreviations for the two finite sums
  set K : ℝ := ∑ n ∈ s, ‖d n‖ with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]; exact Finset.sum_nonneg (fun n _ => norm_nonneg _)
  set D : ℂ := ∑ n ∈ s, d n with hDdef
  have hDle : ‖D‖ ≤ K := by
    rw [hDdef, hKdef]; exact norm_sum_le s d
  have hA0 : 0 ≤ 2 * C^2 + 2 * L * C := by
    nlinarith [sq_nonneg C, mul_nonneg hLnn hCnn]
  -- `c / (x * x) ≤ c / x` for `x ≥ 1`
  have hxx : ∀ c x : ℝ, 0 ≤ c → 1 ≤ x → c / (x * x) ≤ c / x := by
    intro c x hc hx
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc c * x = c * x * 1 := by ring
      _ ≤ c * x * x := mul_le_mul_of_nonneg_left hx (mul_nonneg hc (by linarith))
      _ = c * (x * x) := by ring
  have hCKA : C^2 * K ≤ K * (2*C^2 + 2*L*C) := by
    have hnn : 0 ≤ C^2 + 2*L*C := by nlinarith [sq_nonneg C, mul_nonneg hLnn hCnn]
    have := mul_nonneg hKnn hnn
    nlinarith [this]
  refine ⟨K * (2*C^2 + 2*L*C), mul_nonneg hKnn hA0, ?_, ?_, ?_, ?_⟩
  · -- uniform bound in `R` for the bilinear sum
    intro R t
    have hx1 : 1 ≤ (1 + |t|)^2 := by nlinarith [abs_nonneg t]
    have hterm : ∀ n ∈ s, ‖ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) * d n‖
        ≤ (C^2 / (1 + |t|)^2) * ‖d n‖ := by
      intro n hn
      have hMn : |a n| + |b n| ≤ M := by
        rw [hMdef]
        exact Finset.single_le_sum
          (fun m _ => add_nonneg (abs_nonneg (a m)) (abs_nonneg (b m))) hn
      have ha_le : |a n| ≤ M := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hMn
      have hb_le : |b n| ≤ M := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hMn
      have ha : |a n / (R:ℝ)| ≤ M := by
        rcases Nat.eq_zero_or_pos R with hR | hR
        · rw [hR]; simp [hMnn]
        · have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
          rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (R:ℝ))]
          exact (div_le_self (abs_nonneg _) hR1).trans ha_le
      have hb : |b n / (R:ℝ)| ≤ M := by
        rcases Nat.eq_zero_or_pos R with hR | hR
        · rw [hR]; simp [hMnn]
        · have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
          rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (R:ℝ))]
          exact (div_le_self (abs_nonneg _) hR1).trans hb_le
      have h1 : ‖ψ (t + a n / (R:ℝ))‖ ≤ C / (1 + |t|)^2 := hC _ t ha
      have h2 : ‖ψ (t + b n / (R:ℝ))‖ ≤ C / (1 + |t|)^2 := hC _ t hb
      have hineq : (C/(1 + |t|)^2) * (C/(1 + |t|)^2) ≤ C^2 / (1 + |t|)^2 := by
        rw [div_mul_div_comm, show C * C = C^2 by ring]
        exact hxx (C^2) ((1 + |t|)^2) (sq_nonneg C) hx1
      rw [norm_mul, norm_mul]
      calc ‖ψ (t + a n / (R:ℝ))‖ * ‖ψ (t + b n / (R:ℝ))‖ * ‖d n‖
          ≤ (C/(1 + |t|)^2) * (C/(1 + |t|)^2) * ‖d n‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ (C^2 / (1 + |t|)^2) * ‖d n‖ := mul_le_mul_of_nonneg_right hineq (norm_nonneg _)
    calc ‖∑ n ∈ s, ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) * d n‖
        ≤ ∑ n ∈ s, ‖ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) * d n‖ := norm_sum_le s _
      _ ≤ ∑ n ∈ s, (C^2 / (1 + |t|)^2) * ‖d n‖ := Finset.sum_le_sum hterm
      _ = (C^2 * K) / (1 + |t|)^2 := by
            rw [hKdef, Finset.mul_sum, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro n hn
            ring
      _ ≤ (K * (2*C^2 + 2*L*C)) / (1 + |t|)^2 :=
            div_le_div_of_nonneg_right hCKA (by positivity)
  · -- pointwise bound for `‖ψ t‖^2 * ‖D‖`
    intro t
    have hx1 : 1 ≤ (1 + |t|)^2 := by nlinarith [abs_nonneg t]
    have hineq : ‖ψ t‖^2 ≤ C^2 / (1 + |t|)^2 := by
      have h1 : ‖ψ t‖ ≤ C / (1 + |t|)^2 := hdec t
      calc ‖ψ t‖^2 ≤ (C / (1 + |t|)^2)^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ C^2 / (1 + |t|)^2 := by
            rw [div_pow, pow_two ((1+|t|)^2)]
            exact hxx (C^2) ((1 + |t|)^2) (sq_nonneg C) hx1
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖ψ t‖^2 * ‖D‖)]
    calc ‖ψ t‖^2 * ‖D‖ ≤ (C^2 / (1 + |t|)^2) * K :=
          mul_le_mul hineq hDle (norm_nonneg _) (by positivity)
      _ = (C^2 * K) / (1 + |t|)^2 := by ring
      _ ≤ (K * (2*C^2 + 2*L*C)) / (1 + |t|)^2 :=
            div_le_div_of_nonneg_right hCKA (by positivity)
  · -- `min |t| |u|`-weighted Lipschitz bound
    intro t u
    have hsq1 : (1 + min |t| |u|)^2 ≤ (1 + |t|)^2 := by
      have h : (1 + min |t| |u|) ≤ (1 + |t|) := by linarith [min_le_left |t| |u|]
      exact pow_le_pow_left₀ (by positivity) h 2
    have hsq2 : (1 + min |t| |u|)^2 ≤ (1 + |u|)^2 := by
      have h : (1 + min |t| |u|) ≤ (1 + |u|) := by linarith [min_le_right |t| |u|]
      exact pow_le_pow_left₀ (by positivity) h 2
    have hdec1 : ‖ψ t‖ ≤ C / (1 + min |t| |u|)^2 :=
      (hdec t).trans (div_le_div_of_nonneg_left hCnn (by positivity) hsq1)
    have hdec2 : ‖ψ u‖ ≤ C / (1 + min |t| |u|)^2 :=
      (hdec u).trans (div_le_div_of_nonneg_left hCnn (by positivity) hsq2)
    have hdiff : |‖ψ t‖^2 - ‖ψ u‖^2| ≤ 2 * L * C * |t - u| / (1 + min |t| |u|)^2 := by
      have hsp : ‖ψ t‖^2 - ‖ψ u‖^2 = (‖ψ t‖ - ‖ψ u‖) * (‖ψ t‖ + ‖ψ u‖) := by ring
      rw [hsp, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖ψ t‖ + ‖ψ u‖)]
      have h1 : |‖ψ t‖ - ‖ψ u‖| ≤ L * |t - u| :=
        (abs_norm_sub_norm_le (ψ t) (ψ u)).trans (hLip t u)
      have h2 : ‖ψ t‖ + ‖ψ u‖ ≤ 2 * C / (1 + min |t| |u|)^2 := by
        have h3 := add_le_add hdec1 hdec2
        rw [← add_div] at h3
        calc ‖ψ t‖ + ‖ψ u‖ ≤ (C + C) / (1 + min |t| |u|)^2 := h3
          _ = 2 * C / (1 + min |t| |u|)^2 := by ring
      calc |‖ψ t‖ - ‖ψ u‖| * (‖ψ t‖ + ‖ψ u‖)
            ≤ (L * |t - u|) * (2 * C / (1 + min |t| |u|)^2) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 2 * L * C * |t - u| / (1 + min |t| |u|)^2 := by ring
    have hfac : ‖ψ t‖^2 * ‖D‖ - ‖ψ u‖^2 * ‖D‖ = ‖D‖ * (‖ψ t‖^2 - ‖ψ u‖^2) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (norm_nonneg D)]
    calc ‖D‖ * |‖ψ t‖^2 - ‖ψ u‖^2|
        ≤ K * (2 * L * C * |t - u| / (1 + min |t| |u|)^2) :=
          mul_le_mul hDle hdiff (abs_nonneg _) hKnn
      _ ≤ (K * (2*C^2 + 2*L*C)) / (1 + min |t| |u|)^2 * |t - u| := by
            have hKL : K * (2 * L * C) ≤ K * (2*C^2 + 2*L*C) := by
              apply mul_le_mul_of_nonneg_left _ hKnn
              linarith [sq_nonneg C]
            calc K * (2 * L * C * |t - u| / (1 + min |t| |u|)^2)
                = K * (2 * L * C) * |t - u| / (1 + min |t| |u|)^2 := by ring
              _ ≤ (K * (2*C^2 + 2*L*C)) * |t - u| / (1 + min |t| |u|)^2 := by
                    apply div_le_div_of_nonneg_right _ (by positivity)
                    exact mul_le_mul_of_nonneg_right hKL (abs_nonneg _)
              _ = (K * (2*C^2 + 2*L*C)) / (1 + min |t| |u|)^2 * |t - u| := by ring
  · -- uniform convergence as `R → ∞`
    intro ε hε
    set S : ℝ := ∑ n ∈ s, (|a n| + |b n|) * ‖d n‖ with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]
      exact Finset.sum_nonneg
        (fun n _ => mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _))
    obtain ⟨N, hN⟩ := exists_nat_gt (C * L * S / ε)
    refine ⟨max N 1, ?_⟩
    intro R hR t
    have hRN : (N:ℝ) ≤ (R:ℝ) := by
      have : N ≤ R := le_trans (le_max_left _ _) hR
      exact_mod_cast this
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by
      have : 1 ≤ R := le_trans (le_max_right _ _) hR
      exact_mod_cast this
    have hRpos : (0:ℝ) < (R:ℝ) := by linarith
    have hNR : C * L * S / ε < (R:ℝ) := lt_of_lt_of_le hN hRN
    have hbound : C * L * S / (R:ℝ) ≤ ε := by
      have h1 : C * L * S < (R:ℝ) * ε := (div_lt_iff₀ hε).mp hNR
      rw [div_le_iff₀ hRpos]
      linarith
    have hsum_eq : (∑ n ∈ s, ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) * d n)
        - (ψ t)^2 * D
        = ∑ n ∈ s, (ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) - ψ t * ψ t) * d n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hsum_eq]
    have hterm : ∀ n ∈ s, ‖(ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) - ψ t * ψ t) * d n‖
        ≤ C * L * (|a n| + |b n|) / (R:ℝ) * ‖d n‖ := by
      intro n hn
      have hab : |a n / (R:ℝ)| = |a n| / (R:ℝ) := by
        rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (R:ℝ))]
      have hbb : |b n / (R:ℝ)| = |b n| / (R:ℝ) := by
        rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (R:ℝ))]
      have hl1 : ‖ψ (t + b n / (R:ℝ)) - ψ t‖ ≤ L * (|b n| / (R:ℝ)) := by
        simpa [hbb] using hLip (t + b n / (R:ℝ)) t
      have hl2 : ‖ψ (t + a n / (R:ℝ)) - ψ t‖ ≤ L * (|a n| / (R:ℝ)) := by
        simpa [hab] using hLip (t + a n / (R:ℝ)) t
      have hb1 : ‖ψ (t + a n / (R:ℝ))‖ ≤ C := hbdd _
      have hb2 : ‖ψ t‖ ≤ C := hbdd t
      have hdecomp : ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) - ψ t * ψ t
          = ψ (t + a n / (R:ℝ)) * (ψ (t + b n / (R:ℝ)) - ψ t)
            + (ψ (t + a n / (R:ℝ)) - ψ t) * ψ t := by ring
      have hcore : ‖ψ (t + a n / (R:ℝ)) * (ψ (t + b n / (R:ℝ)) - ψ t)
            + (ψ (t + a n / (R:ℝ)) - ψ t) * ψ t‖
          ≤ C * L * (|a n| + |b n|) / (R:ℝ) := by
        calc ‖ψ (t + a n / (R:ℝ)) * (ψ (t + b n / (R:ℝ)) - ψ t)
              + (ψ (t + a n / (R:ℝ)) - ψ t) * ψ t‖
            ≤ ‖ψ (t + a n / (R:ℝ)) * (ψ (t + b n / (R:ℝ)) - ψ t)‖
              + ‖(ψ (t + a n / (R:ℝ)) - ψ t) * ψ t‖ := norm_add_le _ _
          _ = ‖ψ (t + a n / (R:ℝ))‖ * ‖ψ (t + b n / (R:ℝ)) - ψ t‖
              + ‖ψ (t + a n / (R:ℝ)) - ψ t‖ * ‖ψ t‖ := by rw [norm_mul, norm_mul]
          _ ≤ C * (L * (|b n| / (R:ℝ))) + (L * (|a n| / (R:ℝ))) * C :=
              add_le_add (mul_le_mul hb1 hl1 (by positivity) hCnn)
                (mul_le_mul hl2 hb2 (by positivity) (mul_nonneg hLnn (by positivity)))
          _ = C * L * (|a n| + |b n|) / (R:ℝ) := by ring
      rw [norm_mul, hdecomp]
      exact mul_le_mul_of_nonneg_right hcore (norm_nonneg _)
    calc ‖∑ n ∈ s, (ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) - ψ t * ψ t) * d n‖
        ≤ ∑ n ∈ s, ‖(ψ (t + a n / (R:ℝ)) * ψ (t + b n / (R:ℝ)) - ψ t * ψ t) * d n‖ :=
            norm_sum_le s _
      _ ≤ ∑ n ∈ s, C * L * (|a n| + |b n|) / (R:ℝ) * ‖d n‖ := Finset.sum_le_sum hterm
      _ = (C * L / (R:ℝ)) * S := by
            rw [hSdef, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
      _ ≤ ε := by
            rw [show (C*L/(R:ℝ))*S = C*L*S/(R:ℝ) by ring]
            exact hbound

end Work.KMTPlan.A6
