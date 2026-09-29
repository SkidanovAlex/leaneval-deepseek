import Mathlib
import Submission.Commons.Combinatorics.Multinomial.card_balanced_maps
import Submission.Commons.Combinatorics.Multinomial.balanced_indices
import Submission.Work.Holonomy3.eventually_pow_ge_poly

namespace Work.Holonomy3

/-- The number of balanced multi-indices `i : Fin d → Fin m` equals the central multinomial
coefficient. (Proved in `Submission.Commons.Combinatorics.Multinomial.card_balanced_maps`.) -/
private lemma card_balanced_eq_multinomial (m d : ℕ) (hm : 0 < m) (hmd : m ∣ d) :
    (Finset.univ.filter (fun i : Fin d → Fin m =>
        ∀ s : Fin m, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / m)).card
      = Nat.multinomial Finset.univ (fun _ : Fin m => d / m) :=
  Commons.Combinatorics.Multinomial.card_balanced_maps m d hm hmd

/-- Crude polynomial bound for the central binomial coefficient. -/
private lemma choose_bound (m d : ℕ) (hm : 2 ≤ m) (hd : m - 1 ≤ d) :
    Nat.choose (d + m - 1) (m - 1) ≤ (d + 1) ^ (2 * m - 2) := by
  have h2d : 2 ≤ d + 1 := by omega
  have hA : d + m - 1 ≤ 2 * (d + 1) := by omega
  have hB : 2 * (d + 1) ≤ (d + 1) * (d + 1) := Nat.mul_le_mul_right _ h2d
  have hdm : d + m - 1 ≤ (d + 1) * (d + 1) := le_trans hA hB
  have h3 : ((d + 1) * (d + 1)) ^ (m - 1) = (d + 1) ^ (2 * m - 2) := by
    rw [mul_pow, ← pow_add]
    congr 1
    omega
  calc Nat.choose (d + m - 1) (m - 1) ≤ (d + m - 1) ^ (m - 1) := Nat.choose_le_pow _ _
    _ ≤ ((d + 1) * (d + 1)) ^ (m - 1) := Nat.pow_le_pow_left hdm _
    _ = (d + 1) ^ (2 * m - 2) := h3

/-- In the degenerate case `m = 1` every index is balanced (there is only one species). -/
private lemma count_balanced_one (d : ℕ) :
    (Finset.univ.filter (fun i : Fin d → Fin 1 =>
      ∀ s : Fin 1, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / 1)).card = 1 := by
  have h : (Finset.univ.filter (fun i : Fin d → Fin 1 =>
      ∀ s : Fin 1, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / 1))
      = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _ s
    have h2 : (Finset.univ.filter (fun j : Fin d => i j = s)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro j _
      exact Subsingleton.elim _ _
    rw [h2, Finset.card_univ, Fintype.card_fin, Nat.div_one]
  rw [h, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  simp

/-- Lower bound for the number of balanced multi-indices, in terms of `m ^ d` divided by a fixed
polynomial in `d`. Combines the central-multinomial count with the strict inequality
`m ^ d < multinomial * choose (d + m - 1) (m - 1)` from the Commons library. -/
private lemma count_ge (m d : ℕ) (hm : 2 ≤ m) (hmd : m ∣ d) (hd : 1 ≤ d) :
    (m : ℝ) ^ d / ((d : ℝ) + 1) ^ (2 * m - 2)
      ≤ ((Finset.univ.filter (fun i : Fin d → Fin m =>
          ∀ s : Fin m, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / m)).card : ℝ) := by
  have hm0 : 0 < m := by omega
  have hcard := card_balanced_eq_multinomial m d hm0 hmd
  have hlt := Commons.Combinatorics.Multinomial.balanced_indices m d hm hmd hd
  have hdm : m - 1 ≤ d := by
    have : m ≤ d := Nat.le_of_dvd (by omega : 0 < d) hmd
    omega
  have hch := choose_bound m d hm hdm
  have hlt2 : m ^ d
      < Nat.multinomial Finset.univ (fun _ : Fin m => d / m) * (d + 1) ^ (2 * m - 2) := by
    calc m ^ d
        < Nat.multinomial Finset.univ (fun _ : Fin m => d / m)
            * Nat.choose (d + m - 1) (m - 1) := hlt
      _ ≤ Nat.multinomial Finset.univ (fun _ : Fin m => d / m)
            * (d + 1) ^ (2 * m - 2) := Nat.mul_le_mul_left _ hch
  rw [hcard]
  have hP : (0 : ℝ) < ((d : ℝ) + 1) ^ (2 * m - 2) := by positivity
  rw [div_le_iff₀ hP]
  have hcast : ((m ^ d : ℕ) : ℝ)
      < ((Nat.multinomial Finset.univ (fun _ : Fin m => d / m) * (d + 1) ^ (2 * m - 2) : ℕ) : ℝ) := by
    exact_mod_cast hlt2
  push_cast at hcast
  exact le_of_lt hcast

/-- **Lemma `balanced indices` of the paper** (the parameter count of Lemma `Siegel`). For `d`
divisible by `m`, the number of "balanced" multi-indices `i : Fin d → Fin m` — those in which each
of the `m` function species occurs exactly `d/m` times — is at least `(m - δ)^d` for all
sufficiently large `d`, for `0 < δ < m`. (Indeed it equals `d!/((d/m)!)^m`, asymptotically `m^d`
up to a factor `d^{-(m-1)/2}`.) -/
theorem balanced_indices (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδm : δ < m) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → m ∣ d →
      (m - δ) ^ d ≤ ((Finset.univ.filter (fun i : Fin d → Fin m =>
        ∀ s : Fin m, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / m)).card : ℝ) := by
  rcases Nat.eq_or_lt_of_le hm with h1 | h2
  · obtain rfl : m = 1 := h1.symm
    refine ⟨0, fun d _ _ => ?_⟩
    rw [count_balanced_one d]
    have hδ1 : δ < (1 : ℝ) := by simpa using hδm
    have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
    have h1' : (1 : ℝ) - δ ≤ 1 := by linarith
    simpa using pow_le_one₀ h0 h1'
  · have hm2 : 2 ≤ m := by omega
    have hpos : (0 : ℝ) < (m : ℝ) - δ := by linarith [hδm]
    set r : ℝ := (m : ℝ) / ((m : ℝ) - δ) with hr
    have hr1 : 1 < r := by
      rw [hr, one_lt_div hpos]
      linarith
    obtain ⟨d₁, hd₁⟩ := eventually_pow_ge_poly r hr1 (2 * m - 2)
    refine ⟨max (max 1 (m - 1)) d₁, fun d hd hmd => ?_⟩
    have h1d : max 1 (m - 1) ≤ d := le_trans (le_max_left _ _) hd
    have hd1 : 1 ≤ d := le_trans (le_max_left _ _) h1d
    have hy : ((d : ℝ) + 1) ^ (2 * m - 2) ≤ r ^ d :=
      hd₁ d (le_trans (le_max_right _ _) hd)
    have hcg := count_ge m d hm2 hmd hd1
    have hmr : ((m : ℝ) - δ) * r = (m : ℝ) := by
      rw [hr]
      exact mul_div_cancel₀ _ hpos.ne'
    have hP : (0 : ℝ) < ((d : ℝ) + 1) ^ (2 * m - 2) := by positivity
    have hstep : ((m : ℝ) - δ) ^ d ≤ (m : ℝ) ^ d / ((d : ℝ) + 1) ^ (2 * m - 2) := by
      rw [le_div_iff₀ hP]
      calc ((m : ℝ) - δ) ^ d * ((d : ℝ) + 1) ^ (2 * m - 2)
          ≤ ((m : ℝ) - δ) ^ d * r ^ d := mul_le_mul_of_nonneg_left hy (pow_nonneg hpos.le d)
        _ = (m : ℝ) ^ d := by rw [← mul_pow, hmr]
    exact le_trans hstep hcg

end Work.Holonomy3
