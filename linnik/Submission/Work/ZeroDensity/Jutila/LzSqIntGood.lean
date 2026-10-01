import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selSum_le_selQ_crude
import Submission.Work.LinnikAreas.Density4.selberg_Q_eq_sum_theta
import Submission.Work.LinnikAreas.Density4.selTheta_asymptotic
import Submission.Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
import Submission.Work.LinnikAreas.Density4.dyadic_decay_sigma_half
import Submission.Work.LinnikAreas.Density4.dyadic_decay_sigma_half_sq

namespace Work.ZeroDensity.Jutila

open Finset
open Work.LinnikAreas.Density4

/-! ## Local copy of the sharp Selberg-form bound `selQ z ≤ log z + C`

The module `Submission/Work/LinnikAreas/Density4/selberg_LambdaR_sq_sharp.lean` contains this
argument, but it also imports (for its *other* halves) modules that are still under construction.
We reproduce here exactly the part we need -- `selQ_le_log_add_const` -- from the modules that do
build, keeping this file self-contained. -/

/-- Splitting a sum of `A + x*B + y*C`. -/
private lemma sum_add_mul_split (s : Finset ℕ) (A B C : ℕ → ℝ) (x y : ℝ) :
    (∑ k ∈ s, (A k + x * B k + y * C k))
      = (∑ k ∈ s, A k) + x * (∑ k ∈ s, B k) + y * (∑ k ∈ s, C k) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The weighted main-term/error split for the square of `Theta(Q,r)`. -/
private lemma theta_sq_bound (C0 : ℝ) (hC0 : 0 < C0)
    (hθ : ∀ (Q : ℝ), 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
      |selTheta Q r - (r : ℝ) / (Nat.totient r : ℝ)| ≤
        C0 * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + Q)) ^ (-(3 : ℝ)))
    {Q : ℝ} (hQ : 1 ≤ Q) {r : ℕ} (hr : 1 ≤ r) :
    selTheta Q r ^ 2 ≤ ((r : ℝ) / (Nat.totient r : ℝ)) ^ 2
      + 2 * C0 * (((r : ℝ) / (Nat.totient r : ℝ)) *
          (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * (Real.log (2 + Q)) ^ (-(3 : ℝ)))
      + C0 ^ 2 * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
          (Real.log (2 + Q)) ^ (-(6 : ℝ))) := by
  have hQ3 : (1 : ℝ) < 2 + Q := by linarith
  have hlogpos : 0 < Real.log (2 + Q) := Real.log_pos hQ3
  have hρnn : 0 ≤ (r : ℝ) / (Nat.totient r : ℝ) := by
    apply div_nonneg (by positivity)
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < r)).le
  have h := hθ Q hQ r hr
  set ρ : ℝ := (r : ℝ) / (Nat.totient r : ℝ) with hρdef
  set σ : ℝ := ∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ) with hσdef
  set L : ℝ := (Real.log (2 + Q)) ^ (-(3 : ℝ)) with hLdef
  have hσnn : 0 ≤ σ := by rw [hσdef]; positivity
  have hLnn : 0 ≤ L := by rw [hLdef]; exact Real.rpow_nonneg hlogpos.le (-(3 : ℝ))
  have habs : |selTheta Q r| ≤ ρ + C0 * σ * L := by
    have h2 : |selTheta Q r - ρ| ≤ C0 * σ * L := h
    calc |selTheta Q r| = |(selTheta Q r - ρ) + ρ| := by ring_nf
      _ ≤ |selTheta Q r - ρ| + |ρ| := abs_add_le _ _
      _ ≤ C0 * σ * L + ρ := by rw [abs_of_nonneg hρnn]; linarith
      _ = ρ + C0 * σ * L := by ring
  have hsq : L * L = (Real.log (2 + Q)) ^ (-(6 : ℝ)) := by
    rw [hLdef, ← Real.rpow_add hlogpos]
    congr 1
    norm_num
  have hsq2 : L ^ 2 = (Real.log (2 + Q)) ^ (-(6 : ℝ)) := by
    rw [sq, hsq]
  have h3 : (selTheta Q r) ^ 2 ≤ (ρ + C0 * σ * L) ^ 2 := by
    calc (selTheta Q r) ^ 2 = |selTheta Q r| ^ 2 := (sq_abs _).symm
      _ ≤ (ρ + C0 * σ * L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hexp : (ρ + C0 * σ * L) ^ 2
      = ρ ^ 2 + 2 * C0 * (ρ * σ * L) + C0 ^ 2 * (σ ^ 2 * (Real.log (2 + Q)) ^ (-(6 : ℝ))) := by
    rw [show (ρ + C0 * σ * L) ^ 2
          = ρ ^ 2 + 2 * (ρ * (C0 * σ * L)) + (C0 * σ * L) ^ 2 by ring,
      show (C0 * σ * L) ^ 2 = C0 ^ 2 * (σ ^ 2 * (L ^ 2)) by ring, hsq2]
    ring
  exact h3.trans hexp.le

/-- **`selQ z` is at most `log z + O(1)`** -- the sharp Selberg-sieve value, from the diagonalised
density identity `selberg_Q_eq_sum_theta`, the asymptotic of `Theta` and the two dyadic sums. -/
theorem selQ_le_log_add_const_of
    (hΘ : ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
      |selTheta Q r - (r : ℝ) / (Nat.totient r : ℝ)| ≤
        C * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + Q)) ^ (-(3 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → selQ z ≤ Real.log (z : ℝ) + C := by
  obtain ⟨Cm, hCm, hM⟩ := sum_mu_sq_div_totient_sharp
  obtain ⟨C0, hC0, hθ⟩ := hΘ
  obtain ⟨C2, hC2, hd1⟩ := dyadic_decay_sigma_half
  obtain ⟨C3, hC3, hd2⟩ := dyadic_decay_sigma_half_sq
  refine ⟨Cm + 2 * C0 * C2 + C0 ^ 2 * C3, by positivity, ?_⟩
  intro z hz
  have hz1 : 1 ≤ z := by omega
  have hmain : (∑ k ∈ Finset.Icc 1 z,
      ((ArithmeticFunction.moebius k : ℝ) ^ 2) / (Nat.totient k : ℝ))
      ≤ Real.log (z : ℝ) + Cm := hM z hz1
  have hd1' : (∑ k ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius k : ℝ) ^ 2) / (k : ℝ) *
          (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + (z : ℝ) / k)) ^ (-(3 : ℝ))) ≤ C2 :=
    hd1 z 3 (by norm_num)
  have hd2' : (∑ k ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius k : ℝ) ^ 2) * (Nat.totient k : ℝ) / ((k : ℝ) ^ 2) *
          (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
          (Real.log (2 + (z : ℝ) / k)) ^ (-(6 : ℝ))) ≤ C3 := by
    have h := hd2 z 3 (by norm_num)
    simpa [show (-(6 : ℝ)) = -2 * (3 : ℝ) by norm_num] using h
  have hsum : (∑ k ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius k : ℝ) ^ 2 * (Nat.totient k : ℝ)) / ((k : ℝ) ^ 2) *
          selTheta ((z : ℝ) / k) k ^ 2)
      ≤ ∑ k ∈ Finset.Icc 1 z,
          (((ArithmeticFunction.moebius k : ℝ) ^ 2) / (Nat.totient k : ℝ)
            + 2 * C0 * (((ArithmeticFunction.moebius k : ℝ) ^ 2) / (k : ℝ) *
                (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
                (Real.log (2 + (z : ℝ) / k)) ^ (-(3 : ℝ)))
            + C0 ^ 2 * (((ArithmeticFunction.moebius k : ℝ) ^ 2) * (Nat.totient k : ℝ) /
                ((k : ℝ) ^ 2) * (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
                (Real.log (2 + (z : ℝ) / k)) ^ (-(6 : ℝ)))) := by
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hφ : (0 : ℝ) < (Nat.totient k : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < k)
    have hQ : (1 : ℝ) ≤ (z : ℝ) / k := by
      rw [le_div_iff₀ hk0, one_mul]; exact_mod_cast hkz
    have hterm := theta_sq_bound C0 hC0 hθ hQ (r := k) (by omega)
    have hc : 0 ≤ ((ArithmeticFunction.moebius k : ℝ) ^ 2 * (Nat.totient k : ℝ)) / ((k : ℝ) ^ 2) := by
      positivity
    have hb := mul_le_mul_of_nonneg_left hterm hc
    have e1 : ((ArithmeticFunction.moebius k : ℝ) ^ 2 * (Nat.totient k : ℝ)) / ((k : ℝ) ^ 2) *
          ((k : ℝ) / (Nat.totient k : ℝ)) ^ 2
        = ((ArithmeticFunction.moebius k : ℝ) ^ 2) / (Nat.totient k : ℝ) := by
      field_simp
      try ring
    have e2 : ((ArithmeticFunction.moebius k : ℝ) ^ 2 * (Nat.totient k : ℝ)) / ((k : ℝ) ^ 2) *
          (2 * C0 * (((k : ℝ) / (Nat.totient k : ℝ)) *
            (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
            (Real.log (2 + (z : ℝ) / k)) ^ (-(3 : ℝ))))
        = 2 * C0 * (((ArithmeticFunction.moebius k : ℝ) ^ 2) / (k : ℝ) *
            (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
            (Real.log (2 + (z : ℝ) / k)) ^ (-(3 : ℝ))) := by
      field_simp
      try ring
    have e3 : ((ArithmeticFunction.moebius k : ℝ) ^ 2 * (Nat.totient k : ℝ)) / ((k : ℝ) ^ 2) *
          (C0 ^ 2 * ((∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
            (Real.log (2 + (z : ℝ) / k)) ^ (-(6 : ℝ))))
        = C0 ^ 2 * (((ArithmeticFunction.moebius k : ℝ) ^ 2) * (Nat.totient k : ℝ) /
            ((k : ℝ) ^ 2) * (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
            (Real.log (2 + (z : ℝ) / k)) ^ (-(6 : ℝ))) := by
      ring
    rw [mul_add, mul_add, e1, e2, e3] at hb
    exact hb
  have hsplit := sum_add_mul_split (Finset.Icc 1 z)
    (fun k => ((ArithmeticFunction.moebius k : ℝ) ^ 2) / (Nat.totient k : ℝ))
    (fun k => ((ArithmeticFunction.moebius k : ℝ) ^ 2) / (k : ℝ) *
        (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
        (Real.log (2 + (z : ℝ) / k)) ^ (-(3 : ℝ)))
    (fun k => ((ArithmeticFunction.moebius k : ℝ) ^ 2) * (Nat.totient k : ℝ) / ((k : ℝ) ^ 2) *
        (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
        (Real.log (2 + (z : ℝ) / k)) ^ (-(6 : ℝ)))
    (2 * C0) (C0 ^ 2)
  have hB' : 2 * C0 * (∑ k ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius k : ℝ) ^ 2) / (k : ℝ) *
          (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + (z : ℝ) / k)) ^ (-(3 : ℝ))) ≤ 2 * C0 * C2 :=
    mul_le_mul_of_nonneg_left hd1' (by positivity)
  have hC' : C0 ^ 2 * (∑ k ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius k : ℝ) ^ 2) * (Nat.totient k : ℝ) / ((k : ℝ) ^ 2) *
          (∑ d ∈ k.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
          (Real.log (2 + (z : ℝ) / k)) ^ (-(6 : ℝ))) ≤ C0 ^ 2 * C3 :=
    mul_le_mul_of_nonneg_left hd2' (by positivity)
  rw [selberg_Q_eq_sum_theta z]
  linarith [hsum, hsplit.le, hmain, hB', hC']

/-- `selTheta_asymptotic` with a real (rather than integer) exponent. -/
theorem selTheta_asymptotic_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
      |selTheta Q r - (r : ℝ) / (Nat.totient r : ℝ)| ≤
        C * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + Q)) ^ (-(3 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := selTheta_asymptotic
  refine ⟨C, hC, fun Q hQ r hr => ?_⟩
  have h1 := h Q hQ r hr
  have h2 : (Real.log (2 + Q)) ^ (-3 : ℤ) = (Real.log (2 + Q)) ^ (-(3 : ℝ)) := by norm_num
  rwa [h2] at h1

/-- `selQ z ≤ log z + O(1)`: instantiate `selQ_le_log_add_const_of` with the asymptotic of
`Theta` (`selTheta_asymptotic`, proved in the workspace). -/
theorem selQ_le_log_add_const :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → selQ z ≤ Real.log (z : ℝ) + C :=
  selQ_le_log_add_const_of selTheta_asymptotic_rpow

/-! ## The requested bound -/

/-- Bridge between the Jutila truncated von Mangoldt sum `Lz (z:ℝ) ·` and the Selberg weight
sum appearing in the sharp Selberg-sieve bound: for integer `z`, the two agree. -/
lemma Lz_eq_selSum (z n : ℕ) :
    Lz (z : ℝ) n = ∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d := by
  simp only [Lz, selLam, Nat.cast_le]

/-- **Sharp second moment of the truncated von Mangoldt sum, case `z*z ≤ N`.**

`Σ_{n ≤ N} Λ_z(n)² ≤ N·log z + C·N` for integer `z ≥ 2` with `z*z ≤ N`, sharp leading constant `1`.
Route: the crude floor comparison `selSum_le_selQ_crude` gives
`Σ_{n≤N} Λ_z(n)² ≤ N·selQ z + z²`, the sharp Selberg-form bound `selQ z ≤ log z + C₀`
(following the proof of `selQ_le_log_add_const` in
`Submission/Work/LinnikAreas/Density4/selberg_LambdaR_sq_sharp.lean`, whose ingredients
`selberg_Q_eq_sum_theta`, `selTheta_asymptotic`, `sum_mu_sq_div_totient_sharp`,
`dyadic_decay_sigma_half`, `dyadic_decay_sigma_half_sq` all build) gives `N·log z + C₀·N`,
and `z*z ≤ N` absorbs `z²`.  This is exactly `case1_bound` of that file with `ε = 0`.

Bridge to the Selberg vocabulary: `Lz (z:ℝ) n = ∑ d ∈ n.divisors.filter (fun d => d ≤ z),
selLam z d` (by `simp only [Lz, Nat.cast_le]`). -/
theorem LzSqIntGood :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → z * z ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (Lz (z : ℝ) n) ^ 2) ≤
        (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ) := by
  obtain ⟨C0, hC0pos, hQb⟩ := selQ_le_log_add_const
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro z N hz hzN hzz
  have hz1 : 1 ≤ z := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsum_eq : (∑ n ∈ Finset.Icc 1 N, (Lz (z : ℝ) n) ^ 2)
      = ∑ n ∈ Finset.Icc 1 N,
          (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Lz_eq_selSum]
  have hS := selSum_le_selQ_crude z N hz1
  have hQz := hQb z hz
  have hzz' : (z : ℝ) * (z : ℝ) ≤ (N : ℝ) := by
    have h : ((z * z : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hzz
    simpa [Nat.cast_mul] using h
  have hNQ : (N : ℝ) * selQ z ≤ (N : ℝ) * (Real.log (z : ℝ) + C0) :=
    mul_le_mul_of_nonneg_left hQz (le_of_lt hNpos)
  rw [hsum_eq]
  nlinarith [hS, hNQ, hzz']

end Work.ZeroDensity.Jutila
