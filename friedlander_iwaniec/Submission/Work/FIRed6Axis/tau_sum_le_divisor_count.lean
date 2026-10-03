import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIRed6Axis

open Finset

/-- **The `τ`-mass of a set of annulus points is at most the divisor counts.**  For a finite set `T`
of Gaussian integers of squarefree norm in `[1, 2N]`, and any cutoff `X` with
`d³ ≤ 2N ⟹ d ≤ X`,
`∑_{z ∈ T} τ(|z|²) ≤ 4 ∑_{d ≤ X} τ(d)³ · #{z ∈ T : d ∣ |z|²}`.

The pointwise input `hloc` is the `τ`-localization
`τ(n) ≤ 4 ∑_{d ∣ n, d³ ≤ n} τ(d)³` for squarefree `n ≥ 1` (proved as
`Work.FIRed6Axis.tau_divisors_cube_le`): each `d` occurring in the inner sum satisfies `d ≤ X`, so
the inner sum is at most `∑_{d ∈ (Icc 1 X).filter (· ∣ |z|²)} τ(d)³`; swap the two sums. -/
theorem tau_sum_le_divisor_count (N : ℝ) (X : ℕ) (T : Finset GaussianInt)
    (hloc : ∀ n : ℕ, 1 ≤ n → Squarefree n →
      ((n.divisors.card : ℕ) : ℝ)
        ≤ 4 * ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n),
            (((d.divisors.card : ℕ) : ℝ)) ^ 3)
    (hX : ∀ d : ℕ, d ^ 3 ≤ 2 * N → d ≤ X)
    (hT : ∀ z ∈ T, 1 ≤ Work.FIPlan.gnorm z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N)
    (hsf : ∀ z ∈ T, Squarefree (Work.FIPlan.gnorm z)) :
    (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 4 * ∑ d ∈ Finset.Icc 1 X,
          (((d.divisors.card : ℕ) : ℝ)) ^ 3
            * (((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
  -- Interchange the two sums: group the divisors `d` by the points `z` they divide.
  have hswap :
      (∑ z ∈ T, ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d ∣ Work.FIPlan.gnorm z),
          (((d.divisors.card : ℕ) : ℝ)) ^ 3)
        = ∑ d ∈ Finset.Icc 1 X,
            (((d.divisors.card : ℕ) : ℝ)) ^ 3
              * (((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
    have h1 : (∑ z ∈ T, ∑ d ∈ (Finset.Icc 1 X).filter
          (fun d => d ∣ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ) : ℝ)) ^ 3)
        = ∑ z ∈ T, ∑ d ∈ Finset.Icc 1 X,
            if d ∣ Work.FIPlan.gnorm z then (((d.divisors.card : ℕ) : ℝ)) ^ 3 else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.sum_filter (fun d => d ∣ Work.FIPlan.gnorm z)
        (fun d => (((d.divisors.card : ℕ) : ℝ)) ^ 3)
    rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hterm : ∀ z,
        (if d ∣ Work.FIPlan.gnorm z then (((d.divisors.card : ℕ) : ℝ)) ^ 3 else 0)
        = (if d ∣ Work.FIPlan.gnorm z then (1 : ℝ) else 0)
            * (((d.divisors.card : ℕ) : ℝ)) ^ 3 := by
      intro z; split <;> simp
    simp only [hterm]
    rw [← Finset.sum_mul, Finset.sum_boole]
    ring
  -- Pointwise: the `τ`-localization plus `d ≤ X` for every divisor `d` occurring there.
  have hpoint : ∀ z ∈ T,
      (∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z),
          (((d.divisors.card : ℕ) : ℝ)) ^ 3)
        ≤ ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d ∣ Work.FIPlan.gnorm z),
            (((d.divisors.card : ℕ) : ℝ)) ^ 3 := by
    intro z hz
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro d hd
      obtain ⟨hdmem, hcube⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hdmem
      have hzpos : 0 < Work.FIPlan.gnorm z := (hT z hz).1
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hzpos
      have hc : ((d : ℝ)) ^ 3 ≤ 2 * N := by
        have h1' : ((d ^ 3 : ℕ) : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hcube
        rw [Nat.cast_pow] at h1'
        linarith [(hT z hz).2]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hX d hc⟩, hdvd⟩
    · intro d _ _
      positivity
  calc (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ ∑ z ∈ T, 4 * (∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
            (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ) : ℝ)) ^ 3) :=
          Finset.sum_le_sum (fun z hz => hloc (Work.FIPlan.gnorm z) (hT z hz).1 (hsf z hz))
    _ = 4 * ∑ z ∈ T, (∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
            (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ) : ℝ)) ^ 3) := by
          rw [Finset.mul_sum]
    _ ≤ 4 * ∑ z ∈ T, (∑ d ∈ (Finset.Icc 1 X).filter (fun d => d ∣ Work.FIPlan.gnorm z),
            (((d.divisors.card : ℕ) : ℝ)) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by norm_num)
    _ = 4 * ∑ d ∈ Finset.Icc 1 X,
            (((d.divisors.card : ℕ) : ℝ)) ^ 3
              * (((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
          rw [hswap]

end Work.FIRed6Axis
