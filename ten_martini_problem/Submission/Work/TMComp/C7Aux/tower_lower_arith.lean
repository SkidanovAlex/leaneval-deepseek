import Mathlib

namespace Work.TMComp.C7Aux

open Finset

/-- Shifting identity for a range sum:
`Σ_{t<M} f (t+2) = Σ_{t<M} f (t+1) + f (M+1) - f 1`. -/
lemma sum_range_shift (f : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ range M, f (t + 2) = ∑ t ∈ range M, f (t + 1) + f (M + 1) - f 1 := by
  have h1 : ∑ t ∈ range (M + 1), f (t + 1) = ∑ t ∈ range M, f (t + 2) + f 1 := by
    have h := sum_range_succ' (fun t => f (t + 1)) M
    simpa using h
  have h2 : ∑ t ∈ range (M + 1), f (t + 1) = ∑ t ∈ range M, f (t + 1) + f (M + 1) :=
    sum_range_succ (fun t => f (t + 1)) M
  linarith [h1, h2]

/-- Core partial-sum bound for the contracting defect sequence.  If `D (t+1) ≤ D t / 3 + ε t`
for `1 ≤ t ≤ M` (phrased on shifted indices) and `D (M+1) ≥ 0`, then the partial sum of `D`
over `1..M` is at most `(3/2) (D 1 + Σ_{1..M} ε)`.  The factor `1/3` comes from `m s ≥ 3` and
makes the geometric tail finite. -/
lemma D_sum_bound (D ε : ℕ → ℝ) (M : ℕ)
    (hDM : 0 ≤ D (M + 1))
    (hrec : ∀ t, t < M → D (t + 2) ≤ D (t + 1) / 3 + ε (t + 1)) :
    ∑ t ∈ range M, D (t + 1) ≤ 3 / 2 * (D 1 + ∑ t ∈ range M, ε (t + 1)) := by
  set T := ∑ t ∈ range M, D (t + 1) with hT
  set E := ∑ t ∈ range M, ε (t + 1) with hE
  have hsum : ∑ t ∈ range M, D (t + 2) ≤ T / 3 + E := by
    have hle : ∑ t ∈ range M, D (t + 2) ≤ ∑ t ∈ range M, (D (t + 1) / 3 + ε (t + 1)) :=
      sum_le_sum (fun t ht => hrec t (mem_range.mp ht))
    rw [sum_add_distrib] at hle
    have hdiv : ∑ t ∈ range M, D (t + 1) / 3 = T / 3 := by
      have hc : ∀ t, D (t + 1) / 3 = (1 / 3 : ℝ) * D (t + 1) := fun t => by ring
      simp_rw [hc]
      rw [← Finset.mul_sum, ← hT]
      ring
    rw [hdiv, ← hE] at hle
    exact hle
  have hshift := sum_range_shift D M
  rw [← hT] at hshift
  linarith [hsum, hshift, hDM]

theorem tower_lower_arith (l D ε : ℕ → ℝ) (m : ℕ → ℕ) (S : ℕ) (hS : 1 ≤ S)
    (hm : ∀ s, s < S → 3 ≤ m s) (hε : ∀ s, s < S → 0 ≤ ε s)
    (hD : ∀ s, s ≤ S → 0 ≤ D s)
    (hstep : ∀ s, s < S → l s ≤ l (s+1) + 2 * D s + ε s)
    (hpair : ∀ s, s < S → D (s+1) ≤ D s / (m s) + ε s) :
    l 0 - 2 * D 0 ≤ l S + 3 * D 0 / (m 0) + 7 * ∑ s ∈ Finset.range S, ε s := by
  -- Abstract contraction with ratio `1/3`, using `m s ≥ 3`.
  have hrec : ∀ s, s < S → D (s + 1) ≤ D s / 3 + ε s := by
    intro s hs
    have hDs : 0 ≤ D s := hD s (le_of_lt hs)
    have hm3 : (3 : ℝ) ≤ (m s : ℝ) := by exact_mod_cast hm s hs
    have hdiv : D s / (m s : ℝ) ≤ D s / 3 :=
      div_le_div_of_nonneg_left hDs (by norm_num) hm3
    linarith [hpair s hs, hdiv]
  -- Step 1: sum `hstep` over the first `S` stages (telescoping `l`).
  have hstepsum : l 0 ≤ l S + 2 * (∑ s ∈ range S, D s) + ∑ s ∈ range S, ε s := by
    have h1 : ∑ s ∈ range S, l s ≤ ∑ s ∈ range S, (l (s + 1) + 2 * D s + ε s) :=
      sum_le_sum (fun s hs => hstep s (mem_range.mp hs))
    have hl1 : ∑ s ∈ range S, l s = l 0 + ∑ t ∈ range (S - 1), l (t + 1) := by
      have h := sum_range_succ' l (S - 1)
      rw [Nat.sub_add_cancel hS] at h
      linarith [h]
    have hl2 : ∑ s ∈ range S, l (s + 1) = ∑ t ∈ range (S - 1), l (t + 1) + l S := by
      have h := sum_range_succ (fun t => l (t + 1)) (S - 1)
      rw [Nat.sub_add_cancel hS] at h
      exact h
    have hsplit : ∑ s ∈ range S, (l (s + 1) + 2 * D s + ε s)
        = ∑ s ∈ range S, l (s + 1) + 2 * ∑ s ∈ range S, D s + ∑ s ∈ range S, ε s := by
      rw [sum_add_distrib, sum_add_distrib, ← Finset.mul_sum]
    rw [hl1, hsplit, hl2] at h1
    linarith [h1]
  -- Step 2: geometric bound on the defect sum `Σ D s`, keeping the sharp `1/m 0` remainder.
  have hDbound : 2 * (∑ s ∈ range S, D s)
      ≤ 2 * D 0 + 3 * (D 0 / (m 0)) + 3 * ∑ s ∈ range S, ε s := by
    have hDM : 0 ≤ D ((S - 1) + 1) := by
      rw [Nat.sub_add_cancel hS]; exact hD S le_rfl
    have hrec' : ∀ t, t < S - 1 → D (t + 2) ≤ D (t + 1) / 3 + ε (t + 1) := by
      intro t ht
      have htS : t + 1 < S := by omega
      simpa using hrec (t + 1) htS
    have hT := D_sum_bound D ε (S - 1) hDM hrec'
    have hDsplit : ∑ s ∈ range S, D s = D 0 + ∑ t ∈ range (S - 1), D (t + 1) := by
      have h := sum_range_succ' D (S - 1)
      rw [Nat.sub_add_cancel hS] at h
      linarith [h]
    have hD1 : D 1 ≤ D 0 / (m 0) + ε 0 := by
      have := hpair 0 (by omega)
      simpa using this
    have hEeq : ∑ t ∈ range (S - 1), ε (t + 1) + ε 0 = ∑ s ∈ range S, ε s := by
      have h := sum_range_succ' ε (S - 1)
      rw [Nat.sub_add_cancel hS] at h
      linarith [h]
    have hT2 : ∑ t ∈ range (S - 1), D (t + 1)
        ≤ 3 / 2 * (D 0 / (m 0) + ∑ s ∈ range S, ε s) := by
      linarith [hT, hD1, hEeq]
    rw [hDsplit]
    linarith [hT2]
  have hEnn : 0 ≤ ∑ s ∈ range S, ε s := sum_nonneg (fun s hs => hε s (mem_range.mp hs))
  rw [mul_div_assoc]
  linarith [hstepsum, hDbound, hEnn]

end Work.TMComp.C7Aux
