import Mathlib
import Submission.Work.KMTAreas.A7.randSymbGCoefDefs
import Submission.Work.KMTAreas.A7.randCoeff_data

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

/-- **Telescoping a backward difference over an interval of `ℕ`**:
`∑_{m=c}^{e} (a m - a (m+1)) = a c - a (e+1)`. -/
lemma sum_Icc_sub_succ_eq (a : ℕ → ℂ) {c e : ℕ} (hce : c ≤ e) :
    ∑ m ∈ Finset.Icc c e, (a m - a (m + 1)) = a c - a (e + 1) := by
  induction e, hce using Nat.le_induction with
  | base => simp
  | succ e hce ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

/-- **The telescoping identity.**  For arbitrary sequences `ψ`, `u`, `ε` and any `K`,
`∑_{n<K} ε n (u (n+1) ψ (n+1) - u n ψ n)`
equals the linear combination `∑_{m ≤ K} u m (1_{1≤m≤K} ε (m-1) - 1_{m<K} ε m) ψ m`.
(No hypothesis on `u` is needed: the missing endpoint terms are handled by the `if`s.) -/
lemma sum_range_telescope_aux (ψ u ε : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ Finset.range K, ε n * (u (n + 1) * ψ (n + 1) - u n * ψ n)
      = ∑ m ∈ Finset.range (K + 1),
          u m * ((if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0) - (if m < K then ε m else 0))
            * ψ m := by
  have h1 : ∑ n ∈ Finset.range K, ε n * (u (n + 1) * ψ (n + 1))
      = ∑ m ∈ Finset.range (K + 1), u m * (if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0)
          * ψ m := by
    rw [Finset.sum_range_succ']
    have h0 : u 0 * (if 1 ≤ 0 ∧ 0 ≤ K then ε (0 - 1) else 0) * ψ 0 = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < K := Finset.mem_range.mp hk
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    ring
  have h2 : ∑ n ∈ Finset.range K, ε n * (u n * ψ n)
      = ∑ m ∈ Finset.range (K + 1), u m * (if m < K then ε m else 0) * ψ m := by
    rw [Finset.sum_range_succ]
    have hK : u K * (if K < K then ε K else 0) * ψ K = 0 := by simp
    rw [hK, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < K := Finset.mem_range.mp hk
    rw [if_pos hk']
    ring
  calc ∑ n ∈ Finset.range K, ε n * (u (n + 1) * ψ (n + 1) - u n * ψ n)
      = ∑ n ∈ Finset.range K, ε n * (u (n + 1) * ψ (n + 1))
          - ∑ n ∈ Finset.range K, ε n * (u n * ψ n) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ = (∑ m ∈ Finset.range (K + 1),
            u m * (if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0) * ψ m)
          - ∑ m ∈ Finset.range (K + 1),
              u m * (if m < K then ε m else 0) * ψ m := by
        rw [h1, h2]
    _ = ∑ m ∈ Finset.range (K + 1),
          (u m * (if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0) * ψ m
            - u m * (if m < K then ε m else 0) * ψ m) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ m ∈ Finset.range (K + 1),
          u m * ((if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0) - (if m < K then ε m else 0))
            * ψ m := by
        exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **Partial sums of an interval-like indicator times a backward difference.**  If the level set
of `P` is an interval of `ℕ` and `‖a m‖ ≤ 1`, then `‖∑_{m ∈ (Icc c e).filter P} (a m - a (m+1))‖ ≤ 2`. -/
lemma norm_sum_filter_Icc_sub_succ_le {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k → P j → P k → P m)
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (c e : ℕ) :
    ‖∑ m ∈ (Finset.Icc c e).filter P, (a m - a (m + 1))‖ ≤ 2 := by
  rcases Finset.eq_empty_or_nonempty ((Finset.Icc c e).filter P) with h | h
  · rw [h]; simp
  · have hEq := randCoeff_filter_Icc_eq_Icc hP h
    have hpq : ((Finset.Icc c e).filter P).min' h ≤ ((Finset.Icc c e).filter P).max' h :=
      Finset.min'_le _ _ (Finset.max'_mem _ h)
    rw [hEq, sum_Icc_sub_succ_eq a hpq]
    have h1 : ‖a (((Finset.Icc c e).filter P).min' h)‖ ≤ 1 := ha _
    have h2 : ‖a (((Finset.Icc c e).filter P).max' h + 1)‖ ≤ 1 := ha _
    have h3 := norm_sub_le (a (((Finset.Icc c e).filter P).min' h))
      (a (((Finset.Icc c e).filter P).max' h + 1))
    linarith

theorem randSymbG_telescope (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1) (ha : Monotone a) (K : ℕ) :
    (Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K
        = fun ξ => ∑ m ∈ Finset.range (K + 1),
            Work.KMTAreas.A7.randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m *
              Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ)
    ∧ (∀ u v : ℕ, ‖∑ m ∈ Finset.Icc u v,
        Work.KMTAreas.A7.randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 4) := by
  constructor
  · -- Part 1: the telescoping identity for the symbol.
    funext ξ
    have key : ∀ m : ℕ, smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m ξ
        = (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0) *
            varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ := by
      intro m
      rw [smallSymbG_apply]
      by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m <;> simp [h]
    simp only [randSymb]
    trans ∑ n ∈ Finset.range K, ε n *
        ((if randAct ρ C₀ a l₁ l₂ k₁ k₂ (n + 1) then (1 : ℂ) else 0)
              * varphitildeNt P P.natDegree (Nat.floor (a (n + 1))) k₂ t ξ
            - (if randAct ρ C₀ a l₁ l₂ k₁ k₂ n then (1 : ℂ) else 0)
              * varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ)
    · exact Finset.sum_congr rfl (fun n _ => by rw [key (n + 1), key n])
    · rw [sum_range_telescope_aux
        (fun m => varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ)
        (fun m => if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0) ε K]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m <;>
        simp [randSymbGCoef, teleCoef, h]
  · -- Part 2: the partial sums of the coefficients are bounded by `4`.
    intro u v
    have hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k → randAct ρ C₀ a l₁ l₂ k₁ k₂ j →
        randAct ρ C₀ a l₁ l₂ k₁ k₂ k → randAct ρ C₀ a l₁ l₂ k₁ k₂ m :=
      fun hjm hmk hj hk => randAct_interval ha hjm hmk hj hk
    let A : ℕ → ℂ := fun m => if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0
    have htele : ∀ m, teleCoef ε K m = A m - A (m + 1) := by
      intro m
      have h2 : A (m + 1) = (if m < K then ε m else 0 : ℂ) := by
        change (if 1 ≤ m + 1 ∧ m + 1 ≤ K then ε (m + 1 - 1) else 0 : ℂ)
          = (if m < K then ε m else 0 : ℂ)
        by_cases h : m < K <;> simp [h]
      rw [teleCoef, h2]
    have hA1 : ∀ m, ‖A m‖ ≤ 1 := by
      intro m
      change ‖(if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0 : ℂ)‖ ≤ 1
      by_cases h : 1 ≤ m ∧ m ≤ K
      · rw [if_pos h]; exact hε (m - 1)
      · rw [if_neg h]; simp
    have hcoef : ∀ m, randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m
        = if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then A m - A (m + 1) else 0 := by
      intro m
      rw [randSymbGCoef, htele m]
    have hsum : ∑ m ∈ Finset.Icc u v, randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m
        = ∑ m ∈ (Finset.Icc u v).filter (randAct ρ C₀ a l₁ l₂ k₁ k₂),
            (A m - A (m + 1)) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun m _ => hcoef m)
    rw [hsum]
    exact le_trans
      (norm_sum_filter_Icc_sub_succ_le (P := randAct ρ C₀ a l₁ l₂ k₁ k₂) hP A hA1 u v)
      (by norm_num)

end Work.KMTAreas.A7
