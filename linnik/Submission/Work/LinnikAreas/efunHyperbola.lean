import Mathlib
import Submission.Work.LinnikAreas.hbCount
import Submission.Work.LinnikAreas.hbFilter
import Submission.Work.LinnikAreas.hbSplit

namespace Work.LinnikAreas

/-- **Dirichlet's hyperbola identity.**

For any coefficients `F : ℕ → ℂ` and any `N : ℕ`, with `s = ⌊√N⌋` and `E = ⌊N/(s+1)⌋`,

  `∑_{d ≤ N} F d · ⌊N/d⌋ = ∑_{d ≤ s} F d · ⌊N/d⌋
        + ∑_{e ≤ E} ( ∑_{n ≤ N/e} F n − ∑_{n ≤ s} F n )`.

The left-hand side counts (with weight `F d`) the pairs `(d,m)` with `1 ≤ m` and `d·m ≤ N`.
Splitting at `d = s+1`, the tail `d > s` is reindexed by the complementary variable `m = e`:
for `d > s` each `⌊N/d⌋ = #{e ∈ [1,E] : d·e ≤ N}` (as `⌊N/d⌋ ≤ E`), so after Fubini the total
becomes `∑_{e ≤ E} #{d ∈ (s, N] : d ≤ N/e}`, and the inner sum over `(s, N/e]` is the
difference of the partial sums up to `N/e` and up to `s`. -/
theorem hyperbola_identity (F : ℕ → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, F d * ((N / d : ℕ) : ℂ))
      = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), F d * ((N / d : ℕ) : ℂ))
        + (∑ e ∈ Finset.Icc 1 (N / (Nat.sqrt N + 1)),
            ((∑ n ∈ Finset.Icc 1 (N / e), F n)
              - (∑ n ∈ Finset.Icc 1 (Nat.sqrt N), F n))) := by
  set s := Nat.sqrt N with hs_def
  set E := N / (s + 1) with hE_def
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hswap : ∑ d ∈ Finset.Icc (s + 1) N, F d * ((N / d : ℕ) : ℂ)
      = ∑ e ∈ Finset.Icc 1 E, ∑ d ∈ Finset.Icc (s + 1) (N / e), F d := by
    have hstep : ∀ d ∈ Finset.Icc (s + 1) N,
        F d * ((N / d : ℕ) : ℂ) = ∑ e ∈ Finset.Icc 1 E, (if d * e ≤ N then F d else 0) := by
      intro d hd
      have hd1 : s + 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : 0 < d := by omega
      have hdE : N / d ≤ E := by
        show N / d ≤ N / (s + 1)
        exact Nat.div_le_div_left hd1 (by omega)
      have hcount := hbCount N d E hdpos hdE
      rw [hcount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : d * e ≤ N <;> simp [h]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    have hepos : 0 < e := by
      have := (Finset.mem_Icc.mp he).1; omega
    rw [← Finset.sum_filter, hbFilter N (s + 1) e hepos]
  have hmain : ∑ d ∈ Finset.Icc (s + 1) N, F d * ((N / d : ℕ) : ℂ)
      = ∑ e ∈ Finset.Icc 1 E,
          ((∑ n ∈ Finset.Icc 1 (N / e), F n) - (∑ n ∈ Finset.Icc 1 s, F n)) := by
    rw [hswap]
    apply Finset.sum_congr rfl
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heE : e ≤ E := (Finset.mem_Icc.mp he).2
    have hsd : s + 1 ≤ N / e := by
      have h1 : e * (s + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < s + 1)).mp heE
      exact (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr (by rw [Nat.mul_comm]; exact h1)
    have hle : s ≤ N / e := le_trans (Nat.le_succ s) hsd
    rw [hbSplit F (a := 1) (m := N / e) (s := s) (by omega) hle]
    ring
  rw [hbSplit (fun i => F i * ((N / i : ℕ) : ℂ)) (a := 1) (m := N) (s := s) (by omega) hsN,
    hmain]

theorem efunHyperbola {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (χ (d : ZMod q) : ℂ) * ((N / d : ℕ) : ℂ))
      = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (χ (d : ZMod q) : ℂ) * ((N / d : ℕ) : ℂ))
        + (∑ e ∈ Finset.Icc 1 (N / (Nat.sqrt N + 1)),
            ((∑ n ∈ Finset.Icc 1 (N / e), (χ (n : ZMod q) : ℂ))
              - (∑ n ∈ Finset.Icc 1 (Nat.sqrt N), (χ (n : ZMod q) : ℂ)))) :=
  hyperbola_identity (fun d => (χ (d : ZMod q) : ℂ)) N

end Work.LinnikAreas
