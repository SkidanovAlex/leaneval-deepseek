import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.anFI_sum_eq_gauss_primary
import Submission.Work.FITop4.Red5.sieve_step

namespace Work.FITop4.Red5

/-- **Weighted Gauss identity of the §5 sieve step.**

The weighted sum `∑_{1 ≤ n ≤ 2N} η(n) (if N < n ∧ mn ≤ x ∧ (n,m) = 1 ∧ (n,Π) = 1 ∧ τ(n) ≤ τ
then μ(n)γ(n;C) ã(mn) else 0)` equals the Gaussian double sum over `|w|² = m` and over *primary*
`z` with `1 ≤ |z|² ≤ 2N`, with the same weight conditions read on `|z|²`.

The point is that on the support the square-support `ã(mn) = μ(mn)² a_{mn}` of the companion
sequence degenerates to `a_{mn}`: the support carries `(m,n) = 1` and `m` squarefree, so that
`μ(mn)² = μ(n)²` and hence `μ(n)·ã(mn) = μ(n)³ a_{mn} = μ(n)·a_{mn}` (`moebius_cube`).  The
identity is then the primary form `anFI_sum_eq_gauss_primary` of the paper's (5.2). -/
theorem weighted_gauss_identity
    (m x N Pz : ℕ) (C τ : ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N) (hP2 : 2 ≤ Pz)
    (hsf : Squarefree m) (η : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 (2 * N),
        η n * (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))
      = ∑ w ∈ wSph m,
          ∑ z ∈ primAnn (2 * N),
            (if Nat.Coprime m (Work.FIPlan.gnorm z) ∧ N < Work.FIPlan.gnorm z
                ∧ m * Work.FIPlan.gnorm z ≤ x ∧ PiCond Pz (Work.FIPlan.gnorm z)
                ∧ TauCond τ (Work.FIPlan.gnorm z)
              then η (Work.FIPlan.gnorm z) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
                * Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0) := by
  classical
  -- On the support `(m,n)=1`, `m` squarefree, the square-support `μ(mn)²` collapses to `μ(n)²`,
  -- so that `μ(n)·ã(mn) = μ(n)·a_{mn}`.
  have hkey : ∀ n : ℕ, Nat.Coprime n m →
      (ArithmeticFunction.moebius n : ℝ) * Work.FITop.atilFIa (m * n)
        = (ArithmeticFunction.moebius n : ℝ) * (Work.FIPlan.anFI (m * n) : ℝ) := by
    intro n hcop
    have hsq : (ArithmeticFunction.moebius (m * n) : ℝ) ^ 2
        = (ArithmeticFunction.moebius n : ℝ) ^ 2 := by
      rw [Submission.ASP.moebius_sq_cast (m * n), Submission.ASP.moebius_sq_cast n]
      have hiff : Squarefree (m * n) ↔ Squarefree n := by
        rw [Nat.squarefree_mul hcop.symm]; exact and_iff_right hsf
      by_cases hs : Squarefree n
      · rw [if_pos (hiff.mpr hs), if_pos hs]
      · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs]
    rw [atilFIa_eq, hsq]
    calc (ArithmeticFunction.moebius n : ℝ)
            * (((ArithmeticFunction.moebius n : ℝ)) ^ 2 * (Work.FIPlan.anFI (m * n) : ℝ))
        = ((ArithmeticFunction.moebius n : ℝ)) ^ 3 * (Work.FIPlan.anFI (m * n) : ℝ) := by ring
      _ = (ArithmeticFunction.moebius n : ℝ) * (Work.FIPlan.anFI (m * n) : ℝ) := by
            rw [moebius_cube]
  -- The `g` of the primary identity vanishes off the odd integers because `Π` contains `2`.
  have hodd : ∀ n : ℕ, ¬ Odd n →
      (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
        then η n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n else 0) = 0 := by
    intro n hn
    have h2 : 2 ∣ n := by
      rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
      exact hn
    have hnot : ¬ (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n) := by
      rintro ⟨-, -, -, hpi, -⟩
      exact hpi 2 Nat.prime_two hP2 h2
    rw [if_neg hnot]
  -- Step 1: rewrite the `ã`-sum as an `a`-sum with `g n = (if … then η(n)μ(n)γ(n) else 0)`.
  have hL : (∑ n ∈ Finset.Icc 1 (2 * N),
        η n * (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))
      = ∑ n ∈ Finset.Icc 1 (2 * N),
        (if Nat.Coprime m n then
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
            then η n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n else 0)
          * (Work.FIPlan.anFI (m * n) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases hc : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
    · rw [if_pos hc, if_pos hc, if_pos hc.2.2.1.symm]
      obtain ⟨hNn, hx, hcop, hpi, htau⟩ := hc
      have hk := hkey n hcop
      rw [show (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n * Work.FITop.atilFIa (m * n)
            = Work.FIPlan.gammaTrunc C n * ((ArithmeticFunction.moebius n : ℝ) * Work.FITop.atilFIa (m * n)) by ring,
          hk]
      ring
    · rw [if_neg hc, if_neg hc]
      by_cases hcop : Nat.Coprime m n <;> simp [hcop]
  rw [hL, anFI_sum_eq_gauss_primary m N
        (fun n => if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then η n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n else 0)
        hm hN hodd]
  simp only [wSph, primAnn]
  -- Step 2: match the `(w,z)`-summands; the two support conditions agree.
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  by_cases h1 : Nat.Coprime m (Work.FIPlan.gnorm z)
  · rw [if_pos h1]
    have hc1 : (N < Work.FIPlan.gnorm z ∧ m * Work.FIPlan.gnorm z ≤ x ∧ Nat.Coprime (Work.FIPlan.gnorm z) m
        ∧ PiCond Pz (Work.FIPlan.gnorm z) ∧ TauCond τ (Work.FIPlan.gnorm z))
        ↔ (N < Work.FIPlan.gnorm z ∧ m * Work.FIPlan.gnorm z ≤ x
        ∧ PiCond Pz (Work.FIPlan.gnorm z) ∧ TauCond τ (Work.FIPlan.gnorm z)) := by
      constructor
      · rintro ⟨a1, a2, a3, a4, a5⟩; exact ⟨a1, a2, a4, a5⟩
      · rintro ⟨a1, a2, a4, a5⟩; exact ⟨a1, a2, h1.symm, a4, a5⟩
    have hc2 : (Nat.Coprime m (Work.FIPlan.gnorm z) ∧ N < Work.FIPlan.gnorm z
        ∧ m * Work.FIPlan.gnorm z ≤ x ∧ PiCond Pz (Work.FIPlan.gnorm z) ∧ TauCond τ (Work.FIPlan.gnorm z))
        ↔ (N < Work.FIPlan.gnorm z ∧ m * Work.FIPlan.gnorm z ≤ x
        ∧ PiCond Pz (Work.FIPlan.gnorm z) ∧ TauCond τ (Work.FIPlan.gnorm z)) := by
      constructor
      · rintro ⟨-, a1, a2, a3, a4⟩; exact ⟨a1, a2, a3, a4⟩
      · rintro ⟨a1, a2, a3, a4⟩; exact ⟨h1, a1, a2, a3, a4⟩
    rw [if_congr hc1 rfl rfl, if_congr hc2 rfl rfl, ite_mul, zero_mul]
  · rw [if_neg h1]
    simp [h1]

end Work.FITop4.Red5
