import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

/-- Reduction of a meromorphic germ `h = N / D` to lowest terms: given `N ≠ 0` and `D(0) ≠ 0`,
there are `N', D'` with `D'(0) ≠ 0`, the same germ `h = N'/D'` near `0`, no common root of `N'`
and `D'`, and `N' ≠ 0`.  The reduction is by the gcd of `N` and `D`. -/
theorem germ_reduce {h : ℂ → ℂ} {N D : Polynomial ℂ} (hN : N ≠ 0) (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N) :
    ∃ N' D' : Polynomial ℂ, Polynomial.eval 0 D' ≠ 0 ∧
      (∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D' = Polynomial.eval u N') ∧
      (∀ z, Polynomial.eval z N' = 0 → Polynomial.eval z D' ≠ 0) ∧ N' ≠ 0 := by
  classical
  set g : Polynomial ℂ := GCDMonoid.gcd N D with hg
  have hD_ne : D ≠ 0 := fun hD => hD0 (by rw [hD]; simp)
  have hg_dvd_N : g ∣ N := by rw [hg]; exact GCDMonoid.gcd_dvd_left N D
  have hg_dvd_D : g ∣ D := by rw [hg]; exact GCDMonoid.gcd_dvd_right N D
  have hg_ne : g ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hg_dvd_N
    exact hN hg_dvd_N
  have hmul_N : g * (N / g) = N := EuclideanDomain.mul_div_cancel' hg_ne hg_dvd_N
  have hmul_D : g * (D / g) = D := EuclideanDomain.mul_div_cancel' hg_ne hg_dvd_D
  -- `g 0 ≠ 0`, because `D 0 = g 0 * D' 0 ≠ 0`.
  have hg0 : Polynomial.eval 0 g ≠ 0 := by
    intro h0
    apply hD0
    rw [← hmul_D, Polynomial.eval_mul, h0, zero_mul]
  have hcont : ContinuousAt (fun u : ℂ => Polynomial.eval u g) 0 := by
    have hh := Polynomial.continuousAt_aeval (R := ℂ) (A := ℂ) (p := g) (a := 0)
    simpa [Polynomial.aeval_def] using hh
  have hg_eventually : ∀ᶠ u in nhds (0 : ℂ), Polynomial.eval u g ≠ 0 :=
    hcont.eventually_ne hg0
  -- The same germ near `0`, after cancelling the common factor `g`.
  have hDN' : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u (D / g) = Polynomial.eval u (N / g) := by
    filter_upwards [hDN, hg_eventually] with u hu hgu
    have huN : Polynomial.eval u N = Polynomial.eval u g * Polynomial.eval u (N / g) := by
      rw [← Polynomial.eval_mul, hmul_N]
    have huD : Polynomial.eval u D = Polynomial.eval u g * Polynomial.eval u (D / g) := by
      rw [← Polynomial.eval_mul, hmul_D]
    rw [huD, huN] at hu
    apply mul_left_cancel₀ hgu
    rw [← hu]; ring
  -- `N / g` and `D / g` are coprime, hence have no common root.
  have hcop : IsCoprime (N / g) (D / g) := by
    rw [hg]; exact isCoprime_div_gcd_div_gcd hD_ne
  have hnoroot : ∀ z, Polynomial.eval z (N / g) = 0 → Polynomial.eval z (D / g) ≠ 0 := by
    intro z hz
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcop z with h1 | h2
    · exact absurd hz (by simpa [Polynomial.aeval_def] using h1)
    · simpa [Polynomial.aeval_def] using h2
  have hN' : N / g ≠ 0 := by
    rintro h0
    apply hN
    rw [← hmul_N, h0, mul_zero]
  have hD'0 : Polynomial.eval 0 (D / g) ≠ 0 := by
    intro h0
    apply hD0
    rw [← hmul_D, Polynomial.eval_mul, h0, mul_zero]
  exact ⟨N / g, D / g, hD'0, hDN', hnoroot, hN'⟩

end Work.EQ
