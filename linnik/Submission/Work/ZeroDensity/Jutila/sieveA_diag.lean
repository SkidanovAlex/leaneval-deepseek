import Mathlib
import Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization

namespace Work.ZeroDensity.Jutila

/-- (To be placed in namespace `Work.ZeroDensity.Jutila`, importing
`Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs`, which defines
`A t = Σ_{d,e ≤ t} μ(d)μ(e)/lcm(d,e)` and `W t l = Σ_{l ∣ d ≤ t} μ(d)/d`.)
**Selberg diagonalization of the sieve quadratic form:** `A t = Σ_{l ≤ t} φ(l)·W t l²`.
Proof route: `1/lcm(d,e) = gcd(d,e)/(d·e)`, so `A t = Σ_{d,e} a_d a_e gcd(d,e)` with
`a_d = μ(d)/d`, and the classical diagonalization
`Σ_{d,e} a_d a_e gcd(d,e) = Σ_l φ(l)(Σ_{l∣d} a_d)²` (available in the workspace as
`Commons.NumberTheory.Sieve.sum_gcd_eq_sum_totient_sq`, applied to `T = Finset.Icc 1 t`,
which consists of positive elements and is closed under taking divisors) gives the claim. -/
theorem sieveA_diag (t : ℕ) :
    A t = ∑ l ∈ Finset.Icc 1 t, (Nat.totient l : ℝ) * (W t l) ^ 2 := by
  have hTpos : ∀ d ∈ Finset.Icc 1 t, 0 < d := by
    intro d hd; rw [Finset.mem_Icc] at hd; omega
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ Finset.Icc 1 t → l ∈ Finset.Icc 1 t := by
    intro l d hld hd
    rw [Finset.mem_Icc] at hd ⊢
    obtain ⟨hd1, hdt⟩ := hd
    exact ⟨Nat.pos_of_dvd_of_pos hld (by omega), le_trans (Nat.le_of_dvd (by omega) hld) hdt⟩
  have hpoint : ∀ d ∈ Finset.Icc 1 t, ∀ e ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
          / (Nat.lcm d e : ℝ)
        = (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            * ((ArithmeticFunction.moebius e : ℝ) / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
    intro d hd e he
    rw [Finset.mem_Icc] at hd he
    exact Commons.NumberTheory.Sieve.lcm_term (fun n => (ArithmeticFunction.moebius n : ℝ))
      (by omega) (by omega)
  unfold A W
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hpoint d hd e he))]
  exact Commons.NumberTheory.Sieve.sum_gcd_eq_sum_totient_sq (Finset.Icc 1 t) hTpos hTclosed
    (fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ))

end Work.ZeroDensity.Jutila
