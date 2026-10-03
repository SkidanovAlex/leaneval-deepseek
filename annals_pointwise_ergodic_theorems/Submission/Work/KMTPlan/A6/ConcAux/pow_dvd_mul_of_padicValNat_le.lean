import Mathlib

namespace Work.KMTPlan.A6.ConcAux

/-- If `p ^ k ∣ M * g` and the `p`-adic valuation of `M` is at most `c`, then
`p ^ k ∣ p ^ c * g`: indeed `k ≤ v_p(M) + v_p(g) ≤ c + v_p(g) = v_p(p ^ c * g)`. -/
theorem pow_dvd_mul_of_padicValNat_le (p k c : ℕ) [Fact p.Prime] {M g : ℤ}
    (hM : M ≠ 0) (hg : g ≠ 0) (h : (p : ℤ) ^ k ∣ M * g)
    (hv : padicValNat p M.natAbs ≤ c) :
    (p : ℤ) ^ k ∣ (p : ℤ) ^ c * g := by
  have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
  have hMg : M * g ≠ 0 := mul_ne_zero hM hg
  have hpc : (p : ℤ) ^ c ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp0)
  -- `h` upgrades to the valuation inequality `k ≤ v_p (M * g)`
  have hk : k ≤ padicValInt p (M * g) := by
    rcases (padicValInt_dvd_iff k (M * g)).mp h with h' | h'
    · exact absurd h' hMg
    · exact h'
  -- multiplicativity of the valuation
  have hvmul : padicValInt p (M * g) = padicValInt p M + padicValInt p g :=
    padicValInt.mul hM hg
  have hvM : padicValInt p M ≤ c := hv
  have hpcval : padicValInt p ((p : ℤ) ^ c) = c := by
    rw [show (p : ℤ) ^ c = ((p ^ c : ℕ) : ℤ) from by push_cast; ring]
    rw [padicValInt.of_nat, padicValNat.prime_pow]
  have hkey : k ≤ padicValInt p ((p : ℤ) ^ c * g) := by
    rw [padicValInt.mul hpc hg, hpcval]
    omega
  exact (padicValInt_dvd_iff k ((p : ℤ) ^ c * g)).mpr (Or.inr hkey)

end Work.KMTPlan.A6.ConcAux
