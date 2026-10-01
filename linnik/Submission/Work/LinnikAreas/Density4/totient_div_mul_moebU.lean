import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs
import Submission.Work.LinnikAreas.Density4.moebU_eq_inv_prod

namespace Work.LinnikAreas.Density4

open Finset

/-- Euler's product formula in the form `φ(r)/r = ∏_{p ∣ r} (1 - 1/p)`. -/
lemma totient_div_self_eq_prod (r : ℕ) (hr : 1 ≤ r) :
    (r.totient : ℝ) / (r : ℝ) = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0:ℕ) < r := by omega
    exact_mod_cast this.ne'
  have h := Nat.totient_eq_mul_prod_factors r
  have hR : (r.totient : ℝ) = (r : ℝ) * ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    simpa using this
  rw [hR, mul_div_cancel_left₀ _ hr0]

/-- The local factor identity `(1 - 1/p)(1 - 1/p²)⁻¹ = (1 + 1/p)⁻¹` for a prime `p`. -/
lemma one_sub_inv_mul_one_sub_inv_sq_inv {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ) ^ 2)⁻¹ = (1 + 1 / (p : ℝ))⁻¹ := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have h1p : (1:ℝ) - 1/(p:ℝ) ≠ 0 := by
    have : 1/(p:ℝ) < 1 := by rw [div_lt_one (by positivity)]; exact hp1
    linarith
  have h2 : (1:ℝ) - 1/(p:ℝ)^2 ≠ 0 := by
    have : 1/(p:ℝ)^2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have h3 : (p:ℝ)^2 - 1 ≠ 0 := by
    have : (1:ℝ) < (p:ℝ)^2 := by nlinarith
    linarith
  field_simp
  ring

theorem totient_div_mul_moebU (r : ℕ) (hr : 1 ≤ r) :
    ((r.totient : ℝ) / (r : ℝ)) * moebU r
      = zeta2⁻¹ * ((r : ℝ) / ((r : ℝ) * ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)))) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0:ℕ) < r := by omega
    exact_mod_cast this.ne'
  rw [moebU_eq_inv_prod r hr, totient_div_self_eq_prod r hr]
  have hM : (r : ℝ) / ((r : ℝ) * ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)))
      = ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hr0, one_mul]
  rw [hM]
  have hL : (∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)))
        * (zeta2⁻¹ * ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹)
      = zeta2⁻¹ * ((∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)))
        * ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹) := by ring
  rw [hL, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  exact one_sub_inv_mul_one_sub_inv_sq_inv (Nat.prime_of_mem_primeFactors hp)

end Work.LinnikAreas.Density4
