import Mathlib
import Submission.Work.LinnikAreas.Density4.KappaDefs

namespace Work.LinnikAreas.Density4.KappaSum

open Finset
open scoped BigOperators

noncomputable section

/-- `κ` packaged as an arithmetic function: the pointwise product of the identity
with `∏_{p | n} (1 + 1/p)`. -/
def kappaAF : ArithmeticFunction ℝ :=
  (ArithmeticFunction.id : ArithmeticFunction ℝ).pmul
    (ArithmeticFunction.prodPrimeFactors (fun p => 1 + (1 : ℝ) / (p : ℝ)))

lemma kappaAF_apply (n : ℕ) : kappaAF n = kappaR n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [kappaAF, kappaR]
  · simp only [kappaAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply, ArithmeticFunction.prodPrimeFactors_apply hn, kappaR]

lemma kappaAF_isMult : kappaAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_id.natCast.pmul
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)

lemma kappaR_mul_of_coprime {m n : ℕ} (hcop : m.Coprime n) :
    kappaR (m * n) = kappaR m * kappaR n := by
  rw [← kappaAF_apply, ← kappaAF_apply, ← kappaAF_apply]
  exact kappaAF_isMult.map_mul_of_coprime hcop

/-- `n ↦ 1 / κ(n)` as an arithmetic function. -/
def kappaInvAF : ArithmeticFunction ℝ := ⟨fun n => (kappaR n)⁻¹, by simp [kappaR]⟩

lemma kappaInvAF_apply (n : ℕ) : kappaInvAF n = (kappaR n)⁻¹ := rfl

lemma kappaInvAF_isMult : kappaInvAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [kappaInvAF, kappaR], ?_⟩
  intro m n hm hn hcop
  change (kappaR (m * n))⁻¹ = (kappaR m)⁻¹ * (kappaR n)⁻¹
  rw [kappaR_mul_of_coprime hcop, mul_inv]

/-- Value of `κ` on a prime power: `κ(p ^ (k+1)) = p ^ k · (p + 1)`. -/
lemma kappaR_prime_pow (p k : ℕ) (hp : p.Prime) :
    kappaR (p ^ (k + 1)) = (p : ℝ) ^ k * ((p : ℝ) + 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpf : (p ^ (k + 1)).primeFactors = {p} := Nat.primeFactors_prime_pow (by omega) hp
  simp only [kappaR, hpf, prod_singleton, Nat.cast_pow]
  field_simp
  ring

/-- `d ↦ μ(d) / κ(d)` as an arithmetic function. -/
def hAF : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul kappaInvAF

lemma hAF_apply (d : ℕ) : hAF d = (ArithmeticFunction.moebius d : ℝ) / kappaR d := by
  rw [hAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply, kappaInvAF_apply,
    div_eq_mul_inv]

lemma hAF_isMult : hAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.pmul kappaInvAF_isMult

/-- The divisor-sum function `n ↦ Σ_{d | n} μ(d)/κ(d)`. -/
def LAF : ArithmeticFunction ℝ := hAF * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- The candidate right-hand side `n ↦ n / κ(n)`. -/
def RH : ArithmeticFunction ℝ :=
  (ArithmeticFunction.id : ArithmeticFunction ℝ).pmul kappaInvAF

lemma LAF_apply (n : ℕ) : LAF n = ∑ d ∈ n.divisors, hAF d := by
  rw [LAF, ArithmeticFunction.coe_mul_zeta_apply]

lemma RH_apply (n : ℕ) : RH n = (n : ℝ) / kappaR n := by
  rw [RH, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply,
    kappaInvAF_apply, div_eq_mul_inv]

lemma LAF_isMult : LAF.IsMultiplicative := hAF_isMult.mul ArithmeticFunction.isMultiplicative_zeta.natCast

lemma RH_isMult : RH.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_id.natCast.pmul kappaInvAF_isMult

lemma hAF_one : hAF 1 = 1 := by
  rw [hAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply, kappaInvAF_apply]
  simp [kappaR]

lemma hAF_prime (p : ℕ) (hp : p.Prime) : hAF p = -((p : ℝ) + 1)⁻¹ := by
  rw [hAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.moebius_apply_prime hp, kappaInvAF_apply]
  have hk : kappaR p = (p : ℝ) + 1 := by
    have := kappaR_prime_pow p 0 hp; simpa using this
  rw [hk]; ring

/-- On prime powers, the divisor-sum function agrees with `n ↦ n/κ(n)`. -/
lemma LAF_prime_pow (p j : ℕ) (hp : p.Prime) :
    LAF (p ^ (j + 1)) = RH (p ^ (j + 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [show LAF (p ^ (j + 1)) = ∑ x ∈ (p ^ (j + 1)).divisors, hAF x from
    ArithmeticFunction.coe_mul_zeta_apply]
  rw [Nat.sum_divisors_prime_pow hp]
  have hzero : ∀ x ∈ Finset.range (j + 2), x ∉ Finset.range 2 → hAF (p ^ x) = 0 := by
    intro x _ hx2
    have hx2' : 2 ≤ x := by rw [Finset.mem_range] at hx2; omega
    rw [hAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega : x ≠ 0)]
    rw [if_neg (by omega : ¬ x = 1)]
    simp
  have hsub : Finset.range 2 ⊆ Finset.range (j + 2) := by
    intro x hx; rw [Finset.mem_range] at *; omega
  rw [← Finset.sum_subset hsub hzero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  rw [hAF_one, hAF_prime p hp]
  rw [RH, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply, kappaInvAF_apply]
  rw [kappaR_prime_pow p j hp, Nat.cast_pow]
  field_simp
  ring

/-- The two multiplicative functions coincide. -/
lemma LAF_eq_RH : LAF = RH := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers LAF LAF_isMult RH RH_isMult]
  intro p i hp
  rcases i with _ | j
  · simp only [pow_zero]
    rw [LAF_apply, RH_apply, Nat.divisors_one, Finset.sum_singleton, hAF_one]
    simp [kappaR]
  · exact LAF_prime_pow p j hp

theorem kappa_divisors_identity (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) / kappaR d) =
      (n : ℝ) / kappaR n := by
  rw [← RH_apply n, ← LAF_eq_RH, LAF_apply]
  exact Finset.sum_congr rfl fun d _ => (hAF_apply d).symm

end

end Work.LinnikAreas.Density4.KappaSum
