import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.GroupAction.Ring

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma cubefree_eq_squarefree_mul_sq {d : ℕ} (hd : 0 < d)
    (hcf : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) :
    ∃ d₁ d₂ : ℕ, Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ d = d₁ * d₂ ^ 2 := by
  have hd0 : d ≠ 0 := hd.ne'
  -- Cubefreeness rephrased as a bound on the exponents in the prime factorization.
  have hf2 : ∀ p : ℕ, p.Prime → d.factorization p ≤ 2 := by
    intro p hp
    by_contra h
    push Not at h
    have hle : 3 ≤ d.factorization p := by omega
    have h1 : p ^ 3 ∣ p ^ (d.factorization p) := pow_dvd_pow p hle
    have h2 : p ^ (d.factorization p) ∣ d := (hp.pow_dvd_iff_le_factorization hd0).mpr le_rfl
    exact hcf p hp (h1.trans h2)
  -- Split each exponent e into its parity part (in `f₁`) and its half (in `f₂`).
  let f₁ : ℕ →₀ ℕ := d.factorization.mapRange (fun e => e % 2) (by simp)
  let f₂ : ℕ →₀ ℕ := d.factorization.mapRange (fun e => e / 2) (by simp)
  let d₁ : ℕ := f₁.prod (· ^ ·)
  let d₂ : ℕ := f₂.prod (· ^ ·)
  have hf₁app : ∀ p, f₁ p = d.factorization p % 2 := by intro p; simp [f₁]
  have hf₂app : ∀ p, f₂ p = d.factorization p / 2 := by intro p; simp [f₂]
  have hmem₁ : f₁.support ⊆ d.factorization.support := by
    simp only [f₁]; exact Finsupp.support_mapRange
  have hmem₂ : f₂.support ⊆ d.factorization.support := by
    simp only [f₂]; exact Finsupp.support_mapRange
  have hf₁supp : ∀ p ∈ f₁.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hmem₁ hp)
  have hf₂supp : ∀ p ∈ f₂.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hmem₂ hp)
  have hfac₁ : d₁.factorization = f₁ := Nat.prod_pow_factorization_eq_self hf₁supp
  have hfac₂ : d₂.factorization = f₂ := Nat.prod_pow_factorization_eq_self hf₂supp
  have hd₁0 : d₁ ≠ 0 := by
    change f₁.prod (· ^ ·) ≠ 0
    rw [Finsupp.prod_ne_zero_iff]
    exact fun p hp => pow_ne_zero _ (hf₁supp p hp).ne_zero
  have hd₂0 : d₂ ≠ 0 := by
    change f₂.prod (· ^ ·) ≠ 0
    rw [Finsupp.prod_ne_zero_iff]
    exact fun p hp => pow_ne_zero _ (hf₂supp p hp).ne_zero
  -- Both parts are squarefree.
  have hsq₁ : Squarefree d₁ := by
    rw [Nat.squarefree_iff_factorization_le_one hd₁0]
    intro p
    rw [hfac₁, hf₁app p]
    have := Nat.mod_lt (d.factorization p) (by norm_num : 0 < 2)
    omega
  have hsq₂ : Squarefree d₂ := by
    rw [Nat.squarefree_iff_factorization_le_one hd₂0]
    intro p
    rw [hfac₂, hf₂app p]
    by_cases hp : p.Prime
    · have := hf2 p hp; omega
    · rw [Nat.factorization_eq_zero_of_not_prime d hp]; norm_num
  -- The two parts are coprime: no prime can contribute to both.
  have hgcd0 : Nat.gcd d₁ d₂ ≠ 0 := Nat.gcd_ne_zero_left hd₁0
  have hgcdfact : (Nat.gcd d₁ d₂).factorization = 0 := by
    rw [Nat.factorization_gcd hd₁0 hd₂0]
    ext p
    rw [Finsupp.inf_apply, hfac₁, hfac₂, hf₁app p, hf₂app p, Finsupp.zero_apply]
    by_cases hp : p.Prime
    · have hcases : d.factorization p = 0 ∨ d.factorization p = 1 ∨ d.factorization p = 2 := by
        have := hf2 p hp; omega
      rcases hcases with h | h | h <;> simp [h]
    · rw [Nat.factorization_eq_zero_of_not_prime d hp]; simp
  have hcop : Nat.Coprime d₁ d₂ := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact Nat.eq_of_factorization_eq hgcd0 one_ne_zero
      (fun p => by rw [hgcdfact, Nat.factorization_one])
  -- The product reconstructs `d` because `e = e % 2 + 2 * (e / 2)`.
  have hmain : d₁ * d₂ ^ 2 = d := by
    apply Nat.eq_of_factorization_eq (mul_ne_zero hd₁0 (pow_ne_zero 2 hd₂0)) hd0
    intro p
    rw [Nat.factorization_mul hd₁0 (pow_ne_zero 2 hd₂0), Nat.factorization_pow, hfac₁, hfac₂,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hf₁app p, hf₂app p]
    exact Nat.mod_add_div (d.factorization p) 2
  exact ⟨d₁, d₂, hsq₁, hsq₂, hcop, hmain.symm⟩

end Commons.NumberTheory.FriedlanderIwaniec