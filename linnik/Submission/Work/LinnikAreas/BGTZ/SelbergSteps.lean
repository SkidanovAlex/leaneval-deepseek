import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SelbergAux
import Submission.Work.Sieve.G_at_one_defs

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

private lemma chi_pow_eq_zero_of_dvd (χ₁ : DirichletCharacter ℂ q) {p m : ℕ}
    (hp : p.Prime) (hpq : p ∣ q) (hm : 1 ≤ m) :
    χ₁ (((p : ℕ) ^ m : ℕ) : ZMod q) = 0 := by
  have hnotcop : ¬ Nat.Coprime (p ^ m) q := by
    intro hc
    have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
    have hd : p ∣ Nat.gcd (p ^ m) q := Nat.dvd_gcd h1 hpq
    have hg : Nat.gcd (p ^ m) q = 1 := hc
    rw [hg] at hd
    exact hp.not_dvd_one hd
  have hnu : ¬ IsUnit (((p ^ m : ℕ) : ZMod q)) := by rwa [ZMod.isUnit_iff_coprime]
  rw [MulCharClass.map_nonunit _ hnu]

private lemma aFun_primePow_eq_one_of_dvd (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    {p k : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hk : 1 ≤ k) :
    Work.LinnikAreas.Sieve.aFun χ₁ (p ^ k) = 1 := by
  have hfun : ∀ j, (χ₁ (((p : ZMod q)) ^ j)).re = if j = 0 then (1 : ℝ) else 0 := by
    intro j
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      rw [pow_zero, MulChar.map_one]
      simp
    · rw [if_neg (by omega), show χ₁ ((p : ZMod q) ^ j) = 0 from by
          rw [← Nat.cast_pow]; exact chi_pow_eq_zero_of_dvd χ₁ hp hpq h]
      simp
  rw [(Work.Sieve.aFun_basics χ₁ hreal).2.2 p k hp, Finset.sum_congr rfl (fun j _ => hfun j)]
  rw [Finset.sum_eq_single 0 (by intro i hi hne; simp [hne])
    (by intro h; exact absurd (Finset.mem_range.mpr (by omega : 0 < k + 1)) h)]
  simp

private lemma tsum_geom_one_div (p : ℕ) (hp : 2 ≤ p) :
    (∑' k : ℕ, (1 : ℝ) / (p : ℝ) ^ (k + 1)) = 1 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hr0 : 0 ≤ (1 : ℝ) / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one hppos]; linarith
  have h1 : (∑' k : ℕ, (1 : ℝ) / (p : ℝ) ^ (k + 1)) = ∑' k : ℕ, ((1 : ℝ) / p) ^ (k + 1) := by
    apply tsum_congr; intro k; rw [div_pow, one_pow]
  have h2 : (∑' k : ℕ, ((1 : ℝ) / p) ^ (k + 1))
      = (∑' k : ℕ, ((1 : ℝ) / p) ^ k) * ((1 : ℝ) / p) := by
    rw [← tsum_mul_right]; apply tsum_congr; intro k; rw [pow_succ]
  rw [h1, h2, tsum_geometric_of_lt_one hr0 hr1]
  field_simp

/-- **Local values of `g` and `h`.** -/
theorem gPrime_local (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) :
    (∀ p : ℕ, p.Prime → 0 < Work.LinnikAreas.Sieve.gPrime χ₁ p ∧
      (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ =
        ∑' k : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1)) ∧
    (∀ p : ℕ, p.Prime → p ∣ q → Work.LinnikAreas.Sieve.gPrime χ₁ p = (p : ℝ) - 1 ∧
      Work.LinnikAreas.Sieve.hPrime χ₁ p = (p : ℝ)) ∧
    (∀ p k : ℕ, p.Prime → p ∣ q → 1 ≤ k → Work.LinnikAreas.Sieve.aFun χ₁ (p ^ k) = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    refine ⟨(Work.Sieve.gFun_theory χ₁ hreal).2.1 p hp, ?_⟩
    rw [Work.LinnikAreas.Sieve.gPrime]
    exact inv_inv _
  · intro p hp hpq
    have hseries : (∑' k : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1))
        = 1 / ((p : ℝ) - 1) := by
      rw [show (∑' k : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1))
            = ∑' k : ℕ, (1 : ℝ) / (p : ℝ) ^ (k + 1) from by
            apply tsum_congr; intro k
            rw [aFun_primePow_eq_one_of_dvd χ₁ hreal hp hpq (by omega)]]
      exact tsum_geom_one_div p hp.two_le
    have hg : Work.LinnikAreas.Sieve.gPrime χ₁ p = (p : ℝ) - 1 := by
      rw [Work.LinnikAreas.Sieve.gPrime, hseries, one_div, inv_inv]
    exact ⟨hg, by rw [Work.LinnikAreas.Sieve.hPrime, hg]; ring⟩
  · intro p k hp hpq hk
    exact aFun_primePow_eq_one_of_dvd χ₁ hreal hp hpq hk

/-- **`Q(χ₁) = q/φ(q)`.** -/
theorem Qfun_eq_totient_div (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) :
    Work.Sieve.Qfun χ₁ = (q : ℝ) / (Nat.totient q : ℝ) := by
  have hloc := gPrime_local χ₁ hreal
  have hone : ∀ p ∈ q.primeFactors, (1 + (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹)
      = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
    rw [(hloc.2.1 p hpp hpq).1]
    have hp1 : ((p : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      linarith
    rw [eq_div_iff hp1, add_mul, one_mul, inv_mul_cancel₀ hp1]
    ring
  rw [Work.Sieve.Qfun, Finset.prod_congr rfl hone, Finset.prod_div_distrib]
  have hP : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) :=
    Nat.cast_prod _ _
  have hQ : ((∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [Nat.cast_sub hp1]
    ring_nf
  rw [← hP, ← hQ]
  have hB : ((∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  have hD : ((Nat.totient q : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt ((Nat.totient_pos).mpr (Nat.pos_of_ne_zero (NeZero.ne q))))
  rw [div_eq_div_iff hB hD]
  have hnat : ((Nat.totient q : ℕ) : ℝ) * ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ)
      = (q : ℝ) * ((∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_mul_prod_primeFactors q
  linear_combination hnat

end Work.LinnikAreas.BGTZ
