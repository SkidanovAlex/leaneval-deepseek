import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SelbergAux
import Submission.Work.LinnikAreas.BGTZ.SelbergSteps
import Submission.Work.LinnikAreas.BGTZSetup

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

private lemma tsum_succ_mul_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' m : ℕ, ((m : ℝ) + 1) * r ^ m) = 1 / (1 - r) ^ 2 := by
  have h1 : Summable (fun m : ℕ => (m : ℝ) * r ^ m) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have h2 : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_norm_lt_one hr
  rw [show (∑' m : ℕ, ((m : ℝ) + 1) * r ^ m)
        = (∑' m : ℕ, (m : ℝ) * r ^ m) + (∑' m : ℕ, r ^ m) from by
        rw [← (h1.hasSum.add h2.hasSum).tsum_eq]; apply tsum_congr; intro m; ring]
  rw [tsum_coe_mul_geometric_of_norm_lt_one hr, tsum_geometric_of_norm_lt_one hr]
  field_simp
  ring

private lemma tsum_half_one_add_neg_one_pow {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' m : ℕ, ((1 + (-1 : ℝ) ^ m) / 2) * r ^ m) = 1 / (1 - r ^ 2) := by
  have h2' : ‖-r‖ < 1 := by rwa [norm_neg]
  have h1 : Summable (fun m : ℕ => (1 / 2) * r ^ m) :=
    (summable_geometric_of_norm_lt_one hr).mul_left _
  have h2 : Summable (fun m : ℕ => (1 / 2) * (-r) ^ m) :=
    (summable_geometric_of_norm_lt_one h2').mul_left _
  rw [show (∑' m : ℕ, ((1 + (-1 : ℝ) ^ m) / 2) * r ^ m)
        = (∑' m : ℕ, (1 / 2) * r ^ m) + (∑' m : ℕ, (1 / 2) * (-r) ^ m) from by
        rw [← (h1.hasSum.add h2.hasSum).tsum_eq]; apply tsum_congr; intro m
        rw [neg_pow]; ring]
  have hlt : |r| < 1 := by rwa [Real.norm_eq_abs] at hr
  have h1r : (1 - r) ≠ 0 := by linarith [(abs_lt.mp hlt).2]
  have h1r' : (1 + r) ≠ 0 := by linarith [(abs_lt.mp hlt).1]
  have h1r2 : (1 - r ^ 2) ≠ 0 := by nlinarith [(abs_lt.mp hlt).1, (abs_lt.mp hlt).2]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_norm_lt_one hr,
    tsum_geometric_of_norm_lt_one h2']
  field_simp [h1r, h1r', h1r2]
  ring

private lemma sum_range_neg_one_pow (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j) = (1 + (-1 : ℝ) ^ m) / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by ring, Finset.sum_range_succ, ih, pow_succ]
    ring

/-- **Closed form of `1/h(p)` for `p ∤ q`.** -/
theorem hPrime_inv_closed (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    (Work.LinnikAreas.Sieve.hPrime χ₁ p)⁻¹
      = ((1 + (χ₁ (p : ZMod q)).re) * (p : ℝ) - (χ₁ (p : ZMod q)).re) / (p : ℝ) ^ 2 := by
  obtain ⟨-, hgpos, -, -, -, -, -⟩ := Work.Sieve.gFun_theory χ₁ hreal
  have hptwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hval : χ₁ (p : ZMod q) = (((χ₁ (p : ZMod q)).re : ℝ) : ℂ) := by
    rcases (Work.LinnikAreas.charValTri χ₁ hreal (p : ZMod q)).1 with h | h | h <;>
      rw [h] <;> simp
  have hu : IsUnit (p : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have hne : χ₁ (p : ZMod q) ≠ 0 := (hu.map χ₁).ne_zero
  have hre : (χ₁ (p : ZMod q)).re = 1 ∨ (χ₁ (p : ZMod q)).re = -1 := by
    rcases (Work.LinnikAreas.charValTri χ₁ hreal (p : ZMod q)).1 with h | h | h
    · exact absurd h hne
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [h]; simp)
  have ha : ∀ m, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ m)
      = ∑ j ∈ Finset.range (m + 1), ((χ₁ (p : ZMod q)).re) ^ j := by
    intro m
    rw [(Work.Sieve.aFun_basics χ₁ hreal).2.2 p m hp]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_pow, hval, ← Complex.ofReal_pow]
    simp only [Complex.ofReal_re]
  have hr : ‖(1 : ℝ) / p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hppos]; linarith
  have hAsum : (∑' m : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ m) / (p : ℝ) ^ m)
      = ∑' m : ℕ, (∑ j ∈ Finset.range (m + 1), ((χ₁ (p : ZMod q)).re) ^ j)
          * ((1 : ℝ) / p) ^ m := by
    apply tsum_congr; intro m
    rw [ha m, div_pow, one_pow, mul_one_div, div_eq_mul_inv]
  have hA : (∑' m : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ m) / (p : ℝ) ^ m)
      = 1 / ((1 - 1 / (p : ℝ)) * (1 - (χ₁ (p : ZMod q)).re / (p : ℝ))) := by
    rw [hAsum]
    rcases hre with he | he
    · rw [he]
      rw [show (∑' m : ℕ, (∑ j ∈ Finset.range (m + 1), (1 : ℝ) ^ j) * ((1 : ℝ) / p) ^ m)
            = ∑' m : ℕ, ((m : ℝ) + 1) * ((1 : ℝ) / p) ^ m from by
            apply tsum_congr; intro m
            have h1 : (∑ j ∈ Finset.range (m + 1), (1 : ℝ) ^ j) = (m : ℝ) + 1 := by
              simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
              push_cast; ring
            rw [h1]]
      rw [tsum_succ_mul_geometric hr]
      congr 1
      ring
    · rw [he]
      rw [show (∑' m : ℕ, (∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j) * ((1 : ℝ) / p) ^ m)
            = ∑' m : ℕ, ((1 + (-1 : ℝ) ^ m) / 2) * ((1 : ℝ) / p) ^ m from by
            apply tsum_congr; intro m; rw [sum_range_neg_one_pow m]]
      rw [tsum_half_one_add_neg_one_pow hr]
      congr 1
      ring
  obtain ⟨-, hgpos, -, -, -, -, -⟩ := Work.Sieve.gFun_theory χ₁ hreal
  -- summability of `Σ_m f m`
  have hcard : ∀ m : ℕ, (((p ^ m).divisors.card : ℕ) : ℝ) = (m : ℝ) + 1 := by
    intro m
    rw [Nat.divisors_prime_pow hp m, Finset.card_map, Finset.card_range]
    push_cast; ring
  have hsumm : Summable (fun m : ℕ => Work.LinnikAreas.Sieve.aFun χ₁ (p ^ m) / (p : ℝ) ^ m) := by
    have hg : Summable (fun m : ℕ => ((m : ℝ) + 1) * ((1 : ℝ) / p) ^ m) := by
      have h0 := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.add
        (summable_geometric_of_norm_lt_one hr)
      refine h0.congr (fun m => ?_); ring
    refine Summable.of_nonneg_of_le
      (fun m => div_nonneg (Work.Sieve.aFun_nonneg_le_card χ₁ hreal _).1 (by positivity))
      (fun m => ?_) hg
    rw [show ((1 : ℝ) / p) ^ m = ((p : ℝ) ^ m)⁻¹ by rw [div_pow, one_pow, one_div]]
    rw [div_eq_mul_inv]
    gcongr
    rw [← hcard m]
    exact (Work.Sieve.aFun_nonneg_le_card χ₁ hreal _).2
  have hf0 : Work.LinnikAreas.Sieve.aFun χ₁ (p ^ 0) / (p : ℝ) ^ 0 = 1 := by
    simp [Work.LinnikAreas.Sieve.aFun]
  have hsplit : (∑' m : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ m) / (p : ℝ) ^ m)
      = 1 + (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ := by
    rw [Summable.tsum_eq_zero_add hsumm, hf0, Work.LinnikAreas.Sieve.gPrime, inv_inv]
  have hGpos : 0 < Work.LinnikAreas.Sieve.gPrime χ₁ p := hgpos p hp
  have hfinal : (Work.LinnikAreas.Sieve.hPrime χ₁ p)⁻¹
      = 1 - 1 / (∑' m : ℕ, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ m) / (p : ℝ) ^ m) := by
    have h1 : (1 + (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹) ≠ 0 := by positivity
    have h2 : (Work.LinnikAreas.Sieve.gPrime χ₁ p + 1) ≠ 0 := by positivity
    rw [Work.LinnikAreas.Sieve.hPrime, hsplit]
    field_simp
    ring
  rw [hfinal, hA]
  simp only [one_div, inv_inv]
  have key : 1 - (1 - (p : ℝ)⁻¹) * (1 - (χ₁ (p : ZMod q)).re / (p : ℝ))
      = ((1 + (χ₁ (p : ZMod q)).re) * (p : ℝ) - (χ₁ (p : ZMod q)).re) / (p : ℝ) ^ 2 := by
    field_simp
    ring
  exact key

/-! ## The local sieve factor at `s = 1`, `χ = χ₀` -/

private lemma cpow_neg_one_C (p : ℕ) : (p : ℂ) ^ (-(1 : ℂ)) = (p : ℂ)⁻¹ :=
  Complex.cpow_neg_one _

private lemma cpow_neg_two_C (p : ℕ) : (p : ℂ) ^ (-(2 * (1 : ℂ))) = ((p : ℂ)⁻¹) ^ 2 := by
  have h : (-(2 * (1 : ℂ))) = ((2 : ℂ) * (-1 : ℂ)) := by norm_num
  rw [h]
  exact (Complex.cpow_nat_mul (p : ℂ) 2 (-1 : ℂ)).trans (by rw [Complex.cpow_neg_one])

private lemma inv_eq_ofReal (p : ℕ) : (p : ℂ)⁻¹ = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
  norm_num

private lemma prime_char_one (p : ℕ) (hp : p.Prime) :
    (1 : DirichletCharacter ℂ q) (p : ZMod q) = if p ∣ q then 0 else 1 := by
  by_cases h : p ∣ q
  · rw [if_pos h]
    have hnu : ¬ IsUnit (p : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      exact fun hc => (Nat.Prime.coprime_iff_not_dvd hp).mp hc h
    exact MulCharClass.map_nonunit (1 : DirichletCharacter ℂ q) hnu
  · rw [if_neg h]
    have hu : IsUnit (p : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr h
    exact MulChar.one_apply hu

/-- **The local factor at `s = 1` and `χ = χ₀` is `1/h(p)` (or `0` when `p ∣ q`).** -/
theorem sieveLocal_prime_re (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (p : ℕ) (hp : p.Prime) :
    (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re
      = if p ∣ q then 0 else (Work.LinnikAreas.Sieve.hPrime χ₁ p)⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -⟩ := Work.Sieve.gFun_theory χ₁ hreal
  by_cases hpq : p ∣ q
  · rw [if_pos hpq, sieveLocal, prime_char_one p hp, if_pos hpq]
    simp
  · rw [if_neg hpq, sieveLocal, prime_char_one p hp, if_neg hpq]
    rw [cpow_neg_one_C, cpow_neg_two_C]
    simp only [mul_one, one_pow]
    rw [hPrime_inv_closed χ₁ hreal hp hpq, inv_eq_ofReal p]
    have hkey : (1 + ((χ₁ (p : ZMod q)).re : ℂ)) * (((p : ℝ)⁻¹ : ℝ) : ℂ)
        - ((χ₁ (p : ZMod q)).re : ℂ) * ((((p : ℝ)⁻¹ : ℝ) : ℂ)) ^ 2
        = ((((1 + (χ₁ (p : ZMod q)).re) * (p : ℝ)⁻¹
            - (χ₁ (p : ZMod q)).re * ((p : ℝ)⁻¹) ^ 2 : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hkey, Complex.ofReal_re]
    have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp

/-- **The product of the local factors over the primes of a squarefree `n` is `1/h(n)`
(and `0` when `n` shares a prime with `q`).** -/
theorem sieveLocal_re_prod (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (n : ℕ)
    (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re
      = if Nat.Coprime n q then (Work.LinnikAreas.Sieve.hFun χ₁ n)⁻¹ else 0 := by
  rw [Finset.prod_congr rfl (fun p hp =>
    sieveLocal_prime_re χ₁ hreal p (Nat.prime_of_mem_primeFactors hp))]
  by_cases hcq : Nat.Coprime n q
  · rw [if_pos hcq]
    have hq' : ∀ p ∈ n.primeFactors, ¬ p ∣ q := by
      intro p hp hpq
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
      have : p ∣ Nat.gcd n q := Nat.dvd_gcd hpn hpq
      rw [hcq] at this
      exact hpp.not_dvd_one this
    rw [Finset.prod_congr rfl (fun p hp => if_neg (hq' p hp)), Finset.prod_inv_distrib,
      ← Work.Sieve.hFun_squarefree χ₁ n hn]
  · rw [if_neg hcq]
    have hgcd : Nat.gcd n q ≠ 1 := fun h => hcq h
    obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpn : p ∣ n := Nat.dvd_trans hpgcd (Nat.gcd_dvd_left n q)
    have hpq : p ∣ q := Nat.dvd_trans hpgcd (Nat.gcd_dvd_right n q)
    exact Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne_zero⟩) (by rw [if_pos hpq])

end Work.LinnikAreas.BGTZ
