import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Commons.Analysis.ExponentialSums.integer_poly_complete_sum_bound
import Submission.Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod

/-!
# The complete-sum weight cap on a dyadic block (`c`-scaled modulus)

This file proves `Work.BourgainPlan.Maximal.poly_weight_cap_block`: on the dyadic block
`2^m ≤ q < 2^{m+1}` the complete sums `W_{q·c}(a + s·q)` of modulus `q·c`
(`c = P.leadingCoeff`) decay like `2^{-m·σ}`, `σ = polySig P = 2^{-(d+1)}`, uniformly in the
block.

The proof is the standard reduction of the modulus to lowest terms:

* `g = gcd(b, Q)` with `Q = q·c`, `b = a + s·q`; because `gcd(b, q) = gcd(a, q) = 1` one has
  `g = gcd(b, c) ∣ c`, so `Q' = Q/g ≥ c·q/c = q ≥ 2^m`;
* the summand `r ↦ e(b·P(r)/Q)` is `Q'`-periodic (`exp_eval_div_eq_exp_eval_mod`), hence
  `W_Q(b) = W_{Q'}(b')` with `b' = b/g`, `gcd(b', Q') = 1`;
* `integer_poly_complete_sum_bound` applies to `W_{Q'}(b')` with `ε = σ`, and the exponents
  compare because `2σ ≤ 2^{-(d-1)}`.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open Commons.Analysis.ExponentialSums

set_option autoImplicit false

/-! ## Auxiliary computation lemmas -/

/-- The complex form `2πi·(b·z/q)` of a rational phase agrees with its real form. -/
lemma polyExp_phase_int_div (b : ℤ) (Q : ℕ) (z : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((b : ℂ) * (z : ℂ) / (Q : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I *
          ((((b : ℝ) / (Q : ℝ)) * (z : ℝ) : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

/-- The summand of `polyWeight` with modulus `Q` and numerator `b` is `Q`-periodic in `r`. -/
lemma polyWeight_summand_period (P : Polynomial ℤ) {Q : ℕ} (hQ : 0 < Q) (b : ℤ) (r : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval ((r + Q : ℕ) : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
  have h := exp_eval_div_eq_exp_eval_mod P Q hQ b 1 (r : ℤ)
  rw [polyExp_phase_int_div b Q (P.eval (1 * (Q : ℤ) + (r : ℤ)))] at h
  rw [polyExp_phase_int_div b Q (P.eval (r : ℤ))] at h
  rwa [show ((r + Q : ℕ) : ℤ) = 1 * (Q : ℤ) + (r : ℤ) by push_cast; ring]

/-- `polyWeight` written with the complex (rather than real) form of its phase; this is the shape
in which `integer_poly_complete_sum_bound` is stated. -/
lemma polyWeight_apply (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) :
    polyWeight P Q b = ((Q : ℂ))⁻¹ * ∑ r ∈ Finset.range Q,
      Complex.exp (2 * Real.pi * Complex.I *
        ((b : ℂ) / (Q : ℂ) * ((P.eval (r : ℤ) : ℤ) : ℂ))) := by
  have hterm : ∀ r : ℕ,
      Complex.exp (2 * Real.pi * Complex.I *
          ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
          ((b : ℂ) / (Q : ℂ) * ((P.eval (r : ℤ) : ℤ) : ℂ))) := by
    intro r
    congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_div]
    push_cast
    ring
  unfold polyWeight
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]

/-- A sum of a `Q`-periodic function over `Q * k` consecutive values is `k` times the sum over
one period. -/
lemma polyWeight_periodic_sum_range (F : ℕ → ℂ) {Q : ℕ} (hF : ∀ r, F (r + Q) = F r) (k : ℕ) :
    ∑ r ∈ Finset.range (Q * k), F r = (k : ℂ) * ∑ r ∈ Finset.range Q, F r := by
  have hshift : ∀ k r : ℕ, F (Q * k + r) = F r := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
      intro r
      rw [Nat.mul_succ]
      rw [show Q * k + Q + r = (Q * k + r) + Q by ring]
      rw [hF (Q * k + r), ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [hshift]
    push_cast
    ring

/-- **Period reduction of a complete sum.**  If `Q' ∣ Q`, `Q, Q' > 0` and `b/Q = b'/Q'` (as
rationals), then `polyWeight P Q b = polyWeight P Q' b'`. -/
lemma polyWeight_eq_of_dvd (P : Polynomial ℤ) {Q Q' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (hdvd : Q' ∣ Q) {b b' : ℤ} (hb : b * (Q' : ℤ) = b' * (Q : ℤ)) :
    polyWeight P Q b = polyWeight P Q' b' := by
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [mul_zero] at hk; omega
    · exact h
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  have hQ'R : (Q' : ℝ) ≠ 0 := by positivity
  have hdiv : (b : ℝ) / (Q : ℝ) = (b' : ℝ) / (Q' : ℝ) := by
    rw [div_eq_div_iff hQR hQ'R]
    have hbc := congrArg (fun z : ℤ => (z : ℝ)) hb
    push_cast at hbc
    exact hbc
  have hE : ∀ r : ℕ,
      Complex.exp (2 * Real.pi * Complex.I *
          ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
          ((((b' : ℝ) / (Q' : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
    intro r
    congr 1
    rw [hdiv]
  have hper : ∀ r : ℕ,
      Complex.exp (2 * Real.pi * Complex.I *
          ((((b' : ℝ) / (Q' : ℝ)) * ((P.eval ((r + Q' : ℕ) : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
          ((((b' : ℝ) / (Q' : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) :=
    fun r => polyWeight_summand_period P hQ' b' r
  have hsum : (∑ r ∈ Finset.range Q, Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)))
      = (k : ℂ) * ∑ r ∈ Finset.range Q', Complex.exp (2 * Real.pi * Complex.I *
        ((((b' : ℝ) / (Q' : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
    refine Eq.trans (Finset.sum_congr rfl (fun r _ => hE r)) ?_
    rw [hk]
    exact polyWeight_periodic_sum_range _ hper k
  have hcoef : (Q : ℂ) = (Q' : ℂ) * (k : ℂ) := by rw [hk]; push_cast; ring
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hQ'C : (Q' : ℂ) ≠ 0 := by exact_mod_cast hQ'.ne'
  unfold polyWeight
  rw [hsum, hcoef]
  field_simp

/-! ## The weight cap -/

/-- **Weight cap on a dyadic block (`c`-scaled modulus).**  For an integer polynomial `P` of degree `d ≥ 2` with `c = P.leadingCoeff > 0` there is `A > 0` such that for every `m`, every `q` with `2^m ≤ q < 2^{m+1}`, every `a` coprime to `q` and every `s < c`, the complete sum of modulus `q·c` at the numerator `a + s·q` satisfies `‖W_{q·c}(a + s·q)‖ ≤ A · 2^{−m σ}`, where `σ = polySig P = 2^{−(d+1)}`. -/
theorem poly_weight_cap_block (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m q a s : ℕ), 2^m ≤ q → q < 2^(m+1) → Nat.gcd a q = 1 →
      s < P.leadingCoeff.toNat →
      ‖polyWeight P (q * P.leadingCoeff.toNat) ((a : ℤ) + (s : ℤ) * (q : ℤ))‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P) := by
  have hσpos : 0 < polySig P := by
    rw [polySig, powSig]; positivity
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    integer_poly_complete_sum_bound P.natDegree hd (ε := polySig P) hσpos P rfl
  refine ⟨C₀, hC₀pos, ?_⟩
  intro m q a s h2m hqlt hgcd hs
  -- ### Notations
  set c : ℤ := P.leadingCoeff with hcdef
  have hcpos : 0 < c := hc
  set Cn : ℕ := c.toNat with hCndef
  have hCncast : (Cn : ℤ) = c := by
    rw [hCndef]; exact Int.toNat_of_nonneg hcpos.le
  have hCnpos : 0 < Cn := by
    have : (0 : ℤ) < (Cn : ℤ) := by rw [hCncast]; exact hcpos
    exact_mod_cast this
  have hq1 : 1 ≤ q := le_trans Nat.one_le_two_pow h2m
  set Q : ℕ := q * Cn with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact Nat.mul_pos (by omega) hCnpos
  set A : ℤ := (a : ℤ) + (s : ℤ) * (q : ℤ) with hAdef
  -- ### `A` is coprime to `q`
  have hAcoprime : Int.gcd A (q : ℤ) = 1 := by
    rw [hAdef]
    have hcast : (a : ℤ) + (s : ℤ) * (q : ℤ) = ((a + s * q : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
    rw [Nat.gcd_comm, Nat.gcd_add_mul_right_right, Nat.gcd_comm]
    exact hgcd
  -- ### Reduce `A/Q` to lowest terms
  have hgQpos : 0 < Int.gcd A (Q : ℤ) := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.gcd_pos_of_pos_right _ hQpos
  obtain ⟨g, b', Q'', hgpos, hcopbQ, hAeq, hQeq⟩ :=
    Int.exists_gcd_one' (m := A) (n := (Q : ℤ)) hgQpos
  have hgnn : (0 : ℤ) ≤ (g : ℤ) := by positivity
  have hQzpos : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQpos
  have hQ''pos : 0 < Q'' := by
    by_contra h
    have hle0 : Q'' ≤ 0 := by omega
    have hle : Q'' * (g : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle0 hgnn
    linarith [hQeq, hle]
  set Q' : ℕ := Q''.toNat with hQ'def
  have hQ'cast : (Q' : ℤ) = Q'' := by
    rw [hQ'def]; exact Int.toNat_of_nonneg hQ''pos.le
  have hQ'pos : 0 < Q' := by
    have : (0 : ℤ) < (Q' : ℤ) := by rw [hQ'cast]; exact hQ''pos
    exact_mod_cast this
  have hQeqN : Q = Q' * g := by
    have h : (Q : ℤ) = ((Q' * g : ℕ) : ℤ) := by
      rw [hQeq, ← hQ'cast, Nat.cast_mul]
    exact_mod_cast h
  have hQ'dvd : Q' ∣ Q := ⟨g, hQeqN⟩
  have hb_eq : A * (Q' : ℤ) = b' * (Q : ℤ) := by
    rw [hAeq, hQeq, hQ'cast]; ring
  have hcop' : Int.gcd b' (Q' : ℤ) = 1 := by
    rw [hQ'cast]; exact hcopbQ
  -- ### `Q' ≥ q`
  have hgA : g ∣ A.natAbs := by
    have h1 : (g : ℤ) ∣ A := ⟨b', by rw [hAeq]; ring⟩
    simpa using (Int.natAbs_dvd_natAbs (a := (g : ℤ)) (b := A)).mpr h1
  have hcopAq : Nat.gcd A.natAbs q = 1 := by
    have hh := hAcoprime
    rwa [Int.gcd_eq_natAbs, Int.natAbs_natCast] at hh
  have hcopgq : Nat.Coprime g q := by
    have h1 : Nat.gcd g q ∣ Nat.gcd A.natAbs q :=
      Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left g q) hgA) (Nat.gcd_dvd_right g q)
    rw [hcopAq] at h1
    exact Nat.dvd_one.mp h1
  have hgdvdQ : g ∣ Q := ⟨Q', by rw [hQeqN]; ring⟩
  have hgdvdCn : g ∣ Cn := by
    have hmul : g ∣ q * Cn := by rw [← hQdef]; exact hgdvdQ
    exact (Nat.Coprime.dvd_mul_left (k := g) (n := Cn) hcopgq).mp hmul
  obtain ⟨m', hm'⟩ := hgdvdCn
  have hm'pos : 1 ≤ m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · subst h; rw [mul_zero] at hm'; omega
    · exact h
  have hQ''ge : (q : ℤ) ≤ Q'' := by
    have hgz : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hgpos
    have hmz : (1 : ℤ) ≤ (m' : ℤ) := by exact_mod_cast hm'pos
    have hqz : (0 : ℤ) ≤ (q : ℤ) := by positivity
    have key : Q'' * (g : ℤ) = (q : ℤ) * (m' : ℤ) * (g : ℤ) := by
      rw [← hQeq, hQdef]
      push_cast
      rw [hm']
      push_cast
      ring
    have hcancel : Q'' = (q : ℤ) * (m' : ℤ) := mul_right_cancel₀ (ne_of_gt hgz) key
    nlinarith [hcancel, hmz, hqz]
  have hQ'ge : q ≤ Q' := by
    have : (q : ℤ) ≤ (Q' : ℤ) := by rw [hQ'cast]; exact hQ''ge
    exact_mod_cast this
  have hQ'1 : 1 ≤ Q' := le_trans hq1 hQ'ge
  -- ### The exponent comparison
  have hσle : 2 * polySig P ≤ 1 / (2 : ℝ) ^ (P.natDegree - 1) := by
    have hpow : (2 : ℝ) ^ (P.natDegree + 1) = (2 : ℝ) ^ (P.natDegree - 1) * 4 := by
      rw [show P.natDegree + 1 = (P.natDegree - 1) + 2 by omega, pow_add]
      norm_num
    simp only [polySig, powSig, hpow, one_div]
    have hthis : 2 * ((2 : ℝ) ^ (P.natDegree - 1) * 4)⁻¹
        = ((2 : ℝ) ^ (P.natDegree - 1))⁻¹ / 2 := by
      have hne : ((2 : ℝ) ^ (P.natDegree - 1)) ≠ 0 := by positivity
      field_simp
      ring
    rw [hthis, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact le_mul_of_one_le_right (by positivity) (by norm_num)
  have hσle' : -(1 / (2 : ℝ) ^ (P.natDegree - 1)) + polySig P ≤ -polySig P := by
    linarith [hσle]
  have hαneg : -(1 / (2 : ℝ) ^ (P.natDegree - 1)) + polySig P ≤ 0 := by
    linarith [hσle', hσpos]
  have hpow_le : (Q' : ℝ) ^ (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + polySig P)
      ≤ (2 : ℝ) ^ (-(m : ℝ) * polySig P) := by
    have h2mR : (2 : ℝ) ^ m ≤ (q : ℝ) := by exact_mod_cast h2m
    have hqQ' : (q : ℝ) ≤ (Q' : ℝ) := by exact_mod_cast hQ'ge
    have hbase : (2 : ℝ) ^ m ≤ (Q' : ℝ) := le_trans h2mR hqQ'
    have h1 := Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ) ^ m)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ m) hbase hαneg
    rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
    refine le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
    have hmul : (m : ℝ) * (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + polySig P)
        ≤ (m : ℝ) * (-polySig P) :=
      mul_le_mul_of_nonneg_left hσle' (Nat.cast_nonneg m)
    linarith [hmul]
  -- ### Assembly
  have hred : polyWeight P Q A = polyWeight P Q' b' :=
    polyWeight_eq_of_dvd (P := P) (Q := Q) (Q' := Q') (b := A) (b' := b')
      hQpos hQ'pos hQ'dvd hb_eq
  have hbound : ‖polyWeight P Q' b'‖
      ≤ C₀ * (Q' : ℝ) ^ (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + polySig P) := by
    rw [polyWeight_apply]
    exact hC₀ Q' b' hQ'1 hcop'
  calc ‖polyWeight P Q A‖ = ‖polyWeight P Q' b'‖ := by rw [hred]
    _ ≤ C₀ * (Q' : ℝ) ^ (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + polySig P) := hbound
    _ ≤ C₀ * (2 : ℝ) ^ (-(m : ℝ) * polySig P) :=
        mul_le_mul_of_nonneg_left hpow_le hC₀pos.le

end Work.BourgainPlan.Maximal
