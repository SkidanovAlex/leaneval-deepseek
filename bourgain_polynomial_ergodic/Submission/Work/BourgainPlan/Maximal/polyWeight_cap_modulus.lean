import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.ExponentialSums.integer_poly_complete_sum_bound
import Submission.Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod

/-!
# Cap for the complete sums of modulus `q·c` with numerator `a + s·q`

This file proves `Work.BourgainPlan.Maximal.polyWeight_cap_modulus`: for an integer polynomial
`P : ℤ[X]` of degree `d ≥ 2` with leading coefficient `c = P.leadingCoeff > 0` there is `A > 0`
such that for every `q ≥ 2^m`, every integer `a` coprime to `q` and every integer `s`,

`‖W_{q·c}(a + s·q)‖ ≤ A · 2^{−mσ}`,  `σ = 2^{−(d+1)}`,

where `W_Q(b) = Q⁻¹ ∑_{r<Q} e(b·P(r)/Q)` is the complete sum of modulus `Q`.

This is the weight decay driving the dyadic `q`-block decomposition of the major-arc model
(Bourgain 1989, (6.18)).  It is the block-free form of the cap: no upper bound `q < 2^{m+1}` is
needed, since the exponent comparison uses only `Q' ≥ q ≥ 2^m`.

The proof is the standard reduction of the modulus to lowest terms:

* with `Q = q·c` and `A = a + s·q` one has `gcd(A, q) = gcd(a, q) = 1`; hence any common divisor of
  `A` and `Q = q·c` is coprime to `q`, therefore divides `c`, and the reduced denominator
  `Q' = Q/g` satisfies `Q' ≥ q·c/c = q ≥ 2^m`;
* the summand `r ↦ e(A·P(r)/Q)` is `Q'`-periodic (`exp_eval_div_eq_exp_eval_mod`), so that
  `W_Q(A) = W_{Q'}(b')` with `b' = A/g`, `gcd(b', Q') = 1`;
* `integer_poly_complete_sum_bound` applied with `ε = σ` bounds `W_{Q'}(b')` by
  `C·(Q')^{−1/2^{d−1}+σ}`; since `2σ ≤ 2^{−(d−1)}` the exponent `−1/2^{d−1}+σ` is `≤ −σ ≤ 0`, and
  monotonicity of `x ↦ x^α` for `α ≤ 0` turns `Q' ≥ 2^m` into `(Q')^{α} ≤ 2^{−mσ}`.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open Commons.Analysis.ExponentialSums

set_option autoImplicit false

/-! ## The summand: two spellings of the same phase, and periodicity -/

/-- The phase of the complete sum is `↑((b/Q)·P(r))`, which is also the complex product
`↑b/↑Q · ↑P(r)`; `integer_poly_complete_sum_bound` uses the latter spelling. -/
lemma polyWeightCap_exp_bridge (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) (r : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I *
        (((b : ℝ) : ℂ) / ((Q : ℝ) : ℂ) * (((P.eval (r : ℤ) : ℤ) : ℝ) : ℂ))) := by
  congr 1
  push_cast
  ring

/-- The summand of `polyWeight` with modulus `Q` and numerator `b` is `Q`-periodic in `r`. -/
lemma polyWeightCap_summand_period (P : Polynomial ℤ) {Q : ℕ} (hQ : 0 < Q) (b : ℤ) (r : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval ((r + Q : ℕ) : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
  have h := exp_eval_div_eq_exp_eval_mod P Q hQ b 1 (r : ℤ)
  rw [show Complex.exp (2 * Real.pi * Complex.I *
        ((b : ℂ) * ((P.eval (1 * (Q : ℤ) + (r : ℤ)) : ℤ) : ℂ) / (Q : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (1 * (Q : ℤ) + (r : ℤ)) : ℤ) : ℝ) : ℝ) : ℂ)) by
    congr 1; push_cast; ring] at h
  rw [show Complex.exp (2 * Real.pi * Complex.I *
        ((b : ℂ) * ((P.eval (r : ℤ) : ℤ) : ℂ) / (Q : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) by
    congr 1; push_cast; ring] at h
  rwa [show ((r + Q : ℕ) : ℤ) = 1 * (Q : ℤ) + (r : ℤ) by push_cast; ring]

/-- A sum of a `Q`-periodic function over `Q * k` consecutive values is `k` times the sum over one
period. -/
lemma polyWeightCap_sum_range_mul (F : ℕ → ℂ) {Q : ℕ} (hF : ∀ r, F (r + Q) = F r) (k : ℕ) :
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

/-- **Period reduction of a complete sum.**  If `Q' ∣ Q`, `Q' > 0`, `Q > 0` and `b/Q = b'/Q'` (as
rationals), then `polyWeight P Q b = polyWeight P Q' b'`. -/
lemma polyWeightCap_eq_of_dvd (P : Polynomial ℤ) {Q Q' : ℕ} (hQ' : 0 < Q') (hQ : 0 < Q)
    (hdvd : Q' ∣ Q) {b b' : ℤ} (hb : b * (Q' : ℤ) = b' * (Q : ℤ)) :
    polyWeight P Q b = polyWeight P Q' b' := by
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [mul_zero] at hk; omega
    · exact h
  have hQ'R : (Q' : ℝ) ≠ 0 := by positivity
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  have hdiv : (b : ℝ) / (Q : ℝ) = (b' : ℝ) / (Q' : ℝ) := by
    rw [div_eq_div_iff hQR hQ'R]
    have hbc : (b : ℝ) * (Q' : ℝ) = (b' : ℝ) * (Q : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hb
      push_cast at h
      exact h
    linear_combination hbc
  let F : ℕ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I *
    ((((b' : ℝ) / (Q' : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
  have hper : ∀ r, F (r + Q') = F r := fun r => polyWeightCap_summand_period P hQ' b' r
  have hunit : (∑ r ∈ Finset.range Q, Complex.exp (2 * Real.pi * Complex.I *
        ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)))
      = ∑ r ∈ Finset.range Q, F r := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    dsimp only [F]
    rw [hdiv]
  have hunit' : (∑ r ∈ Finset.range Q', Complex.exp (2 * Real.pi * Complex.I *
        ((((b' : ℝ) / (Q' : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)))
      = ∑ r ∈ Finset.range Q', F r := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    dsimp only [F]
  have hS : (∑ r ∈ Finset.range (Q' * k), F r) = (k : ℂ) * ∑ r ∈ Finset.range Q', F r :=
    polyWeightCap_sum_range_mul F hper k
  have hkey : (Q : ℂ)⁻¹ * (∑ r ∈ Finset.range Q, F r)
      = (Q' : ℂ)⁻¹ * (∑ r ∈ Finset.range Q', F r) := by
    rw [hk, hS, Nat.cast_mul, mul_inv_rev]
    rw [show (k : ℂ)⁻¹ * (Q' : ℂ)⁻¹ * ((k : ℂ) * (∑ r ∈ Finset.range Q', F r))
        = (Q' : ℂ)⁻¹ * ((k : ℂ)⁻¹ * (k : ℂ) * (∑ r ∈ Finset.range Q', F r)) by ring,
      inv_mul_cancel₀ (by exact_mod_cast hkpos.ne' : (k : ℂ) ≠ 0), one_mul]
  calc polyWeight P Q b = (Q : ℂ)⁻¹ * (∑ r ∈ Finset.range Q, F r) := by
        unfold polyWeight; rw [hunit]
    _ = (Q' : ℂ)⁻¹ * (∑ r ∈ Finset.range Q', F r) := hkey
    _ = polyWeight P Q' b' := by unfold polyWeight; rw [hunit']

/-! ## The cap -/

/-- **Cap for the complete sums of modulus `q·c` with numerator `a + s·q`.**  Let `P : ℤ[X]` have
degree `d ≥ 2` and leading coefficient `c = P.leadingCoeff > 0`.  For every `q ≥ 2^m`, every `a` with
`gcd a q = 1` and every integer `s`,

`‖polyWeight P (q·c) (a + s·q)‖ ≤ A · 2^{−mσ}`,  `σ = 2^{−(d+1)}`,  `A = A(P) > 0`.

This is the weight decay driving the dyadic `q`-block decomposition of the major-arc model (Bourgain
1989, (6.18)). -/
theorem polyWeight_cap_modulus (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) (a : ℤ) (s : ℤ) (m : ℕ), 2 ^ m ≤ q → Int.gcd a (q : ℤ) = 1 →
      ‖Work.BourgainPlan.Maximal.polyWeight P (q * P.leadingCoeff.toNat) (a + s * (q : ℤ))‖
        ≤ A * (2 : ℝ) ^ (-(m : ℝ) * ((2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)))) := by
  set σ : ℝ := (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)) with hσdef
  have hσpos : 0 < σ := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    integer_poly_complete_sum_bound P.natDegree hd (ε := σ) hσpos P rfl
  refine ⟨C₀, hC₀pos, ?_⟩
  intro q a s m h2m hgcd
  -- ### Notations
  set c : ℤ := P.leadingCoeff with hcdef
  have hcpos : 0 < c := hc
  set Cn : ℕ := c.toNat with hCndef
  have hCncast : (Cn : ℤ) = c := by rw [hCndef]; exact Int.toNat_of_nonneg hcpos.le
  have hCnpos : 0 < Cn := by
    have : (0 : ℤ) < (Cn : ℤ) := by rw [hCncast]; exact hcpos
    exact_mod_cast this
  have hq1 : 1 ≤ q := le_trans Nat.one_le_two_pow h2m
  set Q : ℕ := q * Cn with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; exact Nat.mul_pos (by omega) hCnpos
  set A : ℤ := a + s * (q : ℤ) with hAdef
  -- ### `A` is coprime to `q`
  have hAcoprime : Int.gcd A (q : ℤ) = 1 := by
    have h := Int.gcd_add_mul_left_left (m := (q : ℤ)) (n := a) (k := s)
    rw [hAdef]
    rw [show a + s * (q : ℤ) = a + (q : ℤ) * s by ring]
    rw [h]
    exact hgcd
  -- ### Reduce `A/Q` to lowest terms
  have hgQpos : 0 < Int.gcd A (Q : ℤ) := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.gcd_pos_of_pos_right _ hQpos
  obtain ⟨g, b', Q'', hgpos, hcopbQ, hAeq, hQeq⟩ :=
    Int.exists_gcd_one' (m := A) (n := (Q : ℤ)) hgQpos
  have hQ''pos : 0 < Q'' := by
    by_contra h
    push_neg at h
    have hle : Q'' * (g : ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith [hQeq, hle]
  set Q' : ℕ := Q''.toNat with hQ'def
  have hQ'cast : (Q' : ℤ) = Q'' := by rw [hQ'def]; exact Int.toNat_of_nonneg hQ''pos.le
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
  -- ### `g ∣ c`
  have hgA : g ∣ A.natAbs := by
    have h1 : (g : ℤ) ∣ A := ⟨b', by rw [hAeq]; ring⟩
    simpa using (Int.natAbs_dvd_natAbs (a := (g : ℤ)) (b := A)).mpr h1
  have hcopAq : Nat.gcd A.natAbs q = 1 := by
    have := hAcoprime
    rwa [Int.gcd_eq_natAbs, Int.natAbs_natCast] at this
  have hcopgq : Nat.Coprime g q := by
    have h1 : Nat.gcd g q ∣ Nat.gcd A.natAbs q :=
      Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left g q) hgA) (Nat.gcd_dvd_right g q)
    rw [hcopAq] at h1
    exact Nat.dvd_one.mp h1
  have hgdvdQ : g ∣ Q := ⟨Q', by rw [hQeqN]; ring⟩
  have hgdvdCn : g ∣ Cn := by
    have hmul : g ∣ q * Cn := by rw [← hQdef]; exact hgdvdQ
    exact (Nat.Coprime.dvd_mul_left (k := g) (n := Cn) hcopgq).mp hmul
  -- ### `Q' ≥ q ≥ 2^m`
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
  have hσeq : σ = ((2 : ℝ) ^ (P.natDegree + 1))⁻¹ := by
    rw [hσdef]
    rw [show -((P.natDegree : ℝ) + 1) = -(((P.natDegree + 1 : ℕ) : ℝ)) by push_cast; ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hσle : 2 * σ ≤ 1 / (2 : ℝ) ^ (P.natDegree - 1) := by
    rw [hσeq]
    have hpow : (2 : ℝ) ^ (P.natDegree + 1) = (2 : ℝ) ^ (P.natDegree - 1) * 4 := by
      rw [show P.natDegree + 1 = (P.natDegree - 1) + 2 by omega, pow_add]
      norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (P.natDegree - 1) := by positivity
    rw [hpow, one_div]
    have h2 : 2 * (((2 : ℝ) ^ (P.natDegree - 1)) * 4)⁻¹
        = (((2 : ℝ) ^ (P.natDegree - 1)))⁻¹ / 2 := by
      field_simp
      ring
    rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hinv : 0 < ((2 : ℝ) ^ (P.natDegree - 1))⁻¹ := inv_pos.mpr hpos
    linarith [hinv]
  have hσle' : -(1 / (2 : ℝ) ^ (P.natDegree - 1)) + σ ≤ -σ := by linarith [hσle]
  have hαneg : -(1 / (2 : ℝ) ^ (P.natDegree - 1)) + σ ≤ 0 := by linarith [hσle', hσpos]
  have hpow_le : (Q' : ℝ) ^ (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + σ)
      ≤ (2 : ℝ) ^ (-(m : ℝ) * σ) := by
    have h2mR : (2 : ℝ) ^ m ≤ (q : ℝ) := by exact_mod_cast h2m
    have hqQ' : (q : ℝ) ≤ (Q' : ℝ) := by exact_mod_cast hQ'ge
    have hbase : (2 : ℝ) ^ m ≤ (Q' : ℝ) := le_trans h2mR hqQ'
    have h1 := Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ) ^ m)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ m) hbase hαneg
    rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
    refine le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
    have hmul : (m : ℝ) * (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + σ)
        ≤ (m : ℝ) * (-σ) :=
      mul_le_mul_of_nonneg_left hσle' (Nat.cast_nonneg m)
    linarith [hmul]
  -- ### Assembly
  have hred : polyWeight P Q A = polyWeight P Q' b' :=
    polyWeightCap_eq_of_dvd (P := P) (Q := Q) (Q' := Q') hQ'pos hQpos hQ'dvd hb_eq
  have hbound : ‖polyWeight P Q' b'‖
      ≤ C₀ * (Q' : ℝ) ^ (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + σ) := by
    have h := hC₀ Q' b' hQ'1 hcop'
    simp only [← polyWeightCap_exp_bridge P Q' b'] at h
    unfold polyWeight
    exact h
  calc ‖polyWeight P Q A‖ = ‖polyWeight P Q' b'‖ := by rw [hred]
    _ ≤ C₀ * (Q' : ℝ) ^ (-(1 / (2 : ℝ) ^ (P.natDegree - 1)) + σ) := hbound
    _ ≤ C₀ * (2 : ℝ) ^ (-(m : ℝ) * σ) :=
        mul_le_mul_of_nonneg_left hpow_le hC₀pos.le

end Work.BourgainPlan.Maximal
