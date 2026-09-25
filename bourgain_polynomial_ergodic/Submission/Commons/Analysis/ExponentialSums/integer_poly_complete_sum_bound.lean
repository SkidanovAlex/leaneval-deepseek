import Mathlib
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality
import Submission.Commons.Analysis.ExponentialSums.monic_poly_complete_sum_bound

open Finset
open scoped BigOperators

namespace Commons.Analysis.ExponentialSums

/-- The leading coefficient of the image of an integer polynomial in `ℝ[X]`. -/
lemma map_leadingCoeff_int (P : Polynomial ℤ) :
    (P.map (Int.castRingHom ℝ)).leadingCoeff = ((P.leadingCoeff : ℤ) : ℝ) := by
  rw [Polynomial.leadingCoeff,
    Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective P,
    Polynomial.coeff_map]
  rfl

/-- **Denominator reduction.**  For `c ≠ 0`, `q ≥ 1`, `gcd a q = 1`, the rational number
`a c / q` can be written as `b / Q` in lowest terms with `Q ≤ q` and `q ≤ |c| Q`. -/
lemma exists_coprime_den (c : ℤ) (hc : c ≠ 0) (q : ℕ) (hq : 1 ≤ q) (a : ℤ)
    (hgcd : Int.gcd a (q : ℤ) = 1) :
    ∃ (b : ℤ) (Q : ℕ), 1 ≤ Q ∧ Int.gcd b (Q : ℤ) = 1 ∧ Q ≤ q ∧
      (q : ℝ) ≤ (|c| : ℝ) * (Q : ℝ) ∧
      ((b : ℝ) / (Q : ℝ) = (a : ℝ) * (c : ℝ) / (q : ℝ)) := by
  set A : ℕ := (a * c).natAbs with hA
  set D : ℕ := Nat.gcd A q with hD
  have hDpos : 0 < D := by rw [hD]; exact Nat.gcd_pos_of_pos_right A (by omega)
  have hDq : D ∣ q := by rw [hD]; exact Nat.gcd_dvd_right A q
  have hDA : D ∣ A := by rw [hD]; exact Nat.gcd_dvd_left A q
  have hDle : D ≤ q := Nat.le_of_dvd (by omega) hDq
  have hg1 : Int.gcd (a * c) (q : ℤ) = D := by
    rw [hD, hA, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  have hcdvd : (D : ℤ) ∣ a * c := by rw [← hg1]; exact Int.gcd_dvd_left _ _
  have hqddvd : (D : ℤ) ∣ (q : ℤ) := by rw [← hg1]; exact Int.gcd_dvd_right _ _
  refine ⟨(a * c) / (D : ℤ), q / D, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.one_le_div_iff hDpos]; exact hDle
  · have hbmul : (a * c) / (D : ℤ) * (D : ℤ) = a * c := Int.ediv_mul_cancel hcdvd
    have hbnat : ((a * c) / (D : ℤ)).natAbs = A / D := by
      have h2 : ((a * c) / (D : ℤ)).natAbs * D = A := by
        have h3 := congrArg Int.natAbs hbmul
        rw [Int.natAbs_mul, Int.natAbs_natCast, ← hA] at h3
        exact h3
      exact Nat.eq_div_of_mul_eq_left (ne_of_gt hDpos) h2
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, hbnat]
    have hcop : (A / D).Coprime (q / D) := by
      rw [hD]
      exact Nat.coprime_div_gcd_div_gcd (by rw [← hD]; exact hDpos)
    exact hcop.gcd_eq_one
  · exact Nat.div_le_self q D
  · have hga_nat : Nat.gcd D a.natAbs = 1 := by
      have h1 : Nat.gcd D a.natAbs ∣ Nat.gcd q a.natAbs :=
        Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left D a.natAbs) hDq) (Nat.gcd_dvd_right D a.natAbs)
      have h2 : Nat.gcd q a.natAbs = 1 := by
        have h3 : Int.gcd (q : ℤ) a = 1 := by rw [Int.gcd_comm]; exact hgcd
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at h3
        exact h3
      rw [h2] at h1
      exact Nat.dvd_one.mp h1
    have hDc : (D : ℤ) ∣ c := by
      have hga : Int.gcd (D : ℤ) a = 1 := by
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
        exact hga_nat
      exact Int.dvd_of_dvd_mul_left_of_gcd_one (by simpa [mul_comm] using hcdvd) hga
    have hDleC : D ≤ c.natAbs := by
      have h5 : (D:ℤ).natAbs ∣ c.natAbs := Int.natAbs_dvd_natAbs.mpr hDc
      rw [Int.natAbs_natCast] at h5
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hc) h5
    have hDcR : (D : ℝ) ≤ (|c| : ℝ) := by
      have h4 : ((c.natAbs : ℕ) : ℝ) = (|c| : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [← h4]
      exact_mod_cast hDleC
    have hQcast : ((q / D : ℕ) : ℝ) = (q : ℝ) / (D : ℝ) :=
      Nat.cast_div hDq (by positivity)
    have hqeq : (q : ℝ) = ((q / D : ℕ) : ℝ) * (D : ℝ) := by
      rw [hQcast]; field_simp
    calc (q : ℝ) = ((q / D : ℕ) : ℝ) * (D : ℝ) := hqeq
      _ ≤ ((q / D : ℕ) : ℝ) * (|c| : ℝ) :=
          mul_le_mul_of_nonneg_left hDcR (by positivity)
      _ = (|c| : ℝ) * ((q / D : ℕ) : ℝ) := by ring
  · have hbmul : (a * c) / (D : ℤ) * (D : ℤ) = a * c := Int.ediv_mul_cancel hcdvd
    have hba : (((a * c) / (D : ℤ) : ℤ) : ℝ) * (D : ℝ) = (a : ℝ) * (c : ℝ) := by
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) hbmul
      push_cast at h3
      exact h3
    have hQcast : ((q / D : ℕ) : ℝ) = (q : ℝ) / (D : ℝ) :=
      Nat.cast_div hDq (by positivity)
    have hQq : ((q / D : ℕ) : ℝ) * (D : ℝ) = (q : ℝ) := by
      rw [hQcast]; field_simp
    have hQne : ((q / D : ℕ) : ℝ) ≠ 0 := by
      have : 1 ≤ q / D := by rw [Nat.one_le_div_iff hDpos]; exact hDle
      positivity
    have hqne : (q : ℝ) ≠ 0 := by positivity
    rw [div_eq_div_iff hQne hqne]
    rw [← hQq, ← hba]
    ring

/-- A normalized complete sum of unit-modulus terms is bounded by `1`. -/
lemma norm_inv_card_mul_sum_le_one (q : ℕ) (hq : 1 ≤ q) (F : ℕ → ℂ) (hF : ∀ r, ‖F r‖ = 1) :
    ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q, F r‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range q, F r‖
      ≤ (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, ‖F r‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (q : ℝ)⁻¹ * (q : ℝ) := by
        rw [Finset.sum_congr rfl (fun r _ => hF r), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
    _ = 1 := by
        rw [inv_mul_cancel₀ (by positivity : (q:ℝ) ≠ 0)]

/-- **Hua-type bound for the complete Weyl sum of an arbitrary integer polynomial.**  For
`P : ℤ[X]` of degree `d ≥ 2`, `q ≥ 1`, `gcd a q = 1` and any `ε > 0`,

`‖q⁻¹ ∑_{r<q} e(a P(r)/q)‖ ≤ C q^{−1/2^{d−1} + ε}`,

with a constant depending on `P`.  This follows from Weyl's inequality
(Commons.Analysis.ExponentialSums.weyl_inequality) applied with `N = q` to the real polynomial
`f = (a/q) P`: writing `q' = q / gcd(a · lead P, q)` for the denominator of `lead f` in lowest
terms (`gcd(a·lead P, q) ∣ lead P` because `gcd a q = 1`, so `q' ≥ q/|lead P|`), the four terms
of Weyl's bound are `≲ |lead P|/q`, `1/q`, `(|lead P|/q)^{d−1}` and `q^{1−d}`, giving
`≲ q^{−1/2^{d−1}} (up to q^ε)`; the small values of `q` are absorbed into the constant.  This
generalises Commons.Analysis.ExponentialSums.hua_bound (pure powers) and supplies the weight
`S(a/q)` of the major-arc approximation for an arbitrary integer polynomial. -/
theorem integer_poly_complete_sum_bound (d : ℕ) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ (P : Polynomial ℤ), P.natDegree = d →
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : ℤ), 1 ≤ q → Int.gcd a (q : ℤ) = 1 →
        ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
            Complex.exp (2 * Real.pi * Complex.I *
              ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖
          ≤ C * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + ε) := by
  intro P hPnat
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C0, hC0pos, hC0⟩ := weyl_inequality d hd1 hε (t := 1) (by norm_num)
  set θ : ℝ := (2:ℝ)^(1-(d:ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθnn : 0 ≤ θ := le_of_lt hθpos
  have hθ_eq : θ = 1 / (2:ℝ)^(d-1) := by
    rw [hθdef]
    have h1 : (1:ℝ) - (d:ℝ) = -(((d-1:ℕ):ℝ)) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    rw [h1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, one_div]
  set c : ℤ := P.leadingCoeff with hcdef
  have hPne : P ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hPnat; omega
  have hc : c ≠ 0 := by rw [hcdef]; exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  set K : ℝ := (|c| : ℝ) + 3 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨max 1 (C0 * K^θ), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro q a hq hgcd
  by_cases hq1 : q = 1
  · subst hq1
    have hbound := norm_inv_card_mul_sum_le_one 1 le_rfl
      (fun r : ℕ => Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℝ) / ((1:ℕ):ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ)))
      (fun r => norm_exp_two_pi_I_mul_ratPoly 1 a P r)
    refine le_trans hbound ?_
    rw [show ((1:ℕ):ℝ) = 1 by norm_num, Real.one_rpow, mul_one]
    exact le_max_left _ _
  · have hq2 : 2 ≤ q := by omega
    have ha : a ≠ 0 := by
      intro h0
      have h : Int.gcd (0:ℤ) (q:ℤ) = 1 := by rw [← h0]; exact hgcd
      rw [Int.gcd_zero_left, Int.natAbs_natCast] at h
      omega
    have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    obtain ⟨b, Q, hQ1, hgcdb, hQle, hqQ, hident⟩ := exists_coprime_den c hc q hq a hgcd
    have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ1
    have hQge : (1:ℤ) ≤ (Q:ℤ) := by exact_mod_cast hQ1
    have hcastQ : ((Q:ℤ):ℝ) = (Q:ℝ) := by push_cast; ring
    set f : Polynomial ℝ := Polynomial.C ((a:ℝ)/(q:ℝ)) * P.map (Int.castRingHom ℝ) with hfdef
    have hlc_ne : ((a:ℝ)/(q:ℝ)) ≠ 0 := div_ne_zero haR (ne_of_gt hqpos)
    have hf_nat : f.natDegree = d := by
      rw [hfdef, Polynomial.natDegree_C_mul hlc_ne,
        Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective P,
        hPnat]
    have hf_lc : f.leadingCoeff = (a:ℝ)/(q:ℝ) * (c:ℝ) := by
      rw [hfdef, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, map_leadingCoeff_int,
        ← hcdef]
    have hlc : |f.leadingCoeff - (b:ℝ)/((Q:ℤ))| ≤ (1:ℝ)/(((Q:ℤ)):ℝ)^2 := by
      rw [hf_lc, hcastQ]
      rw [show (a:ℝ)/(q:ℝ) * (c:ℝ) = (a:ℝ)*(c:ℝ)/(q:ℝ) by ring]
      rw [← hident, sub_self, abs_zero]
      positivity
    have hweyl := hC0 (0:ℤ) q b (Q:ℤ) f hQge hgcdb hf_nat hlc
    rw [hcastQ] at hweyl
    have hsum_eq : (∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ)))
        = ∑ x ∈ Finset.range q,
            Complex.exp (↑(2 * Real.pi * f.eval (((0:ℤ):ℝ) + (x : ℝ))) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      rw [show (((0:ℤ):ℝ) + (r:ℝ)) = (r:ℝ) by norm_num]
      have hev : f.eval ((r:ℝ)) = (a:ℝ)/(q:ℝ) * ((P.eval (r:ℤ):ℤ):ℝ) := by
        rw [hfdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
          Polynomial.eval₂_at_natCast]
        rfl
      rw [hev]
      push_cast
      ring
    have hBnn : 0 ≤ 1/(Q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (Q:ℝ)/(q:ℝ)^d := by positivity
    have h1 : 1/(Q:ℝ) ≤ (|c|:ℝ)/(q:ℝ) := by
      rw [div_le_div_iff₀ hQpos hqpos, one_mul]
      exact hqQ
    have h2 : (|c|:ℝ)/(q:ℝ) ≤ K/(q:ℝ) := by
      apply div_le_div_of_nonneg_right _ hqpos.le
      rw [hKdef]
      have : (0:ℝ) ≤ (|c|:ℝ) := by positivity
      linarith
    have h3 : 1/(q:ℝ)^(d-1) ≤ 1/(q:ℝ) := by
      apply one_div_le_one_div_of_le hqpos
      calc (q:ℝ) = (q:ℝ)^1 := (pow_one _).symm
        _ ≤ (q:ℝ)^(d-1) := pow_le_pow_right₀ hqR1 (by omega)
    have h4 : (Q:ℝ)/(q:ℝ)^d ≤ 1/(q:ℝ) := by
      have h5 : (Q:ℝ)/(q:ℝ)^d ≤ (q:ℝ)/(q:ℝ)^d :=
        div_le_div_of_nonneg_right (by exact_mod_cast hQle) (by positivity)
      have h6 : (q:ℝ)/(q:ℝ)^d = 1/(q:ℝ)^(d-1) := by
        have hp : (q:ℝ)^d = (q:ℝ)^(d-1) * (q:ℝ) := by
          rw [← pow_succ (q:ℝ) (d-1)]; congr 1; omega
        rw [hp, mul_comm]
        field_simp
      rw [h6] at h5
      exact le_trans h5 h3
    have hB_le : 1/(Q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (Q:ℝ)/(q:ℝ)^d ≤ K/(q:ℝ) := by
      have hsum_le : 1/(Q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (Q:ℝ)/(q:ℝ)^d
          ≤ (|c|:ℝ)/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ) := by linarith [h1, h3, h4]
      have heq : (|c|:ℝ)/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ) = K/(q:ℝ) := by
        rw [hKdef]; ring
      rwa [heq] at hsum_le
    have hBpow : (1/(Q:ℝ) + 1/(q:ℝ) + 1/(q:ℝ)^(d-1) + (Q:ℝ)/(q:ℝ)^d)^θ
        ≤ K^θ * (q:ℝ)^(-θ) := by
      have h := Real.rpow_le_rpow hBnn hB_le hθnn
      have h2' : (K/(q:ℝ))^θ = K^θ * (q:ℝ)^(-θ) := by
        rw [Real.div_rpow (le_of_lt hKpos) (le_of_lt hqpos), div_eq_mul_inv,
          ← Real.rpow_neg hqpos.le]
      rwa [h2'] at h
    have hS_bound : ‖∑ x ∈ Finset.range q,
        Complex.exp (↑(2 * Real.pi * f.eval (((0:ℤ):ℝ) + (x:ℝ))) * Complex.I)‖
        ≤ C0 * (q:ℝ)^(1+ε) * (K^θ * (q:ℝ)^(-θ)) :=
      hweyl.trans (mul_le_mul_of_nonneg_left hBpow
        (mul_nonneg hC0pos.le (Real.rpow_nonneg hqpos.le _)))
    have hnorm : ‖((q:ℂ))⁻¹ * ∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℂ))‖
        = (q:ℝ)⁻¹ * ‖∑ x ∈ Finset.range q,
            Complex.exp (↑(2 * Real.pi * f.eval (((0:ℤ):ℝ) + (x:ℝ))) * Complex.I)‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast, hsum_eq]
    rw [hnorm]
    calc (q:ℝ)⁻¹ * ‖∑ x ∈ Finset.range q,
          Complex.exp (↑(2 * Real.pi * f.eval (((0:ℤ):ℝ) + (x:ℝ))) * Complex.I)‖
        ≤ (q:ℝ)⁻¹ * (C0 * (q:ℝ)^(1+ε) * (K^θ * (q:ℝ)^(-θ))) :=
          mul_le_mul_of_nonneg_left hS_bound (inv_nonneg.mpr hqpos.le)
      _ = C0 * K^θ * (q:ℝ)^(ε - θ) := by
          rw [← Real.rpow_neg_one (q:ℝ)]
          have hgoal : (q:ℝ)^(-1:ℝ) * (C0 * (q:ℝ)^(1+ε) * (K^θ * (q:ℝ)^(-θ)))
              = C0 * K^θ * ((q:ℝ)^(-1:ℝ) * (q:ℝ)^(1+ε) * (q:ℝ)^(-θ)) := by ring
          have hmid : (q:ℝ)^(-1:ℝ) * (q:ℝ)^(1+ε) * (q:ℝ)^(-θ) = (q:ℝ)^(ε-θ) := by
            rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
            congr 1; ring
          rw [hgoal, hmid]
      _ = C0 * K^θ * (q:ℝ)^(-(1/(2:ℝ)^(d-1)) + ε) := by
          rw [show ε - θ = -(1/(2:ℝ)^(d-1)) + ε by rw [hθ_eq]; ring]
      _ ≤ max 1 (C0 * K^θ) * (q:ℝ)^(-(1/(2:ℝ)^(d-1)) + ε) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hqpos.le _)

end Commons.Analysis.ExponentialSums
