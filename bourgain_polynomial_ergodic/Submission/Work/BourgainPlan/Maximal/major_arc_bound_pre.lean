import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.Analysis.ExponentialSums.poly_major_arc_approx_coeff

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

/-! ## Helper lemmas for the non-monic major-arc bound

We assemble the "pre-interval" major-arc approximation from the generic
non-monic major-arc estimate `Work.Analysis.ExponentialSums.poly_major_arc_approx_coeff`.
The three ingredients are

* the numerical core `major_arc_rpow_error_bound`: from `q ≤ c N^{1/4}` and
  `|β| ≤ N^{-(d-1/4)}` the error term of the major-arc estimate is `O(N^{-1/2})`;
* the phase identity `major_arc_phase`: `(a+lq)/(qc) + (θ - (a/q+l)/c) = θ`;
* the unfolding lemmas `polyWeylKernel_eq`, `polyModelTermPre_eq` matching our
  vocabulary to that of `poly_major_arc_approx_coeff`. -/

/-- **Numerical core of the major-arc bound.**  For `x ≥ 1`, `c ≥ 1`, `0 ≤ q ≤ c x^{1/4}`
and `|β| ≤ x^{-(d-1/4)}` we have
`|β| q (x+q)^d / x + q/x ≤ (c (c+1)^d + c) x^{-1/2}`. -/
private lemma major_arc_rpow_error_bound (d : ℕ) (x c q β : ℝ) (hx : 1 ≤ x) (hc : 1 ≤ c)
    (hq0 : 0 ≤ q) (hq : q ≤ c * x ^ ((1:ℝ)/4)) (hβ : |β| ≤ x ^ (-((d:ℝ) - (1:ℝ)/4))) :
    |β| * q * (x + q)^d / x + q/x ≤ (c * (c+1)^d + c) * x ^ (-(1/2:ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hx14_le : x ^ ((1:ℝ)/4) ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : ((1:ℝ)/4) ≤ 1)
    rwa [Real.rpow_one] at this
  have hx14nn : 0 ≤ x ^ ((1:ℝ)/4) := Real.rpow_nonneg (le_of_lt hx0) _
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hq_le_cx : q ≤ c * x := by
    calc q ≤ c * x ^ ((1:ℝ)/4) := hq
      _ ≤ c * x := mul_le_mul_of_nonneg_left hx14_le hc0
  have hxq : 0 ≤ x + q := by linarith
  have hsum_le : x + q ≤ (c+1) * x := by nlinarith
  have hpow : (x+q)^d ≤ (c+1)^d * x^d := by
    have h := pow_le_pow_left₀ hxq hsum_le d
    rwa [mul_pow] at h
  have hfac : x ^ (-((d:ℝ) - (1:ℝ)/4)) * x ^ ((1:ℝ)/4) * x ^ d / x = x ^ (-(1/2:ℝ)) := by
    rw [← Real.rpow_natCast x d, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx0,
      ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hT1 : |β| * q * (x+q)^d / x ≤ c * (c+1)^d * x ^ (-(1/2:ℝ)) := by
    have h1 : |β| * q * (x+q)^d
        ≤ c * (c+1)^d * (x ^ (-((d:ℝ) - (1:ℝ)/4)) * x ^ ((1:ℝ)/4) * x ^ d) := by
      calc |β| * q * (x+q)^d
          ≤ x ^ (-((d:ℝ) - (1:ℝ)/4)) * q * (x+q)^d := by gcongr
        _ ≤ x ^ (-((d:ℝ) - (1:ℝ)/4)) * (c * x ^ ((1:ℝ)/4)) * (x+q)^d := by gcongr
        _ ≤ x ^ (-((d:ℝ) - (1:ℝ)/4)) * (c * x ^ ((1:ℝ)/4)) * ((c+1)^d * x^d) := by gcongr
        _ = c * (c+1)^d * (x ^ (-((d:ℝ) - (1:ℝ)/4)) * x ^ ((1:ℝ)/4) * x ^ d) := by ring
    calc |β| * q * (x+q)^d / x
        ≤ c * (c+1)^d * (x ^ (-((d:ℝ) - (1:ℝ)/4)) * x ^ ((1:ℝ)/4) * x ^ d) / x :=
          div_le_div_of_nonneg_right h1 (le_of_lt hx0)
      _ = c * (c+1)^d * x ^ (-(1/2:ℝ)) := by
          rw [← hfac]; ring
  have hT2 : q/x ≤ c * x ^ (-(1/2:ℝ)) := by
    have h1 : q/x ≤ c * x ^ ((1:ℝ)/4) / x := div_le_div_of_nonneg_right hq (le_of_lt hx0)
    have h2 : c * x ^ ((1:ℝ)/4) / x = c * x ^ (-(3/4:ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hx0]
      rw [show ((1:ℝ)/4 + (-1)) = -(3/4:ℝ) by norm_num]
    have h3 : x ^ (-(3/4:ℝ)) ≤ x ^ (-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    linarith [h1, le_of_eq h2, mul_le_mul_of_nonneg_left h3 hc0]
  calc |β| * q * (x+q)^d / x + q/x
      ≤ c * (c+1)^d * x ^ (-(1/2:ℝ)) + c * x ^ (-(1/2:ℝ)) := add_le_add hT1 hT2
    _ = (c * (c+1)^d + c) * x ^ (-(1/2:ℝ)) := by ring

/-- **Phase identity of the non-monic major-arc parametrisation.**
`(a + l q)/(q c) + (θ - (a/q + l)/c) = θ` for `c = P.leadingCoeff`. -/
private lemma major_arc_phase (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (θ : ℝ)
    (hc : 0 < P.leadingCoeff) (hq : q ≠ 0) :
    ((((a:ℤ) + l * (q:ℤ) : ℤ) : ℝ) / ((q * P.leadingCoeff.toNat : ℕ) : ℝ))
        + (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) = θ := by
  have hcN : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hc))
  have hcR : ((P.leadingCoeff:ℝ)) ≠ 0 := by
    have : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
    exact ne_of_gt this
  have hqR : (q:ℝ) ≠ 0 := by
    have : (0:ℝ) < (q:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hq)
    exact ne_of_gt this
  rw [Nat.cast_mul, hcN]
  have hcast : ((((a:ℤ) + l * (q:ℤ) : ℤ)) : ℝ) = (a:ℝ) + (l:ℝ)*(q:ℝ) := by push_cast; ring
  rw [hcast]
  have hkey : ((a:ℝ) + (l:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ))
      = ((a:ℝ)/(q:ℝ) + (l:ℝ))/(P.leadingCoeff:ℝ) := by
    field_simp
  rw [hkey]
  ring

/-- **Arc condition bounds the offset.**  If `|c θ - a/q - l| ≤ R` with `c = P.leadingCoeff > 0`
and `R ≥ 0`, then `|θ - (a/q + l)/c| ≤ R`. -/
private lemma major_arc_beta_bound (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (θ R : ℝ)
    (hc : 0 < P.leadingCoeff) (hR : 0 ≤ R)
    (harc : |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ R) :
    |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ R := by
  have hcRpos : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
  have hcR1 : (1:ℝ) ≤ (P.leadingCoeff:ℝ) := by
    have : (1:ℤ) ≤ P.leadingCoeff := by omega
    exact_mod_cast this
  have hkey : θ - ((a:ℝ)/(q:ℝ) + (l:ℝ))/(P.leadingCoeff:ℝ)
      = ((P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)) / (P.leadingCoeff:ℝ) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hcRpos]
  calc |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| / (P.leadingCoeff:ℝ)
      ≤ R / (P.leadingCoeff:ℝ) := div_le_div_of_nonneg_right harc (le_of_lt hcRpos)
    _ ≤ R := by
        rw [div_le_iff₀ hcRpos]
        nlinarith [hR, hcR1]

/-- **Unfolding the Weyl kernel** into the shape used by `poly_major_arc_approx_coeff`. -/
private lemma polyWeylKernel_eq (P : Polynomial ℤ) (N : ℕ) (Q : ℕ) (b : ℤ) (β θ : ℝ)
    (hθ : (b:ℝ)/(Q:ℝ) + β = θ) :
    polyWeylKernel P N θ = (N:ℂ)⁻¹ *
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        (((((b:ℝ)/(Q:ℝ) + β) * ((P.eval (n:ℤ) : ℤ) : ℝ)) : ℝ) : ℂ))) := by
  unfold polyWeylKernel
  have h1 : ((N:ℝ)⁻¹ : ℂ) = (N:ℂ)⁻¹ := by push_cast; ring
  rw [h1]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [← hθ]

/-- **Unfolding the model term** into the shape used by `poly_major_arc_approx_coeff`. -/
private lemma polyModelTermPre_eq (P : Polynomial ℤ) (N q : ℕ) (a : ℕ) (l : ℤ) (θ : ℝ) :
    polyModelTermPre P N q a l θ
      = ((q * P.leadingCoeff.toNat : ℕ) : ℂ)⁻¹ *
          (∑ r ∈ Finset.range (q * P.leadingCoeff.toNat), Complex.exp (2 * Real.pi * Complex.I *
            ((((((a:ℤ) + l * (q:ℤ) : ℤ) : ℝ) / ((q * P.leadingCoeff.toNat : ℕ) : ℝ)) *
              ((P.eval (r:ℤ) : ℤ) : ℝ) : ℝ) : ℂ)))
        * (∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
            ((((θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)) : ℝ) : ℂ) *
              ((Polynomial.eval (((N:ℝ)*s):ℝ) (P.map (Int.castRingHom ℝ)) : ℝ) : ℂ))))) := by
  simp only [polyModelTermPre, polyWeight, polyProfile, toRealPoly]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub]

/-- **Major-arc approximation of the polynomial Weyl kernel (non-monic "pre-interval" form).**
For an integer polynomial `P` of degree `d ≥ 2` with leading coefficient `c = P.leadingCoeff > 0`,
and `θ` in the arc `|c θ − (a/q + l)| ≤ N^{-(d−1/4)}` with `1 ≤ q ≤ N^{1/4}`, `(a,q) = 1`, `a < q`,
`l : ℤ`, the Weyl kernel `N⁻¹ ∑_{n<N} e(θ P n)` is approximated by the complete sum of modulus
`q·c` and numerator `a + l·q` times the profile at the offset `θ − (a/q + l)/c`:

`‖polyWeylKernel P N θ − polyModelTermPre P N q a l θ‖ ≤ C N^{-c₀}`,

with `c₀, C > 0` depending on `P`.  This is Bourgain (1989), (6.10) in the non-monic form: the
modulus is `q·c` (not `q`) and the profile is evaluated at the *offset* `θ − (a/q + l)/c`.
Route: instantiate the generic major-arc approximation
`Work.Analysis.ExponentialSums.poly_major_arc_approx_coeff`
(`Submission/Work/Analysis/ExponentialSums/poly_major_arc_approx_coeff.lean`, which generalises
`Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff` to non-monic polynomials) with
`β := θ − (a/q + l)/c`, `q ↦ q·c`, `a ↦ a + l·q`: the phase `θ P(n)` splits as
`((a + lq)/(qc)) P(n) + β P(n)`, the first summand is periodic with period `q·c`, and the second
gives the profile.  Its error is `C(1+‖coeffs‖₁)(|β|·qc·(N+qc)^d/N + qc/N)`, which is
`≲ N^{-1/2}` for `|β| ≤ N^{-(d-1/4)}/c` and `q ≤ N^{1/4}`; for the finitely many small `N` absorb
the crude bound `‖kernel‖ ≤ 1`, `‖model‖ ≤ 1` into `C`. -/
theorem major_arc_bound_pre (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ (N q : ℕ) (a : ℕ) (l : ℤ) (θ : ℝ), 1 ≤ q →
        (q : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ)/4) → a < q → Nat.gcd a q = 1 →
        |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
            ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ)/4)) →
        ‖Work.BourgainPlan.Maximal.polyWeylKernel P N θ
          - Work.BourgainPlan.Maximal.polyModelTermPre P N q a l θ‖ ≤ C * (N : ℝ) ^ (-c₀) := by
  obtain ⟨C0, hC0, happrox⟩ :=
    Work.Analysis.ExponentialSums.poly_major_arc_approx_coeff P.natDegree hd
  let A : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|
  have hA0 : 0 ≤ A := by
    show 0 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|
    positivity
  have hcR1 : (1:ℝ) ≤ (P.leadingCoeff:ℝ) := by
    have : (1:ℤ) ≤ P.leadingCoeff := by omega
    exact_mod_cast this
  have hcRpos : (0:ℝ) < (P.leadingCoeff:ℝ) := lt_of_lt_of_le one_pos hcR1
  refine ⟨(1:ℝ)/2,
    C0 * (1 + A) * ((P.leadingCoeff:ℝ) * ((P.leadingCoeff:ℝ)+1)^(P.natDegree) + (P.leadingCoeff:ℝ)) + 2,
    by norm_num, ?_, ?_⟩
  · have h1 : 0 ≤ (P.leadingCoeff:ℝ) * ((P.leadingCoeff:ℝ)+1)^(P.natDegree) + (P.leadingCoeff:ℝ) := by
      positivity
    have h2 : 0 ≤ C0 * (1 + A) := by positivity
    positivity
  · intro N q a l θ hq1 hqN haq hgcd harc
    have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hN1 : 1 ≤ N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exfalso
        subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num : ((1:ℝ)/4) ≠ 0)] at hqN
        linarith [hqR, hqN]
      · exact h
    have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    have hNRpos : (0:ℝ) < (N:ℝ) := by linarith
    have hcN : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hc))
    have hQ1 : 1 ≤ q * P.leadingCoeff.toNat := by
      have h1 : 1 ≤ P.leadingCoeff.toNat := by omega
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    have hQcast : ((q * P.leadingCoeff.toNat : ℕ) : ℝ) = (q:ℝ) * (P.leadingCoeff:ℝ) := by
      rw [Nat.cast_mul, hcN]
    have hQle : ((q * P.leadingCoeff.toNat : ℕ) : ℝ)
        ≤ (P.leadingCoeff:ℝ) * (N:ℝ) ^ ((1:ℝ)/4) := by
      rw [hQcast]
      calc (q:ℝ) * (P.leadingCoeff:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) * (P.leadingCoeff:ℝ) :=
            mul_le_mul_of_nonneg_right hqN (le_of_lt hcRpos)
        _ = (P.leadingCoeff:ℝ) * (N:ℝ)^((1:ℝ)/4) := by ring
    have hβbound :
        |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))|
          ≤ (N:ℝ) ^ (-((P.natDegree:ℝ) - (1:ℝ)/4)) :=
      major_arc_beta_bound P q a l θ ((N:ℝ) ^ (-((P.natDegree:ℝ) - (1:ℝ)/4))) hc
        (Real.rpow_nonneg (le_of_lt hNRpos) _) harc
    have hθ : ((((a:ℤ) + l * (q:ℤ) : ℤ) : ℝ) / ((q * P.leadingCoeff.toNat : ℕ) : ℝ))
        + (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) = θ :=
      major_arc_phase P q a l θ hc (by omega)
    have hbound := happrox N (q * P.leadingCoeff.toNat) ((a:ℤ) + l * (q:ℤ))
      (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) P rfl hQ1 hN1
    have herr := major_arc_rpow_error_bound P.natDegree (N:ℝ) (P.leadingCoeff:ℝ)
      ((q * P.leadingCoeff.toNat : ℕ) : ℝ)
      (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) hNR hcR1 (by positivity) hQle hβbound
    calc ‖polyWeylKernel P N θ - polyModelTermPre P N q a l θ‖
        ≤ C0 * (1 + A) * ((P.leadingCoeff:ℝ) * ((P.leadingCoeff:ℝ)+1)^(P.natDegree)
              + (P.leadingCoeff:ℝ)) * (N:ℝ) ^ (-(1/2:ℝ)) := by
          rw [polyWeylKernel_eq P N (q * P.leadingCoeff.toNat) ((a:ℤ) + l * (q:ℤ))
                (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) θ hθ,
              polyModelTermPre_eq P N q a l θ]
          refine le_trans hbound ?_
          have hcoef : 0 ≤ C0 * (1 + A) := by positivity
          calc C0 * (1 + A) * (|θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))|
                * ((q * P.leadingCoeff.toNat : ℕ) : ℝ)
                * ((N:ℝ) + ((q * P.leadingCoeff.toNat : ℕ) : ℝ)) ^ (P.natDegree) / (N:ℝ)
              + ((q * P.leadingCoeff.toNat : ℕ) : ℝ) / (N:ℝ))
              ≤ C0 * (1 + A) * (((P.leadingCoeff:ℝ) * ((P.leadingCoeff:ℝ)+1)^(P.natDegree)
                    + (P.leadingCoeff:ℝ)) * (N:ℝ) ^ (-(1/2:ℝ))) :=
                mul_le_mul_of_nonneg_left herr hcoef
            _ = C0 * (1 + A) * ((P.leadingCoeff:ℝ) * ((P.leadingCoeff:ℝ)+1)^(P.natDegree)
                    + (P.leadingCoeff:ℝ)) * (N:ℝ) ^ (-(1/2:ℝ)) := by ring
      _ ≤ (C0 * (1 + A) * ((P.leadingCoeff:ℝ) * ((P.leadingCoeff:ℝ)+1)^(P.natDegree)
              + (P.leadingCoeff:ℝ)) + 2) * (N:ℝ) ^ (-(1/2:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hNRpos) _)
          linarith

end Work.BourgainPlan.Maximal
