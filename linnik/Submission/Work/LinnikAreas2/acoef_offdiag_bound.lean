import Mathlib
import Submission.Work.LinnikAreas2.d1_of_area1
import Submission.Work.LinnikAreas.Density4.det_split

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas2

noncomputable section

/-!
## HB (11.11): the off-diagonal bound on the `a`-coefficients

The coefficients `a_n = w_χ^{1/2} (Σ_{d|n}θ_d) χ(n) n^{1/2-ρ} wt_n^{1/2}` of HB (11.11) satisfy
`a_{n,χ} * conj(a_{n,χ'}) = √(w_χ w_{χ'}) · (Σ_{d|n}θ_d)² (χ χ'^{-1})(n) n^{1-ρ-conj ρ'} wt_n`.
Hence the whole off-diagonal inner product `‖Σ_n a_{n,χ} conj(a_{n,χ'})‖` is `√(w_χ w_{χ'})` times
the detector sum appearing in HB (11.16).

The only subtlety in the formalisation is that the weight `wt_n = e^{-n/X} - e^{-nL²/U}` is *not*
assumed non-negative: the hypothesis of the statement involves the sum with the *signed* weight
`wt_n`, whereas the term `a_{n,χ} conj(a_{n,χ'})` involves `(√wt_n)² = max(wt_n, 0)`.  We exploit the
fact that `wt_n`, for `n ≥ 1`, has the sign of `(log q)²/q^u - 1/q^x`, which is *independent of n*:
either every weight is `≥ 0` and the identity is pointwise, or every weight is `≤ 0` and all the
terms `a_{n,χ} conj(a_{n,χ'})` vanish.

This is why the statement needs no `hwt : ∀ n, 0 ≤ WT q u x n` hypothesis.
-/

/-! ### The weight `WT`, and the uniformity of its sign in `n` -/

lemma WT_unfold (q : ℕ) (u x : ℝ) (n : ℕ) :
    WT q u x n
      = Real.exp (-(n:ℝ) * (1/(q:ℝ)^x)) - Real.exp (-(n:ℝ) * ((Real.log q)^2/(q:ℝ)^u)) := by
  have h1 : -(n:ℝ)/(q:ℝ)^x = -(n:ℝ)*(1/(q:ℝ)^x) := by ring
  have h2 : -(n:ℝ)*(Real.log q)^2/(q:ℝ)^u = -(n:ℝ)*((Real.log q)^2/(q:ℝ)^u) := by ring
  simp only [WT, Work.LinnikAreas2.wt, h1, h2]

lemma WT_zero (q : ℕ) (u x : ℝ) : WT q u x 0 = 0 := by
  simp [WT, Work.LinnikAreas2.wt]

/-- `WT` at `n = 1` is `e^{-1/(q^x)} - e^{-(log q)²/q^u}`; its sign determines the sign of every
later term (the comparison is the same for all `n ≥ 1`). -/
lemma WT_nonneg_of_one_nonneg {q : ℕ} {u x : ℝ} (h : 0 ≤ WT q u x 1) :
    ∀ n : ℕ, 0 ≤ WT q u x n := by
  have hab : 1/(q:ℝ)^x ≤ (Real.log q)^2/(q:ℝ)^u := by
    rw [WT_unfold q u x 1] at h
    have h' : Real.exp (-(1:ℝ) * ((Real.log q)^2/(q:ℝ)^u))
        ≤ Real.exp (-(1:ℝ) * (1/(q:ℝ)^x)) := by linarith
    have h'' := Real.exp_le_exp.mp h'
    linarith
  intro n
  rw [WT_unfold q u x n]
  have hmono : (n:ℝ) * (1/(q:ℝ)^x) ≤ (n:ℝ) * ((Real.log q)^2/(q:ℝ)^u) :=
    mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)
  have hexp : Real.exp (-(n:ℝ) * ((Real.log q)^2/(q:ℝ)^u))
      ≤ Real.exp (-(n:ℝ) * (1/(q:ℝ)^x)) := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith

/-- Conversely, if `WT` at `n = 1` is negative then every `WT` is `≤ 0`. -/
lemma WT_nonpos_of_one_neg {q : ℕ} {u x : ℝ} (h : WT q u x 1 < 0) :
    ∀ n : ℕ, WT q u x n ≤ 0 := by
  have hba : (Real.log q)^2/(q:ℝ)^u < 1/(q:ℝ)^x := by
    rw [WT_unfold q u x 1] at h
    have h' : Real.exp (-(1:ℝ) * (1/(q:ℝ)^x))
        < Real.exp (-(1:ℝ) * ((Real.log q)^2/(q:ℝ)^u)) := by linarith
    have h'' := Real.exp_lt_exp.mp h'
    linarith
  intro n
  rcases n with _ | k
  · simp [WT_zero]
  · rw [WT_unfold q u x (k+1)]
    push_cast
    have hpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have hmono : ((k:ℝ) + 1) * ((Real.log q)^2/(q:ℝ)^u) ≤ ((k:ℝ) + 1) * (1/(q:ℝ)^x) :=
      le_of_lt (mul_lt_mul_of_pos_left hba hpos)
    have hexp : Real.exp (-((k:ℝ) + 1) * (1/(q:ℝ)^x))
        ≤ Real.exp (-((k:ℝ) + 1) * ((Real.log q)^2/(q:ℝ)^u)) := by
      apply Real.exp_le_exp.mpr
      linarith
    linarith

/-! ### The pointwise conjugation identity -/

/-- **The off-diagonal identity.**  The product of the `a`-coefficient of `χ` with the conjugate of
the `a`-coefficient of `χ'` is `√(w_χ w_{χ'})` times the summand of the off-diagonal detector sum
of HB (11.16), provided the weight is non-negative. -/
lemma acoef_mul_conj_eq {q : ℕ} [NeZero q] {u w x : ℝ}
    (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ) {wc wc' : ℝ} (n : ℕ)
    (hwt : 0 ≤ WT q u x n) :
    acoef q u w x χ ρ wc n * (starRingEnd ℂ) (acoef q u w x χ' ρ' wc' n)
      = ((Real.sqrt wc * Real.sqrt wc' : ℝ) : ℂ)
        * (((((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ))^2
            * ((χ * (χ')⁻¹) (n : ZMod q))
            * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ (ρ'))))
            * (((WT q u x n : ℝ)) : ℂ)) := by
  rcases n with _ | m
  · simp [acoef, Work.LinnikAreas.Density4.thetaS_zero]
  · have hx : (((m+1 : ℕ) : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero
    have hcp : (starRingEnd ℂ) (((m+1 : ℕ) : ℂ) ^ ((1/2:ℂ) - ρ'))
        = (((m+1 : ℕ) : ℂ)) ^ ((starRingEnd ℂ) ((1/2:ℂ)-ρ')) := by
      have h := Complex.cpow_conj (((m+1 : ℕ) : ℂ)) ((1/2:ℂ)-ρ') hx
      rw [Complex.conj_natCast] at h
      exact h.symm
    have hcχ : (starRingEnd ℂ) (χ' (((m+1 : ℕ)) : ZMod q))
        = (χ'⁻¹) (((m+1 : ℕ)) : ZMod q) := MulChar.star_apply' χ' _
    have hn0 : (((m+1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
    have hz : (((m+1 : ℕ) : ℂ)) ^ ((1/2:ℂ)-ρ) * (((m+1 : ℕ) : ℂ)) ^ ((starRingEnd ℂ) ((1/2:ℂ)-ρ'))
        = (((m+1 : ℕ) : ℂ)) ^ ((1:ℂ) - ρ - (starRingEnd ℂ) ρ') := by
      rw [← Complex.cpow_add _ _ hn0]
      congr 1
      rw [map_sub]
      have h12 : (starRingEnd ℂ) ((1/2 : ℂ)) = (1/2 : ℂ) := by
        rw [map_div₀, map_one, Complex.conj_ofNat]
      rw [h12]
      ring
    have hW : ((Real.sqrt (WT q u x (m+1)) : ℝ):ℂ) * ((Real.sqrt (WT q u x (m+1)) : ℝ):ℂ)
        = ((WT q u x (m+1) : ℝ):ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hwt]
    have hA : ((Real.sqrt wc : ℝ):ℂ) * ((Real.sqrt wc' : ℝ):ℂ)
        = ((Real.sqrt wc * Real.sqrt wc' : ℝ):ℂ) := (Complex.ofReal_mul _ _).symm
    simp only [acoef, Work.LinnikAreas.Density4.thetaS]
    simp only [map_mul, Complex.conj_ofReal, hcχ, hcp]
    have key : ∀ (p p' S a b z z' r : ℂ),
        p * S * a * z * r * (p' * S * b * z' * r) = (p*p')*(S*S)*(a*b)*(z*z')*(r*r) := by
      intro p p' S a b z z' r; ring
    rw [key]
    rw [hA, MulChar.mul_apply, hz, hW]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-! ### The off-diagonal bound -/

theorem acoef_offdiag_bound {q : ℕ} [NeZero q] {u w x : ℝ}
    (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ) {wc wc' c2 : ℝ}
    (hwc : 0 ≤ wc) (hwc' : 0 ≤ wc')
    (hoff : ‖∑' n : ℕ, ((((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ))^2
          * ((χ * (χ')⁻¹) (n : ZMod q))
          * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ (ρ'))))
          * (((Work.LinnikAreas2.WT q u x n : ℝ)) : ℂ)‖ ≤ c2) :
    ‖∑' n : ℕ, Work.LinnikAreas2.acoef q u w x χ ρ wc n * (starRingEnd ℂ) (Work.LinnikAreas2.acoef q u w x χ' ρ' wc' n)‖
      ≤ c2 * Real.sqrt (wc * wc') := by
  have hc2 : 0 ≤ c2 := le_trans (norm_nonneg _) hoff
  by_cases h1 : 0 ≤ WT q u x 1
  · -- every weight is non-negative: the identity is pointwise
    have hwt : ∀ n : ℕ, 0 ≤ WT q u x n := WT_nonneg_of_one_nonneg h1
    have hA0 : 0 ≤ Real.sqrt wc * Real.sqrt wc' :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hAc : ‖((Real.sqrt wc * Real.sqrt wc' : ℝ) : ℂ)‖
        = Real.sqrt wc * Real.sqrt wc' := by
      simpa [abs_of_nonneg hA0] using
        RCLike.norm_ofReal (K := ℂ) (Real.sqrt wc * Real.sqrt wc')
    have hEq : (∑' n : ℕ, acoef q u w x χ ρ wc n
          * (starRingEnd ℂ) (acoef q u w x χ' ρ' wc' n))
        = ((Real.sqrt wc * Real.sqrt wc' : ℝ) : ℂ)
          * (∑' n : ℕ, ((((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ))^2
              * ((χ * (χ')⁻¹) (n : ZMod q))
              * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ (ρ'))))
              * (((WT q u x n : ℝ)) : ℂ)) := by
      rw [tsum_congr (fun n => acoef_mul_conj_eq χ χ' ρ ρ' n (hwt n)), tsum_mul_left]
    rw [hEq, norm_mul, hAc]
    calc Real.sqrt wc * Real.sqrt wc'
            * ‖∑' n : ℕ, ((((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ))^2
                * ((χ * (χ')⁻¹) (n : ZMod q))
                * ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ (ρ'))))
                * (((WT q u x n : ℝ)) : ℂ)‖
          ≤ Real.sqrt wc * Real.sqrt wc' * c2 := mul_le_mul_of_nonneg_left hoff hA0
      _ = c2 * Real.sqrt (wc * wc') := by rw [Real.sqrt_mul hwc]; ring
  · -- every weight is non-positive: all the terms vanish
    have h1neg : WT q u x 1 < 0 := lt_of_not_ge h1
    have hsign : ∀ n : ℕ, WT q u x n ≤ 0 := WT_nonpos_of_one_neg h1neg
    have hzero : ∀ n : ℕ, acoef q u w x χ ρ wc n
        * (starRingEnd ℂ) (acoef q u w x χ' ρ' wc' n) = 0 := by
      intro n
      have hs : Real.sqrt (WT q u x n) = 0 := Real.sqrt_eq_zero_of_nonpos (hsign n)
      simp [acoef, hs]
    rw [tsum_congr hzero, tsum_zero, norm_zero]
    exact mul_nonneg hc2 (Real.sqrt_nonneg _)

end

end Work.LinnikAreas2
