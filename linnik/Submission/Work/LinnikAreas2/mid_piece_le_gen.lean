import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas2.MidBoundsHarmonic2
import Submission.Work.LinnikAreas.Density4.sum_mul_diff_le

namespace Work.LinnikAreas2

open scoped BigOperators
open Work.LinnikAreas.Density4

/-- Public restatement of the (private) `wt_diff_bounds` of
`Submission/Work/LinnikAreas/Density4/mid_piece_le.lean`: on the range `⌊U⌋ < n ≤ ⌊V⌋` the
two sums of weight *differences* are bounded by `log(V/U)` and `1` respectively.  Independent of
the constant `C₁`, so reused verbatim. -/
lemma wt_diff_bounds_gen {L U V X : ℝ} (hU : 0 < U) (hX : 0 < X)
    (hUV : U < V) (hcase : U ≤ L^2 * X) (hAB : Nat.floor U + 1 ≤ Nat.floor V) :
    (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        Real.log ((n:ℝ)/U) * (wt L U X n - wt L U X (n+1)) ≤ Real.log (V/U))
    ∧ (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        (wt L U X n - wt L U X (n+1)) ≤ 1) := by
  have hV : (0:ℝ) < V := lt_trans hU hUV
  have hA1 : 1 ≤ Nat.floor U + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hBpos : (0:ℝ) < ((Nat.floor V : ℕ) : ℝ) := by
    have h : 1 ≤ Nat.floor V := le_trans hA1 hAB
    exact_mod_cast h
  have hU_lt_A : U < ((Nat.floor U + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one U
  have hBle : ((Nat.floor V : ℕ) : ℝ) ≤ V := Nat.floor_le hV.le
  have hA_le_B : ((Nat.floor U + 1 : ℕ) : ℝ) ≤ ((Nat.floor V : ℕ) : ℝ) := by exact_mod_cast hAB
  have hU_lt_B : U < ((Nat.floor V : ℕ) : ℝ) := lt_of_lt_of_le hU_lt_A hA_le_B
  constructor
  · rw [sum_Icc_eq_sum_Ico_succ
        (f := fun n => Real.log ((n:ℝ)/U) * (wt L U X n - wt L U X (n+1)))
        (Nat.floor U + 1) (Nat.floor V)]
    have hc0 : 0 ≤ Real.log (((Nat.floor U + 1 : ℕ) : ℝ)/U) :=
      Real.log_nonneg ((one_le_div hU).mpr hU_lt_A.le)
    have hcB : 0 ≤ Real.log (((Nat.floor V : ℕ) : ℝ)/U) :=
      Real.log_nonneg ((one_le_div hU).mpr hU_lt_B.le)
    have hcmono : ∀ n, Nat.floor U + 1 + 1 ≤ n → n ≤ Nat.floor V →
        Real.log (((n-1 : ℕ):ℝ)/U) ≤ Real.log ((n:ℝ)/U) := by
      intro n hn1 hn2
      have hn1' : Nat.floor U + 1 ≤ n - 1 := by omega
      have h1 : (0:ℝ) < ((n-1 : ℕ):ℝ)/U := by
        have h2 : (1:ℝ) ≤ ((n-1:ℕ):ℝ) := by
          have h3 : 1 ≤ n - 1 := le_trans hA1 hn1'
          exact_mod_cast h3
        positivity
      apply Real.log_le_log h1
      apply div_le_div_of_nonneg_right _ hU.le
      have h5 : n - 1 ≤ n := Nat.sub_le n 1
      exact_mod_cast h5
    have hkey := sum_mul_diff_le (c := fun n => Real.log ((n:ℝ)/U)) (w := wt L U X)
      (A := Nat.floor U + 1) (B := Nat.floor V) (by omega) hc0 hcB hcmono
      (fun n => wt_nonneg hU hX hcase n) (fun n => wt_le_one hU hX n)
    refine le_trans hkey (Real.log_le_log ?_ ?_)
    · exact div_pos hBpos hU
    · exact div_le_div_of_nonneg_right hBle hU.le
  · rw [sum_Icc_eq_sum_Ico_succ (f := fun n => (wt L U X n - wt L U X (n+1)))
        (Nat.floor U + 1) (Nat.floor V)]
    exact le_trans (sum_Ico_diff_le (w := wt L U X) (fun n => wt_nonneg hU hX hcase n)
      (Nat.floor U + 1) (Nat.floor V + 1)) (wt_le_one hU hX _)

/-- **HB (11.14), the "mid" range `⌊U⌋ < n ≤ ⌊V⌋`, with a general constant `C₁`.**

This is `Work.LinnikAreas.Density4.mid_piece_le` with the hardcoded constant `1` of the input
hypothesis `h1` (and of the corresponding term on the right-hand side) promoted to a parameter
`C₁ > 0`.  The proof of `mid_piece_le` consumes `h1` only as an upper bound and splits the
resulting sum linearly in the constant, so it generalises verbatim; only the final arithmetic
identity has `C₁` in place of `1`. -/
theorem mid_piece_le_gen {ε C₁ L U V X : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁) (hL : 0 < L)
    (hU : 0 < U) (hX : 0 < X) (hU1 : 1 ≤ U) (hUV : U < V) (hcase : U ≤ L^2 * X)
    (h1 : ∀ N : ℕ, U ≤ (N:ℝ) → (N:ℝ) ≤ V →
      Work.LinnikAreas2.psSum U V N
        ≤ (1+ε) * (N:ℝ) * Real.log ((N:ℝ)/U) / (Real.log (V/U))^2
          + C₁ * (N:ℝ) / (Real.log (V/U))^2) :
    ∑ n ∈ Finset.Ico (Nat.floor U + 1) (Nat.floor V + 1),
        Work.LinnikAreas2.psSum U V n
          * (Work.LinnikAreas2.phiW L U X n - Work.LinnikAreas2.phiW L U X (n+1))
      ≤ (1+ε)/2
        + (1+ε)*(1/Real.log (V/U) + 1/(V*Real.log (V/U)) + 1/(2*V^2*(Real.log (V/U))^2))
        + C₁*(1/Real.log (V/U) + 1/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)) := by
  have hV : (0:ℝ) < V := lt_trans hU hUV
  have hΛpos : 0 < Real.log (V/U) := Real.log_pos ((one_lt_div hU).mpr hUV)
  rcases lt_or_ge (Nat.floor V) (Nat.floor U + 1) with hBA | hAB
  · -- the range is empty and the bound is trivial (the right-hand side is positive)
    rw [Finset.Ico_eq_empty_of_le (by omega : Nat.floor V + 1 ≤ Nat.floor U + 1),
      Finset.sum_empty]
    have hP : 0 < 1/Real.log (V/U) + 1/(V*Real.log (V/U)) + 1/(2*V^2*(Real.log (V/U))^2) := by
      have ha : 0 < 1/Real.log (V/U) := one_div_pos.mpr hΛpos
      have hb : 0 < 1/(V*Real.log (V/U)) := one_div_pos.mpr (mul_pos hV hΛpos)
      have hc : 0 < 1/(2*V^2*(Real.log (V/U))^2) :=
        one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (pow_pos hV 2)) (pow_pos hΛpos 2))
      linarith
    have hQ : 0 < 1/Real.log (V/U) + 1/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2) := by
      have ha : 0 < 1/Real.log (V/U) := one_div_pos.mpr hΛpos
      have hb : 0 < 1/(Real.log (V/U))^2 := one_div_pos.mpr (pow_pos hΛpos 2)
      have hc : 0 < 1/(V*(Real.log (V/U))^2) :=
        one_div_pos.mpr (mul_pos hV (pow_pos hΛpos 2))
      linarith
    have hA : 0 < (1+ε)*(1/Real.log (V/U) + 1/(V*Real.log (V/U))
        + 1/(2*V^2*(Real.log (V/U))^2)) := mul_pos (by linarith) hP
    have hB : 0 < C₁*(1/Real.log (V/U) + 1/(Real.log (V/U))^2
        + 1/(V*(Real.log (V/U))^2)) := mul_pos hC₁ hQ
    linarith
  · -- `⌊U⌋+1 ≤ ⌊V⌋`: the nonempty range of HB (11.14)
    have hA1 : 1 ≤ Nat.floor U + 1 := by omega
    have hU_lt_A : U < ((Nat.floor U + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one U
    have hBle : ((Nat.floor V : ℕ) : ℝ) ≤ V := Nat.floor_le hV.le
    -- pointwise: HB's `A(n)` bound against the actual increments `k(n) = φ n - φ (n+1)`
    have hpt : ∀ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        psSum U V n * (phiW L U X n - phiW L U X (n+1))
          ≤ (1+ε)/(Real.log (V/U))^2
              * (Real.log ((n:ℝ)/U)
                  * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
            + C₁/(Real.log (V/U))^2
              * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := le_trans hA1 hn.1
      have hnU : U ≤ (n:ℝ) := by
        have h : ((Nat.floor U + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
        linarith
      have hnV : (n:ℝ) ≤ V := by
        have h : (n:ℝ) ≤ ((Nat.floor V : ℕ) : ℝ) := by exact_mod_cast hn.2
        linarith
      have hps := h1 n hnU hnV
      have hk : 0 ≤ phiW L U X n - phiW L U X (n+1) := phiW_sub_nonneg hU hX hcase hn1
      have hident := phiW_sub_ident (L := L) (U := U) (X := X) hn1
      have hstep := mul_le_mul_of_nonneg_right hps hk
      calc psSum U V n * (phiW L U X n - phiW L U X (n+1))
          ≤ ((1+ε) * (n:ℝ) * Real.log ((n:ℝ)/U) / (Real.log (V/U))^2
              + C₁ * (n:ℝ) / (Real.log (V/U))^2) * (phiW L U X n - phiW L U X (n+1)) := hstep
        _ = ((1+ε) * Real.log ((n:ℝ)/U) + C₁) * (n:ℝ) / (Real.log (V/U))^2
              * (phiW L U X n - phiW L U X (n+1)) := by ring
        _ = ((1+ε) * Real.log ((n:ℝ)/U) + C₁) / (Real.log (V/U))^2
              * ((n:ℝ) * (phiW L U X n - phiW L U X (n+1))) := by ring
        _ = ((1+ε) * Real.log ((n:ℝ)/U) + C₁) / (Real.log (V/U))^2
              * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)) := by rw [hident]
        _ = (1+ε)/(Real.log (V/U))^2
              * (Real.log ((n:ℝ)/U)
                  * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
            + C₁/(Real.log (V/U))^2
              * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)) := by ring
    rw [← sum_Icc_eq_sum_Ico_succ
        (f := fun n => psSum U V n * (phiW L U X n - phiW L U X (n+1)))
        (Nat.floor U + 1) (Nat.floor V)]
    refine le_trans (Finset.sum_le_sum hpt) ?_
    -- split the weighted sum into the four sums of HB (11.14), linearly in `C₁`
    have hsplit : ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
          ((1+ε)/(Real.log (V/U))^2
              * (Real.log ((n:ℝ)/U)
                  * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
            + C₁/(Real.log (V/U))^2
              * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
        = (1+ε)/(Real.log (V/U))^2 * (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
              Real.log ((n:ℝ)/U)
                * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
          + C₁/(Real.log (V/U))^2 * (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
              ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [hsplit]
    -- the four bounds: `sum_mul_diff_le`/`sum_Ico_diff_le` (log- and plain weight differences)
    -- and `sum_log_div_le`/`sum_one_div_succ_le_log` (the harmonic pieces)
    have hb1 : ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        Real.log ((n:ℝ)/U) * (wt L U X n - wt L U X (n+1)) ≤ Real.log (V/U) :=
      (wt_diff_bounds_gen hU hX hUV hcase hAB).1
    have hb2 : ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        (wt L U X n - wt L U X (n+1)) ≤ 1 :=
      (wt_diff_bounds_gen hU hX hUV hcase hAB).2
    have hb3 : ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        Real.log ((n:ℝ)/U) * (wt L U X (n+1)/((n:ℝ)+1))
        ≤ (Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2) :=
      (mid_bounds_harmonic hU hX hU1 hUV hAB).1
    have hb4 : ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        wt L U X (n+1)/((n:ℝ)+1) ≤ Real.log (V/U) + 1/V :=
      (mid_bounds_harmonic hU hX hU1 hUV hAB).2
    have hSA : (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
          Real.log ((n:ℝ)/U) * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
        ≤ Real.log (V/U) + ((Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2)) := by
      have h1' : (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
            Real.log ((n:ℝ)/U) * ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
          = ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
              (Real.log ((n:ℝ)/U) * (wt L U X n - wt L U X (n+1))
                + Real.log ((n:ℝ)/U) * (wt L U X (n+1)/((n:ℝ)+1))) :=
        Finset.sum_congr rfl (fun n _ => by ring)
      rw [h1', Finset.sum_add_distrib]
      linarith [hb1, hb3]
    have hSB : (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
          ((wt L U X n - wt L U X (n+1)) + wt L U X (n+1)/((n:ℝ)+1)))
        ≤ 1 + (Real.log (V/U) + 1/V) := by
      rw [Finset.sum_add_distrib]
      linarith [hb2, hb4]
    have hc1 : 0 ≤ (1+ε)/(Real.log (V/U))^2 := div_nonneg (by linarith) (sq_nonneg _)
    have hc2 : 0 ≤ C₁/(Real.log (V/U))^2 := div_nonneg hC₁.le (sq_nonneg _)
    -- the residual arithmetic, linear in `C₁`
    have hkey : (1+ε)/(Real.log (V/U))^2
          * (Real.log (V/U) + ((Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2)))
        + C₁/(Real.log (V/U))^2 * (1 + (Real.log (V/U) + 1/V))
        ≤ (1+ε)/2
          + (1+ε)*(1/Real.log (V/U) + 1/(V*Real.log (V/U)) + 1/(2*V^2*(Real.log (V/U))^2))
          + C₁*(1/Real.log (V/U) + 1/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)) := by
      have hΛne : Real.log (V/U) ≠ 0 := ne_of_gt hΛpos
      have hVne : V ≠ 0 := ne_of_gt hV
      have hid : (1+ε)/(Real.log (V/U))^2
            * (Real.log (V/U) + ((Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2)))
          + C₁/(Real.log (V/U))^2 * (1 + (Real.log (V/U) + 1/V))
          = (1+ε)/2
            + (1+ε)*(1/Real.log (V/U) + 1/(V*Real.log (V/U)) + 1/(2*V^2*(Real.log (V/U))^2))
            + C₁*(1/Real.log (V/U) + 1/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)) := by
        field_simp
        ring
      rw [hid]
    linarith [mul_le_mul_of_nonneg_left hSA hc1, mul_le_mul_of_nonneg_left hSB hc2]

end Work.LinnikAreas2
