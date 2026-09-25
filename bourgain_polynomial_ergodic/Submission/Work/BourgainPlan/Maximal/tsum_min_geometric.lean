import Mathlib

/-!
# The `ℤ`-sum of the minimum of two geometric sequences

For `A B : ℕ` with `A, B > 0` and reals `P, Q ≥ 0` the series
`∑_{m ∈ ℤ} min (P * 2^{-A m}) (Q * 2^{B m})`
is summable and bounded by a constant times the weighted geometric mean
`P^{B/(A+B)} Q^{A/(A+B)}`.  This is a standard "crossing point" estimate: the
summed sequence is unimodal, increasing (like `Q 2^{B m}`) up to the crossing
point and decreasing (like `P 2^{-A m}`) afterwards.

The proof picks the crossing point `K = ⌈log₂(P/Q)/(A+B)⌉`, splits the `ℤ`-sum
into the two half lines `m < K` and `m ≥ K` through which it decays
geometrically, and evaluates the two resulting geometric series.
-/

namespace Work.BourgainPlan.Maximal

/-- `y * (x/y)^c = x^c * y^(1-c)` for `x, y > 0`. -/
private lemma mul_div_rpow_aux (x y c : ℝ) (hx : 0 < x) (hy : 0 < y) :
    y * (x/y)^c = x^c * y^(1-c) := by
  rw [Real.div_rpow hx.le hy.le]
  have h1 : y * (x^c / y^c) = x^c * (y / y^c) := by ring
  rw [h1, show y / y^c = y^(1:ℝ) / y^c by rw [Real.rpow_one], ← Real.rpow_sub hy (1:ℝ) c]

/-- `2 ^ (a * logb 2 (x/y) / (a+b)) = (x/y) ^ (a/(a+b))` for `x, y > 0`. -/
private lemma two_rpow_mul_logb_aux (x y a b : ℝ) (hx : 0 < x) (hy : 0 < y) (hab : a + b ≠ 0) :
    (2:ℝ)^(a * (Real.logb 2 (x / y) / (a + b))) = (x/y)^(a/(a+b)) := by
  have hxy : 0 < x/y := div_pos hx hy
  have h2 : (2:ℝ)^(Real.logb 2 (x/y)) = x/y := Real.rpow_logb (by norm_num) (by norm_num) hxy
  have hle : (0:ℝ) ≤ 2 := by norm_num
  rw [show a * (Real.logb 2 (x / y) / (a + b)) = Real.logb 2 (x/y) * (a/(a+b)) by field_simp]
  rw [Real.rpow_mul hle, h2]

/-- `2 ^ (-(a * logb 2 (x/y) / (a+b))) = (y/x) ^ (a/(a+b))` for `x, y > 0`. -/
private lemma two_rpow_neg_mul_logb_aux (x y a b : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hab : a + b ≠ 0) :
    (2:ℝ)^(-(a * (Real.logb 2 (x / y) / (a + b)))) = (y/x)^(a/(a+b)) := by
  have hxy : 0 < x/y := div_pos hx hy
  have h2 : (2:ℝ)^(Real.logb 2 (x/y)) = x/y := Real.rpow_logb (by norm_num) (by norm_num) hxy
  have hle : (0:ℝ) ≤ 2 := by norm_num
  rw [show -(a * (Real.logb 2 (x / y) / (a + b))) = Real.logb 2 (x/y) * (-(a/(a+b))) by field_simp]
  rw [Real.rpow_mul hle, h2, Real.rpow_neg hxy.le, ← Real.inv_rpow hxy.le, inv_div]

private lemma one_sub_div_add_aux (a b : ℝ) (h : a + b ≠ 0) : 1 - a/(a+b) = b/(a+b) := by
  field_simp
  ring

private lemma one_sub_div_add_comm_aux (a b : ℝ) (h : a + b ≠ 0) : 1 - b/(a+b) = a/(a+b) := by
  field_simp
  ring

/-- The crossing point: there is an integer `K` such that `P * 2^{-A K}` and `Q * 2^{B K}`
are both controlled by the weighted geometric mean `P^{B/(A+B)} Q^{A/(A+B)}`. -/
private lemma exists_crossing_point_aux (A B : ℕ) (hA : 0 < A) (hB : 0 < B) {P Q : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) :
    ∃ K : ℤ,
      P * (2 : ℝ) ^ (-(A : ℤ) * K) ≤
        P ^ ((B : ℝ) / ((A : ℝ) + (B : ℝ))) * Q ^ ((A : ℝ) / ((A : ℝ) + (B : ℝ)))
      ∧ Q * (2 : ℝ) ^ ((B : ℤ) * K) ≤
        2 ^ B * (P ^ ((B : ℝ) / ((A : ℝ) + (B : ℝ))) * Q ^ ((A : ℝ) / ((A : ℝ) + (B : ℝ)))) := by
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hABne : ((A:ℝ) + (B:ℝ)) ≠ 0 := by positivity
  set r : ℝ := Real.logb 2 (P/Q) / ((A:ℝ)+(B:ℝ)) with hr
  refine ⟨⌈r⌉, ?_, ?_⟩
  · have h2Ar : (2:ℝ)^(-((A:ℝ)*r)) = (Q/P)^((A:ℝ)/((A:ℝ)+(B:ℝ))) := by
      rw [hr]
      exact two_rpow_neg_mul_logb_aux P Q (A:ℝ) (B:ℝ) hP hQ hABne
    have hid : P * (Q/P)^((A:ℝ)/((A:ℝ)+(B:ℝ)))
        = P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^((A:ℝ)/((A:ℝ)+(B:ℝ))) :=
      calc P * (Q/P)^((A:ℝ)/((A:ℝ)+(B:ℝ)))
          = Q^((A:ℝ)/((A:ℝ)+(B:ℝ))) * P^(1 - (A:ℝ)/((A:ℝ)+(B:ℝ))) :=
            mul_div_rpow_aux Q P ((A:ℝ)/((A:ℝ)+(B:ℝ))) hQ hP
        _ = P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^((A:ℝ)/((A:ℝ)+(B:ℝ))) := by
            rw [one_sub_div_add_aux (A:ℝ) (B:ℝ) hABne]
            ring
    calc P * (2:ℝ)^(-(A:ℤ)*⌈r⌉)
        ≤ P * (2:ℝ)^(-((A:ℝ)*r)) := by
          apply mul_le_mul_of_nonneg_left _ hP.le
          rw [← Real.rpow_intCast (2:ℝ) (-(A:ℤ)*⌈r⌉)]
          rw [Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)]
          push_cast
          nlinarith [Int.le_ceil r]
      _ = P * (Q/P)^((A:ℝ)/((A:ℝ)+(B:ℝ))) := by rw [h2Ar]
      _ = P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^((A:ℝ)/((A:ℝ)+(B:ℝ))) := hid
  · have h2Br : (2:ℝ)^((B:ℝ)*r) = (P/Q)^((B:ℝ)/((A:ℝ)+(B:ℝ))) := by
      rw [hr]
      have key := two_rpow_mul_logb_aux P Q (B:ℝ) (A:ℝ) hP hQ (by positivity : (B:ℝ)+(A:ℝ) ≠ 0)
      simpa [add_comm] using key
    have hid : Q * (P/Q)^((B:ℝ)/((A:ℝ)+(B:ℝ)))
        = P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^((A:ℝ)/((A:ℝ)+(B:ℝ))) :=
      calc Q * (P/Q)^((B:ℝ)/((A:ℝ)+(B:ℝ)))
          = P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^(1 - (B:ℝ)/((A:ℝ)+(B:ℝ))) :=
            mul_div_rpow_aux P Q ((B:ℝ)/((A:ℝ)+(B:ℝ))) hP hQ
        _ = P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^((A:ℝ)/((A:ℝ)+(B:ℝ))) := by
            rw [one_sub_div_add_comm_aux (A:ℝ) (B:ℝ) hABne]
    calc Q * (2:ℝ)^((B:ℤ)*⌈r⌉)
        ≤ Q * ((2:ℝ)^B * (2:ℝ)^((B:ℝ)*r)) := by
          apply mul_le_mul_of_nonneg_left _ hQ.le
          rw [← Real.rpow_intCast (2:ℝ) ((B:ℤ)*⌈r⌉)]
          rw [← Real.rpow_natCast (2:ℝ) B]
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          rw [Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)]
          push_cast
          nlinarith [Int.ceil_lt_add_one r]
      _ = Q * (2:ℝ)^B * (2:ℝ)^((B:ℝ)*r) := by ring
      _ = (2:ℝ)^B * (Q * (P/Q)^((B:ℝ)/((A:ℝ)+(B:ℝ)))) := by rw [h2Br]; ring
      _ = 2^B * (P^((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q^((A:ℝ)/((A:ℝ)+(B:ℝ)))) := by rw [hid]

private lemma two_zpow_neg_lt_one_aux (a : ℕ) (ha : 0 < a) : (2:ℝ)^(-(a:ℤ)) < 1 := by
  have h1 : (1:ℤ) ≤ (a:ℤ) := by exact_mod_cast ha
  have h2 : -(a:ℤ) ≤ (-1:ℤ) := by omega
  have h3 : (2:ℝ)^(-(a:ℤ)) ≤ (2:ℝ)^((-1:ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) h2
  have h4 : (2:ℝ)^((-1:ℤ)) < 1 := by norm_num
  linarith

private lemma inv_one_sub_le_two_aux (a : ℕ) (ha : 0 < a) :
    (1 - (2:ℝ)^(-(a:ℤ)))⁻¹ ≤ 2 := by
  have h2 : (2:ℝ)^(-(a:ℤ)) ≤ 1/2 := by
    have h1 : (1:ℤ) ≤ (a:ℤ) := by exact_mod_cast ha
    have h2 : -(a:ℤ) ≤ (-1:ℤ) := by omega
    calc (2:ℝ)^(-(a:ℤ)) ≤ (2:ℝ)^((-1:ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) h2
      _ = 1/2 := by norm_num
  have h3 : (1:ℝ)/2 ≤ 1 - (2:ℝ)^(-(a:ℤ)) := by linarith
  calc (1 - (2:ℝ)^(-(a:ℤ)))⁻¹ = 1/(1 - (2:ℝ)^(-(a:ℤ))) := by rw [one_div]
    _ ≤ 1/(1/2) := one_div_le_one_div_of_le (by norm_num) h3
    _ = 2 := by norm_num

/-- Splitting `2 ^ (-(a) * (K + n))` into a constant times a geometric sequence. -/
private lemma zpow_shift_aux (a : ℕ) (K : ℤ) (n : ℕ) :
    (2:ℝ)^((-(a:ℤ))*(K + (n:ℤ))) = (2:ℝ)^((-(a:ℤ))*K) * ((2:ℝ)^(-(a:ℤ)))^n := by
  have h : (2:ℝ)^((-(a:ℤ))*(n:ℤ)) = ((2:ℝ)^(-(a:ℤ)))^n := by rw [zpow_mul, zpow_natCast]
  rw [show (-(a:ℤ))*(K + (n:ℤ)) = (-(a:ℤ))*K + (-(a:ℤ))*(n:ℤ) by ring]
  rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  exact congrArg (fun t => (2:ℝ)^((-(a:ℤ))*K) * t) h

private lemma summable_mul_two_zpow_add_aux (a : ℕ) (ha : 0 < a) (c : ℝ) (K : ℤ) :
    Summable fun n : ℕ => c * (2:ℝ)^((-(a:ℤ))*(K + (n:ℤ))) := by
  have hpos : (0:ℝ) < (2:ℝ)^(-(a:ℤ)) := zpow_pos (by norm_num) _
  have hnorm : ‖(2:ℝ)^(-(a:ℤ))‖ < 1 := by
    rw [Real.norm_of_nonneg hpos.le]; exact two_zpow_neg_lt_one_aux a ha
  refine ((summable_geometric_of_norm_lt_one hnorm).mul_left
    (c * (2:ℝ)^((-(a:ℤ))*K))).congr (fun n => ?_)
  rw [zpow_shift_aux a K n]
  ring

private lemma tsum_mul_two_zpow_add_aux (a : ℕ) (ha : 0 < a) (c : ℝ) (K : ℤ) :
    ∑' n : ℕ, c * (2:ℝ)^((-(a:ℤ))*(K + (n:ℤ)))
      = c * (2:ℝ)^((-(a:ℤ))*K) * (1 - (2:ℝ)^(-(a:ℤ)))⁻¹ := by
  have hpos : (0:ℝ) < (2:ℝ)^(-(a:ℤ)) := zpow_pos (by norm_num) _
  have hlt : (2:ℝ)^(-(a:ℤ)) < 1 := two_zpow_neg_lt_one_aux a ha
  rw [show (∑' n : ℕ, c * (2:ℝ)^((-(a:ℤ))*(K + (n:ℤ))))
      = ∑' n : ℕ, (c * (2:ℝ)^((-(a:ℤ))*K)) * ((2:ℝ)^(-(a:ℤ)))^n from
    tsum_congr (fun n => by rw [zpow_shift_aux a K n]; ring)]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hpos.le hlt]

private lemma summable_mul_two_zpow_sub_aux (b : ℕ) (hb : 0 < b) (c : ℝ) (K : ℤ) :
    Summable fun n : ℕ => c * (2:ℝ)^((b:ℤ)*(K - 1 - (n:ℤ))) := by
  refine (summable_mul_two_zpow_add_aux b hb c (1 - K)).congr (fun n => ?_)
  rw [show (-(b:ℤ))*((1-K) + (n:ℤ)) = (b:ℤ)*(K - 1 - (n:ℤ)) by ring]

private lemma tsum_mul_two_zpow_sub_aux (b : ℕ) (hb : 0 < b) (c : ℝ) (K : ℤ) :
    ∑' n : ℕ, c * (2:ℝ)^((b:ℤ)*(K - 1 - (n:ℤ)))
      = c * (2:ℝ)^((b:ℤ)*(K-1)) * (1 - (2:ℝ)^(-(b:ℤ)))⁻¹ := by
  rw [show (∑' n : ℕ, c * (2:ℝ)^((b:ℤ)*(K - 1 - (n:ℤ))))
      = ∑' n : ℕ, c * (2:ℝ)^((-(b:ℤ))*((1-K) + (n:ℤ))) from
    tsum_congr (fun n => by
      rw [show (b:ℤ)*(K - 1 - (n:ℤ)) = (-(b:ℤ))*((1-K) + (n:ℤ)) by ring])]
  rw [tsum_mul_two_zpow_add_aux b hb c (1 - K), show (-(b:ℤ))*(1-K) = (b:ℤ)*(K-1) by ring]

/-- Splitting a `ℤ`-indexed sum at an arbitrary integer into its two half lines. -/
private lemma tsum_int_split_aux (f : ℤ → ℝ) (K : ℤ)
    (h1 : Summable fun n : ℕ => f (K - 1 - (n : ℤ)))
    (h2 : Summable fun n : ℕ => f (K + (n : ℤ))) :
    ∑' m : ℤ, f m = (∑' n : ℕ, f (K - 1 - (n : ℤ))) + (∑' n : ℕ, f (K + (n : ℤ))) := by
  have hshift : ∑' m : ℤ, f m = ∑' m : ℤ, f (m + K) := by
    simpa using (Equiv.tsum_eq (Equiv.addRight K) f).symm
  have h1' : Summable fun n : ℕ => f (-((n : ℤ) + 1) + K) :=
    h1.congr (fun n => by congr 1; ring)
  have h2' : Summable fun n : ℕ => f ((n : ℤ) + K) :=
    h2.congr (fun n => by congr 1; ring)
  have hsplit : ∑' m : ℤ, f (m + K)
      = (∑' n : ℕ, f ((n:ℤ) + K)) + (∑' n : ℕ, f (-((n : ℤ) + 1) + K)) :=
    tsum_of_nat_of_neg_add_one h2' h1'
  have e1 : (∑' n : ℕ, f ((n:ℤ) + K)) = ∑' n : ℕ, f (K + (n:ℤ)) :=
    tsum_congr (fun n => by congr 1; ring)
  have e2 : (∑' n : ℕ, f (-((n : ℤ) + 1) + K)) = ∑' n : ℕ, f (K - 1 - (n:ℤ)) :=
    tsum_congr (fun n => by congr 1; ring)
  rw [hshift, hsplit, e1, e2, add_comm]

/-- The main estimate for `P, Q > 0`. -/
private lemma tsum_min_geometric_pos_aux (A B : ℕ) (hA : 0 < A) (hB : 0 < B) {P Q : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) :
    Summable (fun m : ℤ => min (P * (2:ℝ)^(-(A:ℤ)*m)) (Q * (2:ℝ)^((B:ℤ)*m))) ∧
    ∑' m : ℤ, min (P * (2:ℝ)^(-(A:ℤ)*m)) (Q * (2:ℝ)^((B:ℤ)*m))
      ≤ 4 * P ^ ((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q ^ ((A:ℝ)/((A:ℝ)+(B:ℝ))) := by
  obtain ⟨K, hK1, hK2⟩ := exists_crossing_point_aux A B hA hB hP hQ
  set M : ℝ := P ^ ((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q ^ ((A:ℝ)/((A:ℝ)+(B:ℝ))) with hM
  have hsumA : Summable fun n : ℕ => P * (2:ℝ)^((-(A:ℤ))*(K + (n:ℤ))) :=
    summable_mul_two_zpow_add_aux A hA P K
  have hsumB : Summable fun n : ℕ => Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ))) :=
    summable_mul_two_zpow_sub_aux B hB Q K
  have hP2 : P * (2:ℝ)^((-(A:ℤ))*K) ≤ M := by rw [hM]; exact hK1
  have hQ2 : Q * (2:ℝ)^((B:ℤ)*(K-1)) ≤ M := by
    have hpow : (2:ℝ)^((B:ℤ)*(K-1)) = (2:ℝ)^((B:ℤ)*K) / 2^B := by
      rw [show (B:ℤ)*(K-1) = (B:ℤ)*K - (B:ℤ) by ring,
        zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_natCast]
    rw [hpow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < 2^B)]
    rw [hM]
    linarith [hK2]
  have hMnonneg : (0:ℝ) ≤ M := by rw [hM]; positivity
  have hnegA : (0:ℝ) ≤ P * (2:ℝ)^((-(A:ℤ))*K) :=
    mul_nonneg hP.le (zpow_nonneg (by norm_num) _)
  have hnegB : (0:ℝ) ≤ Q * (2:ℝ)^((B:ℤ)*(K-1)) :=
    mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)
  have hbndA : (∑' n : ℕ,
      min (P * (2:ℝ)^(-(A:ℤ)*(K + (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K + (n:ℤ))))) ≤ 2 * M := by
    have hmin : Summable fun n : ℕ =>
        min (P * (2:ℝ)^(-(A:ℤ)*(K + (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K + (n:ℤ)))) :=
      Summable.of_nonneg_of_le
        (fun n => le_min (mul_nonneg hP.le (zpow_nonneg (by norm_num) _))
          (mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)))
        (fun n => min_le_left _ _) hsumA
    calc (∑' n : ℕ, min (P * (2:ℝ)^(-(A:ℤ)*(K + (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K + (n:ℤ)))))
        ≤ ∑' n : ℕ, P * (2:ℝ)^((-(A:ℤ))*(K + (n:ℤ))) :=
          Summable.tsum_le_tsum (fun n => min_le_left _ _) hmin hsumA
      _ = P * (2:ℝ)^((-(A:ℤ))*K) * (1 - (2:ℝ)^(-(A:ℤ)))⁻¹ :=
          tsum_mul_two_zpow_add_aux A hA P K
      _ ≤ 2 * M := by
          calc P * (2:ℝ)^((-(A:ℤ))*K) * (1 - (2:ℝ)^(-(A:ℤ)))⁻¹ ≤ M * 2 :=
                mul_le_mul hP2 (inv_one_sub_le_two_aux A hA)
                  (inv_nonneg.mpr (by linarith [two_zpow_neg_lt_one_aux A hA])) hMnonneg
            _ = 2 * M := by ring
  have hbndB : (∑' n : ℕ,
      min (P * (2:ℝ)^(-(A:ℤ)*(K - 1 - (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ))))) ≤ 2 * M := by
    have hmin : Summable fun n : ℕ =>
        min (P * (2:ℝ)^(-(A:ℤ)*(K - 1 - (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ)))) :=
      Summable.of_nonneg_of_le
        (fun n => le_min (mul_nonneg hP.le (zpow_nonneg (by norm_num) _))
          (mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)))
        (fun n => min_le_right _ _) hsumB
    calc (∑' n : ℕ,
          min (P * (2:ℝ)^(-(A:ℤ)*(K - 1 - (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ)))))
        ≤ ∑' n : ℕ, Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ))) :=
          Summable.tsum_le_tsum (fun n => min_le_right _ _) hmin hsumB
      _ = Q * (2:ℝ)^((B:ℤ)*(K-1)) * (1 - (2:ℝ)^(-(B:ℤ)))⁻¹ :=
          tsum_mul_two_zpow_sub_aux B hB Q K
      _ ≤ 2 * M := by
          calc Q * (2:ℝ)^((B:ℤ)*(K-1)) * (1 - (2:ℝ)^(-(B:ℤ)))⁻¹ ≤ M * 2 :=
                mul_le_mul hQ2 (inv_one_sub_le_two_aux B hB)
                  (inv_nonneg.mpr (by linarith [two_zpow_neg_lt_one_aux B hB])) hMnonneg
            _ = 2 * M := by ring
  -- summability of the two halves of the original sequence
  have hhalf2 : Summable fun n : ℕ =>
      min (P * (2:ℝ)^(-(A:ℤ)*(n:ℤ))) (Q * (2:ℝ)^((B:ℤ)*(n:ℤ))) := by
    have hmaj : Summable fun n : ℕ => P * (2:ℝ)^((-(A:ℤ))*((0:ℤ) + (n:ℤ))) :=
      summable_mul_two_zpow_add_aux A hA P 0
    have hmaj' : Summable fun n : ℕ => P * (2:ℝ)^(-(A:ℤ)*(n:ℤ)) :=
      hmaj.congr (fun n => by rw [show (-(A:ℤ))*((0:ℤ) + (n:ℤ)) = -(A:ℤ)*(n:ℤ) by ring])
    exact Summable.of_nonneg_of_le
      (fun n => le_min (mul_nonneg hP.le (zpow_nonneg (by norm_num) _))
        (mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)))
      (fun n => min_le_left _ _) hmaj'
  have hhalf1 : Summable fun n : ℕ =>
      min (P * (2:ℝ)^(-(A:ℤ)*(-((n:ℤ) + 1)))) (Q * (2:ℝ)^((B:ℤ)*(-((n:ℤ) + 1)))) := by
    have hmaj : Summable fun n : ℕ => Q * (2:ℝ)^((B:ℤ)*(0 - 1 - (n:ℤ))) :=
      summable_mul_two_zpow_sub_aux B hB Q 0
    have hmaj' : Summable fun n : ℕ => Q * (2:ℝ)^((B:ℤ)*(-((n:ℤ) + 1))) :=
      hmaj.congr (fun n => by rw [show (B:ℤ)*(0 - 1 - (n:ℤ)) = (B:ℤ)*(-((n:ℤ) + 1)) by ring])
    exact Summable.of_nonneg_of_le
      (fun n => le_min (mul_nonneg hP.le (zpow_nonneg (by norm_num) _))
        (mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)))
      (fun n => min_le_right _ _) hmaj'
  have hsumf : Summable fun m : ℤ =>
      min (P * (2:ℝ)^(-(A:ℤ)*m)) (Q * (2:ℝ)^((B:ℤ)*m)) :=
    Summable.of_nat_of_neg_add_one hhalf2 hhalf1
  -- summability of the two shifted pieces (for the split)
  have hsh1 : Summable fun n : ℕ =>
      min (P * (2:ℝ)^(-(A:ℤ)*(K - 1 - (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ)))) :=
    Summable.of_nonneg_of_le
      (fun n => le_min (mul_nonneg hP.le (zpow_nonneg (by norm_num) _))
        (mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)))
      (fun n => min_le_right _ _) hsumB
  have hsh2 : Summable fun n : ℕ =>
      min (P * (2:ℝ)^(-(A:ℤ)*(K + (n:ℤ)))) (Q * (2:ℝ)^((B:ℤ)*(K + (n:ℤ)))) :=
    Summable.of_nonneg_of_le
      (fun n => le_min (mul_nonneg hP.le (zpow_nonneg (by norm_num) _))
        (mul_nonneg hQ.le (zpow_nonneg (by norm_num) _)))
      (fun n => min_le_left _ _) hsumA
  refine ⟨hsumf, ?_⟩
  have hsp := tsum_int_split_aux
    (fun m : ℤ => min (P * (2:ℝ)^(-(A:ℤ)*m)) (Q * (2:ℝ)^((B:ℤ)*m))) K hsh1 hsh2
  calc ∑' m : ℤ, min (P * (2:ℝ)^(-(A:ℤ)*m)) (Q * (2:ℝ)^((B:ℤ)*m))
      = (∑' n : ℕ, min (P * (2:ℝ)^(-(A:ℤ)*(K - 1 - (n:ℤ))))
            (Q * (2:ℝ)^((B:ℤ)*(K - 1 - (n:ℤ)))))
        + (∑' n : ℕ, min (P * (2:ℝ)^(-(A:ℤ)*(K + (n:ℤ))))
            (Q * (2:ℝ)^((B:ℤ)*(K + (n:ℤ))))) := hsp
    _ ≤ 2 * M + 2 * M := add_le_add hbndB hbndA
    _ = 4 * M := by ring
    _ = 4 * P ^ ((B:ℝ)/((A:ℝ)+(B:ℝ))) * Q ^ ((A:ℝ)/((A:ℝ)+(B:ℝ))) := by rw [hM]; ring

theorem tsum_min_geometric (A B : ℕ) (hA : 0 < A) (hB : 0 < B) : ∃ C : ℝ, 0 ≤ C ∧ ∀ P Q : ℝ, 0 ≤ P → 0 ≤ Q → Summable (fun m : ℤ => min (P * (2 : ℝ) ^ (-(A : ℤ) * m)) (Q * (2 : ℝ) ^ ((B : ℤ) * m))) ∧ ∑' m : ℤ, min (P * (2 : ℝ) ^ (-(A : ℤ) * m)) (Q * (2 : ℝ) ^ ((B : ℤ) * m)) ≤ C * P ^ ((B : ℝ) / ((A : ℝ) + (B : ℝ))) * Q ^ ((A : ℝ) / ((A : ℝ) + (B : ℝ))) := by
  refine ⟨4, by norm_num, ?_⟩
  intro P Q hP hQ
  rcases eq_or_lt_of_le hP with hP0 | hPpos
  · rw [← hP0]
    have hfun : (fun m : ℤ => min ((0:ℝ) * (2:ℝ)^(-(A:ℤ)*m)) (Q * (2:ℝ)^((B:ℤ)*m)))
        = fun _ => (0:ℝ) := by
      funext m
      rw [zero_mul, min_eq_left (mul_nonneg hQ (zpow_nonneg (by norm_num) _))]
    rw [hfun]
    refine ⟨summable_zero, ?_⟩
    rw [tsum_zero, Real.zero_rpow (by positivity : (B:ℝ)/((A:ℝ)+(B:ℝ)) ≠ 0)]
    simp
  · rcases eq_or_lt_of_le hQ with hQ0 | hQpos
    · rw [← hQ0]
      have hfun : (fun m : ℤ => min (P * (2:ℝ)^(-(A:ℤ)*m)) ((0:ℝ) * (2:ℝ)^((B:ℤ)*m)))
          = fun _ => (0:ℝ) := by
        funext m
        rw [zero_mul, min_eq_right (mul_nonneg hP (zpow_nonneg (by norm_num) _))]
      rw [hfun]
      refine ⟨summable_zero, ?_⟩
      rw [tsum_zero, Real.zero_rpow (by positivity : (A:ℝ)/((A:ℝ)+(B:ℝ)) ≠ 0)]
      simp
    · exact tsum_min_geometric_pos_aux A B hA hB hPpos hQpos

end Work.BourgainPlan.Maximal
