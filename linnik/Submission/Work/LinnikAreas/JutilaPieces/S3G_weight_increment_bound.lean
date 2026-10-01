import Mathlib

/-!
# Weight-increment bound of the `S₃` assembly

Re-homing of `Work.LinnikAreas.Density4.BzS3.S3G_weight_increment_bound` (which is stubbed in that
file).  With `w(m) = (log m − α)(log m − β)` we prove

  `Σ_{m ≤ X−1} |w(m+1) − w(m)|·√m ≤ C·√X·(1+|log(2X) − α|)·(1+|log(2X) − β|)`

for `X ≥ 2` and `α, β ≥ 0`, with an absolute constant `C` (here `C = 200`).

The proof is elementary.  Writing `a = log m`, `b = log(m+1)`, `L = log(2X)` and `d = b − a ≥ 0`,

  `w(m+1) − w(m) = (b−α)(b−β) − (a−α)(a−β) = (b−a)·(a+b−α−β)`,

so `|w(m+1) − w(m)| ≤ (1/m)·(2L − a − b + |L−α| + |L−β|)` because `|b − a| = log((m+1)/m) ≤ 1/m`,
`a + b = log(m(m+1)) ≤ 2L` (as `m(m+1) ≤ X² ≤ (2X)²`), `2L − a − b ≤ 2(L − a) = 2 log(2X/m)`, and
`|2L − α − β| ≤ |L−α| + |L−β|`.  Multiplying by `√m` and summing,

  `Σ ≤ 2·Σ_{m≤X} log(2X/m)/√m + (|L−α|+|L−β|)·Σ_{m≤X} 1/√m`,

and the two sums are bounded by `100√X` and `2√X` respectively (the first via
`log u ≤ 4u^{1/4}` and `Σ m^{-3/4} ≤ 4·2^{1/4}X^{1/4}`; the second by `1/√m ≤ 2(√m − √(m−1))`).
This gives `200√X + 2√X(|L−α|+|L−β|) ≤ 200√X(1+|L−α|)(1+|L−β|)`.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-! ## Elementary summation and real-analysis lemmas -/

/-- `√m/m = 1/√m` for `m ≥ 1`. -/
lemma sqrt_div_self_nat (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (m : ℝ) / (m : ℝ) = 1 / Real.sqrt (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hs : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
    rw [← pow_two]; exact Real.sq_sqrt hm0.le
  field_simp
  linarith [hsq]

/-- `1/√m ≤ 2(√m − √(m−1))` for `m ≥ 1`. -/
lemma inv_sqrt_le_two_sqrt_sub (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / Real.sqrt (m : ℝ) ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h : 0 < m := by omega
    exact_mod_cast h
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  have hspos : (0 : ℝ) ≤ Real.sqrt (((m-1 : ℕ)) : ℝ) := Real.sqrt_nonneg _
  have hle : Real.sqrt (((m-1 : ℕ)) : ℝ) ≤ Real.sqrt (m : ℝ) := by
    apply Real.sqrt_le_sqrt
    have hmle : (m-1 : ℕ) ≤ m := by omega
    exact_mod_cast hmle
  have hsq1 : (Real.sqrt (m : ℝ))^2 = (m : ℝ) := Real.sq_sqrt hm0.le
  have hsq2 : (Real.sqrt (((m-1 : ℕ)) : ℝ))^2 = (((m-1 : ℕ)) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hden : (0 : ℝ) < Real.sqrt (m : ℝ) + Real.sqrt (((m-1 : ℕ)) : ℝ) := by linarith
  have hkey : (Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ))
      * (Real.sqrt (m : ℝ) + Real.sqrt (((m-1 : ℕ)) : ℝ)) = (m : ℝ) - (((m-1 : ℕ)) : ℝ) := by
    rw [show (Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ))
        * (Real.sqrt (m : ℝ) + Real.sqrt (((m-1 : ℕ)) : ℝ))
        = (Real.sqrt (m : ℝ))^2 - (Real.sqrt (((m-1 : ℕ)) : ℝ))^2 by ring, hsq1, hsq2]
  have hdiff : Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ)
      = ((m : ℝ) - (((m-1 : ℕ)) : ℝ))
        / (Real.sqrt (m : ℝ) + Real.sqrt (((m-1 : ℕ)) : ℝ)) := by
    rw [eq_div_iff (ne_of_gt hden)]; linarith [hkey]
  rw [hdiff, ← mul_div_assoc, div_le_div_iff₀ hsm hden]
  have hsub : (m : ℝ) - (((m-1 : ℕ)) : ℝ) = 1 := by
    have h1 : ((m-1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; norm_num
    linarith
  rw [hsub]
  linarith

/-- The telescoping sum `∑_{m ≤ X} (√m − √(m−1)) = √X`. -/
lemma sum_Icc_sqrt_sub_pred (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, (Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ)))
      = Real.sqrt (X : ℝ) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rcases Nat.eq_zero_or_pos X with hX0 | hXpos
    · subst hX0; simp
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1), ih]
      have h1 : ((X+1 : ℕ) - 1 : ℕ) = X := by omega
      rw [h1]; ring

/-- `∑_{m ≤ X} 1/√m ≤ 2√X`. -/
lemma inv_sqrt_sum_le (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, (1 : ℝ)/Real.sqrt (m : ℝ)) ≤ 2 * Real.sqrt (X : ℝ) := by
  calc (∑ m ∈ Finset.Icc 1 X, (1 : ℝ)/Real.sqrt (m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 X, 2 * (Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        simp only [Finset.mem_Icc] at hm
        exact inv_sqrt_le_two_sqrt_sub m hm.1
    _ = 2 * (∑ m ∈ Finset.Icc 1 X, (Real.sqrt (m : ℝ) - Real.sqrt (((m-1 : ℕ)) : ℝ))) := by
        rw [Finset.mul_sum]
    _ = 2 * Real.sqrt (X : ℝ) := by rw [sum_Icc_sqrt_sub_pred X]

/-- `(Y/m)^{1/4}/√m = Y^{1/4}·m^{-3/4}` for `Y ≥ 0`, `m > 0`. -/
lemma rpow_quarter_div_sqrt (Y m : ℝ) (hY : 0 ≤ Y) (hm : 0 < m) :
    (Y/m)^(1/4 : ℝ)/Real.sqrt m = Y^(1/4 : ℝ) * m^(-(3/4) : ℝ) := by
  have h1 : m^(1/4 : ℝ) * m^(1/2 : ℝ) = m^(3/4 : ℝ) := by
    rw [← Real.rpow_add hm]; norm_num
  rw [Real.div_rpow hY hm.le, Real.sqrt_eq_rpow, div_div, h1, div_eq_mul_inv,
      ← Real.rpow_neg hm.le]

/-- `∑_{m ≤ X} m^{-3/4} ≤ 4·2^{1/4}·X^{1/4}` for `X ≥ 1`. -/
lemma rpow34_sum_le (X : ℕ) (hX : 1 ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, ((m : ℝ) ^ (-(3/4) : ℝ)))
      ≤ 4 * (2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ) := by
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hant : AntitoneOn (fun x : ℝ => x ^ (-(3/4) : ℝ)) (Set.Icc (1 : ℝ) (1 + (X : ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by linarith [hx.1]
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by norm_num)
  have hint := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := X) hant
  have hcast : ∀ i : ℕ, (1 : ℝ) + ↑(i+1) = ↑(i+2) := by intro i; push_cast; ring
  simp only [hcast] at hint
  have hint2 : (∑ i ∈ Finset.range X, ((i+2 : ℕ) : ℝ) ^ (-(3/4) : ℝ))
      = (∑ m ∈ Finset.Ico 2 (X+2), (m : ℝ) ^ (-(3/4) : ℝ)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  rw [hint2] at hint
  have hsplit : (∑ m ∈ Finset.Icc 1 X, ((m : ℝ) ^ (-(3/4) : ℝ)))
      = (1 : ℝ) ^ (-(3/4) : ℝ) + ∑ m ∈ Finset.Ico 2 (X+1), ((m : ℝ) ^ (-(3/4) : ℝ)) := by
    have h1 : Finset.Icc 1 X = Finset.Ico 1 (X+1) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have h2 : (∑ m ∈ (Finset.Ico (1 : ℕ) 2 : Finset ℕ), ((m : ℝ) ^ (-(3/4) : ℝ)))
        + (∑ m ∈ Finset.Ico 2 (X+1), ((m : ℝ) ^ (-(3/4) : ℝ)))
        = ∑ m ∈ Finset.Ico 1 (X+1), ((m : ℝ) ^ (-(3/4) : ℝ)) :=
      Finset.sum_Ico_consecutive (fun m : ℕ => ((m : ℝ) ^ (-(3/4) : ℝ))) (by norm_num : 1 ≤ 2)
        (by omega : 2 ≤ X + 1)
    have h3 : (∑ m ∈ (Finset.Ico (1 : ℕ) 2 : Finset ℕ), ((m : ℝ) ^ (-(3/4) : ℝ)))
        = (1 : ℝ) ^ (-(3/4) : ℝ) := by
      rw [show (Finset.Ico (1 : ℕ) 2 : Finset ℕ) = {1} from by
        ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega]
      simp
    rw [h1, ← h2, h3]
  have hmono : (∑ m ∈ Finset.Ico 2 (X+1), ((m : ℝ) ^ (-(3/4) : ℝ)))
      ≤ (∑ m ∈ Finset.Ico 2 (X+2), ((m : ℝ) ^ (-(3/4) : ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm; simp only [Finset.mem_Ico] at *; omega
    · intro m hm1 hm2
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)) (-(3/4))
  have hintval : (∫ x in (1 : ℝ)..(1 + (X : ℝ)), x ^ (-(3/4) : ℝ))
      = 4 * ((1 + (X : ℝ)) ^ (1/4 : ℝ) - 1) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3/4)))]
    rw [show (-(3/4 : ℝ)) + 1 = 1/4 by norm_num, Real.one_rpow]
    ring
  have hfin : (1 + (X : ℝ)) ^ (1/4 : ℝ) ≤ (2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ) := by
    have h1 : (1 + (X : ℝ)) ^ (1/4 : ℝ) ≤ ((2 : ℝ) * (X : ℝ)) ^ (1/4 : ℝ) :=
      Real.rpow_le_rpow (x := 1 + (X : ℝ)) (y := 2 * (X : ℝ)) (z := (1/4 : ℝ)) (by positivity)
        (by linarith) (by norm_num)
    have h2 : ((2 : ℝ) * (X : ℝ)) ^ (1/4 : ℝ) = (2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ) :=
      Real.mul_rpow (x := (2 : ℝ)) (y := (X : ℝ)) (z := (1/4 : ℝ)) (by norm_num) hX0.le
    rw [h2] at h1; exact h1
  have hone : (1 : ℝ) ^ (-(3/4) : ℝ) = 1 := Real.one_rpow _
  rw [hsplit, hone]
  linarith [hint, hmono, hfin, hintval]

/-- `∑_{m ≤ X} log(2X/m)/√m ≤ 100·√X` for `X ≥ 1`. -/
lemma log_div_sqrt_sum_le (X : ℕ) (hX : 1 ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, Real.log (2 * (X : ℝ) / (m : ℝ)) / Real.sqrt (m : ℝ))
      ≤ 100 * Real.sqrt (X : ℝ) := by
  have hterm : ∀ m ∈ Finset.Icc 1 X, Real.log (2 * (X : ℝ) / (m : ℝ))/Real.sqrt (m : ℝ)
      ≤ 4 * (2 * (X : ℝ))^(1/4 : ℝ) * (m : ℝ)^(-(3/4) : ℝ) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have h : 0 < m := by omega
      exact_mod_cast h
    have hX0 : (0 : ℝ) < (X : ℝ) := by
      have h : 0 < X := by omega
      exact_mod_cast h
    have h2X0 : (0 : ℝ) < 2 * (X : ℝ) := by linarith
    have hY : (0 : ℝ) ≤ 2 * (X : ℝ) := le_of_lt h2X0
    have hnonneg : (0 : ℝ) ≤ 2 * (X : ℝ)/(m : ℝ) := div_nonneg hY (le_of_lt hm0)
    have hlog := Real.log_le_rpow_div (x := 2 * (X : ℝ)/(m : ℝ)) (ε := (1/4 : ℝ)) hnonneg
      (by norm_num)
    have hlog' : Real.log (2 * (X : ℝ)/(m : ℝ)) ≤ 4 * ((2 * (X : ℝ)/(m : ℝ))^(1/4 : ℝ)) := by
      have h : ((2 * (X : ℝ)/(m : ℝ))^(1/4 : ℝ))/(1/4 : ℝ)
          = 4 * ((2 * (X : ℝ)/(m : ℝ))^(1/4 : ℝ)) := by ring
      linarith [hlog]
    have hid := rpow_quarter_div_sqrt (2 * (X : ℝ)) (m : ℝ) hY hm0
    calc Real.log (2 * (X : ℝ)/(m : ℝ))/Real.sqrt (m : ℝ)
        ≤ 4 * ((2 * (X : ℝ)/(m : ℝ))^(1/4 : ℝ)) / Real.sqrt (m : ℝ) :=
          div_le_div_of_nonneg_right hlog' (Real.sqrt_nonneg _)
      _ = 4 * (((2 * (X : ℝ)/(m : ℝ))^(1/4 : ℝ)) / Real.sqrt (m : ℝ)) := by ring
      _ = 4 * ((2 * (X : ℝ))^(1/4 : ℝ) * (m : ℝ)^(-(3/4) : ℝ)) := by rw [hid]
      _ = 4 * (2 * (X : ℝ))^(1/4 : ℝ) * (m : ℝ)^(-(3/4) : ℝ) := by ring
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have h : 0 < X := by omega
    exact_mod_cast h
  calc (∑ m ∈ Finset.Icc 1 X, Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 X, 4 * (2 * (X : ℝ))^(1/4 : ℝ) * (m : ℝ)^(-(3/4) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = 4 * (2 * (X : ℝ))^(1/4 : ℝ)
          * (∑ m ∈ Finset.Icc 1 X, (m : ℝ)^(-(3/4) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 * (X : ℝ))^(1/4 : ℝ) * (4 * (2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rpow34_sum_le X hX) (by positivity)
    _ = 16 * (2 : ℝ)^(1/2 : ℝ) * Real.sqrt (X : ℝ) := by
        have h1 : (2 * (X : ℝ))^(1/4 : ℝ) = (2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ) :=
          Real.mul_rpow (x := (2 : ℝ)) (y := (X : ℝ)) (z := (1/4 : ℝ)) (by norm_num) hX0.le
        have h2 : (2 : ℝ)^(1/4 : ℝ) * (2 : ℝ)^(1/4 : ℝ) = (2 : ℝ)^(1/2 : ℝ) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
        have h3 : (X : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ) = (X : ℝ)^(1/2 : ℝ) := by
          rw [← Real.rpow_add hX0]; norm_num
        have h4 : (X : ℝ)^(1/2 : ℝ) = Real.sqrt (X : ℝ) := (Real.sqrt_eq_rpow _).symm
        rw [h1]
        rw [show (4 * ((2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ))
              * (4 * (2 : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ)))
              = 16 * ((2 : ℝ)^(1/4 : ℝ) * (2 : ℝ)^(1/4 : ℝ))
                * ((X : ℝ)^(1/4 : ℝ) * (X : ℝ)^(1/4 : ℝ)) by ring]
        rw [h2, h3, h4]
    _ ≤ 100 * Real.sqrt (X : ℝ) := by
        have h2half : (2 : ℝ)^(1/2 : ℝ) ≤ 2 := by
          have h' : (2 : ℝ)^(1/2 : ℝ) ≤ (2 : ℝ)^(1 : ℝ) := by
            rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
            norm_num
          rwa [Real.rpow_one] at h'
        have hs : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right h2half hs]

/-! ## The pointwise weight-increment bound -/

/-- Pointwise bound for the increment of `w(t) = (log t − α)(log t − β)`: for `1 ≤ m`, `m + 1 ≤ X`,
`X ≥ 2`,
  `|w(m+1) − w(m)|·√m ≤ (2 log(2X/m) + |log(2X) − α| + |log(2X) − β|)/√m`. -/
lemma weight_diff_mul_sqrt_le (X m : ℕ) (α β : ℝ) (hX : 2 ≤ X) (hm : 1 ≤ m) (hmX : m + 1 ≤ X) :
    |(Real.log (((m+1:ℕ):ℝ)) - α) * (Real.log (((m+1:ℕ):ℝ)) - β)
      - (Real.log (m:ℝ) - α) * (Real.log (m:ℝ) - β)| * Real.sqrt (m:ℝ)
      ≤ (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |Real.log (2*(X:ℝ)) - α|
          + |Real.log (2*(X:ℝ)) - β|) / Real.sqrt (m:ℝ) := by
  set a : ℝ := Real.log (m:ℝ) with ha
  set b : ℝ := Real.log (((m+1:ℕ)):ℝ) with hb
  set L : ℝ := Real.log (2*(X:ℝ)) with hL
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmp0 : (0:ℝ) < (((m+1:ℕ)):ℝ) := by positivity
  have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h2X0 : (0:ℝ) < 2*(X:ℝ) := by linarith
  have hab : a ≤ b := by
    rw [ha, hb]
    exact Real.log_le_log hm0 (by exact_mod_cast (by omega : m ≤ m+1))
  have hsum2L : a + b ≤ 2*L := by
    rw [ha, hb, hL]
    have hmX' : (m:ℝ) ≤ (X:ℝ) := by exact_mod_cast (by omega : m ≤ X)
    have hmpX : (((m+1:ℕ)):ℝ) ≤ (X:ℝ) := by exact_mod_cast hmX
    rw [← Real.log_mul (ne_of_gt hm0) (ne_of_gt hmp0)]
    rw [show (2:ℝ) * Real.log (2*(X:ℝ)) = Real.log (2*(X:ℝ)) + Real.log (2*(X:ℝ)) by ring,
        ← Real.log_mul (ne_of_gt h2X0) (ne_of_gt h2X0)]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hdiff : b - a ≤ 1/(m:ℝ) := by
    rw [ha, hb]
    have hpos : (0:ℝ) < (((m+1:ℕ)):ℝ)/(m:ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (ne_of_gt hmp0) (ne_of_gt hm0)] at h
    have hval : (((m+1:ℕ)):ℝ)/(m:ℝ) - 1 = 1/(m:ℝ) := by
      field_simp
      push_cast
      ring
    linarith
  have hdiffabs : |b - a| ≤ 1/(m:ℝ) := by
    rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]
    exact hdiff
  have h1 : |a + b - α - β| ≤ (2*L - (a+b)) + (|L - α| + |L - β|) := by
    have hde : a + b - α - β = (a + b - 2*L) + (2*L - α - β) := by ring
    rw [hde]
    have hA : |a + b - 2*L| = 2*L - (a+b) := by rw [abs_of_nonpos (by linarith)]; ring
    have hB : |2*L - α - β| = |(L - α) + (L - β)| := by congr 1; ring
    calc |(a + b - 2*L) + (2*L - α - β)| ≤ |a + b - 2*L| + |2*L - α - β| := abs_add_le _ _
      _ = (2*L - (a+b)) + |(L - α) + (L - β)| := by rw [hA, hB]
      _ ≤ (2*L - (a+b)) + (|L - α| + |L - β|) := by linarith [abs_add_le (L-α) (L-β)]
  have hlog2 : L - a = Real.log (2*(X:ℝ)/(m:ℝ)) := by
    rw [hL, ha, Real.log_div (ne_of_gt h2X0) (ne_of_gt hm0)]
  have h2Lsub : 2*L - (a + b) ≤ 2 * Real.log (2*(X:ℝ)/(m:ℝ)) := by
    have hle : 2*L - (a+b) ≤ 2*L - 2*a := by linarith
    linarith [hlog2]
  have main : |(b - α)*(b - β) - (a - α)*(a - β)|
      ≤ (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) / (m:ℝ) := by
    have hval : (b - α)*(b - β) - (a - α)*(a - β) = (b - a)*(a + b - α - β) := by ring
    rw [hval, abs_mul]
    calc |b - a| * |a + b - α - β|
        ≤ (1/(m:ℝ)) * ((2*L - (a+b)) + (|L - α| + |L - β|)) :=
          mul_le_mul hdiffabs h1 (abs_nonneg _) (by positivity)
      _ ≤ (1/(m:ℝ)) * (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [h2Lsub]
      _ = (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) / (m:ℝ) := by ring
  have hgoal : |(b - α)*(b - β) - (a - α)*(a - β)| * Real.sqrt (m:ℝ)
      ≤ (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) / Real.sqrt (m:ℝ) := by
    calc |(b - α)*(b - β) - (a - α)*(a - β)| * Real.sqrt (m:ℝ)
        ≤ ((2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) / (m:ℝ))
            * Real.sqrt (m:ℝ) :=
          mul_le_mul_of_nonneg_right main (Real.sqrt_nonneg _)
      _ = (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) / Real.sqrt (m:ℝ) := by
          rw [show ((2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|) / (m:ℝ))
                * Real.sqrt (m:ℝ)
                = (2 * Real.log (2*(X:ℝ)/(m:ℝ)) + |L - α| + |L - β|)
                  * (Real.sqrt (m:ℝ)/(m:ℝ)) by ring,
              sqrt_div_self_nat m hm, mul_one_div]
  rw [ha, hb, hL] at hgoal
  exact hgoal

/-! ## The main bound -/

/-- **Weight-increment bound of the `S₃` assembly** (re-homing of
`Work.LinnikAreas.Density4.BzS3.S3G_weight_increment_bound`, stubbed in that file).  With
`w(m) = (log m − α)(log m − β)`,

  `Σ_{m ≤ X−1} |w(m+1) − w(m)|·√m ≤ C·√X·(1+|log(2X) − α|)·(1+|log(2X) − β|)`

for `X ≥ 2`, `0 ≤ α`, `0 ≤ β`.  Pure Mathlib.  Note
`w(m+1) − w(m) = log((m+1)/m)·(log(m(m+1)) − α − β)`, so `|w'|·√m ≪ (1+|log(2m)−α|)(1+|log(2m)−β|)/√m`;
summing gives `≪ √X` times the log-factor at `2X` (worst case `α ≈ β ≈ log(2X)` gives the convergent
`√X·∫₀¹(1+log(1/s))²s^{-1/2}ds ≈ 26√X`), with the `m = 1` boundary term absorbed by `√X`. -/
theorem S3G_weight_increment_bound : ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ) (α β : ℝ),
    2 ≤ X → 0 ≤ α → 0 ≤ β →
    (∑ m ∈ Finset.Icc 1 (X - 1),
        |(Real.log ((m + 1 : ℕ) : ℝ) - α) * (Real.log ((m + 1 : ℕ) : ℝ) - β)
          - (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)| * Real.sqrt (m : ℝ))
      ≤ C * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  refine ⟨200, by norm_num, ?_⟩
  intro X α β hX hα hβ
  set L : ℝ := Real.log (2 * (X : ℝ)) with hL
  have hX1 : 1 ≤ X := by omega
  have hu : 0 ≤ |L - α| := abs_nonneg _
  have hv : 0 ≤ |L - β| := abs_nonneg _
  have hs : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  have hsub : Finset.Icc 1 (X - 1) ⊆ Finset.Icc 1 X := by
    intro m hm; simp only [Finset.mem_Icc] at *; omega
  have hstep : (∑ m ∈ Finset.Icc 1 (X - 1),
        |(Real.log ((m + 1 : ℕ) : ℝ) - α) * (Real.log ((m + 1 : ℕ) : ℝ) - β)
          - (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)| * Real.sqrt (m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 (X - 1),
          (2 * Real.log (2 * (X : ℝ)/(m : ℝ)) + |L - α| + |L - β|) / Real.sqrt (m : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hml : m + 1 ≤ X := by omega
    have h := weight_diff_mul_sqrt_le X m α β hX hm.1 hml
    rw [hL]
    exact h
  have hsplit : (∑ m ∈ Finset.Icc 1 (X - 1),
          (2 * Real.log (2 * (X : ℝ)/(m : ℝ)) + |L - α| + |L - β|) / Real.sqrt (m : ℝ))
      = 2 * (∑ m ∈ Finset.Icc 1 (X - 1), Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ))
        + (|L - α| + |L - β|)
          * (∑ m ∈ Finset.Icc 1 (X - 1), (1 : ℝ)/Real.sqrt (m : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hA : (∑ m ∈ Finset.Icc 1 (X - 1), Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ))
      ≤ 100 * Real.sqrt (X : ℝ) := by
    calc (∑ m ∈ Finset.Icc 1 (X - 1), Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 X, Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro m hm1 hm2
          simp only [Finset.mem_Icc] at hm1
          have hm0 : (0 : ℝ) < (m : ℝ) := by
            have h : 0 < m := by omega
            exact_mod_cast h
          apply div_nonneg _ (Real.sqrt_nonneg _)
          apply Real.log_nonneg
          rw [le_div_iff₀ hm0]
          have hmX : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hm1.2
          linarith
      _ ≤ 100 * Real.sqrt (X : ℝ) := log_div_sqrt_sum_le X hX1
  have hB : (|L - α| + |L - β|)
        * (∑ m ∈ Finset.Icc 1 (X - 1), (1 : ℝ)/Real.sqrt (m : ℝ))
      ≤ (|L - α| + |L - β|) * (2 * Real.sqrt (X : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc (∑ m ∈ Finset.Icc 1 (X - 1), (1 : ℝ)/Real.sqrt (m : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 X, (1 : ℝ)/Real.sqrt (m : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro m hm1 hm2
          exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt (X : ℝ) := inv_sqrt_sum_le X
  have htotal : 2 * (∑ m ∈ Finset.Icc 1 (X - 1),
          Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ))
        + (|L - α| + |L - β|)
          * (∑ m ∈ Finset.Icc 1 (X - 1), (1 : ℝ)/Real.sqrt (m : ℝ))
      ≤ 200 * Real.sqrt (X : ℝ) * (1 + |L - α|) * (1 + |L - β|) := by
    have h1 : 2 * (∑ m ∈ Finset.Icc 1 (X - 1),
          Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ)) ≤ 2 * (100 * Real.sqrt (X : ℝ)) :=
      by linarith [hA]
    have h3 : 200 * Real.sqrt (X : ℝ) + 2 * Real.sqrt (X : ℝ) * (|L - α| + |L - β|)
        ≤ 200 * Real.sqrt (X : ℝ) * (1 + |L - α|) * (1 + |L - β|) := by
      nlinarith [mul_nonneg hs (add_nonneg hu hv), mul_nonneg hs (mul_nonneg hu hv)]
    linarith [h1, hB, h3]
  calc (∑ m ∈ Finset.Icc 1 (X - 1),
        |(Real.log ((m + 1 : ℕ) : ℝ) - α) * (Real.log ((m + 1 : ℕ) : ℝ) - β)
          - (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)| * Real.sqrt (m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 (X - 1),
          (2 * Real.log (2 * (X : ℝ)/(m : ℝ)) + |L - α| + |L - β|) / Real.sqrt (m : ℝ) := hstep
    _ = 2 * (∑ m ∈ Finset.Icc 1 (X - 1), Real.log (2 * (X : ℝ)/(m : ℝ)) / Real.sqrt (m : ℝ))
        + (|L - α| + |L - β|)
          * (∑ m ∈ Finset.Icc 1 (X - 1), (1 : ℝ)/Real.sqrt (m : ℝ)) := hsplit
    _ ≤ 200 * Real.sqrt (X : ℝ) * (1 + |L - α|) * (1 + |L - β|) := htotal

end

end Work.LinnikAreas.JutilaPieces
