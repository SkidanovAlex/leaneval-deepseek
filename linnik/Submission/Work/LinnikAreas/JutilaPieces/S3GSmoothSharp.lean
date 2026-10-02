import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.HarmonicLogBound

namespace Work.LinnikAreas.JutilaPieces

/-! ## Elementary two-sided bounds for `log (m+1) - log m` -/

private lemma log_sub_log_bounds {m : ℕ} (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)
      ∧ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hP : (0 : ℝ) < (m : ℝ) + 1 := by linarith only [hmpos]
  have hlog : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) = Real.log (1 + 1 / (m : ℝ)) := by
    rw [← Real.log_div (x := (m : ℝ) + 1) (y := (m : ℝ)) (ne_of_gt hP) (ne_of_gt hmpos)]
    congr 1
    field_simp
  constructor
  · rw [hlog]
    have h2 : 1 + 1 / (m : ℝ) = ((m : ℝ) / ((m : ℝ) + 1))⁻¹ := by field_simp
    rw [h2, Real.log_inv]
    have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) / ((m : ℝ) + 1) by positivity)
    have hsub : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
      field_simp
      ring
    linarith only [hle, hsub]
  · rw [hlog]
    have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (m : ℝ) by positivity)
    linarith only [hle]

/-! ## `log x ≤ 4 x^{1/4}` and a corollary -/

private lemma LogFourRpow' (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (zero_le_one) hx (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [Real.one_rpow] at h
  have hypos : 0 < x ^ (1 / 4 : ℝ) := lt_of_lt_of_le zero_lt_one hy1
  have h1 := Real.log_le_sub_one_of_pos hypos
  have h2 := Real.log_rpow hxpos (1 / 4 : ℝ)
  rw [h2] at h1
  linarith only [h1]

private lemma log2X_sq_le (X : ℕ) (hX : 1 ≤ X) :
    (Real.log (2 * (X : ℝ)) + 1) ^ 2 ≤ 81 * Real.sqrt (X : ℝ) := by
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have h2X1 : (1 : ℝ) ≤ 2 * (X : ℝ) := by linarith only [hX1R]
  have hlog := LogFourRpow' (2 * (X : ℝ)) h2X1
  have hmul : (2 * (X : ℝ)) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
  have h2q : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) / 4 ≤ 1 by norm_num)
    simpa [Real.rpow_one] using h
  have hX4n : (0 : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hX4_1 : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (zero_le_one) hX1R (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [Real.one_rpow] at h
  have hstep : (2 : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right h2q hX4n
  rw [hmul] at hlog
  have hbig : Real.log (2 * (X : ℝ)) + 1 ≤ 9 * (X : ℝ) ^ (1 / 4 : ℝ) := by
    linarith only [hlog, hstep, hX4_1]
  have hnonneg : 0 ≤ Real.log (2 * (X : ℝ)) + 1 := by
    have : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg h2X1
    linarith only [this]
  have hsq : (Real.log (2 * (X : ℝ)) + 1) ^ 2 ≤ (9 * (X : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    have h := mul_self_le_mul_self hnonneg hbig
    simpa [pow_two] using h
  have hrhs : (9 * (X : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = 81 * Real.sqrt (X : ℝ) := by
    have h4sq : ((X : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (X : ℝ) := by
      rw [Real.sqrt_eq_rpow,
        show ((X : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = ((X : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) from
          (Real.rpow_natCast _ 2).symm,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [mul_pow, h4sq]
    norm_num
  rw [hrhs] at hsq
  exact hsq

/-! ## Telescoping against an explicit antiderivative -/

private lemma telescoping_F (F : ℝ → ℝ) :
    ∀ X : ℕ, 1 ≤ X →
      (∑ m ∈ Finset.Icc 1 (X - 1), (F ((m : ℝ) + 1) - F (m : ℝ))) = F (X : ℝ) - F 1 := by
  intro X hX
  induction X, hX using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have h1 : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
      rw [Nat.add_sub_cancel]
      conv_lhs => rw [h1]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [Nat.sub_add_cancel hn, ih]
      push_cast
      ring

private lemma sum_Icc_sub_antideriv (F g : ℝ → ℝ) (X : ℕ) (hX : 1 ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, g (m : ℝ)) - F (X : ℝ)
      = (∑ m ∈ Finset.Icc 1 (X - 1), (g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))))
        + (g (X : ℝ) - F 1) := by
  have hsplit : (∑ m ∈ Finset.Icc 1 X, g (m : ℝ))
      = (∑ m ∈ Finset.Icc 1 (X - 1), g (m : ℝ)) + g (X : ℝ) := by
    conv_lhs => rw [show X = (X - 1) + 1 from (Nat.sub_add_cancel hX).symm]
    rw [Finset.sum_Icc_succ_top (by omega)]
    congr 1
    rw [Nat.sub_add_cancel hX]
  have htele := telescoping_F F X hX
  have hsum :
      (∑ m ∈ Finset.Icc 1 (X - 1), (g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))))
        = (∑ m ∈ Finset.Icc 1 (X - 1), g (m : ℝ)) - (F (X : ℝ) - F 1) := by
    rw [Finset.sum_sub_distrib, htele]
  rw [hsplit, hsum]
  ring

/-! ## The exact algebraic identity for the Abel/Euler–Maclaurin error term -/

private lemma eta_identity (α β x : ℝ) :
    (Real.log x - α) * (Real.log x - β)
      - ((x + 1) * ((Real.log (x + 1) - α - 1) * (Real.log (x + 1) - β - 1) + 1)
          - x * ((Real.log x - α - 1) * (Real.log x - β - 1) + 1))
    = (Real.log (x + 1) + Real.log x - α - β)
        * (1 - (Real.log (x + 1) - Real.log x) * (x + 1))
      + ((Real.log (x + 1) - Real.log x) * (2 * x + 1) - 2) := by
  ring

private lemma eta_bound (α β : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    |(Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)
      - (((m : ℝ) + 1)
            * ((Real.log ((m : ℝ) + 1) - α - 1) * (Real.log ((m : ℝ) + 1) - β - 1) + 1)
          - (m : ℝ) * ((Real.log (m : ℝ) - α - 1) * (Real.log (m : ℝ) - β - 1) + 1))|
    ≤ (|Real.log ((m : ℝ) + 1) - α| + |Real.log (m : ℝ) - β| + 1) / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith only [hmpos]
  obtain ⟨hlo, hhi⟩ := log_sub_log_bounds hm
  rw [eta_identity α β (m : ℝ)]
  set A : ℝ := Real.log ((m : ℝ) + 1) with hA
  set B : ℝ := Real.log (m : ℝ) with hB
  set d : ℝ := A - B with hd
  have hdlo : 1 / ((m : ℝ) + 1) ≤ d := by rw [hd, hA, hB]; exact hlo
  have hdhi : d ≤ 1 / (m : ℝ) := by rw [hd, hA, hB]; exact hhi
  have h1 : |1 - d * ((m : ℝ) + 1)| ≤ 1 / (m : ℝ) := by
    rw [abs_le]
    constructor
    · have hle : d * ((m : ℝ) + 1) ≤ 1 + 1 / (m : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hdhi (le_of_lt hm1pos)
        have h4 : (1 / (m : ℝ)) * ((m : ℝ) + 1) = 1 + 1 / (m : ℝ) := by
          rw [mul_add, mul_one, div_mul_cancel₀ (1 : ℝ) (ne_of_gt hmpos)]
        rw [h4] at h
        exact h
      linarith only [hle]
    · have hge : 1 ≤ d * ((m : ℝ) + 1) := by
        calc (1 : ℝ) = (1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1) :=
              (div_mul_cancel₀ (1 : ℝ) (by positivity : ((m : ℝ) + 1) ≠ 0)).symm
          _ ≤ d * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_right hdlo (le_of_lt hm1pos)
      have hpos : 0 < 1 / (m : ℝ) := by positivity
      linarith only [hge, hpos]
  have h2 : |d * (2 * (m : ℝ) + 1) - 2| ≤ 1 / (m : ℝ) := by
    rw [abs_le]
    constructor
    · have hge : (1 / ((m : ℝ) + 1)) * (2 * (m : ℝ) + 1) ≤ d * (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hdlo (by linarith only [hmpos] : (0 : ℝ) ≤ 2 * (m : ℝ) + 1)
      have h5 : (1 / ((m : ℝ) + 1)) * (2 * (m : ℝ) + 1) = 2 - 1 / ((m : ℝ) + 1) := by
        field_simp
        ring
      have h6 : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) :=
        one_div_le_one_div_of_le hmpos (by linarith only [])
      linarith only [hlo, hhi, hge, h5]
    · have hle : d * (2 * (m : ℝ) + 1) ≤ (1 / (m : ℝ)) * (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hdhi (by linarith only [hmpos] : (0 : ℝ) ≤ 2 * (m : ℝ) + 1)
      have h7 : (1 / (m : ℝ)) * (2 * (m : ℝ) + 1) = 2 + 1 / (m : ℝ) := by field_simp
      rw [h7] at hle
      linarith only [hle]
  calc |(A + B - α - β) * (1 - d * ((m : ℝ) + 1)) + (d * (2 * (m : ℝ) + 1) - 2)|
      ≤ |(A + B - α - β) * (1 - d * ((m : ℝ) + 1))| + |d * (2 * (m : ℝ) + 1) - 2| :=
        abs_add_le _ _
    _ = |A + B - α - β| * |1 - d * ((m : ℝ) + 1)| + |d * (2 * (m : ℝ) + 1) - 2| := by rw [abs_mul]
    _ ≤ |A + B - α - β| * (1 / (m : ℝ)) + 1 / (m : ℝ) := by
        refine add_le_add ?_ h2
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ (|A - α| + |B - β|) * (1 / (m : ℝ)) + 1 / (m : ℝ) := by
        have h3 : |A + B - α - β| ≤ |A - α| + |B - β| := by
          calc |A + B - α - β| = |(A - α) + (B - β)| := by congr 1; ring
            _ ≤ |A - α| + |B - β| := abs_add_le _ _
        have h4 : |A + B - α - β| * (1 / (m : ℝ)) ≤ (|A - α| + |B - β|) * (1 / (m : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
        linarith only [h4]
    _ = (|A - α| + |B - β| + 1) / (m : ℝ) := by ring

/-! ## The final numerical assembly -/

private lemma sqrt_le_mul_self {A Z : ℝ} (hA : 1 ≤ A) (hZ : 1 ≤ Z) :
    Real.sqrt Z ≤ A * Z := by
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hsZ1 : 1 ≤ Real.sqrt Z := Real.one_le_sqrt.mpr hZ
  have hs : Real.sqrt Z * Real.sqrt Z = Z := by simpa [pow_two] using Real.sq_sqrt hZ0
  have hsZ2 : Real.sqrt Z ≤ Z := by nlinarith only [hsZ1, hs, Real.sqrt_nonneg Z, hZ]
  have hAZ : Z ≤ A * Z := by nlinarith only [hA, hZ0, hZ]
  linarith only [hsZ2, hAZ]

private lemma final_numeric {A B L Z C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hZ : 1 ≤ Z)
    (hL : L ≤ 5 * Real.sqrt Z) (hL0 : 0 ≤ L)
    (hC : C ≤ A + B + 2 * L) :
    C * L + A * B + 82 * (A * B * Z) ≤ 1000 * A * B * Z := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hAB : 1 ≤ A * B := by nlinarith only [hA, hB]
  have hABZ : 1 ≤ A * B * Z := by nlinarith only [hAB, hZ]
  have hCL1 : C * L ≤ (A + B + 2 * L) * L := mul_le_mul_of_nonneg_right hC hL0
  have hAL : A * L ≤ 5 * (A * B * Z) := by
    have h1 : A * L ≤ A * (5 * Real.sqrt Z) := mul_le_mul_of_nonneg_left hL hA0
    have h2 : Real.sqrt Z ≤ B * Z := sqrt_le_mul_self hB hZ
    nlinarith only [h1, h2, hA0, hA]
  have hBL : B * L ≤ 5 * (A * B * Z) := by
    have h1 : B * L ≤ B * (5 * Real.sqrt Z) := mul_le_mul_of_nonneg_left hL hB0
    have h2 : Real.sqrt Z ≤ A * Z := sqrt_le_mul_self hA hZ
    nlinarith only [h1, h2, hB0, hB]
  have hL2 : 2 * L ^ 2 ≤ 50 * (A * B * Z) := by
    have hs : Real.sqrt Z * Real.sqrt Z = Z := by simpa [pow_two] using Real.sq_sqrt hZ0
    have h1 : L ^ 2 ≤ 25 * Z := by nlinarith only [hL, hL0, hs, Real.sqrt_nonneg Z]
    nlinarith only [h1, hABZ, hZ0, hAB, hZ]
  have hCLE : C * L ≤ 60 * (A * B * Z) := by linarith only [hCL1, hAL, hBL, hL2]
  have hAB_le : A * B ≤ A * B * Z := by nlinarith only [hAB, hZ]
  linarith only [hCLE, hAB_le, hABZ, hCL1, hAL, hBL, hL2]

/-- **Smooth-weight main term of the `S₃` assembly** (re-homing of
`Work.ZeroDensity.Jutila.S3GSmoothSharp`, importable from here; with
`wfun α β m = (log m − α)(log m − β)` of `LinnikAreas.Density4.BzS3.S3GAuxDefs` written out, so
that no workspace import is needed):

  `Σ_{m≤X} (log m − α)(log m − β) = X·((log X − α − 1)(log X − β − 1) + 1) + O(√X·(1+|log(2X)−α|)·(1+|log(2X)−β|))`.

Route (first-order Euler–Maclaurin for `f(t) = (log t − α)(log t − β)` on `[1,X]`):
`Σ_{m≤X} f(m) = ∫_1^X f + (f(1)+f(X))/2 + ∫_1^X (t − ⌊t⌋ − 1/2)·f'(t) dt` — equivalently prove
`|Σ_{m≤X} f(m) − ∫_1^X f| ≤ |f(X)| + ∫_1^X |f'(t)| dt` by Abel summation / bounded variation
(the `m = 1` term is `αβ`, absorbed into the constant).  Then
`∫_1^X (log t − α)(log t − β) dt = X((log X − α − 1)(log X − β − 1) + 1) − (αβ + α + β + 2)`
(antiderivative `t·((log t − α − 1)(log t − β − 1) + 1)`), `|f(X)| ≤ (1+|log(2X)−α|)(1+|log(2X)−β|)`,
`|f'(t)| ≤ 2(1+|log t|+|α|+|β|)/t` and `∫_1^X (1+|log t|+|α|+|β|)/t dt ≪ (1+|α|+|β|)log X + log²X`,
which is `≪ √X(1+|log(2X)−α|)(1+|log(2X)−β|)` using `log²t ≤ 16√t` (t ≥ 1) and the trivial
`(1+|α|+|β|) ≤ 3(1+|log(2X)−α|)(1+|log(2X)−β|)·(1+log(2X))²` with `log³X ≪ √X`. -/
theorem S3GSmoothSharp :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℕ) (α β : ℝ), 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |(∑ m ∈ Finset.Icc 1 X, (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β))
        - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)|
      ≤ K * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
          * Real.sqrt (X : ℝ) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro X α β hX hα hβ
  have hX1 : 1 ≤ X := by omega
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith only [hX1R]
  have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1R
  let F : ℝ → ℝ := fun t => t * ((Real.log t - α - 1) * (Real.log t - β - 1) + 1)
  let g : ℝ → ℝ := fun t => (Real.log t - α) * (Real.log t - β)
  set A' : ℝ := 1 + |Real.log (2 * (X : ℝ)) - α| with hA'def
  set B' : ℝ := 1 + |Real.log (2 * (X : ℝ)) - β| with hB'def
  change |(∑ m ∈ Finset.Icc 1 X, g (m : ℝ)) - F (X : ℝ)| ≤ 1000 * A' * B' * Real.sqrt (X : ℝ)
  have hA'1 : 1 ≤ A' := by
    rw [hA'def]; linarith only [abs_nonneg (Real.log (2 * (X : ℝ)) - α)]
  have hB'1 : 1 ≤ B' := by
    rw [hB'def]; linarith only [abs_nonneg (Real.log (2 * (X : ℝ)) - β)]
  have hlog2X : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log (X : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hXpos)
  have hlog2l1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [this]
  have hAX : |Real.log (X : ℝ) - α| ≤ A' := by
    rw [hA'def]
    have hd : Real.log (X : ℝ) - Real.log (2 * (X : ℝ)) = -Real.log 2 := by rw [hlog2X]; ring
    calc |Real.log (X : ℝ) - α|
        = |(Real.log (X : ℝ) - Real.log (2 * (X : ℝ))) + (Real.log (2 * (X : ℝ)) - α)| := by
          congr 1; ring
      _ ≤ |Real.log (X : ℝ) - Real.log (2 * (X : ℝ))| + |Real.log (2 * (X : ℝ)) - α| :=
          abs_add_le _ _
      _ = Real.log 2 + |Real.log (2 * (X : ℝ)) - α| := by
          rw [hd, abs_neg, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
      _ ≤ 1 + |Real.log (2 * (X : ℝ)) - α| := by linarith only [hlog2l1]
  have hBX : |Real.log (X : ℝ) - β| ≤ B' := by
    rw [hB'def]
    have hd : Real.log (X : ℝ) - Real.log (2 * (X : ℝ)) = -Real.log 2 := by rw [hlog2X]; ring
    calc |Real.log (X : ℝ) - β|
        = |(Real.log (X : ℝ) - Real.log (2 * (X : ℝ))) + (Real.log (2 * (X : ℝ)) - β)| := by
          congr 1; ring
      _ ≤ |Real.log (X : ℝ) - Real.log (2 * (X : ℝ))| + |Real.log (2 * (X : ℝ)) - β| :=
          abs_add_le _ _
      _ = Real.log 2 + |Real.log (2 * (X : ℝ)) - β| := by
          rw [hd, abs_neg, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
      _ ≤ 1 + |Real.log (2 * (X : ℝ)) - β| := by linarith only [hlog2l1]
  have hterm : ∀ m ∈ Finset.Icc 1 (X - 1),
      |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|
        ≤ (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1) / (m : ℝ) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hbase : |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|
        ≤ (|Real.log ((m : ℝ) + 1) - α| + |Real.log (m : ℝ) - β| + 1) / (m : ℝ) := by
      simpa only [F, g] using eta_bound α β hm1
    have hmX : (m : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (le_trans hm2 (Nat.sub_le X 1))
    have hmX1 : m + 1 ≤ X := by omega
    have hlogm1_le : Real.log (m : ℝ) ≤ Real.log (X : ℝ) := Real.log_le_log hmpos hmX
    have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
    have hlogm1p0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith only [hmpos])
    have hlogm1X : Real.log ((m : ℝ) + 1) ≤ Real.log (X : ℝ) := by
      refine Real.log_le_log (by linarith only [hmpos]) ?_
      exact_mod_cast hmX1
    have hA : |Real.log ((m : ℝ) + 1) - α| ≤ |Real.log (X : ℝ) - α| + Real.log (X : ℝ) := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : -(Real.log (X : ℝ) - α) ≤ |Real.log (X : ℝ) - α| := neg_le_abs _
        linarith only [hlogm1p0, h1]
      · have h1 : Real.log (X : ℝ) - α ≤ |Real.log (X : ℝ) - α| := le_abs_self _
        linarith only [hlogm1X, hlogX0, h1]
    have hB : |Real.log (m : ℝ) - β| ≤ |Real.log (X : ℝ) - β| + Real.log (X : ℝ) := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : -(Real.log (X : ℝ) - β) ≤ |Real.log (X : ℝ) - β| := neg_le_abs _
        linarith only [hlogm0, hlogX0, h1]
      · have h1 : Real.log (X : ℝ) - β ≤ |Real.log (X : ℝ) - β| := le_abs_self _
        linarith only [hlogm1_le, hlogX0, h1]
    have hstep :
        (|Real.log ((m : ℝ) + 1) - α| + |Real.log (m : ℝ) - β| + 1) / (m : ℝ)
          ≤ (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1) / (m : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith only [hA, hB]
    exact hbase.trans hstep
  have hC0 : 0 ≤ |Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1 := by
    positivity
  have hsum : (∑ m ∈ Finset.Icc 1 (X - 1), |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|)
      ≤ (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1)
          * (1 + Real.log (X : ℝ)) := by
    have h1 : (∑ m ∈ Finset.Icc 1 (X - 1), |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|)
        ≤ ∑ m ∈ Finset.Icc 1 (X - 1),
            (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1) / (m : ℝ) :=
      Finset.sum_le_sum hterm
    have h2 : (∑ m ∈ Finset.Icc 1 (X - 1),
            (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1) / (m : ℝ))
        = (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1)
            * (∑ m ∈ Finset.Icc 1 (X - 1), 1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      ring
    have h3 : (∑ m ∈ Finset.Icc 1 (X - 1), 1 / (m : ℝ)) ≤ 1 + Real.log (X : ℝ) := by
      have h := HarmonicLogBound (X - 1)
      have h4 : Real.log (((X - 1 : ℕ)) : ℝ) ≤ Real.log (X : ℝ) := by
        refine Real.log_le_log (by exact_mod_cast (by omega : 0 < X - 1)) ?_
        exact_mod_cast Nat.sub_le X 1
      linarith only [h, h4]
    calc (∑ m ∈ Finset.Icc 1 (X - 1), |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|)
        ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hC0
  have hgX : |g (X : ℝ)| ≤ A' * B' := by
    simp only [g, abs_mul]
    exact mul_le_mul hAX hBX (abs_nonneg _) (le_trans zero_le_one hA'1)
  have hF1 : |F 1| ≤ 82 * (A' * B' * Real.sqrt (X : ℝ)) := by
    have hL2nn : 0 ≤ Real.log (2 * (X : ℝ)) :=
      Real.log_nonneg (by linarith only [hX1R] : (1 : ℝ) ≤ 2 * (X : ℝ))
    have hval : F 1 = (α + 1) * (β + 1) + 1 := by
      simp only [F]
      rw [Real.log_one]
      ring
    rw [hval]
    have hpos : 0 ≤ (α + 1) * (β + 1) + 1 := by positivity
    rw [abs_of_nonneg hpos]
    have hA1 : α + 1 ≤ (Real.log (2 * (X : ℝ)) + 1) * A' := by
      rw [hA'def]
      have hAbs : 0 ≤ |Real.log (2 * (X : ℝ)) - α| := abs_nonneg _
      have h1 : α ≤ Real.log (2 * (X : ℝ)) + |Real.log (2 * (X : ℝ)) - α| := by
        have hh := neg_le_abs (Real.log (2 * (X : ℝ)) - α); linarith only [hh]
      have hprod : 0 ≤ Real.log (2 * (X : ℝ)) * |Real.log (2 * (X : ℝ)) - α| :=
        mul_nonneg hL2nn hAbs
      have hexp : (Real.log (2 * (X : ℝ)) + 1) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          = Real.log (2 * (X : ℝ)) + Real.log (2 * (X : ℝ)) * |Real.log (2 * (X : ℝ)) - α|
            + 1 + |Real.log (2 * (X : ℝ)) - α| := by ring
      rw [hexp]
      linarith only [h1, hprod]
    have hB1 : β + 1 ≤ (Real.log (2 * (X : ℝ)) + 1) * B' := by
      rw [hB'def]
      have hAbs : 0 ≤ |Real.log (2 * (X : ℝ)) - β| := abs_nonneg _
      have h1 : β ≤ Real.log (2 * (X : ℝ)) + |Real.log (2 * (X : ℝ)) - β| := by
        have hh := neg_le_abs (Real.log (2 * (X : ℝ)) - β); linarith only [hh]
      have hprod : 0 ≤ Real.log (2 * (X : ℝ)) * |Real.log (2 * (X : ℝ)) - β| :=
        mul_nonneg hL2nn hAbs
      have hexp : (Real.log (2 * (X : ℝ)) + 1) * (1 + |Real.log (2 * (X : ℝ)) - β|)
          = Real.log (2 * (X : ℝ)) + Real.log (2 * (X : ℝ)) * |Real.log (2 * (X : ℝ)) - β|
            + 1 + |Real.log (2 * (X : ℝ)) - β| := by ring
      rw [hexp]
      linarith only [h1, hprod]
    have hsq : (Real.log (2 * (X : ℝ)) + 1) ^ 2 ≤ 81 * Real.sqrt (X : ℝ) := log2X_sq_le X hX1
    have hAB : (α + 1) * (β + 1) ≤ (Real.log (2 * (X : ℝ)) + 1) ^ 2 * (A' * B') := by
      have h := mul_le_mul hA1 hB1 (by linarith only [hβ] : (0 : ℝ) ≤ β + 1)
        (by positivity : (0 : ℝ) ≤ (Real.log (2 * (X : ℝ)) + 1) * A')
      calc (α + 1) * (β + 1)
          ≤ ((Real.log (2 * (X : ℝ)) + 1) * A') * ((Real.log (2 * (X : ℝ)) + 1) * B') := h
        _ = (Real.log (2 * (X : ℝ)) + 1) ^ 2 * (A' * B') := by ring
    have hsqrt1 : 1 ≤ Real.sqrt (X : ℝ) := by rw [Real.one_le_sqrt]; exact hX1R
    have hAB1 : 1 ≤ A' * B' := by nlinarith only [hA'1, hB'1]
    nlinarith only [hAB, hsq, hAB1, hsqrt1, Real.sqrt_nonneg (X : ℝ),
      sq_nonneg (Real.log (2 * (X : ℝ)) + 1)]
  have step1 : |(∑ m ∈ Finset.Icc 1 X, g (m : ℝ)) - F (X : ℝ)|
      ≤ (∑ m ∈ Finset.Icc 1 (X - 1), |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|)
        + |g (X : ℝ)| + |F 1| := by
    rw [sum_Icc_sub_antideriv F g X hX1]
    have h2 : |g (X : ℝ) - F 1| ≤ |g (X : ℝ)| + |F 1| := by
      have h := abs_add_le (g (X : ℝ)) (-(F 1))
      simpa [sub_eq_add_neg] using h
    calc |(∑ m ∈ Finset.Icc 1 (X - 1), (g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))))
            + (g (X : ℝ) - F 1)|
        ≤ |(∑ m ∈ Finset.Icc 1 (X - 1), (g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))))|
            + |g (X : ℝ) - F 1| := abs_add_le _ _
      _ ≤ (∑ m ∈ Finset.Icc 1 (X - 1), |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|)
            + (|g (X : ℝ)| + |F 1|) :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _) h2
      _ = _ := by ring
  have step2 : (∑ m ∈ Finset.Icc 1 (X - 1), |g (m : ℝ) - (F ((m : ℝ) + 1) - F (m : ℝ))|)
        + |g (X : ℝ)| + |F 1|
      ≤ (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1)
          * (1 + Real.log (X : ℝ)) + A' * B' + 82 * (A' * B' * Real.sqrt (X : ℝ)) := by
    have h := add_le_add (add_le_add hsum hgX) hF1
    linarith only [h, hsum, hgX, hF1]
  have hL_le : 1 + Real.log (X : ℝ) ≤ 5 * Real.sqrt (Real.sqrt (X : ℝ)) := by
    have h4 := LogFourRpow' (X : ℝ) hX1R
    have h41 : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) := by
      have h := Real.rpow_le_rpow (zero_le_one) hX1R (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      rwa [Real.one_rpow] at h
    have hsqrt : Real.sqrt (Real.sqrt (X : ℝ)) = (X : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hXpos)]
      norm_num
    rw [hsqrt]
    linarith only [h4, h41]
  have hCle : (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1)
      ≤ A' + B' + 2 * (1 + Real.log (X : ℝ)) := by
    linarith only [hAX, hBX]
  have step3 := final_numeric (A := A') (B := B') (L := 1 + Real.log (X : ℝ))
    (Z := Real.sqrt (X : ℝ))
    (C := |Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 * Real.log (X : ℝ) + 1)
    hA'1 hB'1 (by rw [Real.one_le_sqrt]; exact hX1R) hL_le (by positivity) hCle
  exact step1.trans (step2.trans step3)

end Work.LinnikAreas.JutilaPieces
