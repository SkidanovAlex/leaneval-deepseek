import Mathlib
import Submission.Work.HP.Defs

set_option autoImplicit false

/-!
# Real-variable arithmetic for the case-F estimate

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 2023:
the per-pair bound in "case F" of the second moment has to be summed over pairs and compared
with `A^{N-2-1/3} B^2` (with `N = N_{d,n}` the number of degree-`d` monomials in `n+1`
variables).  Summing produces the two expressions

* `A^{N-n-1} * (B^{1/m})^{2(n-d)} * B^{4/m}` and
* `A^{N-n-2-(n-1)/2} * (B^{1/m})^{n-1} * B^{4/m}`,   where `m = n+1-d`,

and one has to show that both are at most a constant times `A^{N-2-1/3} B^2`, uniformly over
`A ∈ [B/log B, B^2]` and large `B`.

The three ingredients are
* `caseF_decomp`   : rewriting the summands as `A^{N-7/3} * (A^e * B^f) * B^2`;
* `caseF_exp_neg`  : the two resulting exponent sums `e + f` are negative (this is where the
  exclusions `(d,n) ∉ {(2,2),(3,3)}` are needed);
* `caseF_master`   : for `e < 0` and `e + f < 0`, `A^e * B^f * (log B + 1)^q` is bounded,
  which rests on `caseF_rpow_log_absorb` (powers of `log B` are dominated by any negative
  power of `B`).
-/

noncomputable section

namespace Work.HP.Sig2

open Work.HP

/-- Arithmetic input for the case-F estimate: with `m = n + 1 - d` the exponents
`4/3 - n + 2/m` and `(5 - 9n)/6 + (n+3)/m - 2` are both negative. -/
theorem caseF_exp_neg (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    0 < (((n + 1 - d : ℕ)) : ℝ) ∧
    (4 / 3 - (n : ℝ) + 2 / (((n + 1 - d : ℕ)) : ℝ) < 0) ∧
    ((5 - 9 * (n : ℝ)) / 6 + ((n : ℝ) + 3) / (((n + 1 - d : ℕ)) : ℝ) - 2 < 0) := by
  have hm1 : 1 ≤ n + 1 - d := by omega
  have hmpos : (0 : ℝ) < (((n + 1 - d : ℕ)) : ℝ) := by
    have : 0 < n + 1 - d := by omega
    exact_mod_cast this
  have hm1R : (1 : ℝ) ≤ (((n + 1 - d : ℕ)) : ℝ) := by exact_mod_cast hm1
  refine ⟨hmpos, ?_, ?_⟩
  · by_cases hn : 4 ≤ n
    · have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h2m : 2 / (((n + 1 - d : ℕ)) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hmpos]; nlinarith [hm1R]
      linarith
    · have hn2 : 2 ≤ n := le_trans hd hdn
      have hn3 : n ≤ 3 := by omega
      interval_cases n
      · have hd2 : d = 2 := by omega
        subst hd2
        exact absurd rfl h22
      · have hd3 : d ≠ 3 := by intro h; exact h33 (by simp [h])
        have hd2 : d = 2 := by omega
        subst hd2
        norm_num
  · by_cases hn : 4 ≤ n
    · have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnm : ((n : ℝ) + 3) / (((n + 1 - d : ℕ)) : ℝ) ≤ ((n : ℝ) + 3) := by
        rw [div_le_iff₀ hmpos]; nlinarith [hm1R]
      linarith
    · have hn2 : 2 ≤ n := le_trans hd hdn
      have hn3 : n ≤ 3 := by omega
      interval_cases n
      · have hd2 : d = 2 := by omega
        subst hd2
        exact absurd rfl h22
      · have hd3 : d ≠ 3 := by intro h; exact h33 (by simp [h])
        have hd2 : d = 2 := by omega
        subst hd2
        norm_num

/-- `B ^ p * (log B + 1) ^ r` is bounded for large `B` when `p < 0`. -/
theorem caseF_rpow_log_absorb (p r : ℝ) (hp : p < 0) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → B ^ p * (Real.log B + 1) ^ r ≤ K := by
  by_cases hrle : r ≤ 0
  · refine ⟨1, 2, one_pos, by norm_num, ?_⟩
    intro B hB
    have hB1 : (1 : ℝ) ≤ B := by linarith
    have hB0 : (0 : ℝ) < B := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB1]
    have h1 : B ^ p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hB1 (le_of_lt hp)
    have h2 : (Real.log B + 1) ^ r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlog1 hrle
    have h3 : (0 : ℝ) ≤ (Real.log B + 1) ^ r := Real.rpow_nonneg (by linarith) r
    calc B ^ p * (Real.log B + 1) ^ r ≤ 1 * 1 := mul_le_mul h1 h2 h3 (by norm_num)
      _ = 1 := by ring
  · have hrpos : 0 < r := not_le.mp hrle
    set ε : ℝ := -p / (2 * r) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      exact div_pos (by linarith) (by linarith)
    set D : ℝ := ε⁻¹ + 1 with hDdef
    have hDpos : 0 < D := by rw [hDdef]; linarith [inv_pos.mpr hεpos]
    refine ⟨D ^ r, Real.exp 2, Real.rpow_pos_of_pos hDpos r, Real.exp_pos 2, ?_⟩
    intro B hB
    have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos 2) hB
    have hB1gt : (1 : ℝ) < B := by
      have h : (1 : ℝ) < Real.exp 2 := by
        have h' := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
        rwa [Real.exp_zero] at h'
      linarith
    have hB1 : (1 : ℝ) ≤ B := le_of_lt hB1gt
    have hlogpos : 0 < Real.log B := Real.log_pos hB1gt
    have hlog : Real.log B ≤ B ^ ε / ε := Real.log_le_rpow_div (le_of_lt hBpos) hεpos
    have hBε1 : (1 : ℝ) ≤ B ^ ε := Real.one_le_rpow hB1 (le_of_lt hεpos)
    have hD : Real.log B + 1 ≤ D * B ^ ε := by
      have h4 : B ^ ε / ε = ε⁻¹ * B ^ ε := by rw [div_eq_inv_mul]
      rw [h4] at hlog
      have h5 : ε⁻¹ * B ^ ε + 1 ≤ ε⁻¹ * B ^ ε + B ^ ε := by linarith
      have h6 : ε⁻¹ * B ^ ε + B ^ ε = D * B ^ ε := by rw [hDdef]; ring
      linarith
    have hrpow : (Real.log B + 1) ^ r ≤ (D * B ^ ε) ^ r :=
      Real.rpow_le_rpow (by linarith) hD (le_of_lt hrpos)
    have hsplit : (D * B ^ ε) ^ r = D ^ r * B ^ (ε * r) := by
      rw [Real.mul_rpow (le_of_lt hDpos) (Real.rpow_nonneg (le_of_lt hBpos) ε),
        Real.rpow_mul (le_of_lt hBpos) ε r]
    have hεr : ε * r = -p / 2 := by
      rw [hεdef]
      field_simp
    have hpr : p + -p / 2 = p / 2 := by ring
    calc B ^ p * (Real.log B + 1) ^ r
        ≤ B ^ p * (D ^ r * B ^ (ε * r)) :=
          mul_le_mul_of_nonneg_left (le_trans hrpow (le_of_eq hsplit))
            (Real.rpow_nonneg (le_of_lt hBpos) p)
      _ = D ^ r * (B ^ p * B ^ (ε * r)) := by ring
      _ = D ^ r * B ^ (p + ε * r) := by rw [← Real.rpow_add hBpos]
      _ = D ^ r * B ^ (p / 2) := by rw [hεr, hpr]
      _ ≤ D ^ r * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hDpos r).le
          exact Real.rpow_le_one_of_one_le_of_nonpos hB1 (by linarith)
      _ = D ^ r := by ring

/-- If `eA < 0`, `eA + eB < 0` and `A ≥ B / log B`, then `A ^ eA * B ^ eB * (log B + 1) ^ q`
is bounded by a constant for all large `B`. -/
theorem caseF_master (eA eB : ℝ) (q : ℕ) (hA : eA < 0) (hsum : eA + eB < 0) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      A ^ eA * B ^ eB * (Real.log B + 1) ^ q ≤ K := by
  obtain ⟨K, B₀', hK, hB₀', hbound⟩ := caseF_rpow_log_absorb (eA + eB) ((q : ℝ) - eA) hsum
  have hexp2gt1 : (1 : ℝ) < Real.exp 2 := by
    have h := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
    rwa [Real.exp_zero] at h
  refine ⟨K, max B₀' (Real.exp 2), hK, lt_of_lt_of_le hB₀' (le_max_left _ _), ?_⟩
  intro A B hB hAle hAge
  have hB₀le : B₀' ≤ B := le_trans (le_max_left _ _) hB
  have hB1 : (1 : ℝ) < B := lt_of_lt_of_le hexp2gt1 (le_trans (le_max_right _ _) hB)
  have hBpos : 0 < B := by linarith
  have hlogpos : 0 < Real.log B := Real.log_pos hB1
  have hBlpos : 0 < B / Real.log B := div_pos hBpos hlogpos
  have hApos : 0 < A := lt_of_lt_of_le hBlpos hAle
  have hLpos : 0 < Real.log B + 1 := by linarith
  have hkey : A ^ eA ≤ B ^ eA * (Real.log B + 1) ^ (-eA) := by
    calc A ^ eA ≤ (B / Real.log B) ^ eA :=
          Real.rpow_le_rpow_of_nonpos hBlpos hAle (le_of_lt hA)
      _ = B ^ eA * (Real.log B) ^ (-eA) := by
          rw [Real.div_rpow (le_of_lt hBpos) (le_of_lt hlogpos),
            Real.rpow_neg (le_of_lt hlogpos), div_eq_mul_inv]
      _ ≤ B ^ eA * (Real.log B + 1) ^ (-eA) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (le_of_lt hlogpos) (by linarith) (by linarith))
            (Real.rpow_nonneg (le_of_lt hBpos) eA)
  have hstep1 : A ^ eA * B ^ eB ≤ (B ^ eA * (Real.log B + 1) ^ (-eA)) * B ^ eB :=
    mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg (le_of_lt hBpos) eB)
  have hstep2 : A ^ eA * B ^ eB * (Real.log B + 1) ^ q
      ≤ (B ^ eA * (Real.log B + 1) ^ (-eA)) * B ^ eB * (Real.log B + 1) ^ q :=
    mul_le_mul_of_nonneg_right hstep1 (pow_nonneg (le_of_lt hLpos) q)
  have hbadd : B ^ eA * B ^ eB = B ^ (eA + eB) := (Real.rpow_add hBpos eA eB).symm
  have hLadd : (Real.log B + 1) ^ (-eA) * (Real.log B + 1) ^ q
      = (Real.log B + 1) ^ ((q : ℝ) - eA) := by
    rw [← Real.rpow_natCast (Real.log B + 1) q, ← Real.rpow_add hLpos]
    congr 1
    ring
  have hmul : (B ^ eA * (Real.log B + 1) ^ (-eA)) * B ^ eB * (Real.log B + 1) ^ q
      = B ^ (eA + eB) * (Real.log B + 1) ^ ((q : ℝ) - eA) := by
    rw [← hbadd, ← hLadd]
    ring
  calc A ^ eA * B ^ eB * (Real.log B + 1) ^ q
      ≤ (B ^ eA * (Real.log B + 1) ^ (-eA)) * B ^ eB * (Real.log B + 1) ^ q := hstep2
    _ = B ^ (eA + eB) * (Real.log B + 1) ^ ((q : ℝ) - eA) := hmul
    _ ≤ K := hbound B hB₀le

/-- The two case-F summands, rewritten in the normal form `A ^ (N - 7/3) * (A ^ a * B ^ b) * B ^ 2`
used to compare them with `A ^ (N - 2 - 1/3) * B ^ 2`. -/
theorem caseF_decomp (d n : ℕ) (hdn : d ≤ n) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
        * B ^ (4 / ((n : ℝ) + 1 - d))
      = A ^ ((NN d n : ℝ) - 7 / 3) *
          (A ^ (4 / 3 - (n : ℝ)) * B ^ (2 / ((n : ℝ) + 1 - d))) * B ^ 2 ∧
    A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
        * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1) * B ^ (4 / ((n : ℝ) + 1 - d))
      = A ^ ((NN d n : ℝ) - 7 / 3) *
          (A ^ ((5 - 9 * (n : ℝ)) / 6) * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2)) * B ^ 2 := by
  have hmpos : (0 : ℝ) < (n : ℝ) + 1 - d := by
    have h : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hAexp1 : (NN d n : ℝ) - (n : ℝ) - 1 = ((NN d n : ℝ) - 7 / 3) + (4 / 3 - (n : ℝ)) := by
    ring
  have hBexp1 : (1 / ((n : ℝ) + 1 - d)) * (2 * ((n : ℝ) - d)) + 4 / ((n : ℝ) + 1 - d)
      = 2 / ((n : ℝ) + 1 - d) + 2 := by
    field_simp
    ring
  have hAexp2 : (NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2
      = ((NN d n : ℝ) - 7 / 3) + (5 - 9 * (n : ℝ)) / 6 := by
    ring
  have hBexp2 : (1 / ((n : ℝ) + 1 - d)) * ((n : ℝ) - 1) + 4 / ((n : ℝ) + 1 - d)
      = ((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2 + 2 := by
    field_simp
    ring
  constructor
  · have hmain : A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
        * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d)) * B ^ (4 / ((n : ℝ) + 1 - d))
        = A ^ ((NN d n : ℝ) - 7 / 3)
          * (A ^ (4 / 3 - (n : ℝ)) * B ^ (2 / ((n : ℝ) + 1 - d))) * B ^ (2 : ℝ) := by
      calc A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
            * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d)) * B ^ (4 / ((n : ℝ) + 1 - d))
          = A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
              * B ^ ((1 / ((n : ℝ) + 1 - d)) * (2 * ((n : ℝ) - d)))
              * B ^ (4 / ((n : ℝ) + 1 - d)) := by
            rw [← Real.rpow_mul (le_of_lt hB)]
        _ = A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
              * (B ^ ((1 / ((n : ℝ) + 1 - d)) * (2 * ((n : ℝ) - d)))
                * B ^ (4 / ((n : ℝ) + 1 - d))) := by
            rw [mul_assoc]
        _ = A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
              * B ^ ((1 / ((n : ℝ) + 1 - d)) * (2 * ((n : ℝ) - d))
                  + 4 / ((n : ℝ) + 1 - d)) := by
            rw [← Real.rpow_add hB]
        _ = A ^ (((NN d n : ℝ) - 7 / 3) + (4 / 3 - (n : ℝ)))
              * B ^ (2 / ((n : ℝ) + 1 - d) + 2) := by
            rw [hAexp1, hBexp1]
        _ = A ^ ((NN d n : ℝ) - 7 / 3) * A ^ (4 / 3 - (n : ℝ))
              * B ^ (2 / ((n : ℝ) + 1 - d) + 2) := by
            rw [Real.rpow_add hA]
        _ = A ^ ((NN d n : ℝ) - 7 / 3) * A ^ (4 / 3 - (n : ℝ))
              * (B ^ (2 / ((n : ℝ) + 1 - d)) * B ^ (2 : ℝ)) := by
            rw [Real.rpow_add hB]
        _ = A ^ ((NN d n : ℝ) - 7 / 3)
              * (A ^ (4 / 3 - (n : ℝ)) * B ^ (2 / ((n : ℝ) + 1 - d))) * B ^ (2 : ℝ) := by
            ring
    simpa using hmain
  · have hmain : A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
        * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1) * B ^ (4 / ((n : ℝ) + 1 - d))
        = A ^ ((NN d n : ℝ) - 7 / 3)
          * (A ^ ((5 - 9 * (n : ℝ)) / 6) * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2))
          * B ^ (2 : ℝ) := by
      calc A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
            * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1) * B ^ (4 / ((n : ℝ) + 1 - d))
          = A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
              * B ^ ((1 / ((n : ℝ) + 1 - d)) * ((n : ℝ) - 1))
              * B ^ (4 / ((n : ℝ) + 1 - d)) := by
            rw [← Real.rpow_mul (le_of_lt hB)]
        _ = A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
              * (B ^ ((1 / ((n : ℝ) + 1 - d)) * ((n : ℝ) - 1))
                * B ^ (4 / ((n : ℝ) + 1 - d))) := by
            rw [mul_assoc]
        _ = A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
              * B ^ ((1 / ((n : ℝ) + 1 - d)) * ((n : ℝ) - 1) + 4 / ((n : ℝ) + 1 - d)) := by
            rw [← Real.rpow_add hB]
        _ = A ^ (((NN d n : ℝ) - 7 / 3) + (5 - 9 * (n : ℝ)) / 6)
              * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2 + 2) := by
            rw [hAexp2, hBexp2]
        _ = A ^ ((NN d n : ℝ) - 7 / 3) * A ^ ((5 - 9 * (n : ℝ)) / 6)
              * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2 + 2) := by
            rw [Real.rpow_add hA]
        _ = A ^ ((NN d n : ℝ) - 7 / 3) * A ^ ((5 - 9 * (n : ℝ)) / 6)
              * (B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) * B ^ (2 : ℝ)) := by
            rw [Real.rpow_add hB]
        _ = A ^ ((NN d n : ℝ) - 7 / 3)
              * (A ^ ((5 - 9 * (n : ℝ)) / 6) * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2))
              * B ^ (2 : ℝ) := by
            ring
    simpa using hmain

/-- Real-variable arithmetic for the case-F estimate: for `B ≥ B₀`, `B/log B ≤ A ≤ B²` and
`(d,n) ∉ {(2,2),(3,3),(4,4)}`, the two powers coming from the summation of the per-pair bound
are dominated by `A^{N-2-1/3} B²` up to a constant. -/
theorem caseF_arith (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) (h44 : (d, n) ≠ (4, 4)) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
              * B ^ (4 / ((n : ℝ) + 1 - d))
          + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
              * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1)
              * B ^ (4 / ((n : ℝ) + 1 - d)))
          * (Real.log B + 1) ^ 3
      ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  obtain ⟨hmpos, hexp1, hexp2⟩ := caseF_exp_neg d n hd hdn h22 h33
  have hmcast : (((n + 1 - d : ℕ)) : ℝ) = (n : ℝ) + 1 - d := by
    rw [Nat.cast_sub (by omega : d ≤ n + 1), Nat.cast_add, Nat.cast_one]
  have hexp1' : 4 / 3 - (n : ℝ) + 2 / ((n : ℝ) + 1 - d) < 0 := by
    rw [← hmcast]; exact hexp1
  have hexp2' : (5 - 9 * (n : ℝ)) / 6 + (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) < 0 := by
    rw [← hmcast]; linarith [hexp2]
  have hd2n : (2 : ℝ) ≤ (n : ℝ) := by
    have h : 2 ≤ n := le_trans hd hdn
    exact_mod_cast h
  have hne1 : 4 / 3 - (n : ℝ) < 0 := by linarith
  have hne2 : (5 - 9 * (n : ℝ)) / 6 < 0 := by linarith
  obtain ⟨K₁, B₁, hK₁, hB₁, hb₁⟩ :=
    caseF_master (4 / 3 - (n : ℝ)) (2 / ((n : ℝ) + 1 - d)) 3 hne1 hexp1'
  obtain ⟨K₂, B₂, hK₂, hB₂, hb₂⟩ :=
    caseF_master ((5 - 9 * (n : ℝ)) / 6) (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) 3 hne2 hexp2'
  refine ⟨max (C * (K₁ + K₂)) 1, max B₁ (max B₂ (Real.exp 2)), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · exact lt_of_lt_of_le hB₁ (le_max_left _ _)
  · intro A B hB hAle hAge
    have hB₁le : B₁ ≤ B := le_trans (le_max_left _ _) hB
    have hB₂le : B₂ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
    have hexpB : Real.exp 2 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
    have hexp2gt1 : (1 : ℝ) < Real.exp 2 := by
      have h := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
      rwa [Real.exp_zero] at h
    have hB1gt : (1 : ℝ) < B := lt_of_lt_of_le hexp2gt1 hexpB
    have hBpos : 0 < B := by linarith
    have hlogpos : 0 < Real.log B := Real.log_pos hB1gt
    have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogpos) hAle
    obtain ⟨hd1, hd2⟩ := caseF_decomp d n hdn A B hApos hBpos
    have h1 := hb₁ A B hB₁le hAle hAge
    have h2 := hb₂ A B hB₂le hAle hAge
    have hPnn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hApos) _) (sq_nonneg B)
    have hCnn : (0 : ℝ) ≤ C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := mul_nonneg hC hPnn
    have hKle : C * (K₁ + K₂) ≤ max (C * (K₁ + K₂)) 1 := le_max_left _ _
    set T1 : ℝ := A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
      * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d)) * B ^ (4 / ((n : ℝ) + 1 - d)) with hT1
    set T2 : ℝ := A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
      * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1) * B ^ (4 / ((n : ℝ) + 1 - d)) with hT2
    calc C * (T1 + T2) * (Real.log B + 1) ^ 3
        = C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)
              * (A ^ (4 / 3 - (n : ℝ)) * B ^ (2 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
          + C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)
              * (A ^ ((5 - 9 * (n : ℝ)) / 6)
                  * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) * (Real.log B + 1) ^ 3) := by
          rw [hd1, hd2]
          ring
      _ ≤ C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) * K₁
          + C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) * K₂ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h1 hCnn
          · exact mul_le_mul_of_nonneg_left h2 hCnn
      _ = C * (K₁ + K₂) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
      _ ≤ max (C * (K₁ + K₂)) 1 * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
          mul_le_mul_of_nonneg_right hKle hPnn
      _ = max (C * (K₁ + K₂)) 1 * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
          have hN : A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) = A ^ ((NN d n : ℝ) - 7 / 3) := by
            congr 1
            ring
          rw [hN]
          ring

end Work.HP.Sig2
