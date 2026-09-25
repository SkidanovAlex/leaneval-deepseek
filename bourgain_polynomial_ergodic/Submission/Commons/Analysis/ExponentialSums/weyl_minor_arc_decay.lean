import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

/-- **Minor-arc decay for the degree-`k` Weyl sum** (Bourgain 1989, §5, leading coefficient
form).

Let `k ≥ 2`, `0 < δ ≤ 1/4` and let `f : ℝ[X]` have `natDegree = k`.  Suppose that for every
integer `q` with `1 ≤ q ≤ N^δ` and every integer `a` the leading coefficient of `f` is far from
`a/q`:

`‖f.leadingCoeff − a/q‖ > N^{-k+δ}`.

Then the normalized Weyl sum decays: `‖N⁻¹ ∑_{x<N} e(f(x))‖ ≤ C N^{-ν}` for some `ν > 0`
depending only on `k` and `δ` (in fact `ν = δ 2^{-k}`).

Apply Dirichlet's approximation result to the leading coefficient with parameter `N^{k-δ}`,
obtaining `y ≤ N^{k-δ}` and `‖lead f − x/y‖ ≤ 1/(y N^{k-δ})`.  If `y ≤ N^δ` this contradicts
the hypothesis, so `y > N^δ` (and `y ≤ N^{k-δ}`), which is exactly what is needed to evaluate
Weyl's inequality (`Commons.Analysis.ExponentialSums.weyl_inequality`, with `t = 1`) and get
`(1/y + 1/N + 1/N^{k-1} + y/N^k)^{2^{1-k}} ≲ N^{-δ 2^{-k}}`. -/
theorem weyl_minor_arc_decay (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (C ν : ℝ), 0 < C ∧ 0 < ν ∧
      ∀ (N : ℕ) (f : Polynomial ℝ), f.natDegree = k → 2 ≤ N →
        (∀ (q : ℤ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ →
          (N : ℝ) ^ (-(k : ℝ) + δ) < |f.leadingCoeff - (a : ℝ) / (q : ℝ)|) →
        ‖(N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * (((Polynomial.eval (x : ℝ) f : ℝ)) : ℂ))‖
          ≤ C * (N : ℝ) ^ (-ν) := by
  set ν : ℝ := δ * (2 : ℝ) ^ (-(k : ℝ)) with hνdef
  have hνpos : 0 < ν := by
    rw [hνdef]; exact mul_pos hδ0 (Real.rpow_pos_of_pos (by norm_num) _)
  have hνhalf_pos : 0 < ν / 2 := by linarith
  obtain ⟨Cw, hCwpos, hCw⟩ :=
    weyl_inequality k (by omega) (ε := ν / 2) hνhalf_pos (t := 1) (by norm_num)
  refine ⟨6 * Cw, ν, by linarith, hνpos, ?_⟩
  intro N f hf hN hminor
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkexp_pos : 0 < (k : ℝ) - δ := by linarith
  have hNrpow_pos : 0 < (N : ℝ) ^ ((k : ℝ) - δ) := Real.rpow_pos_of_pos hNpos _
  have hNrpow_ge1 : 1 ≤ (N : ℝ) ^ ((k : ℝ) - δ) :=
    Real.one_le_rpow hN1.le hkexp_pos.le
  -- Dirichlet parameter
  set M : ℕ := Nat.ceil ((N : ℝ) ^ ((k : ℝ) - δ)) + 1 with hMdef
  have hM_gt : (N : ℝ) ^ ((k : ℝ) - δ) < (M : ℝ) := by
    have h := Nat.le_ceil ((N : ℝ) ^ ((k : ℝ) - δ))
    rw [hMdef]; push_cast; linarith
  have hMpos : 0 < M := by rw [hMdef]; exact Nat.succ_pos _
  have hM_le : (M : ℝ) ≤ 3 * (N : ℝ) ^ ((k : ℝ) - δ) := by
    have h := Nat.ceil_lt_add_one (le_of_lt hNrpow_pos)
    rw [hMdef]; push_cast
    linarith [h, hNrpow_ge1]
  -- Dirichlet's theorem
  obtain ⟨r, hrbound, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le (f.leadingCoeff) (n := M) hMpos
  have hrc : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
  have hdenpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hden1 : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  -- denominator exceeds N^δ
  have hy_gt : (N : ℝ) ^ δ < (r.den : ℝ) := by
    by_contra hle
    rw [not_lt] at hle
    have hmin := hminor (r.den : ℤ) (r.num) (by exact_mod_cast r.pos) (by exact_mod_cast hle)
    have hmin' : (N : ℝ) ^ (-(k : ℝ) + δ) < |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)| := by
      simpa using hmin
    have hb1 : |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)|
        ≤ 1 / (((M : ℝ) + 1) * (r.den : ℝ)) := by
      have h := hrbound
      rw [hrc] at h
      simpa using h
    have hbig : (N : ℝ) ^ ((k : ℝ) - δ) < ((M : ℝ) + 1) * (r.den : ℝ) := by
      have h1 : (N : ℝ) ^ ((k : ℝ) - δ) < (M : ℝ) + 1 := by linarith
      nlinarith [h1, hden1, hMpos]
    have hstep : 1 / (((M : ℝ) + 1) * (r.den : ℝ)) < (N : ℝ) ^ (-(k : ℝ) + δ) := by
      have hNexp : (N : ℝ) ^ (-(k : ℝ) + δ) = 1 / ((N : ℝ) ^ ((k : ℝ) - δ)) := by
        rw [show (-(k : ℝ) + δ) = -((k : ℝ) - δ) by ring, Real.rpow_neg hNpos.le, one_div]
      rw [hNexp]
      exact one_div_lt_one_div_of_lt hNrpow_pos hbig
    linarith [hmin', lt_of_le_of_lt hb1 hstep]
  -- coprimality
  have hgcd : Int.gcd r.num (r.den : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.Coprime.gcd_eq_one (by simpa using r.reduced)
  -- Weyl applies
  have hb : |f.leadingCoeff - ((r.num : ℤ) : ℝ) / ((r.den : ℤ) : ℝ)| ≤ 1 / (((r.den : ℤ) : ℝ)) ^ 2 := by
    have hb1 : |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)|
        ≤ 1 / (((M : ℝ) + 1) * (r.den : ℝ)) := by
      have h := hrbound
      rw [hrc] at h
      simpa using h
    have hdenM : (r.den : ℝ) ≤ (M : ℝ) + 1 := by
      have h : (r.den : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrden
      linarith
    have hle : 1 / (((M : ℝ) + 1) * (r.den : ℝ)) ≤ 1 / (r.den : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hdenM, hdenpos]
    have hmain : |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2 :=
      le_trans hb1 hle
    simpa using hmain
  have hWeyl := hCw 0 N r.num (r.den : ℤ) f (by exact_mod_cast r.pos) hgcd hf hb
  -- bracket
  set Br : ℝ := 1 / (r.den : ℝ) + 1 / (N : ℝ) + 1 / ((N : ℝ) ^ (k - 1)) + (r.den : ℝ) / (N : ℝ) ^ k with hBr
  have hbreq : (1 / ((r.den : ℤ) : ℝ) + 1 / ((N : ℝ)) + 1 / ((N : ℝ) ^ (k - 1)) + ((r.den : ℤ) : ℝ) / (N : ℝ) ^ k) = Br := by
    rw [hBr]; push_cast; ring
  have hA : 1 / (r.den : ℝ) ≤ (N : ℝ) ^ (-δ) := by
    have h1 : 1 / (r.den : ℝ) < (N : ℝ) ^ (-δ) := by
      have hNexp : (N : ℝ) ^ (-δ) = 1 / ((N : ℝ) ^ δ) := by
        rw [Real.rpow_neg hNpos.le, one_div]
      rw [hNexp]
      exact one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hNpos δ) hy_gt
    exact h1.le
  have hB : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-δ) := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
    simpa [Real.rpow_neg_one, one_div] using h1
  have hC : 1 / ((N : ℝ) ^ (k - 1)) ≤ (N : ℝ) ^ (-δ) := by
    have hexp : -(((k - 1 : ℕ) : ℝ)) ≤ -δ := by
      have : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
        have : 1 ≤ k - 1 := by omega
        exact_mod_cast this
      linarith
    have h1 : (N : ℝ) ^ (-(((k - 1 : ℕ) : ℝ))) ≤ (N : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le hexp
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast] at h1
    simpa using h1
  have hD : (r.den : ℝ) / (N : ℝ) ^ k ≤ 3 * (N : ℝ) ^ (-δ) := by
    have hyden : (r.den : ℝ) ≤ 3 * (N : ℝ) ^ ((k : ℝ) - δ) :=
      le_trans (by exact_mod_cast hrden) hM_le
    calc (r.den : ℝ) / (N : ℝ) ^ k
        ≤ (3 * (N : ℝ) ^ ((k : ℝ) - δ)) / (N : ℝ) ^ k :=
          div_le_div_of_nonneg_right hyden (by positivity)
      _ = 3 * (N : ℝ) ^ (-δ) := by
          rw [mul_div_assoc, ← Real.rpow_natCast (N : ℝ) k,
            ← Real.rpow_sub hNpos ((k : ℝ) - δ) (k : ℝ)]
          congr 1
          ring
  have hbr_le : Br ≤ 6 * (N : ℝ) ^ (-δ) := by
    rw [hBr]; linarith [hA, hB, hC, hD]
  have hbr_nn : 0 ≤ Br := by rw [hBr]; positivity
  -- combine
  have hWeyl' : ‖∑ x ∈ Finset.range N,
      Complex.exp (↑(2 * Real.pi * Polynomial.eval ((0 : ℤ) + (x : ℝ)) f) * Complex.I)‖
      ≤ Cw * (N : ℝ) ^ (1 + ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) := by
    rw [hbreq] at hWeyl
    simpa using hWeyl
  have hsum_eq : (∑ x ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (((Polynomial.eval (x : ℝ) f : ℝ)) : ℂ)))
      = ∑ x ∈ Finset.range N,
        Complex.exp (↑(2 * Real.pi * Polynomial.eval ((0 : ℤ) + (x : ℝ)) f) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    push_cast
    ring
  have hpow_le : Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) ≤ 6 * (N : ℝ) ^ (-(2 * ν)) := by
    have h2pos : 0 ≤ (2 : ℝ) ^ (1 - (k : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h61 : (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) ≤ 6 := by
      have hle1 : (2 : ℝ) ^ (1 - (k : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      calc (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) ≤ (6 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hle1
        _ = 6 := Real.rpow_one 6
    calc Br ^ ((2:ℝ) ^ (1 - (k : ℝ)))
        ≤ (6 * (N : ℝ) ^ (-δ)) ^ ((2:ℝ) ^ (1 - (k : ℝ))) := Real.rpow_le_rpow hbr_nn hbr_le h2pos
      _ = (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) * ((N : ℝ) ^ (-δ)) ^ ((2:ℝ) ^ (1 - (k : ℝ))) :=
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _)
      _ = (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) * (N : ℝ) ^ (-δ * (2:ℝ) ^ (1 - (k : ℝ))) := by
            rw [← Real.rpow_mul hNpos.le]
      _ ≤ 6 * (N : ℝ) ^ (-δ * (2:ℝ) ^ (1 - (k : ℝ))) := by
            apply mul_le_mul_of_nonneg_right h61 (Real.rpow_nonneg hNpos.le _)
      _ = 6 * (N : ℝ) ^ (-(2 * ν)) := by
            have hexp : -δ * (2:ℝ) ^ (1 - (k : ℝ)) = -(2 * ν) := by
              rw [hνdef]
              have h2e : (2 : ℝ) ^ (1 - (k : ℝ)) = 2 * (2 : ℝ) ^ (-(k : ℝ)) := by
                rw [show (1 : ℝ) - (k : ℝ) = 1 + (-(k : ℝ)) by ring]
                rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
              rw [h2e]; ring
            rw [hexp]
  have hkey : (N : ℝ) ^ (1 + ν / 2) * (N : ℝ)⁻¹ = (N : ℝ) ^ (ν / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hkey2 : (N : ℝ) ^ (ν / 2) * (N : ℝ) ^ (-(2 * ν)) = (N : ℝ) ^ (ν / 2 - 2 * ν) := by
    rw [← Real.rpow_add hNpos]
    congr 1
  have hfin : (N : ℝ) ^ (ν / 2 - 2 * ν) ≤ (N : ℝ) ^ (-ν) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  calc ‖(N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (((Polynomial.eval (x : ℝ) f : ℝ)) : ℂ))‖
      = ‖∑ x ∈ Finset.range N,
        Complex.exp (↑(2 * Real.pi * Polynomial.eval ((0 : ℤ) + (x : ℝ)) f) * Complex.I)‖ * (N : ℝ)⁻¹ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast, hsum_eq, mul_comm]
    _ ≤ (Cw * (N : ℝ) ^ (1 + ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ)))) * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hWeyl' (by positivity)
    _ = Cw * (N : ℝ) ^ (ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) := by
          rw [show (Cw * (N : ℝ) ^ (1 + ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ)))) * (N : ℝ)⁻¹
                = Cw * ((N : ℝ) ^ (1 + ν / 2) * (N : ℝ)⁻¹) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) by ring,
            hkey]
    _ ≤ Cw * (N : ℝ) ^ (ν / 2) * (6 * (N : ℝ) ^ (-(2 * ν))) :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = 6 * Cw * (N : ℝ) ^ (ν / 2 - 2 * ν) := by
          rw [show Cw * (N : ℝ) ^ (ν / 2) * (6 * (N : ℝ) ^ (-(2 * ν)))
                = 6 * Cw * ((N : ℝ) ^ (ν / 2) * (N : ℝ) ^ (-(2 * ν))) by ring, hkey2]
    _ ≤ 6 * Cw * (N : ℝ) ^ (-ν) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)

end Commons.Analysis.ExponentialSums