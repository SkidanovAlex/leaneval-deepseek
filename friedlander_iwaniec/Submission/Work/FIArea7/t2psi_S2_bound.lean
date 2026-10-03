import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Work.FIArea7.t2psi_S2_tauSum_le
import Submission.Work.FIArea7.t2psi_S2_tauFour_sqrt_le
import Submission.Work.FIArea7.t2psi_S2_inner_le
import Submission.Work.FIArea7.t2psi_S2_double_sum_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

-- Useful imports: `Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube`
-- (`τ(m n) ≤ τ(m)τ(n)`), `Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`
-- (`τ(n) ≤ C n^ε`, used only to turn `τ(c)^4 c^{1/2}` into `C·c`, the constant being absorbed),
-- `Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit`
-- (`∑_{a ≤ Y} τ(a)^4 / a ≪ log^{16} Y`), and the discrete Abel bound
-- `‖∑_{m ≤ M} log m · b m‖ ≤ 8 log(M+2) sup_{t ≤ M} ‖∑_{m≤t} b m‖`.
/-- **The second Vaughan term `S₂`.**  For each fixed pair `(a,b)` the inner `m`-sum has
coefficient `1` and parameter `m' = c·(ab)`, so Proposition 23.2 (`Prop232`) gives
`d(|k|+1) τ(cab)^4 √(cab) (N/(ab))^{3/4} log(cN+2)`; summing the *bounds* over `a,b ≤ Y` with
`τ(cab) ≤ τ(c)τ(a)τ(b)` and `∑_{a≤Y} τ(a)^4 a^{-1/4} ≪ Y^{3/4} log^{16} Y` gives
`≪ c · d · (|k|+1) · N^{3/4} · Y^{3/2} · (log cN)^B`. -/
theorem t2psi_S2_bound (h32 : Work.FIArea7.Prop232) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ (N c d Y : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
        1 ≤ N → 1 ≤ c → 1 ≤ d → 1 ≤ Y →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a b' : ℤ), chi (⟨a + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a, b'⟩) →
        (∀ (a b' : ℤ), chi (⟨a, b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a, b'⟩) →
        ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / (a * b)),
                Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ((a * b) * m))‖
          ≤ K * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * (Y : ℝ) ^ ((3:ℝ)/2)
              * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ B := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea7.t2psi_S2_tauSum_le
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea7.t2psi_S2_tauFour_sqrt_le
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FIArea7.t2psi_S2_inner_le h32
  refine ⟨max 1 (C3 * C2 * C1 ^ 2), 34, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    by norm_num, ?_⟩
  intro N c d Y k chi hN hc hd hY hnorm hmul hper1 hper2
  -- the logarithm `L = log(cN+2)`
  set L : ℝ := Real.log ((c : ℝ) * (N : ℝ) + 2) with hLdef
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Real.log_pos
    nlinarith
  have hLnonneg : 0 ≤ L := hLpos.le
  -- the pointwise bound got from Proposition 23.2 for each pair `(a,b)` with `a·b ≤ N`
  have hpt : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a * b ≤ N →
      ‖∑ m ∈ Finset.Icc 1 (N / (a * b)),
          Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ((a * b) * m))‖
        ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((c.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt c
            * (N : ℝ) ^ ((3:ℝ)/4) * L
            * ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
            * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) := by
    intro a b ha hb hab
    have h := hC3 N c d k chi a b hN hc hd ha hb hab hnorm hmul hper1 hper2
    simpa only [hLdef] using h
  have hD := Work.FIArea7.t2psi_S2_double_sum_le N c d Y k chi C3 hC3pos.le hN hc hpt
  -- the two weight sums
  set S1 : ℝ := ∑ a ∈ Finset.Icc 1 Y,
      (if a ≤ N then ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)) else 0)
    with hS1def
  set S2 : ℝ := ∑ b ∈ Finset.Icc 1 Y,
      (if b ≤ N then ArithmeticFunction.vonMangoldt b *
        ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) else 0)
    with hS2def
  -- the first weight sum, by the divisor-power estimate
  have hS1le : S1 ≤ C1 * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4))
      * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 16 := by
    rw [hS1def]
    have hsub : (Finset.Icc 1 Y).filter (fun a => a ≤ N) ⊆ Finset.Icc 1 (min Y N) := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      exact Finset.mem_Icc.mpr ⟨ha.1.1, le_min ha.1.2 ha.2⟩
    rw [← Finset.sum_filter]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ?_))
      (hC1 (min Y N))
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  -- the second weight sum (the von Mangoldt weight costs one logarithm)
  have hS2le : S2 ≤ L * (C1 * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4))
      * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 16) := by
    rw [hS2def]
    have hsub : (Finset.Icc 1 Y).filter (fun b => b ≤ N) ⊆ Finset.Icc 1 (min Y N) := by
      intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      exact Finset.mem_Icc.mpr ⟨hb.1.1, le_min hb.1.2 hb.2⟩
    have hstep : ∀ b ∈ (Finset.Icc 1 Y).filter (fun b => b ≤ N),
        ArithmeticFunction.vonMangoldt b * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4))
          ≤ L * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) := by
      intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      obtain ⟨⟨hb1, _⟩, hbN⟩ := hb
      have hlog : ArithmeticFunction.vonMangoldt b ≤ L := by
        rw [hLdef]
        have h1 : ArithmeticFunction.vonMangoldt b ≤ Real.log (b : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        have h2 : Real.log (b : ℝ) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < b)) (by exact_mod_cast hbN)
        have h3 : Real.log (N : ℝ) ≤ Real.log ((c : ℝ) * (N : ℝ) + 2) := by
          apply Real.log_le_log (by exact_mod_cast (by omega : 0 < N))
          nlinarith
        linarith
      exact mul_le_mul_of_nonneg_right hlog
        (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
    rw [← Finset.sum_filter]
    calc ∑ b ∈ (Finset.Icc 1 Y).filter (fun b => b ≤ N),
          ArithmeticFunction.vonMangoldt b * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4))
        ≤ ∑ b ∈ (Finset.Icc 1 Y).filter (fun b => b ≤ N),
            L * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) :=
          Finset.sum_le_sum hstep
      _ = L * ∑ b ∈ (Finset.Icc 1 Y).filter (fun b => b ≤ N),
            ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) :=
          (Finset.mul_sum _ _ L).symm
      _ ≤ L * ∑ b ∈ Finset.Icc 1 (min Y N),
            ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ hLnonneg
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
      _ ≤ L * (C1 * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4))
            * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 16) :=
          mul_le_mul_of_nonneg_left (hC1 (min Y N)) hLnonneg
  -- the two exponents combine
  have hQA2 : ((((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4)) ^ 2)
      = ((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2) := by
    rw [← Real.rpow_natCast (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4)) 2,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((min Y N : ℕ) : ℝ))]
    norm_num
  have hY32 : ((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2) ≤ (Y : ℝ) ^ ((3:ℝ)/2) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.min_le_left Y N) (by norm_num)
  have hLAleL : Real.log (((min Y N : ℕ) : ℝ) + 2) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by positivity)
    have hAN : ((min Y N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.min_le_right Y N
    nlinarith
  have hLAnn : 0 ≤ Real.log (((min Y N : ℕ) : ℝ) + 2) := by
    apply Real.log_nonneg
    have h : (0:ℝ) ≤ ((min Y N : ℕ) : ℝ) := by positivity
    linarith
  have hLA32 : (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32 ≤ L ^ 32 :=
    pow_le_pow_left₀ hLAnn hLAleL 32
  -- the `τ(c)^4 √c ≪ c` step
  have hA0le : C3 * (d : ℝ) * (|(k : ℝ)| + 1) * ((((c.divisors.card : ℕ) : ℝ)) ^ 4)
        * Real.sqrt c * (N : ℝ) ^ ((3:ℝ)/4) * L
      ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (C2 * (c : ℝ)) * (N : ℝ) ^ ((3:ℝ)/4) * L := by
    have hτ := hC2 c
    have hnn : 0 ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * L := by positivity
    calc C3 * (d : ℝ) * (|(k : ℝ)| + 1) * ((((c.divisors.card : ℕ) : ℝ)) ^ 4)
          * Real.sqrt c * (N : ℝ) ^ ((3:ℝ)/4) * L
        = (C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * L)
            * (((((c.divisors.card : ℕ) : ℝ)) ^ 4) * Real.sqrt c) := by ring
      _ ≤ (C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * L)
            * (C2 * (c : ℝ)) := mul_le_mul_of_nonneg_left hτ hnn
      _ = C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (C2 * (c : ℝ)) * (N : ℝ) ^ ((3:ℝ)/4) * L := by ring
  -- the whole double sum
  have hmain : ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
          ∑ m ∈ Finset.Icc 1 (N / (a * b)),
            Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ((a * b) * m))‖
      ≤ max 1 (C3 * C2 * C1 ^ 2) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
          * (N : ℝ) ^ ((3:ℝ)/4) * (Y : ℝ) ^ ((3:ℝ)/2) * L ^ 34 := by
    have hS1nn : 0 ≤ S1 := by
      rw [hS1def]
      refine Finset.sum_nonneg fun a _ => ?_
      split_ifs with h
      · exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
      · exact le_refl 0
    have hS2nn : 0 ≤ S2 := by
      rw [hS2def]
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs with h
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
      · exact le_refl 0
    have hMM : ((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2)
          * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32
        ≤ (Y : ℝ) ^ ((3:ℝ)/2) * L ^ 32 :=
      mul_le_mul hY32 hLA32 (by positivity) (by positivity)
    have hMM2 : ((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2)
          * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32 * L ^ 2
        ≤ (Y : ℝ) ^ ((3:ℝ)/2) * L ^ 32 * L ^ 2 :=
      mul_le_mul hMM (le_refl (L ^ 2)) (by positivity) (by positivity)
    refine le_trans hD ?_
    calc C3 * (d : ℝ) * (|(k : ℝ)| + 1) * ((((c.divisors.card : ℕ) : ℝ)) ^ 4) * Real.sqrt c
          * (N : ℝ) ^ ((3:ℝ)/4) * L * S1 * S2
        ≤ (C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (C2 * (c : ℝ)) * (N : ℝ) ^ ((3:ℝ)/4) * L)
            * (C1 * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4))
                * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 16)
            * (L * (C1 * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4))
                * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 16)) :=
          mul_le_mul (mul_le_mul hA0le hS1le hS1nn (by positivity)) hS2le hS2nn (by positivity)
      _ = C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
            * ((((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/4)) ^ 2)
            * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32 * L ^ 2 := by ring
      _ = C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
            * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2))
            * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32 * L ^ 2 := by rw [hQA2]
      _ ≤ C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
            * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 32 * L ^ 2 := by
          have hZ : 0 ≤ C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * (N : ℝ) ^ ((3:ℝ)/4) := by positivity
          calc C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
                * (((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2))
                * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32 * L ^ 2
              = (C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4))
                  * ((((min Y N : ℕ) : ℝ) ^ ((3:ℝ)/2)
                      * (Real.log (((min Y N : ℕ) : ℝ) + 2)) ^ 32 * L ^ 2)) := by ring
            _ ≤ (C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4))
                  * (((Y : ℝ) ^ ((3:ℝ)/2) * L ^ 32 * L ^ 2)) :=
                mul_le_mul_of_nonneg_left hMM2 hZ
            _ = C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
                  * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 32 * L ^ 2 := by ring
      _ = C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
            * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34 := by ring
      _ ≤ max 1 (C3 * C2 * C1 ^ 2) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
            * (N : ℝ) ^ ((3:ℝ)/4) * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34 := by
          have hK : C3 * C2 * C1 ^ 2 ≤ max 1 (C3 * C2 * C1 ^ 2) := le_max_right _ _
          have hnn : 0 ≤ (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
              * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34 := by positivity
          calc C3 * C2 * C1 ^ 2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4)
                * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34
              = (C3 * C2 * C1 ^ 2) * ((c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
                  * (N : ℝ) ^ ((3:ℝ)/4) * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34) := by ring
            _ ≤ max 1 (C3 * C2 * C1 ^ 2) * ((c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
                  * (N : ℝ) ^ ((3:ℝ)/4) * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34) :=
                mul_le_mul_of_nonneg_right hK hnn
            _ = max 1 (C3 * C2 * C1 ^ 2) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
                  * (N : ℝ) ^ ((3:ℝ)/4) * ((Y : ℝ) ^ ((3:ℝ)/2)) * L ^ 34 := by ring
  have hconv : L ^ 34 = (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ (34:ℝ) := by
    rw [hLdef]
    exact (Real.rpow_natCast (Real.log ((c : ℝ) * (N : ℝ) + 2)) 34).symm
  rw [hconv] at hmain
  exact hmain

end Work.FIArea7
