/-
# `Submission.Work.FIArea3.pairBracketPrim2`

The per-`z₁` joint divisor average over the polar box, for **primitive** `z₁`, in the sharp regime
`u := θ√N ≥ N^{3/8}`.  With `τ(n) = n.divisors.card`:

  `Σ_{z₂ ∈ polar box} τ(|z₂|²)·τ(|Δ(z₁,z₂)|) ≤ C·u²·(log N)^{2^19}`.

The estimate is assembled here from three independent blocks:

* **the reduction** `Work.FIArea3.pj_bracket_reduce` (module `CrudeBracketReduce`): FI Lemma 2.2
  with `k = 4` splits both `τ`'s at `K₁ = ⌈(2N)^{1/4}⌉`, `K₂ = ⌈(4πθN)^{1/4}⌉`,
  `JointCount.joint_double_sum_bound_aux` rearranges, and the per-`(d,e)` lattice count
  `Work.FIArea3.jointCountNoBox` turns the sum into `65536·(π u² D₁ + 80 u D₂ + D₃)`, where
  `Dᵢ = Work.FIArea3.dsumᵢ K₁ K₂` are the three divisor sums of `PairBracketDefs`;
* **the divisor-sum bounds** `Work.FIArea3.dsum_bounds`:
  `D₁ ≤ Cd(log K₂+2)^{2^9}(log K₁+2)^{2^18}`,
  `D₂ ≤ Cd√K₁K₂(log K₁+2)^{2^17}(log K₂+2)^{2^8}`,
  `D₃ ≤ Cd K₁K₂(log K₁+2)^{2^9}(log K₂+2)^{2^8}`;
* **the product and log bounds** `Work.FIArea3.sqrtK1_K2_le`, `Work.FIArea3.K1_K2_le` and
  `Work.FIArea3.logK_le_logN`: `√K₁K₂ ≤ 8N^{3/8} ≤ 8u`, `K₁K₂ ≤ 16N^{1/2} ≤ 16u²` and
  `log Kᵢ + 2 ≤ log N`.

The closing power bookkeeping (`pb2_close_arith` below — the exponents `2^18+2^9 = 262656`,
`2^{17}+2^8 = 131328`, `2^9+2^8 = 768` are all `≤ 2^19 = 524288`), the reduction of the two
ceilings to `2·(·)^{1/4}` (`pb2_ceil_..._le`) and `log N ≥ 2^19` (`pb2_logN_ge`, from
`u ≥ N^{3/8}` together with `θ = (log x)^{-A'}`, `A' ≥ 2^{20}`) are proved in this file.
-/
import Mathlib
import Submission.Work.FIArea3.CrudeBracketReduce
import Submission.Work.FIArea3.dsum_bounds
import Submission.Work.FIArea3.logK_le_logN
import Submission.Work.FIArea3.sqrtK1_K2_le
import Submission.Work.FIArea3.K1_K2_le
import Submission.Work.FIArea3.BoxDefs

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. Bookkeeping facts about the parameters -/

/-- In the sharp regime `N^{3/8} ≤ θ√N` one has `N^{7/8} ≤ θN`, hence `1 ≤ θN`. -/
theorem pb2_theta_N_ge_one (Pa : Work.FITop.Params)
    (hu : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) :
    (1 : ℝ) ≤ Pa.θ * Pa.N := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have h1 : Pa.N ^ ((3 : ℝ) / 8) * Real.sqrt Pa.N
      ≤ (Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N :=
    mul_le_mul_of_nonneg_right hu (Real.sqrt_nonneg _)
  have h2 : Pa.N ^ ((3 : ℝ) / 8) * Real.sqrt Pa.N = Pa.N ^ ((7 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]; norm_num
  have h3 : (Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N = Pa.θ * Pa.N := by
    rw [mul_assoc, ← sq, Real.sq_sqrt hNpos.le]
  rw [h2, h3] at h1
  exact le_trans (Real.one_le_rpow Pa.hN1 (by norm_num)) h1

/-- In the sharp regime `4πθN ≥ 1`, so `(4πθN)^{1/4} ≥ 1`. -/
theorem pb2_one_le_four_pi_mul (Pa : Work.FITop.Params)
    (hu : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) :
    (1 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
  have hθN1 : (1 : ℝ) ≤ Pa.θ * Pa.N := pb2_theta_N_ge_one Pa hu
  have h4pi : (1 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (4 * Real.pi) * (Pa.θ * Pa.N) :=
        mul_le_mul h4pi hθN1 zero_le_one (by linarith [Real.pi_gt_three])
    _ = 4 * Real.pi * Pa.θ * Pa.N := by ring

/-- `⌈(2N)^{1/4}⌉ ≤ 2·(2N)^{1/4}` for `N ≥ 1`. -/
theorem pb2_ceil_two_N_le (N : ℝ) (hN : 1 ≤ N) :
    (Nat.ceil ((2 * N) ^ ((1 : ℝ) / 4)) : ℝ) ≤ 2 * (2 * N) ^ ((1 : ℝ) / 4) := by
  have h2N : (0 : ℝ) ≤ 2 * N := by linarith
  have h1 : (1 : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by linarith) (by norm_num)
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg h2N ((1 : ℝ) / 4))
  linarith

/-- `⌈(4πθN)^{1/4}⌉ ≤ 2·(4πθN)^{1/4}` in the sharp regime. -/
theorem pb2_ceil_four_pi_le (Pa : Work.FITop.Params)
    (hu : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) :
    (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) : ℝ)
      ≤ 2 * (4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4) := by
  have h4 : (1 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := pb2_one_le_four_pi_mul Pa hu
  have hx4 : (1 : ℝ) ≤ (4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow h4 (by norm_num)
  have hnn : (0 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by linarith
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hnn ((1 : ℝ) / 4))
  linarith

/-- `log N ≥ 2^19` in the sharp regime `N^{3/8} ≤ θ√N`: dividing by `√N` gives `θ ≥ N^{-1/8}`,
i.e. `(1/8)·log N ≥ A'·loglog x ≥ 2^{20}/16`. -/
theorem pb2_logN_ge (Pa : Work.FITop.Params)
    (h : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) :
    (2 : ℝ) ^ (19 : ℕ) ≤ Real.log Pa.N := by
  have hN1 : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hsqrt_pos : 0 < Real.sqrt Pa.N := Real.sqrt_pos.mpr hN1
  have hθge : Pa.N ^ (-(1 : ℝ) / 8) ≤ Pa.θ := by
    have h1 : Pa.N ^ ((3 : ℝ) / 8) / Real.sqrt Pa.N ≤ Pa.θ := by
      rw [div_le_iff₀ hsqrt_pos]; linarith [h]
    have h2 : Pa.N ^ ((3 : ℝ) / 8) / Real.sqrt Pa.N = Pa.N ^ (-(1 : ℝ) / 8) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hN1]
      norm_num
    rwa [h2] at h1
  have hlogx : 0 < Real.log (Pa.x : ℝ) := by
    have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by
      have hlt : 1 < Pa.x := Nat.lt_of_lt_of_le (by norm_num) Pa.hx
      exact_mod_cast hlt
    exact Real.log_pos hx1
  have hlogθ : Real.log Pa.θ = -Pa.A' * Real.log (Real.log (Pa.x : ℝ)) := by
    rw [Pa.hθ, Real.log_rpow hlogx]
  have hlogN : Real.log (Pa.N ^ (-(1 : ℝ) / 8)) = -(1 : ℝ) / 8 * Real.log Pa.N := by
    rw [Real.log_rpow hN1]
  have hlogle : Real.log (Pa.N ^ (-(1 : ℝ) / 8)) ≤ Real.log Pa.θ :=
    Real.log_le_log (Real.rpow_pos_of_pos hN1 _) hθge
  rw [hlogN, hlogθ] at hlogle
  have hll : (1 / 16 : ℝ) ≤ Real.log (Real.log (Pa.x : ℝ)) := Work.FIArea3.pj_loglog_ge Pa
  have hA' : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
  nlinarith [hlogle, hll, hA']

/-! ## 2. Closing power bookkeeping -/

/-- **Closing arithmetic of the bracket bound.**  With `u > 0`, `L ≥ 1`, log-variables
`log K₁ + 2 ≤ L`, `log K₂ + 2 ≤ L`, product bounds `√K₁K₂ ≤ 16u`, `K₁K₂ ≤ 16u²` and the
divisor-sum bounds of `Work.FIArea3.dsum_bounds` at `(K₁,K₂)`,

  `65536·(π u² D₁ + 80 u D₂ + D₃) ≤ 2^30·Cd·u²·L^{2^19}`. -/
private lemma pb2_close_arith (Cd u L : ℝ) (K1 K2 : ℕ) (D1 D2 D3 : ℝ)
    (hCd : 0 < Cd) (hu : 0 < u) (hL : 1 ≤ L)
    (hLK1le : Real.log (K1 : ℝ) + 2 ≤ L) (hLK2le : Real.log (K2 : ℝ) + 2 ≤ L)
    (hsq : Real.sqrt (K1 : ℝ) * (K2 : ℝ) ≤ 16 * u)
    (hkk : (K1 : ℝ) * (K2 : ℝ) ≤ 16 * u ^ 2)
    (hD1 : D1 ≤ Cd * (Real.log (K2 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K1 : ℝ) + 2) ^ (262144 : ℕ))
    (hD2 : D2 ≤ Cd * Real.sqrt (K1 : ℝ) * (K2 : ℝ)
              * (Real.log (K1 : ℝ) + 2) ^ (131072 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ))
    (hD3 : D3 ≤ Cd * (K1 : ℝ) * (K2 : ℝ)
              * (Real.log (K1 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ)) :
    65536 * (Real.pi * u ^ 2 * D1 + 80 * u * D2 + D3)
      ≤ (2 : ℝ) ^ (30 : ℕ) * Cd * u ^ 2 * L ^ ((2 : ℕ) ^ (19 : ℕ)) := by
  have hCdnn : (0 : ℝ) ≤ Cd := hCd.le
  have hunn : (0 : ℝ) ≤ u := hu.le
  have hLnn : (0 : ℝ) ≤ L := le_trans (by norm_num) hL
  have hu2nn : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
  have hK1nn : (0 : ℝ) ≤ Real.log (K1 : ℝ) + 2 := by
    have := Real.log_natCast_nonneg K1; linarith only [this]
  have hK2nn : (0 : ℝ) ≤ Real.log (K2 : ℝ) + 2 := by
    have := Real.log_natCast_nonneg K2; linarith only [this]
  have p512 : (Real.log (K2 : ℝ) + 2) ^ (512 : ℕ) ≤ L ^ (512 : ℕ) :=
    pow_le_pow_left₀ hK2nn hLK2le 512
  have p262 : (Real.log (K1 : ℝ) + 2) ^ (262144 : ℕ) ≤ L ^ (262144 : ℕ) :=
    pow_le_pow_left₀ hK1nn hLK1le 262144
  have p131 : (Real.log (K1 : ℝ) + 2) ^ (131072 : ℕ) ≤ L ^ (131072 : ℕ) :=
    pow_le_pow_left₀ hK1nn hLK1le 131072
  have p256 : (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ) ≤ L ^ (256 : ℕ) :=
    pow_le_pow_left₀ hK2nn hLK2le 256
  have p512' : (Real.log (K1 : ℝ) + 2) ^ (512 : ℕ) ≤ L ^ (512 : ℕ) :=
    pow_le_pow_left₀ hK1nn hLK1le 512
  have hD1b : D1 ≤ Cd * L ^ (262656 : ℕ) := by
    calc D1 ≤ Cd * (Real.log (K2 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K1 : ℝ) + 2) ^ (262144 : ℕ) := hD1
      _ = Cd * ((Real.log (K2 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K1 : ℝ) + 2) ^ (262144 : ℕ)) := by rw [mul_assoc]
      _ ≤ Cd * (L ^ (512 : ℕ) * L ^ (262144 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul p512 p262 (pow_nonneg hK1nn _) (pow_nonneg hLnn _)) hCdnn
      _ = Cd * L ^ (262656 : ℕ) := by
          have hp : (512 : ℕ) + 262144 = 262656 := by norm_num
          rw [← pow_add, hp]
  have hD2b : D2 ≤ Cd * (16 * u) * L ^ (131328 : ℕ) := by
    have hstep : Cd * Real.sqrt (K1 : ℝ) * (K2 : ℝ) ≤ Cd * (16 * u) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hsq hCdnn
    calc D2 ≤ Cd * Real.sqrt (K1 : ℝ) * (K2 : ℝ)
              * (Real.log (K1 : ℝ) + 2) ^ (131072 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ) := hD2
      _ ≤ Cd * (16 * u) * (Real.log (K1 : ℝ) + 2) ^ (131072 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep (pow_nonneg hK1nn _))
            (pow_nonneg hK2nn _)
      _ = Cd * (16 * u) * ((Real.log (K1 : ℝ) + 2) ^ (131072 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ)) := by rw [mul_assoc]
      _ ≤ Cd * (16 * u) * (L ^ (131072 : ℕ) * L ^ (256 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul p131 p256 (pow_nonneg hK2nn _) (pow_nonneg hLnn _))
            (mul_nonneg hCdnn (by linarith only [hu] : (0 : ℝ) ≤ 16 * u))
      _ = Cd * (16 * u) * L ^ (131328 : ℕ) := by
          have hp : (131072 : ℕ) + 256 = 131328 := by norm_num
          rw [← pow_add, hp]
  have hD3b : D3 ≤ Cd * (16 * u ^ 2) * L ^ (768 : ℕ) := by
    have hstep : Cd * (K1 : ℝ) * (K2 : ℝ) ≤ Cd * (16 * u ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hkk hCdnn
    calc D3 ≤ Cd * (K1 : ℝ) * (K2 : ℝ)
              * (Real.log (K1 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ) := hD3
      _ ≤ Cd * (16 * u ^ 2) * (Real.log (K1 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep (pow_nonneg hK1nn _))
            (pow_nonneg hK2nn _)
      _ = Cd * (16 * u ^ 2) * ((Real.log (K1 : ℝ) + 2) ^ (512 : ℕ)
              * (Real.log (K2 : ℝ) + 2) ^ (256 : ℕ)) := by rw [mul_assoc]
      _ ≤ Cd * (16 * u ^ 2) * (L ^ (512 : ℕ) * L ^ (256 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul p512' p256 (pow_nonneg hK2nn _) (pow_nonneg hLnn _))
            (mul_nonneg hCdnn (by positivity))
      _ = Cd * (16 * u ^ 2) * L ^ (768 : ℕ) := by
          have hp : (512 : ℕ) + 256 = 768 := by norm_num
          rw [← pow_add, hp]
  have h1 : Real.pi * u ^ 2 * D1 ≤ Cd * u ^ 2 * (Real.pi * L ^ (262656 : ℕ)) := by
    calc Real.pi * u ^ 2 * D1 ≤ Real.pi * u ^ 2 * (Cd * L ^ (262656 : ℕ)) :=
          mul_le_mul_of_nonneg_left hD1b (mul_nonneg Real.pi_pos.le hu2nn)
      _ = Cd * u ^ 2 * (Real.pi * L ^ (262656 : ℕ)) := by ring
  have h2 : 80 * u * D2 ≤ Cd * u ^ 2 * (1280 * L ^ (131328 : ℕ)) := by
    calc 80 * u * D2 ≤ 80 * u * (Cd * (16 * u) * L ^ (131328 : ℕ)) :=
          mul_le_mul_of_nonneg_left hD2b (by positivity)
      _ = Cd * u ^ 2 * (1280 * L ^ (131328 : ℕ)) := by ring
  have h3 : D3 ≤ Cd * u ^ 2 * (16 * L ^ (768 : ℕ)) := by
    calc D3 ≤ Cd * (16 * u ^ 2) * L ^ (768 : ℕ) := hD3b
      _ = Cd * u ^ 2 * (16 * L ^ (768 : ℕ)) := by ring
  have hcomb : Real.pi * u ^ 2 * D1 + 80 * u * D2 + D3
      ≤ Cd * u ^ 2 * (Real.pi * L ^ (262656 : ℕ) + 1280 * L ^ (131328 : ℕ)
          + 16 * L ^ (768 : ℕ)) := by
    have hh : Cd * u ^ 2 * (Real.pi * L ^ (262656 : ℕ) + 1280 * L ^ (131328 : ℕ)
          + 16 * L ^ (768 : ℕ))
        = Cd * u ^ 2 * (Real.pi * L ^ (262656 : ℕ)) + Cd * u ^ 2 * (1280 * L ^ (131328 : ℕ))
          + Cd * u ^ 2 * (16 * L ^ (768 : ℕ)) := by ring
    rw [hh]; linarith only [h1, h2, h3]
  have e1 : L ^ (262656 : ℕ) ≤ L ^ ((2 : ℕ) ^ (19 : ℕ)) := pow_le_pow_right₀ hL (by norm_num)
  have e2 : L ^ (131328 : ℕ) ≤ L ^ ((2 : ℕ) ^ (19 : ℕ)) := pow_le_pow_right₀ hL (by norm_num)
  have e3 : L ^ (768 : ℕ) ≤ L ^ ((2 : ℕ) ^ (19 : ℕ)) := pow_le_pow_right₀ hL (by norm_num)
  have hE : Real.pi * L ^ (262656 : ℕ) + 1280 * L ^ (131328 : ℕ) + 16 * L ^ (768 : ℕ)
      ≤ (Real.pi + 1296) * L ^ ((2 : ℕ) ^ (19 : ℕ)) := by
    have c1 := mul_le_mul_of_nonneg_left e1 Real.pi_pos.le
    have c2 := mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 1280)
    have c3 := mul_le_mul_of_nonneg_left e3 (by norm_num : (0 : ℝ) ≤ 16)
    linarith only [c1, c2, c3]
  have hbig : 65536 * (Real.pi + 1296) ≤ (2 : ℝ) ^ (30 : ℕ) := by
    have h30 : (2 : ℝ) ^ (30 : ℕ) = 1073741824 := by norm_num
    linarith only [Real.pi_lt_four, h30]
  calc 65536 * (Real.pi * u ^ 2 * D1 + 80 * u * D2 + D3)
      ≤ 65536 * (Cd * u ^ 2 * (Real.pi * L ^ (262656 : ℕ) + 1280 * L ^ (131328 : ℕ)
          + 16 * L ^ (768 : ℕ))) := mul_le_mul_of_nonneg_left hcomb (by norm_num)
    _ ≤ 65536 * (Cd * u ^ 2 * ((Real.pi + 1296) * L ^ ((2 : ℕ) ^ (19 : ℕ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hE (mul_nonneg hCdnn hu2nn)
    _ = (65536 * (Real.pi + 1296)) * (Cd * u ^ 2 * L ^ ((2 : ℕ) ^ (19 : ℕ))) := by ring
    _ ≤ (2 : ℝ) ^ (30 : ℕ) * (Cd * u ^ 2 * L ^ ((2 : ℕ) ^ (19 : ℕ))) :=
        mul_le_mul_of_nonneg_right hbig (mul_nonneg (mul_nonneg hCdnn hu2nn) (pow_nonneg hLnn _))
    _ = (2 : ℝ) ^ (30 : ℕ) * Cd * u ^ 2 * L ^ ((2 : ℕ) ^ (19 : ℕ)) := by ring

/-! ## 3. The assembled bracket bound -/

theorem pairBracketPrim2 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt),
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      Nat.Coprime z₁.re.natAbs z₁.im.natAbs →
      (∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N) →
      (∑ z₂ ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.gnorm z₂).divisors.card : ℕ) : ℝ)
            * (((Work.FIPlan.absDelta z₁ z₂).divisors.card : ℕ) : ℝ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ 2 * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := Work.FIArea3.dsum_bounds
  refine ⟨(2 : ℝ) ^ (30 : ℕ) * Cd, mul_pos (by norm_num) hCdpos, ?_⟩
  intro Pa φ z₁ hu hcop hbox
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea3.pj_theta_le_one Pa
  have hu_pos : 0 < Pa.θ * Real.sqrt Pa.N := mul_pos Pa.hθ0 (Real.sqrt_pos.mpr hNpos)
  have hlogN : (2 : ℝ) ^ (19 : ℕ) ≤ Real.log Pa.N := pb2_logN_ge Pa hu
  have hL1 : (1 : ℝ) ≤ Real.log Pa.N := by
    have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (19 : ℕ) := by norm_num
    linarith
  -- the two ceilings against the real fourth roots
  have hK1ge : (1 : ℝ) ≤ ((Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ) : ℝ) := by
    exact le_trans (Real.one_le_rpow (by linarith only [hN1] : (1 : ℝ) ≤ 2 * Pa.N)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) (Nat.le_ceil _)
  have hK2ge : (1 : ℝ) ≤ ((Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ) : ℝ) := by
    exact le_trans (Real.one_le_rpow (pb2_one_le_four_pi_mul Pa hu)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) (Nat.le_ceil _)
  have hK1le : ((Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ) : ℝ)
      ≤ 2 * (2 * Pa.N) ^ ((1 : ℝ) / 4) := pb2_ceil_two_N_le Pa.N hN1
  have hK2le : ((Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ) : ℝ)
      ≤ 2 * (4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4) := pb2_ceil_four_pi_le Pa hu
  -- the logarithmic bounds on the two cutoffs
  have hLK1le : Real.log (((Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ)) : ℝ) + 2
      ≤ Real.log Pa.N :=
    Work.FIArea3.logK_le_logN Pa.N 1 _ 2 hN1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlogN hK1ge (by simpa using hK1le)
  have hLK2le : Real.log (((Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ)) : ℝ)
      + 2 ≤ Real.log Pa.N :=
    Work.FIArea3.logK_le_logN Pa.N Pa.θ _ (4 * Real.pi) hN1 Pa.hθ0 hθ1
      (by positivity) (by nlinarith [Real.pi_lt_four]) hlogN hK2ge (by simpa using hK2le)
  -- the two product bounds `√K₁K₂ ≤ 8N^{3/8}` and `K₁K₂ ≤ 16N^{1/2}`
  have hsq : Real.sqrt (((Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ)) : ℝ)
        * (((Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ)) : ℝ)
      ≤ 16 * (Pa.θ * Real.sqrt Pa.N) := by
    have h := Work.FIArea3.sqrtK1_K2_le Pa.N Pa.θ _ _ hN1 Pa.hθ0 hθ1
      hK1ge hK1le hK2ge hK2le
    have h8 : 8 * Pa.N ^ ((3 : ℝ) / 8) ≤ 8 * (Pa.θ * Real.sqrt Pa.N) :=
      mul_le_mul_of_nonneg_left hu (by norm_num)
    linarith only [h, h8, hu_pos.le]
  have hkk : (((Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ)) : ℝ)
        * (((Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) : ℕ)) : ℝ)
      ≤ 16 * (Pa.θ * Real.sqrt Pa.N) ^ 2 := by
    have h := Work.FIArea3.K1_K2_le Pa.N Pa.θ _ _ hN1 Pa.hθ0 hθ1
      hK1ge hK1le hK2ge hK2le
    have h34 : Pa.N ^ ((3 : ℝ) / 4) ≤ (Pa.θ * Real.sqrt Pa.N) ^ 2 := by
      have hsq' : (Pa.N ^ ((3 : ℝ) / 8)) ^ 2 ≤ (Pa.θ * Real.sqrt Pa.N) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hu 2
      have hpow : (Pa.N ^ ((3 : ℝ) / 8)) ^ 2 = Pa.N ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
      rwa [hpow] at hsq'
    have h12 : Pa.N ^ ((1 : ℝ) / 2) ≤ (Pa.θ * Real.sqrt Pa.N) ^ 2 :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)) h34
    linarith only [h, h12]
  have hclose := pb2_close_arith Cd (Pa.θ * Real.sqrt Pa.N) (Real.log Pa.N)
    (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
    (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)))
    (Work.FIArea3.dsum1 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
      (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4))))
    (Work.FIArea3.dsum2 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
      (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4))))
    (Work.FIArea3.dsum3 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
      (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4))))
    hCdpos hu_pos hL1 hLK1le hLK2le hsq hkk
    (hCd _ _).1 (hCd _ _).2.1 (hCd _ _).2.2
  exact le_trans (Work.FIArea3.pj_bracket_reduce Pa φ z₁ hcop hbox) hclose

end

end Work.FIArea3
