import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.semiPairCount_card_le
import Submission.Work.NumberTheory.Chen.BTermCount.primeCharSumBound
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Work.NumberTheory.Chen.BTermCount.sumInvTotientLogBound
import Submission.Work.NumberTheory.Chen.BTermCount.bPairCountLeSelf
import Submission.Work.NumberTheory.Chen.BTermCount.blockStartLeAdd
import Submission.Work.NumberTheory.Chen.BTermCount.blockCountCastLe
import Submission.Work.NumberTheory.Chen.BTermCount.blodSumUVLe
import Submission.Work.NumberTheory.Chen.BTermCount.blodSumUSqrtVLe
import Submission.Work.NumberTheory.Chen.BTermCount.blodSumVSqrtULe
import Submission.Work.NumberTheory.Chen.BTermCount.blodSumSqrtUVLe
import Submission.Work.NumberTheory.Chen.BTermCount.blodW1Le

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000

private theorem blodUMulBlodVLe (x M Y j : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hj : j < blockCount M Y) :
    (blodU M j : ℝ) * (blodV x M j : ℝ) ≤ 4 * (x : ℝ) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hx32R : (32:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hQle : blockStart M j ≤ Y + M := blockStartLeAdd M Y j hM hj
  have hQle' : (blockStart M j : ℝ) ≤ (Y:ℝ) + (M:ℝ) := by exact_mod_cast hQle
  have hYM : (M:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hMY
  have hQpos : (0:ℝ) < (blockStart M j : ℝ) := by
    have h : 0 < blockStart M j := Nat.mul_pos (by omega) (pow_pos (by norm_num : (0:ℕ) < 2) j)
    exact_mod_cast h
  have hQ : (blockStart M j : ℝ) ≤ 4*(x:ℝ)^((1:ℝ)/3) := by
    calc (blockStart M j : ℝ) ≤ (Y:ℝ) + (M:ℝ) := hQle'
      _ ≤ 2*(Y:ℝ) := by linarith only [hYM]
      _ ≤ 2*(2*(x:ℝ)^((1:ℝ)/3)) := by linarith only [hY]
      _ = 4*(x:ℝ)^((1:ℝ)/3) := by ring
  have h8 : (8:ℝ) ≤ (32:ℝ)^((2:ℝ)/3) := by
    rw [show (8:ℝ) = (2:ℝ)^(3:ℝ) by norm_num [Real.rpow_natCast],
      show (32:ℝ) = (2:ℝ)^(5:ℝ) by norm_num [Real.rpow_natCast],
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      show (5:ℝ) * (2/3) = 10/3 by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h8x : 8*(x:ℝ)^((1:ℝ)/3) ≤ (x:ℝ) := by
    have h23 : (x:ℝ)^((2:ℝ)/3) * (x:ℝ)^((1:ℝ)/3) = (x:ℝ) := by
      rw [← Real.rpow_add hx0, show (2:ℝ)/3 + 1/3 = 1 by norm_num, Real.rpow_one]
    calc 8*(x:ℝ)^((1:ℝ)/3) ≤ (x:ℝ)^((2:ℝ)/3) * (x:ℝ)^((1:ℝ)/3) :=
          mul_le_mul_of_nonneg_right
            (le_trans h8 (Real.rpow_le_rpow (by norm_num) hx32R (by norm_num)))
            (Real.rpow_nonneg hx0.le _)
      _ = (x:ℝ) := h23
  have hu : (blodU M j : ℝ) = 2*(blockStart M j : ℝ) := by rw [blodU]; push_cast; ring
  have hv : (blodV x M j : ℝ) = (((x+2)/blockStart M j : ℕ) : ℝ) + 1 := by rw [blodV]; push_cast; ring
  have hdiv : (((x+2)/blockStart M j : ℕ) : ℝ) ≤ ((x+2 : ℕ) : ℝ)/(blockStart M j : ℝ) :=
    Nat.cast_div_le
  have hcancel : (blockStart M j : ℝ) * (((x:ℝ)+2)/(blockStart M j : ℝ)) = (x:ℝ)+2 :=
    mul_div_cancel₀ _ (ne_of_gt hQpos)
  calc (blodU M j : ℝ)*(blodV x M j : ℝ)
      = 2*(blockStart M j : ℝ) * ((((x+2)/blockStart M j : ℕ) : ℝ) + 1) := by rw [hu, hv]
    _ ≤ 2*(blockStart M j : ℝ) * (((x:ℝ)+2)/(blockStart M j : ℝ) + 1) := by
          have hdiv' : (((x+2)/blockStart M j : ℕ) : ℝ) ≤ ((x:ℝ)+2)/(blockStart M j : ℝ) := by
            simpa using hdiv
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith only [hdiv']
    _ = 2*((x:ℝ)+2) + 2*(blockStart M j : ℝ) := by
          rw [mul_add, mul_one, mul_assoc, hcancel]
    _ ≤ 2*((x:ℝ)+2) + 8*(x:ℝ)^((1:ℝ)/3) := by linarith only [hQ]
    _ ≤ 4*(x:ℝ) := by linarith only [h8x, hx32R]

private theorem natLog2Le (D x : ℕ) (hD : 1 ≤ D) (hDx : D ≤ x) (hx : 8 ≤ x) :
    ((Nat.log 2 D : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
  have hD0 : (0:ℕ) < D := by omega
  have hp : 2 ^ Nat.log 2 D ≤ D := Nat.pow_log_le_self 2 (by omega)
  have hp' : (2:ℝ) ^ Nat.log 2 D ≤ (D:ℝ) := by exact_mod_cast hp
  have hpowpos : (0:ℝ) < (2:ℝ) ^ Nat.log 2 D := by positivity
  have h1 : ((Nat.log 2 D : ℕ) : ℝ) * Real.log 2 ≤ Real.log (D:ℝ) := by
    have h := Real.log_le_log hpowpos hp'
    rwa [Real.log_pow] at h
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD0
  have hDx' : (D:ℝ) ≤ (x:ℝ) := by exact_mod_cast hDx
  have h2 : Real.log (D:ℝ) ≤ Real.log (x:ℝ) := Real.log_le_log hDpos hDx'
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2:ℝ)) (by norm_num)
    norm_num at h; linarith only [h]
  have h3 : ((Nat.log 2 D : ℕ) : ℝ) ≤ Real.log (x:ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith only [h1, h2]
  calc ((Nat.log 2 D : ℕ) : ℝ) ≤ Real.log (x:ℝ) / Real.log 2 := h3
    _ ≤ 2 * Real.log (x:ℝ) := by
        rw [div_le_iff₀ hlog2pos]
        have hxnn : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
        nlinarith only [hlog2half, hxnn]


/-! ## The pointwise bound for one block summand -/

private lemma blodTermLe (x M Y D R₀ j : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hD : 2 ≤ D) (hDx : D ≤ x) (hR₀ : 1 ≤ R₀)
    (hj : j < blockCount M Y) :
    Real.sqrt ((blodU M j : ℝ) * (bPairCount Y (blodV x M j) : ℝ)) *
      (2 * Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)) / (2 : ℝ) ^ (Nat.log 2 R₀)
        + 2 * Real.sqrt (blodU M j : ℝ) * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 2 * Real.sqrt (blodV x M j : ℝ) * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 4 * (2 : ℝ) ^ (Nat.log 2 D + 1)) *
      Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2)
    ≤ (8 * Real.log (x : ℝ) / (R₀ : ℝ)) * ((blodU M j : ℝ) * (blodV x M j : ℝ))
      + (12 * (Real.log (x : ℝ)) ^ 2) * ((blodU M j : ℝ) * Real.sqrt (blodV x M j : ℝ))
      + (12 * (Real.log (x : ℝ)) ^ 2) * ((blodV x M j : ℝ) * Real.sqrt (blodU M j : ℝ))
      + (16 * (D : ℝ) * Real.log (x : ℝ))
          * Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)) := by
  have hx8 : 8 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  set L := Real.log (x : ℝ) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hL2 : (2:ℝ) ≤ L := by
    have hle : Real.log 32 ≤ L := by
      rw [hL]; exact Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have h32 : (2:ℝ) ≤ Real.log 32 := by
      have h2 : (1/2:ℝ) ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (x := (2:ℝ)) (by norm_num)
        norm_num at h; linarith
      have hp : Real.log 32 = 5 * Real.log 2 := by
        rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
      rw [hp]; linarith
    linarith
  set u := (blodU M j : ℝ) with hu
  set v := (blodV x M j : ℝ) with hv
  set B := (bPairCount Y (blodV x M j) : ℝ) with hB
  -- positivity of `u`, `v`
  have hQpos : 0 < blockStart M j := Nat.mul_pos (by omega) (pow_pos (by norm_num : (0:ℕ) < 2) j)
  have huval : u = 2 * (blockStart M j : ℝ) := by rw [hu, blodU]; push_cast; ring
  have hupos : 0 < u := by rw [huval]; positivity
  have hvval : v = (((x + 2) / blockStart M j : ℕ) : ℝ) + 1 := by rw [hv, blodV]; push_cast; ring
  have hvpos : 0 < v := by rw [hvval]; positivity
  have hBv : B ≤ v := by
    rw [hB, hv]
    exact_mod_cast bPairCountLeSelf Y (blodV x M j)
  have hB0 : 0 ≤ B := by positivity
  have hsqrt_le : Real.sqrt (u * B) ≤ Real.sqrt (u * v) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBv (le_of_lt hupos))
  -- `2 ^ Nat.log 2 R₀ > R₀ / 2`
  have hR0pos : (0:ℝ) < (R₀ : ℝ) := by exact_mod_cast (by omega : 0 < R₀)
  have hR0pow : (R₀ : ℝ) / 2 < (2:ℝ) ^ (Nat.log 2 R₀) := by
    have h : (R₀ : ℝ) < (2:ℝ) ^ (Nat.log 2 R₀ + 1) := by
      have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) R₀
      exact_mod_cast h1
    rw [pow_succ] at h; linarith
  have hR0powpos : (0:ℝ) < (2:ℝ) ^ (Nat.log 2 R₀) := by positivity
  have hdiv1 : 2 * Real.sqrt (u * v) / (2:ℝ) ^ (Nat.log 2 R₀)
      ≤ 4 * Real.sqrt (u * v) / (R₀ : ℝ) := by
    rw [div_le_div_iff₀ hR0powpos hR0pos]
    have hs : 0 ≤ Real.sqrt (u * v) := Real.sqrt_nonneg _
    nlinarith [hR0pow, hs]
  -- `Nat.log 2 D ≤ 2 L`
  have hKle : ((Nat.log 2 D + 1 : ℕ) : ℝ) ≤ 3 * L := by
    have h := natLog2Le D x (by omega) hDx hx8
    push_cast
    linarith
  have h4 : 4 * (2:ℝ) ^ (Nat.log 2 D + 1) ≤ 8 * (D : ℝ) := by
    have hp : 2 ^ Nat.log 2 D ≤ D := Nat.pow_log_le_self 2 (by omega : D ≠ 0)
    have hp2 : (2:ℝ) ^ Nat.log 2 D ≤ (D : ℝ) := by exact_mod_cast hp
    have : (2:ℝ) ^ (Nat.log 2 D + 1) = (2:ℝ) ^ Nat.log 2 D * 2 := pow_succ _ _
    rw [this]; linarith
  have hbr : 2 * Real.sqrt (u * v) / (2:ℝ) ^ (Nat.log 2 R₀)
        + 2 * Real.sqrt u * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 2 * Real.sqrt v * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 4 * (2:ℝ) ^ (Nat.log 2 D + 1)
      ≤ 4 * Real.sqrt (u * v) / (R₀ : ℝ) + 6 * Real.sqrt u * L + 6 * Real.sqrt v * L
        + 8 * (D : ℝ) := by
    have h2 : 2 * Real.sqrt u * ((Nat.log 2 D + 1 : ℕ) : ℝ) ≤ 6 * Real.sqrt u * L := by
      nlinarith [hKle, Real.sqrt_nonneg u]
    have h3 : 2 * Real.sqrt v * ((Nat.log 2 D + 1 : ℕ) : ℝ) ≤ 6 * Real.sqrt v * L := by
      nlinarith [hKle, Real.sqrt_nonneg v]
    linarith [hdiv1, h2, h3, h4]
  -- the logarithm
  have huv_le : u * v ≤ 4 * (x : ℝ) := by
    rw [hu, hv]; exact blodUMulBlodVLe x M Y j hx hM hMY hY hj
  have hlog_le : Real.log (2 * u * v + 2) ≤ 2 * L := by
    have h8 : 2 * u * v + 2 ≤ 10 * (x : ℝ) := by nlinarith only [huv_le, hx1]
    have hpos : 0 < 2 * u * v + 2 := by positivity
    have hlog8 : Real.log 10 ≤ L := by
      rw [hL]; exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 10 ≤ x))
    calc Real.log (2 * u * v + 2) ≤ Real.log (10 * (x : ℝ)) := Real.log_le_log hpos h8
      _ = Real.log 10 + L := by rw [Real.log_mul (by norm_num) (by positivity), hL]
      _ ≤ 2 * L := by linarith only [hlog8]
  -- the sqrt identities
  have hsq : Real.sqrt (u * v) * Real.sqrt (u * v) = u * v := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  have hsq_u : Real.sqrt (u * v) * Real.sqrt u = u * Real.sqrt v := by
    have h : Real.sqrt (u * v) * Real.sqrt u = Real.sqrt ((u * v) * u) :=
      (Real.sqrt_mul (by positivity : (0:ℝ) ≤ u * v) u).symm
    rw [h, show (u * v) * u = u ^ 2 * v by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ u ^ 2) v, Real.sqrt_sq (le_of_lt hupos)]
  have hsq_v : Real.sqrt (u * v) * Real.sqrt v = v * Real.sqrt u := by
    have h : Real.sqrt (u * v) * Real.sqrt v = Real.sqrt ((u * v) * v) :=
      (Real.sqrt_mul (by positivity : (0:ℝ) ≤ u * v) v).symm
    rw [h, show (u * v) * v = v ^ 2 * u by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ v ^ 2) u, Real.sqrt_sq (le_of_lt hvpos)]
  have hident : Real.sqrt (u * v)
        * (4 * Real.sqrt (u * v) / (R₀ : ℝ) + 6 * Real.sqrt u * L + 6 * Real.sqrt v * L
            + 8 * (D : ℝ)) * (2 * L)
      = (8 * L / (R₀ : ℝ)) * (u * v) + (12 * L ^ 2) * (u * Real.sqrt v)
        + (12 * L ^ 2) * (v * Real.sqrt u) + (16 * (D : ℝ) * L) * Real.sqrt (u * v) := by
    have hstep : Real.sqrt (u * v)
          * (4 * Real.sqrt (u * v) / (R₀ : ℝ) + 6 * Real.sqrt u * L + 6 * Real.sqrt v * L
              + 8 * (D : ℝ)) * (2 * L)
        = (4 * (Real.sqrt (u * v) * Real.sqrt (u * v)) / (R₀ : ℝ)
            + 6 * (Real.sqrt (u * v) * Real.sqrt u) * L
            + 6 * (Real.sqrt (u * v) * Real.sqrt v) * L
            + 8 * (D : ℝ) * Real.sqrt (u * v)) * (2 * L) := by ring
    rw [hstep, hsq, hsq_u, hsq_v]; ring
  -- assemble
  have hBR0 : 0 ≤ 2 * Real.sqrt (u * v) / (2:ℝ) ^ (Nat.log 2 R₀)
        + 2 * Real.sqrt u * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 2 * Real.sqrt v * ((Nat.log 2 D + 1 : ℕ) : ℝ)
        + 4 * (2:ℝ) ^ (Nat.log 2 D + 1) := by positivity
  calc Real.sqrt (u * B)
        * (2 * Real.sqrt (u * v) / (2:ℝ) ^ (Nat.log 2 R₀)
          + 2 * Real.sqrt u * ((Nat.log 2 D + 1 : ℕ) : ℝ)
          + 2 * Real.sqrt v * ((Nat.log 2 D + 1 : ℕ) : ℝ)
          + 4 * (2:ℝ) ^ (Nat.log 2 D + 1)) * Real.log (2 * u * v + 2)
      ≤ Real.sqrt (u * B)
        * (2 * Real.sqrt (u * v) / (2:ℝ) ^ (Nat.log 2 R₀)
          + 2 * Real.sqrt u * ((Nat.log 2 D + 1 : ℕ) : ℝ)
          + 2 * Real.sqrt v * ((Nat.log 2 D + 1 : ℕ) : ℝ)
          + 4 * (2:ℝ) ^ (Nat.log 2 D + 1)) * (2 * L) := by
        refine mul_le_mul_of_nonneg_left hlog_le ?_
        positivity
    _ ≤ Real.sqrt (u * v)
        * (4 * Real.sqrt (u * v) / (R₀ : ℝ) + 6 * Real.sqrt u * L + 6 * Real.sqrt v * L
            + 8 * (D : ℝ)) * (2 * L) := by
        have h1 : Real.sqrt (u * B)
            * (2 * Real.sqrt (u * v) / (2:ℝ) ^ (Nat.log 2 R₀)
              + 2 * Real.sqrt u * ((Nat.log 2 D + 1 : ℕ) : ℝ)
              + 2 * Real.sqrt v * ((Nat.log 2 D + 1 : ℕ) : ℝ)
              + 4 * (2:ℝ) ^ (Nat.log 2 D + 1))
            ≤ Real.sqrt (u * v)
            * (4 * Real.sqrt (u * v) / (R₀ : ℝ) + 6 * Real.sqrt u * L + 6 * Real.sqrt v * L
                + 8 * (D : ℝ)) :=
          mul_le_mul hsqrt_le hbr hBR0 (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (8 * L / (R₀ : ℝ)) * (u * v) + (12 * L ^ 2) * (u * Real.sqrt v)
        + (12 * L ^ 2) * (v * Real.sqrt u) + (16 * (D : ℝ) * L) * Real.sqrt (u * v) := hident

theorem bRemUNwArithConsume (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ∀ (M Y D R₀ : ℕ), (x : ℝ) ^ ((1 : ℝ) / 14) ≤ M → M ≤ Y → (M : ℝ) ≤ (x : ℝ) + 2 →
        (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) → 2 ≤ D →
        D ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ →
        ⌊(Real.log (x : ℝ)) ^ C'⌋₊ ≤ R₀ →
        blodW1 D * blodLSBlockSum x M Y D R₀ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  have hA3 : (0:ℝ) < A + 3 := by linarith
  have hA4 : (0:ℝ) < A + 4 := by linarith
  refine ⟨A + 20, by linarith, A + 20, by linarith, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 32,
      Work.NumberTheory.Chen.BTermCount.eventually_const_le_nat_log 24576,
      Work.NumberTheory.Chen.BTermCount.eventually_nat_log_pow_mul_le_rpow (A+4) (1/3) hA4 (by norm_num) 73728,
      Work.NumberTheory.Chen.BTermCount.eventually_nat_log_pow_mul_le_rpow (A+3) (1/28) hA3 (by norm_num) 24576,
      Work.NumberTheory.Chen.BTermCount.eventually_nat_log_pow_mul_le_rpow (A+4) (5/6) hA4 (by norm_num) 18432]
    with x hx32 hxlogbig hE3 hE4 hE5
  intro M Y D R₀ hMlo hMY hMx hY hD2 hDle hR0le
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hM1 : 1 ≤ M := by
    have h1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/14) := Real.one_le_rpow hx1 (by norm_num)
    exact_mod_cast (le_trans h1 hMlo)
  set L := Real.log (x:ℝ) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hLbig : (24576:ℝ) ≤ L := by rw [hL]; exact hxlogbig
  have hL1 : (1:ℝ) ≤ L := by linarith only [hLbig]
  have hL17 : (24576:ℝ) ≤ L^17 := by
    have hle : L ≤ L^17 := by
      calc L = L^1 := (pow_one L).symm
        _ ≤ L^17 := pow_le_pow_right₀ hL1 (by norm_num)
    linarith only [hLbig, hle]
  -- the rpow bookkeeping
  have hL3div : L^(A+3)/L^A = L^3 := by
    rw [← Real.rpow_sub hLpos, show A+3-A = ((3:ℕ):ℝ) by ring, Real.rpow_natCast]
  have hL4div : L^(A+4)/L^A = L^4 := by
    rw [← Real.rpow_sub hLpos, show A+4-A = ((4:ℕ):ℝ) by ring, Real.rpow_natCast]
  have hL3fac : L^(A+3) = L^A * L^3 := by
    rw [show A+3 = A + ((3:ℕ):ℝ) by ring, Real.rpow_add hLpos, Real.rpow_natCast]
  have hL4fac : L^(A+4) = L^A * L^4 := by
    rw [show A+4 = A + ((4:ℕ):ℝ) by ring, Real.rpow_add hLpos, Real.rpow_natCast]
  have hL20fac : L^(A+20) = L^(A+3) * L^17 := by
    rw [show A+20 = (A+3) + ((17:ℕ):ℝ) by ring, Real.rpow_add hLpos, Real.rpow_natCast]
  have hL20fac2 : L^(A+20) = L^A * L^20 := by
    rw [show A+20 = A + ((20:ℕ):ℝ) by ring, Real.rpow_add hLpos, Real.rpow_natCast]
  have hx23 : (x:ℝ)^((2:ℝ)/3) = (x:ℝ)/x^((1:ℝ)/3) := by
    have h := Real.rpow_sub hx0 (1:ℝ) ((1:ℝ)/3)
    rw [show (1:ℝ) - 1/3 = 2/3 by norm_num, Real.rpow_one] at h
    exact h
  have hx16 : (x:ℝ)^((1:ℝ)/6) = (x:ℝ)/x^((5:ℝ)/6) := by
    have h := Real.rpow_sub hx0 (1:ℝ) ((5:ℝ)/6)
    rw [show (1:ℝ) - 5/6 = 1/6 by norm_num, Real.rpow_one] at h
    exact h
  -- floor consequences
  have hDleR : (D:ℝ) ≤ Real.sqrt (x:ℝ)/L^(A+20) := by
    have h1 : (D:ℝ) ≤ ((⌊Real.sqrt (x:ℝ)/L^(A+20)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hDle
    have h2 : ((⌊Real.sqrt (x:ℝ)/L^(A+20)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (x:ℝ)/L^(A+20) :=
      Nat.floor_le (by positivity)
    linarith only [h1, h2]
  have hDxR : (D:ℝ) ≤ (x:ℝ) := by
    have hsqrtx1 : (1:ℝ) ≤ Real.sqrt (x:ℝ) := Real.one_le_sqrt.mpr hx1
    have hsqrtxx : Real.sqrt (x:ℝ) ≤ (x:ℝ) := by
      calc Real.sqrt (x:ℝ) = Real.sqrt (x:ℝ) * 1 := by ring
        _ ≤ Real.sqrt (x:ℝ) * Real.sqrt (x:ℝ) :=
            mul_le_mul_of_nonneg_left hsqrtx1 (Real.sqrt_nonneg _)
        _ = (x:ℝ) := Real.mul_self_sqrt hx0.le
    have hLge1 : (1:ℝ) ≤ L^(A+20) := Real.one_le_rpow hL1 (by linarith)
    have hdiv : Real.sqrt (x:ℝ)/L^(A+20) ≤ (x:ℝ) :=
      le_trans (div_le_self (Real.sqrt_nonneg _) hLge1) hsqrtxx
    linarith only [hDleR, hdiv]
  have hDx : D ≤ x := by exact_mod_cast hDxR
  have hLC'2 : (2:ℝ) ≤ L^(A+20) := by
    calc (2:ℝ) ≤ L := by linarith only [hLbig]
      _ = L^1 := (Real.rpow_one L).symm
      _ ≤ L^(A+20) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hA])
  have hR0ge : L^(A+20)/2 ≤ (R₀:ℝ) := by
    have h1 : ((⌊L^(A+20)⌋₊ : ℕ) : ℝ) ≤ (R₀:ℝ) := by exact_mod_cast hR0le
    have h2 : L^(A+20) - 1 < ((⌊L^(A+20)⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (L^(A+20)); linarith only [this]
    linarith only [h1, h2, hLC'2]
  have hInvR0 : 1/(R₀:ℝ) ≤ 2/L^(A+20) := by
    have hpos : (0:ℝ) < L^(A+20)/2 := by positivity
    have hR0pos : (0:ℝ) < (R₀:ℝ) := lt_of_lt_of_le hpos hR0ge
    rw [div_le_div_iff₀ hR0pos (Real.rpow_pos_of_pos hLpos _)]
    linarith only [hR0ge]
  have hR01 : 1 ≤ R₀ := by
    have h2 : (1:ℝ) ≤ L^(A+20)/2 := by linarith only [hLC'2]
    have : (1:ℝ) ≤ (R₀:ℝ) := le_trans h2 hR0ge
    exact_mod_cast this
  have hW1 : blodW1 D ≤ 16*L := by
    rw [hL]; exact blodW1Le D x hD2 hDx
  -- the block sum decomposition
  have hLSnn : 0 ≤ blodLSBlockSum x M Y D R₀ := by
    rw [blodLSBlockSum]
    refine Finset.sum_nonneg (fun j hj => ?_)
    have harg : (1:ℝ) ≤ 2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2 := by
      have h1 : (0:ℝ) ≤ (blodU M j : ℝ) := by positivity
      have h2 : (0:ℝ) ≤ (blodV x M j : ℝ) := by positivity
      nlinarith only [h1, h2]
    have hlog : 0 ≤ Real.log (2 * (blodU M j : ℝ) * (blodV x M j : ℝ) + 2) :=
      Real.log_nonneg (by linarith only [harg])
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) hlog
  have hsum : blodLSBlockSum x M Y D R₀ ≤
      (8*L/(R₀:ℝ)) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*(blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*Real.sqrt (blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodV x M j:ℝ)*Real.sqrt (blodU M j:ℝ))
      + (16*(D:ℝ)*L) * (∑ j ∈ Finset.range (blockCount M Y), Real.sqrt ((blodU M j:ℝ)*(blodV x M j:ℝ))) := by
    have h0 : blodLSBlockSum x M Y D R₀ ≤
        ∑ j ∈ Finset.range (blockCount M Y),
          ((8*L/(R₀:ℝ)) * ((blodU M j:ℝ)*(blodV x M j:ℝ))
           + (12*L^2) * ((blodU M j:ℝ)*Real.sqrt (blodV x M j:ℝ))
           + (12*L^2) * ((blodV x M j:ℝ)*Real.sqrt (blodU M j:ℝ))
           + (16*(D:ℝ)*L) * Real.sqrt ((blodU M j:ℝ)*(blodV x M j:ℝ))) := by
      rw [blodLSBlockSum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact blodTermLe x M Y D R₀ j hx32 hM1 hMY hY hD2 hDx hR01 (Finset.mem_range.mp hj)
    refine le_trans h0 ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the four sum bounds
  have hS1 := blodSumUVLe x M Y hx32 hM1 hMY hY
  have hS2 := blodSumUSqrtVLe x M Y hx32 hM1 hMY hY
  have hS3 := blodSumVSqrtULe x M Y hx32 hM1 hMY hY hMlo
  have hS4 := blodSumSqrtUVLe x M Y hx32 hM1 hMY hY
  have hBIG : (8*L/(R₀:ℝ)) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*(blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*Real.sqrt (blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodV x M j:ℝ)*Real.sqrt (blodU M j:ℝ))
      + (16*(D:ℝ)*L) * (∑ j ∈ Finset.range (blockCount M Y), Real.sqrt ((blodU M j:ℝ)*(blodV x M j:ℝ)))
      ≤ (8*L/(R₀:ℝ))*(12*(x:ℝ)*L) + (12*L^2)*(48*(x:ℝ)^((2:ℝ)/3)*L)
        + (12*L^2)*(8*((x:ℝ)+2)/(x:ℝ)^((1:ℝ)/28) + 12*(x:ℝ)^((1:ℝ)/6)*L)
        + (16*(D:ℝ)*L)*(6*Real.sqrt (x:ℝ)*L) := by
    have hc1 : (0:ℝ) ≤ 8*L/(R₀:ℝ) := by positivity
    have hc2 : (0:ℝ) ≤ 12*L^2 := by positivity
    have hc3 : (0:ℝ) ≤ 12*L^2 := by positivity
    have hc4 : (0:ℝ) ≤ 16*(D:ℝ)*L := by positivity
    have h1 := mul_le_mul_of_nonneg_left hS1 hc1
    have h2 := mul_le_mul_of_nonneg_left hS2 hc2
    have h3 := mul_le_mul_of_nonneg_left hS3 hc3
    have h4 := mul_le_mul_of_nonneg_left hS4 hc4
    exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  -- the five pieces
  have hpiece1 : 1536*(x:ℝ)*L^3/(R₀:ℝ) ≤ ((x:ℝ)/L^A)/8 := by
    have h1 : 1536*(x:ℝ)*L^3/(R₀:ℝ) ≤ 1536*(x:ℝ)*L^3*(2/L^(A+20)) := by
      rw [show 1536*(x:ℝ)*L^3/(R₀:ℝ) = 1536*(x:ℝ)*L^3*(1/(R₀:ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left hInvR0 (by positivity)
    have h2 : 1536*(x:ℝ)*L^3*(2/L^(A+20)) = ((x:ℝ)/L^A)*(3072/L^17) := by
      rw [← hL3div, hL20fac]
      first | (field_simp; ring) | field_simp
    have h3 : ((x:ℝ)/L^A)*(3072/L^17) ≤ ((x:ℝ)/L^A)*(1/8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (x:ℝ)/L^A)
      rw [div_le_iff₀ (pow_pos hLpos 17)]
      have h := div_le_div_of_nonneg_right hL17 (by norm_num : (0:ℝ) ≤ 8)
      rw [show (24576:ℝ)/8 = 3072 by norm_num,
          show (L:ℝ)^17/8 = 1/8*L^17 by ring] at h
      exact h
    calc 1536*(x:ℝ)*L^3/(R₀:ℝ) ≤ 1536*(x:ℝ)*L^3*(2/L^(A+20)) := h1
      _ = ((x:ℝ)/L^A)*(3072/L^17) := h2
      _ ≤ ((x:ℝ)/L^A)*(1/8) := h3
      _ = ((x:ℝ)/L^A)/8 := by ring
  have hpiece2 : 9216*(x:ℝ)^((2:ℝ)/3)*L^4 ≤ ((x:ℝ)/L^A)/8 := by
    have h1 : ((x:ℝ)/L^A)*(9216*L^(A+4)/x^((1:ℝ)/3)) = 9216*(x:ℝ)^((2:ℝ)/3)*L^4 := by
      rw [hx23, hL4fac]
      first | (field_simp; ring) | field_simp
    rw [← h1]
    have h2 : ((x:ℝ)/L^A)*(9216*L^(A+4)/x^((1:ℝ)/3)) ≤ ((x:ℝ)/L^A)*(1/8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (x:ℝ)/L^A)
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
      have h := div_le_div_of_nonneg_right hE3 (by norm_num : (0:ℝ) ≤ 8)
      rw [show (73728:ℝ)*L^(A+4)/8 = 9216*L^(A+4) by ring,
          show (x:ℝ)^((1:ℝ)/3)/8 = 1/8*(x:ℝ)^((1:ℝ)/3) by ring] at h
      exact h
    calc ((x:ℝ)/L^A)*(9216*L^(A+4)/x^((1:ℝ)/3)) ≤ ((x:ℝ)/L^A)*(1/8) := h2
      _ = ((x:ℝ)/L^A)/8 := by ring
  have hpiece3 : 1536*((x:ℝ)+2)*L^3/(x:ℝ)^((1:ℝ)/28) ≤ ((x:ℝ)/L^A)/8 := by
    have h1 : 1536*((x:ℝ)+2)*L^3/(x:ℝ)^((1:ℝ)/28)
        ≤ 3072*(x:ℝ)*L^3/(x:ℝ)^((1:ℝ)/28) := by
      have hx2 : (x:ℝ)+2 ≤ 2*(x:ℝ) := by
        have h32 : (32:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx32
        linarith only [h32]
      have hden : (0:ℝ) < (x:ℝ)^((1:ℝ)/28) := Real.rpow_pos_of_pos hx0 _
      have hnum : 1536*((x:ℝ)+2)*L^3 ≤ 1536*(2*(x:ℝ))*L^3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 (by norm_num)) (by positivity)
      calc 1536*((x:ℝ)+2)*L^3/(x:ℝ)^((1:ℝ)/28)
          = 1536*((x:ℝ)+2)*L^3/(x:ℝ)^((1:ℝ)/28) := rfl
        _ ≤ 1536*(2*(x:ℝ))*L^3/(x:ℝ)^((1:ℝ)/28) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hden)
        _ = 3072*(x:ℝ)*L^3/(x:ℝ)^((1:ℝ)/28) := by ring
    have h2 : 3072*(x:ℝ)*L^3/(x:ℝ)^((1:ℝ)/28)
        = ((x:ℝ)/L^A)*(3072*L^(A+3)/x^((1:ℝ)/28)) := by
      rw [hL3fac]
      first | (field_simp; ring) | field_simp
    have h3 : ((x:ℝ)/L^A)*(3072*L^(A+3)/x^((1:ℝ)/28)) ≤ ((x:ℝ)/L^A)*(1/8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (x:ℝ)/L^A)
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
      have h := div_le_div_of_nonneg_right hE4 (by norm_num : (0:ℝ) ≤ 8)
      rw [show (24576:ℝ)*L^(A+3)/8 = 3072*L^(A+3) by ring,
          show (x:ℝ)^((1:ℝ)/28)/8 = 1/8*(x:ℝ)^((1:ℝ)/28) by ring] at h
      exact h
    calc 1536*((x:ℝ)+2)*L^3/(x:ℝ)^((1:ℝ)/28)
        ≤ 3072*(x:ℝ)*L^3/(x:ℝ)^((1:ℝ)/28) := h1
      _ = ((x:ℝ)/L^A)*(3072*L^(A+3)/x^((1:ℝ)/28)) := h2
      _ ≤ ((x:ℝ)/L^A)*(1/8) := h3
      _ = ((x:ℝ)/L^A)/8 := by ring
  have hpiece4 : 2304*(x:ℝ)^((1:ℝ)/6)*L^4 ≤ ((x:ℝ)/L^A)/8 := by
    have h1 : ((x:ℝ)/L^A)*(2304*L^(A+4)/x^((5:ℝ)/6)) = 2304*(x:ℝ)^((1:ℝ)/6)*L^4 := by
      rw [hx16, hL4fac]
      first | (field_simp; ring) | field_simp
    rw [← h1]
    have h2 : ((x:ℝ)/L^A)*(2304*L^(A+4)/x^((5:ℝ)/6)) ≤ ((x:ℝ)/L^A)*(1/8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (x:ℝ)/L^A)
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
      have h := div_le_div_of_nonneg_right hE5 (by norm_num : (0:ℝ) ≤ 8)
      rw [show (18432:ℝ)*L^(A+4)/8 = 2304*L^(A+4) by ring,
          show (x:ℝ)^((5:ℝ)/6)/8 = 1/8*(x:ℝ)^((5:ℝ)/6) by ring] at h
      exact h
    calc ((x:ℝ)/L^A)*(2304*L^(A+4)/x^((5:ℝ)/6)) ≤ ((x:ℝ)/L^A)*(1/8) := h2
      _ = ((x:ℝ)/L^A)/8 := by ring
  have hpiece5 : 1536*(D:ℝ)*Real.sqrt (x:ℝ)*L^3 ≤ ((x:ℝ)/L^A)/4 := by
    have hsqrt : (D:ℝ)*Real.sqrt (x:ℝ) ≤ (x:ℝ)/L^(A+20) := by
      calc (D:ℝ)*Real.sqrt (x:ℝ) ≤ (Real.sqrt (x:ℝ)/L^(A+20))*Real.sqrt (x:ℝ) :=
            mul_le_mul_of_nonneg_right hDleR (Real.sqrt_nonneg _)
        _ = (x:ℝ)/L^(A+20) := by
            rw [div_mul_eq_mul_div, mul_comm, Real.mul_self_sqrt hx0.le]
    have h1 : 1536*(D:ℝ)*Real.sqrt (x:ℝ)*L^3 ≤ 1536*((x:ℝ)/L^(A+20))*L^3 := by
      calc 1536*(D:ℝ)*Real.sqrt (x:ℝ)*L^3 = 1536*((D:ℝ)*Real.sqrt (x:ℝ))*L^3 := by ring
        _ ≤ 1536*((x:ℝ)/L^(A+20))*L^3 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ L^3)
            exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    have h2 : 1536*((x:ℝ)/L^(A+20))*L^3 = ((x:ℝ)/L^A)*(1536/L^17) := by
      rw [← hL3div, hL20fac]
      first | (field_simp; ring) | field_simp
    have h3 : ((x:ℝ)/L^A)*(1536/L^17) ≤ ((x:ℝ)/L^A)*(1/4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (x:ℝ)/L^A)
      rw [div_le_iff₀ (pow_pos hLpos 17)]
      have h := div_le_div_of_nonneg_right hL17 (by norm_num : (0:ℝ) ≤ 4)
      rw [show (24576:ℝ)/4 = 6144 by norm_num,
          show (L:ℝ)^17/4 = 1/4*L^17 by ring] at h
      linarith only [h]
    calc 1536*(D:ℝ)*Real.sqrt (x:ℝ)*L^3 ≤ 1536*((x:ℝ)/L^(A+20))*L^3 := h1
      _ = ((x:ℝ)/L^A)*(1536/L^17) := h2
      _ ≤ ((x:ℝ)/L^A)*(1/4) := h3
      _ = ((x:ℝ)/L^A)/4 := by ring
  -- final assembly
  have hmain1 : blodW1 D * blodLSBlockSum x M Y D R₀ ≤
      16*L * ((8*L/(R₀:ℝ)) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*(blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*Real.sqrt (blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodV x M j:ℝ)*Real.sqrt (blodU M j:ℝ))
      + (16*(D:ℝ)*L) * (∑ j ∈ Finset.range (blockCount M Y), Real.sqrt ((blodU M j:ℝ)*(blodV x M j:ℝ)))) := by
    have h1 : blodW1 D * blodLSBlockSum x M Y D R₀ ≤ 16*L*blodLSBlockSum x M Y D R₀ :=
      mul_le_mul_of_nonneg_right hW1 hLSnn
    have h2 : 16*L*blodLSBlockSum x M Y D R₀ ≤
        16*L * ((8*L/(R₀:ℝ)) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*(blodV x M j:ℝ))
        + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*Real.sqrt (blodV x M j:ℝ))
        + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodV x M j:ℝ)*Real.sqrt (blodU M j:ℝ))
        + (16*(D:ℝ)*L) * (∑ j ∈ Finset.range (blockCount M Y), Real.sqrt ((blodU M j:ℝ)*(blodV x M j:ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    exact le_trans h1 h2
  have hmain2 : 16*L * ((8*L/(R₀:ℝ)) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*(blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodU M j:ℝ)*Real.sqrt (blodV x M j:ℝ))
      + (12*L^2) * (∑ j ∈ Finset.range (blockCount M Y), (blodV x M j:ℝ)*Real.sqrt (blodU M j:ℝ))
      + (16*(D:ℝ)*L) * (∑ j ∈ Finset.range (blockCount M Y), Real.sqrt ((blodU M j:ℝ)*(blodV x M j:ℝ))))
      ≤ 16*L * ((8*L/(R₀:ℝ))*(12*(x:ℝ)*L) + (12*L^2)*(48*(x:ℝ)^((2:ℝ)/3)*L)
        + (12*L^2)*(8*((x:ℝ)+2)/(x:ℝ)^((1:ℝ)/28) + 12*(x:ℝ)^((1:ℝ)/6)*L)
        + (16*(D:ℝ)*L)*(6*Real.sqrt (x:ℝ)*L)) :=
    mul_le_mul_of_nonneg_left hBIG (by positivity)
  have hmain3 : 16*L * ((8*L/(R₀:ℝ))*(12*(x:ℝ)*L) + (12*L^2)*(48*(x:ℝ)^((2:ℝ)/3)*L)
        + (12*L^2)*(8*((x:ℝ)+2)/(x:ℝ)^((1:ℝ)/28) + 12*(x:ℝ)^((1:ℝ)/6)*L)
        + (16*(D:ℝ)*L)*(6*Real.sqrt (x:ℝ)*L)) ≤ (x:ℝ)/L^A := by
    have hexp : 16*L * ((8*L/(R₀:ℝ))*(12*(x:ℝ)*L) + (12*L^2)*(48*(x:ℝ)^((2:ℝ)/3)*L)
        + (12*L^2)*(8*((x:ℝ)+2)/(x:ℝ)^((1:ℝ)/28) + 12*(x:ℝ)^((1:ℝ)/6)*L)
        + (16*(D:ℝ)*L)*(6*Real.sqrt (x:ℝ)*L))
        = 1536*(x:ℝ)*L^3/(R₀:ℝ) + 9216*(x:ℝ)^((2:ℝ)/3)*L^4
          + 1536*((x:ℝ)+2)*L^3/(x:ℝ)^((1:ℝ)/28) + 2304*(x:ℝ)^((1:ℝ)/6)*L^4
          + 1536*(D:ℝ)*Real.sqrt (x:ℝ)*L^3 := by ring
    rw [hexp]
    have h12 := add_le_add hpiece1 hpiece2
    have h123 := add_le_add h12 hpiece3
    have h1234 := add_le_add h123 hpiece4
    have h12345 := add_le_add h1234 hpiece5
    refine le_trans h12345 ?_
    have hQ : (0:ℝ) ≤ (x:ℝ)/L^A := by positivity
    linarith only [hQ]
  exact le_trans hmain1 (le_trans hmain2 hmain3)


end Work.NumberTheory.Chen.BTermCount
