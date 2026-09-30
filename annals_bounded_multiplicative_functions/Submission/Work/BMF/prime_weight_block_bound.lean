import Mathlib
import Submission.Work.BMF.Psi1_local_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dyadic block bound `prime_weight_block_bound`

Single-block estimate feeding `Work.BMF.Psi1_L2_local_mass`: for primes `p, q` and `0 < α ≤ 1`
the summand `(log q)/q^(1+α) * pairK (log p - log q)` is bounded by `blkBound α (blkIdx p) (blkIdx q)`.

The proof splits into the *weight* bound (using `q ∈ (2^(k-1), 2^k]`, `k = blkIdx q`) and the
*kernel* bound (using `|log p - log q| ≥ log 2 · max 0 (|blkIdx p - blkIdx q| - 1)`).
-/

namespace Work.BMF

open Real

noncomputable section

lemma pwbb_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma pwbb_cast_sub_one {x : ℕ} (hx : 1 ≤ x) : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
  rw [Nat.cast_sub hx]; norm_num

/-- `log q ≤ (blkIdx q) * log 2` for a prime `q`. -/
lemma pwbb_log_le_blkIdx (x : ℕ) (hx : x.Prime) :
    Real.log (x : ℝ) ≤ (blkIdx x : ℝ) * Real.log 2 := by
  obtain ⟨_, hhi⟩ := blkIdx_spec hx.one_lt
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx.pos
  have hle : (x : ℝ) ≤ (2 : ℝ) ^ (blkIdx x) := by
    have h : ((x : ℕ) : ℝ) ≤ (((2 : ℕ) ^ blkIdx x : ℕ) : ℝ) := by exact_mod_cast hhi
    have h2 : (((2 : ℕ) ^ blkIdx x : ℕ) : ℝ) = (2 : ℝ) ^ (blkIdx x) := by push_cast; ring
    rwa [h2] at h
  have h := Real.log_le_log hxpos hle
  rwa [Real.log_pow] at h

/-- `(blkIdx x - 1) * log 2 < log x` for a prime `x`. -/
lemma pwbb_log_lt_blkIdx (x : ℕ) (hx : x.Prime) :
    ((blkIdx x : ℝ) - 1) * Real.log 2 < Real.log (x : ℝ) := by
  have hx1 : 1 ≤ blkIdx x := one_le_blkIdx_of_prime hx
  obtain ⟨hlo, _⟩ := blkIdx_spec hx.one_lt
  have hloR : (((2 : ℕ) ^ (blkIdx x - 1) : ℕ) : ℝ) < (x : ℝ) := by exact_mod_cast hlo
  have h2pos : (0 : ℝ) < (((2 : ℕ) ^ (blkIdx x - 1) : ℕ) : ℝ) := by positivity
  have h := Real.log_lt_log h2pos hloR
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  rwa [pwbb_cast_sub_one hx1] at h

/-- Reciprocal weight bound on the block of `q`. -/
lemma pwbb_inv_rpow_le (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (q : ℕ) (hq : q.Prime) :
    ((q : ℝ) ^ (1 + α))⁻¹ ≤
      4 * (2 : ℝ) ^ (-(blkIdx q : ℝ)) * (2 : ℝ) ^ (-(blkIdx q : ℝ) * α) := by
  have hq1 : 1 ≤ blkIdx q := one_le_blkIdx_of_prime hq
  obtain ⟨hlo, _⟩ := blkIdx_spec hq.one_lt
  have hloR : (2 : ℝ) ^ ((blkIdx q : ℝ) - 1) < (q : ℝ) := by
    have h1 : (((2 : ℕ) ^ (blkIdx q - 1) : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hlo
    have h2 : (((2 : ℕ) ^ (blkIdx q - 1) : ℕ) : ℝ) = (2 : ℝ) ^ ((blkIdx q : ℝ) - 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, pwbb_cast_sub_one hq1]
    rwa [h2] at h1
  have hbase : (0 : ℝ) < (2 : ℝ) ^ ((blkIdx q : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hexp : (0 : ℝ) ≤ 1 + α := by linarith
  have hden : (2 : ℝ) ^ (((blkIdx q : ℝ) - 1) * (1 + α)) ≤ (q : ℝ) ^ (1 + α) := by
    have h := Real.rpow_le_rpow hbase.le hloR.le hexp
    rwa [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)] at h
  have hdenpos : (0 : ℝ) < (2 : ℝ) ^ (((blkIdx q : ℝ) - 1) * (1 + α)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hinv : ((q : ℝ) ^ (1 + α))⁻¹ ≤ ((2 : ℝ) ^ (((blkIdx q : ℝ) - 1) * (1 + α)))⁻¹ := by
    have h := one_div_le_one_div_of_le hdenpos hden
    simpa only [one_div] using h
  rw [show ((2 : ℝ) ^ (((blkIdx q : ℝ) - 1) * (1 + α)))⁻¹
        = (2 : ℝ) ^ (-(((blkIdx q : ℝ) - 1) * (1 + α))) from
        (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm] at hinv
  refine hinv.trans ?_
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; norm_num
  rw [h4, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [hα1]

/-- Weight bound: `(log q)/q^(1+α)` is bounded by the block quantity. -/
lemma pwbb_weight_le (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (q : ℕ) (hq : q.Prime) :
    Real.log q / (q : ℝ) ^ (1 + α) ≤
      4 * (blkIdx q : ℝ) * Real.log 2 * (2 : ℝ) ^ (-(blkIdx q : ℝ)) *
        (2 : ℝ) ^ (-(blkIdx q : ℝ) * α) := by
  have hlog := pwbb_log_le_blkIdx q hq
  have hinv := pwbb_inv_rpow_le α hα0 hα1 q hq
  have hpos : (0 : ℝ) ≤ ((q : ℝ) ^ (1 + α))⁻¹ := by
    rw [inv_nonneg]; exact Real.rpow_nonneg (by positivity) _
  have hb : (0 : ℝ) ≤ (blkIdx q : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) pwbb_log_two_pos.le
  rw [div_eq_mul_inv]
  calc Real.log (q : ℝ) * ((q : ℝ) ^ (1 + α))⁻¹
      ≤ ((blkIdx q : ℝ) * Real.log 2) *
          (4 * (2 : ℝ) ^ (-(blkIdx q : ℝ)) * (2 : ℝ) ^ (-(blkIdx q : ℝ) * α)) :=
        mul_le_mul hlog hinv hpos hb
      _ = 4 * (blkIdx q : ℝ) * Real.log 2 * (2 : ℝ) ^ (-(blkIdx q : ℝ)) *
            (2 : ℝ) ^ (-(blkIdx q : ℝ) * α) := by ring

/-- Kernel bound: the Gaussian pair kernel decays at least as fast as the block-distance factor. -/
lemma pwbb_kernel_le (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    Real.log 2 * max 0 (|(blkIdx p : ℝ) - (blkIdx q : ℝ)| - 1) ≤
      |Real.log p - Real.log q| := by
  have hp1 := pwbb_log_lt_blkIdx p hp
  have hp2 := pwbb_log_le_blkIdx p hp
  have hq1 := pwbb_log_lt_blkIdx q hq
  have hq2 := pwbb_log_le_blkIdx q hq
  rcases lt_trichotomy (blkIdx p) (blkIdx q) with hlt | heq | hgt
  · have hjkle : ((blkIdx p : ℝ)) ≤ (blkIdx q : ℝ) := by exact_mod_cast le_of_lt hlt
    have hneg : 0 ≤ (blkIdx q : ℝ) - (blkIdx p : ℝ) - 1 := by
      have hsucc : ((blkIdx p : ℝ)) + 1 ≤ (blkIdx q : ℝ) := by
        exact_mod_cast hlt
      linarith
    have habs : |(blkIdx p : ℝ) - (blkIdx q : ℝ)| = (blkIdx q : ℝ) - (blkIdx p : ℝ) := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs, max_eq_right hneg,
      abs_of_nonpos (by nlinarith [hp1, hq2, pwbb_log_two_pos] :
        Real.log p - Real.log q ≤ 0)]
    nlinarith [hp2, hq1]
  · rw [heq]; simp
  · have hklej : ((blkIdx q : ℝ)) ≤ (blkIdx p : ℝ) := by exact_mod_cast le_of_lt hgt
    have hneg : 0 ≤ (blkIdx p : ℝ) - (blkIdx q : ℝ) - 1 := by
      have hsucc : ((blkIdx q : ℝ)) + 1 ≤ (blkIdx p : ℝ) := by
        exact_mod_cast hgt
      linarith
    have habs : |(blkIdx p : ℝ) - (blkIdx q : ℝ)| = (blkIdx p : ℝ) - (blkIdx q : ℝ) :=
      abs_of_nonneg (by linarith)
    rw [habs, max_eq_right hneg,
      abs_of_nonneg (by nlinarith [hq1, hp2, pwbb_log_two_pos] :
        (0 : ℝ) ≤ Real.log p - Real.log q)]
    nlinarith [hp1, hq2]

theorem pairK_kernel_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    pairK (Real.log p - Real.log q) ≤
      Real.exp (-(Real.log 2) ^ 2 *
        (max 0 (|(blkIdx p : ℝ) - (blkIdx q : ℝ)| - 1)) ^ 2) := by
  set D : ℝ := max 0 (|(blkIdx p : ℝ) - (blkIdx q : ℝ)| - 1)
  have hDnn : 0 ≤ D := le_max_left _ _
  have hker : Real.log 2 * D ≤ |Real.log p - Real.log q| := pwbb_kernel_le p q hp hq
  have hsq : (Real.log 2 * D) ^ 2 ≤ (Real.log p - Real.log q) ^ 2 := by
    have h := mul_self_le_mul_self (mul_nonneg pwbb_log_two_pos.le hDnn) hker
    simpa [sq] using h
  rw [pairK]
  apply Real.exp_le_exp.mpr
  nlinarith [hsq]

theorem prime_weight_log_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (q : ℕ) (hq : q.Prime) :
    Real.log q / (q : ℝ) ^ (1 + α) ≤
      4 * (blkIdx q : ℝ) * Real.log 2 * (2 : ℝ) ^ (-(blkIdx q : ℝ)) *
        (2 : ℝ) ^ (-(blkIdx q : ℝ) * α) :=
  pwbb_weight_le α hα0 hα1 q hq

theorem prime_weight_block_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    Real.log q / (q : ℝ) ^ (1 + α) * Work.BMF.pairK (Real.log p - Real.log q) ≤
      Work.BMF.blkBound α (Work.BMF.blkIdx p) (Work.BMF.blkIdx q) := by
  have hw := pwbb_weight_le α hα0 hα1 q hq
  have hk := pairK_kernel_bound p q hp hq
  calc Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q)
      ≤ (4 * (blkIdx q : ℝ) * Real.log 2 * (2 : ℝ) ^ (-(blkIdx q : ℝ)) *
            (2 : ℝ) ^ (-(blkIdx q : ℝ) * α)) *
          Real.exp (-(Real.log 2) ^ 2 *
            (max 0 (|(blkIdx p : ℝ) - (blkIdx q : ℝ)| - 1)) ^ 2) :=
        mul_le_mul hw hk (pairK_nonneg _) (by positivity)
    _ = blkBound α (blkIdx p) (blkIdx q) := by
        rw [blkBound]; ring

end

end Work.BMF
