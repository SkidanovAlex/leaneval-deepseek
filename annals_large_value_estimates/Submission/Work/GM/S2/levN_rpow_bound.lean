import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

namespace Work.GM.S2

/-!
# The size of `levN` (GM §6 bookkeeping)

`levN N η Nhb kk = max (⌈Ylev N η kk⌉+1) (⌈√(M N)⌉+1) (Nhb+1) 2` is the `N`-parameter
of the Heath–Brown input at the dyadic level `kk`.  Since

* `Ylev N η kk ≤ 5 N^{3/5}` (the level hypothesis `6η ≤ 1/10` keeps the exponent below `3/5`),
* `√(M N) = N^{3/5}` because `M N = N^{6/5}`,

we get `levN ≤ (Nhb + 22) N^{3/5}`, hence the `δ/8`-th power bound used to absorb the
loss of the Heath–Brown input.
-/

/-- `√(M N) = N^{3/5}`. -/
lemma sqrt_M_eq_rpow (N : ℕ) :
    Real.sqrt (Submission.LargeValues.M N) = (N : ℝ) ^ (3 / 5 : ℝ) := by
  rw [Submission.LargeValues.M, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
  norm_num

/-- The truncation length at level `kk` is at most `5 N^{3/5}`. -/
lemma Ylev_le_five_rpow (N : ℕ) (η : ℝ) (hη2 : 6 * η ≤ 1 / 10) (hN : 1 ≤ N)
    (kk K : ℕ) (hkk : kk < K) (hK : (2 : ℝ) ^ K ≤ 4 * Submission.LargeValues.M N) :
    Ylev N η kk ≤ 5 * (N : ℝ) ^ (3 / 5 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hMN1 : 1 ≤ Submission.LargeValues.M N := by
    rw [Submission.LargeValues.M]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hMNpos : 0 < Submission.LargeValues.M N := lt_of_lt_of_le zero_lt_one hMN1
  have hpowK : (2 : ℝ) ^ (kk + 1) ≤ 4 * Submission.LargeValues.M N := by
    have h1 : (2 : ℝ) ^ (kk + 1) ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hb : 1 + (2 : ℝ) ^ (kk + 1) ≤ 5 * Submission.LargeValues.M N := by linarith
  have h1 : (1 + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η
      ≤ 5 * (Submission.LargeValues.M N) ^ (1 + η) := by
    rw [Real.rpow_add hMNpos, Real.rpow_one]
    have := mul_le_mul_of_nonneg_right hb (le_of_lt (Real.rpow_pos_of_pos hMNpos η))
    nlinarith [this]
  have h2 : (Submission.LargeValues.M N) ^ (1 + η) = (N : ℝ) ^ ((6 / 5) * (1 + η)) := by
    rw [Submission.LargeValues.M, ← Real.rpow_mul (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
  have h3 : ((6 / 5) * (1 + η) : ℝ) ≤ 8 / 5 := by linarith
  have h4 : (N : ℝ) ^ ((6 / 5) * (1 + η)) ≤ (N : ℝ) ^ (8 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 h3
  have h5 : (N : ℝ) ^ (8 / 5 : ℝ) = (N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) := by
    rw [show (8 / 5 : ℝ) = (3 / 5) + 1 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
  have hZ : ((1 + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η) / (N : ℝ)
      ≤ 5 * (N : ℝ) ^ (3 / 5 : ℝ) := by
    rw [div_le_iff₀ hNpos]
    calc (1 + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η
        ≤ 5 * (Submission.LargeValues.M N) ^ (1 + η) := h1
      _ = 5 * (N : ℝ) ^ ((6 / 5) * (1 + η)) := by rw [h2]
      _ ≤ 5 * (N : ℝ) ^ (8 / 5 : ℝ) := by linarith
      _ = 5 * (N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) := by rw [h5]; ring
  unfold Ylev
  refine max_le ?_ hZ
  linarith [Real.one_le_rpow hN1 (show (0 : ℝ) ≤ 3 / 5 by norm_num)]

theorem levN_rpow_bound (N : ℕ) (η δ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hη2 : 6 * η ≤ 1 / 10)
    (hδ : 0 < δ) (hN : 1 ≤ N) (Nhb kk K : ℕ) (hkk : kk < K)
    (hK : (2 : ℝ) ^ K ≤ 4 * Submission.LargeValues.M N) :
    ((Work.GM.S2.levN N η Nhb kk : ℕ) : ℝ) ^ (δ / 8)
      ≤ ((Nhb : ℝ) + 22) ^ (δ / 8) * (N : ℝ) ^ (3 * δ / 40) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hNhb : (0 : ℝ) ≤ (Nhb : ℝ) := Nat.cast_nonneg Nhb
  have hN15 : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hN15nn : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 5 : ℝ) := le_trans zero_le_one hN15
  set R : ℝ := ((Nhb : ℝ) + 22) * (N : ℝ) ^ (3 / 5 : ℝ) with hR
  have hYlev : Ylev N η kk ≤ 5 * (N : ℝ) ^ (3 / 5 : ℝ) :=
    Ylev_le_five_rpow N η hη2 hN kk K hkk hK
  have hYlevnn : (0 : ℝ) ≤ Ylev N η kk := by
    rw [Ylev]; exact le_trans zero_le_one (le_max_left _ _)
  -- `22 N^{3/5} ≤ R`
  have hbig : 22 * (N : ℝ) ^ (3 / 5 : ℝ) ≤ R := by
    rw [hR]
    exact mul_le_mul_of_nonneg_right (by linarith) hN15nn
  have hA : ((Nat.ceil (Ylev N η kk) : ℕ) : ℝ) + 1 ≤ R := by
    have hcl : ((Nat.ceil (Ylev N η kk) : ℕ) : ℝ) < Ylev N η kk + 1 :=
      Nat.ceil_lt_add_one hYlevnn
    nlinarith [hcl, hYlev, hN15, hbig]
  have hB : ((Nat.ceil (Real.sqrt (Submission.LargeValues.M N)) : ℕ) : ℝ) + 1 ≤ R := by
    rw [sqrt_M_eq_rpow N]
    have hcl : ((Nat.ceil ((N : ℝ) ^ (3 / 5 : ℝ)) : ℕ) : ℝ)
        < (N : ℝ) ^ (3 / 5 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one hN15)
    nlinarith [hcl, hN15, hbig]
  have hC : (Nhb : ℝ) + 1 ≤ R := by
    rw [hR]
    have h2 : ((Nhb : ℝ) + 22) * 1 ≤ ((Nhb : ℝ) + 22) * (N : ℝ) ^ (3 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hN15 (by linarith)
    linarith
  have hD : (2 : ℝ) ≤ R := by
    rw [hR]
    have h2 : ((Nhb : ℝ) + 22) * 1 ≤ ((Nhb : ℝ) + 22) * (N : ℝ) ^ (3 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hN15 (by linarith)
    linarith
  have hlev : ((levN N η Nhb kk : ℕ) : ℝ) ≤ R := by
    unfold levN
    push_cast
    exact max_le (max_le hA hB) (max_le hC hD)
  have hbase : (0 : ℝ) ≤ ((levN N η Nhb kk : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp : (0 : ℝ) ≤ δ / 8 := by linarith
  have hmono : ((levN N η Nhb kk : ℕ) : ℝ) ^ (δ / 8) ≤ R ^ (δ / 8) :=
    Real.rpow_le_rpow hbase hlev hexp
  have hrpow : ((N : ℝ) ^ (3 / 5 : ℝ)) ^ (δ / 8) = (N : ℝ) ^ (3 * δ / 40) := by
    rw [← Real.rpow_mul hNnn (3 / 5) (δ / 8)]
    congr 1
    ring
  calc ((levN N η Nhb kk : ℕ) : ℝ) ^ (δ / 8) ≤ R ^ (δ / 8) := hmono
    _ = ((Nhb : ℝ) + 22) ^ (δ / 8) * (N : ℝ) ^ (3 * δ / 40) := by
        rw [hR, Real.mul_rpow (by linarith) hN15nn, hrpow]

end Work.GM.S2
