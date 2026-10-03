import Mathlib

/-!
# The final arithmetic of the Appendix C weak-type bound

This is the last, purely numerical step in the proof of
`Work.Analysis.Concentration.Corollary1WeakType` (Krause--Mirek--Tao, Appendix C,
Corollary `cor:1`).

The counting argument produces, for the level set
`A = {y : t ≤ |P^{-1}(y)|}` and the derivative `P'` of degree `d' = d - 1`,

  `A.card * (t / d) ≤ C' * p ^ (k - (K₀ - A₀)/d')`,

where `K₀` is the least integer with `t / d ≤ p ^ K₀` and `A₀` is the (uniform in `p`)
bound `p ^ A₀ ≤ d · (d!)^{d+1}` coming from the analytic part.  The lemma turns this,
together with `A₀ ≤ K₀`, into the weak-type bound

  `A.card ≤ max ((d·(d!)^{d+1})^{d/(d-1)}) (C' · d·(d!)^{d+1} · d²) · t^{-d/(d-1)} · p^k`.

The point is that the two tails `t^{-1}` (from dividing by `t/d`) and
`p^{-(K₀-A₀)/d'}` (from the counting) combine, using `t/d ≤ p ^ K₀` and `p ^ A₀ ≤ D`,
into the single decay `t^{-d/(d-1)}`.
-/

namespace Work.KMTPlan.A6.ConcAux2

theorem weakType_bound_of_count {p t A C' : ℝ} {k K₀ A₀ d d' : ℕ} (hp : 2 ≤ p) (ht : 0 < t) (hd : 2 ≤ d) (hd' : (d' : ℝ) = (d : ℝ) - 1) (hC' : 0 < C') (hA : 0 ≤ A) (hAK : A₀ ≤ K₀) (hT : (p : ℝ) ^ A₀ ≤ (d : ℝ) * (d.factorial : ℝ) ^ (d + 1)) (hK : t / (d : ℝ) ≤ (p : ℝ) ^ K₀) (hcount : A * (t / (d : ℝ)) ≤ C' * (p : ℝ) ^ ((k : ℝ) - ((K₀ - A₀ : ℕ) : ℝ) / (d' : ℝ))) : A ≤ (max (((d : ℝ) * (d.factorial : ℝ) ^ (d + 1)) ^ ((d : ℝ) / ((d : ℝ) - 1))) (C' * ((d : ℝ) * (d.factorial : ℝ) ^ (d + 1)) * (d : ℝ) ^ 2)) * t ^ (-((d : ℝ) / ((d : ℝ) - 1))) * (p : ℝ) ^ k := by
  set D : ℝ := (d : ℝ) * (d.factorial : ℝ) ^ (d + 1) with hD
  set sj : ℝ := (d : ℝ) / ((d : ℝ) - 1) with hsj
  set m : ℝ := ((K₀ - A₀ : ℕ) : ℝ) with hm
  have hp_pos : 0 < p := by linarith
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hd_pos : 0 < (d:ℝ) := by linarith
  have hd'_pos : 0 < (d':ℝ) := by rw [hd']; linarith
  have hd'_one : 1 ≤ (d':ℝ) := by rw [hd']; linarith
  have hfact_pos : 0 < (d.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hD_pos : 0 < D := by rw [hD]; exact mul_pos hd_pos (pow_pos hfact_pos _)
  have hD_ge1 : 1 ≤ D := by
    rw [hD]
    have h1 : (1:ℝ) ≤ (d:ℝ) := by linarith
    have h2 : (1:ℝ) ≤ (d.factorial:ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos d))
    have h3 : (1:ℝ) ≤ (d.factorial:ℝ)^(d+1) := one_le_pow₀ h2
    have hmul := mul_le_mul h1 h3 (by norm_num) hd_pos.le
    simpa using hmul
  have hm_cast : m = (K₀:ℝ) - (A₀:ℝ) := by
    rw [hm, Nat.cast_sub hAK]
  have hK' : t / (d:ℝ) ≤ p ^ (K₀:ℝ) := by rw [Real.rpow_natCast]; exact hK
  have hT' : p ^ (A₀:ℝ) ≤ D := by rw [Real.rpow_natCast]; exact hT
  -- `t / (d * D) ≤ p ^ m`, the two input bounds combined
  have hpmm : t / ((d:ℝ) * D) ≤ p ^ m := by
    have h1 : t / ((d:ℝ) * D) = (t/(d:ℝ))/D := by ring
    rw [h1]
    calc (t/(d:ℝ))/D ≤ (t/(d:ℝ))/ p^(A₀:ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hp_pos _) hT'
      _ ≤ p^(K₀:ℝ)/p^(A₀:ℝ) := div_le_div_of_nonneg_right hK' (Real.rpow_nonneg hp_pos.le _)
      _ = p ^ ((K₀:ℝ) - (A₀:ℝ)) := (Real.rpow_sub hp_pos _ _).symm
      _ = p ^ m := by rw [hm_cast]
  -- inverting gives `p ^ (-m) ≤ d * D / t`
  have hpm_neg : p ^ (-m) ≤ (d:ℝ) * D / t := by
    rw [Real.rpow_neg hp_pos.le]
    have hpos : 0 < t / ((d:ℝ) * D) := div_pos ht (mul_pos hd_pos hD_pos)
    have hpmpos : 0 < p ^ m := Real.rpow_pos_of_pos hp_pos m
    calc (p^m)⁻¹ ≤ (t / ((d:ℝ)*D))⁻¹ := (inv_le_inv₀ hpmpos hpos).mpr hpmm
      _ = (d:ℝ) * D / t := inv_div _ _
  -- raising to the power `1/d'`
  have hp_le_bound : p ^ (-(m/(d':ℝ))) ≤ ((d:ℝ)*D/t) ^ (1/(d':ℝ)) := by
    have heq : p ^ (-(m/(d':ℝ))) = (p ^ (-m)) ^ (1/(d':ℝ)) := by
      rw [← Real.rpow_mul hp_pos.le]
      congr 1
      ring
    rw [heq]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hp_pos.le _) hpm_neg (by positivity)
  have hrpow_sub : p ^ ((k:ℝ) - m/(d':ℝ)) = (p:ℝ)^k * p ^ (-(m/(d':ℝ))) := by
    rw [Real.rpow_sub hp_pos, Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hp_pos.le]
  have hdt : ((d:ℝ)/t) * (t/(d:ℝ)) = 1 := by field_simp
  -- divide the counting inequality by `t/d`
  have hA_le : A ≤ (d:ℝ)/t * (C' * p ^ ((k:ℝ) - m/(d':ℝ))) := by
    have hAeq : (d:ℝ)/t * (A * (t/(d:ℝ))) = A := by
      rw [← mul_assoc, mul_comm ((d:ℝ)/t) A, mul_assoc, hdt, mul_one]
    calc A = (d:ℝ)/t * (A * (t/(d:ℝ))) := hAeq.symm
      _ ≤ (d:ℝ)/t * (C' * p ^ ((k:ℝ) - m/(d':ℝ))) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
  have hA_le2 : A ≤ (d:ℝ)/t * (C' * ((p:ℝ)^k * ((d:ℝ)*D/t)^(1/(d':ℝ)))) := by
    calc A ≤ (d:ℝ)/t * (C' * p ^ ((k:ℝ) - m/(d':ℝ))) := hA_le
      _ = (d:ℝ)/t * (C' * ((p:ℝ)^k * p ^ (-(m/(d':ℝ))))) := by rw [hrpow_sub]
      _ ≤ (d:ℝ)/t * (C' * ((p:ℝ)^k * ((d:ℝ)*D/t)^(1/(d':ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hC'.le
          exact mul_le_mul_of_nonneg_left hp_le_bound (pow_nonneg hp_pos.le k)
  have h1sj : 1 + 1/(d':ℝ) = sj := by
    rw [hsj, hd']
    have hne : (d:ℝ) - 1 ≠ 0 := by linarith [hdR]
    field_simp
    ring
  have hd_d : (d:ℝ) * (d:ℝ)^(1/(d':ℝ)) = (d:ℝ)^sj := by
    have hh : (d:ℝ)^sj = (d:ℝ) ^ (1 + 1/(d':ℝ)) := by rw [h1sj]
    rw [hh, Real.rpow_add hd_pos, Real.rpow_one]
  have ht_rp : t ^ ((-1:ℝ)) * t ^ (-(1/(d':ℝ))) = t ^ (-sj) := by
    have h : (-1:ℝ) + -(1/(d':ℝ)) = -sj := by
      rw [← h1sj]; ring
    rw [← Real.rpow_add ht, h]
  -- the two `t`-powers and the `d`-powers combine
  have harith : (d:ℝ)/t * ((d:ℝ)*D/t)^(1/(d':ℝ)) = (d:ℝ)^sj * D^(1/(d':ℝ)) * t^(-sj) := by
    have hsplit : ((d:ℝ)*D/t)^(1/(d':ℝ)) = ((d:ℝ)*D)^(1/(d':ℝ)) * t ^ (-(1/(d':ℝ))) := by
      rw [Real.div_rpow (by positivity) ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le]
    have hmul2 : ((d:ℝ)*D)^(1/(d':ℝ)) = (d:ℝ)^(1/(d':ℝ)) * D^(1/(d':ℝ)) :=
      Real.mul_rpow (by positivity) hD_pos.le
    rw [hsplit, hmul2]
    rw [show (d:ℝ)/t * ((d:ℝ)^(1/(d':ℝ)) * D^(1/(d':ℝ)) * t^(-(1/(d':ℝ))))
          = ((d:ℝ) * (d:ℝ)^(1/(d':ℝ))) * D^(1/(d':ℝ)) * (t ^ ((-1:ℝ)) * t^(-(1/(d':ℝ)))) from by
          rw [div_eq_mul_inv, Real.rpow_neg_one]; ring]
    rw [hd_d, ht_rp]
  have hstep : A ≤ C' * (d:ℝ)^sj * D^(1/(d':ℝ)) * t^(-sj) * (p:ℝ)^k := by
    calc A ≤ (d:ℝ)/t * (C' * ((p:ℝ)^k * ((d:ℝ)*D/t)^(1/(d':ℝ)))) := hA_le2
      _ = C' * ((d:ℝ)/t * ((d:ℝ)*D/t)^(1/(d':ℝ))) * (p:ℝ)^k := by ring
      _ = C' * ((d:ℝ)^sj * D^(1/(d':ℝ)) * t^(-sj)) * (p:ℝ)^k := by rw [harith]
      _ = C' * (d:ℝ)^sj * D^(1/(d':ℝ)) * t^(-sj) * (p:ℝ)^k := by ring
  have hdsj : (d:ℝ)^sj ≤ (d:ℝ)^2 := by
    have hle : sj ≤ (2:ℝ) := by
      rw [hsj, div_le_iff₀ (by linarith : (0:ℝ) < (d:ℝ) - 1)]
      linarith [hdR]
    have h := Real.rpow_le_rpow_of_exponent_le (x := (d:ℝ)) (by linarith : (1:ℝ) ≤ (d:ℝ)) hle
    rwa [Real.rpow_two] at h
  have hDsj : D^(1/(d':ℝ)) ≤ D := by
    have hle : 1/(d':ℝ) ≤ 1 := by rw [div_le_one hd'_pos]; exact hd'_one
    calc D^(1/(d':ℝ)) ≤ D^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hD_ge1 hle
      _ = D := Real.rpow_one D
  have hprod : (d:ℝ)^sj * D^(1/(d':ℝ)) ≤ (d:ℝ)^2 * D :=
    mul_le_mul hdsj hDsj (Real.rpow_nonneg hD_pos.le _) (pow_nonneg hd_pos.le _)
  have hconst : C' * (d:ℝ)^sj * D^(1/(d':ℝ)) ≤ max (D^sj) (C' * D * (d:ℝ)^2) := by
    calc C' * (d:ℝ)^sj * D^(1/(d':ℝ)) = C' * ((d:ℝ)^sj * D^(1/(d':ℝ))) := by ring
      _ ≤ C' * ((d:ℝ)^2 * D) := mul_le_mul_of_nonneg_left hprod hC'.le
      _ = C' * D * (d:ℝ)^2 := by ring
      _ ≤ max (D^sj) (C' * D * (d:ℝ)^2) := le_max_right _ _
  exact le_trans hstep (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg ht.le _)) (pow_nonneg hp_pos.le k))

end Work.KMTPlan.A6.ConcAux2
