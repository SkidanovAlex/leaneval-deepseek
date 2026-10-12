import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.SumInvPow` — the elementary reciprocal-power sums on `ℕ`

The lattice sums of `Work.BoseB7AK.K15R.LevelDefs` reduce to sums over the *level*
`m`, and the chapter's estimates need the three elementary bounds on
`∑_{m ∈ Icc M N}`:

* `sum_Icc_inv_sq_le`: `∑ 1/m² ≤ 2/M` for `M ≥ 1` (from Mathlib's
  `sum_Ioo_inv_sq_le`);
* `sum_Icc_inv_pow4_le`: `∑ 1/m⁴ ≤ 2/M³` for `M ≥ 1` (obtained from the `m^{-2}`
  bound by factoring out `1/M²`);
* `sum_Icc_inv_le_log`: `∑ 1/m ≤ 1 + log N - log M` for `1 ≤ M ≤ N` (the
  harmonic/logarithm bound of `Mathlib.NumberTheory.Harmonic.Bounds`, shifted to a
  range starting at `M`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

/-- `∑_{m ∈ Icc M N} 1/m² ≤ 2/M` for `M ≥ 1`: the congruence-free form of
Mathlib's `sum_Ioo_inv_sq_le` on the range `Icc M N = Ioo (M-1) (N+1)`. -/
lemma sum_Icc_inv_sq_le (M N : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) ^ 2 ≤ 2 / (M : ℝ) := by
  have h1 : Finset.Icc M N = Finset.Ioo (M - 1) (N + 1) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ioo]; omega
  rw [h1]
  have h2 : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have h := sum_Ioo_inv_sq_le (α := ℝ) (M - 1) (N + 1)
  rw [h2] at h
  refine le_trans ?_ h
  refine Finset.sum_le_sum (fun m _ => ?_)
  exact le_of_eq (by rw [one_div])

/-- `∑_{m ∈ Icc M N} 1/m⁴ ≤ 2/M³` for `M ≥ 1`.  Pointwise `1/m⁴ = (1/m²)²` and
`1/m² ≤ 1/M²` on the range, so the `m^{-2}` bound with the factor `1/M²` gives
`(1/M²)·(2/M) = 2/M³`. -/
lemma sum_Icc_inv_pow4_le (M N : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) ^ 4 ≤ 2 / (M : ℝ) ^ 3 := by
  have hsq := sum_Icc_inv_sq_le M N hM
  calc ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) ^ 4
      ≤ ∑ m ∈ Finset.Icc M N, (1 / (M : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hmM : M ≤ m := (Finset.mem_Icc.mp hm).1
        have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
        have hle : 1 / (m : ℝ) ^ 2 ≤ 1 / (M : ℝ) ^ 2 :=
          one_div_le_one_div_of_le (pow_pos hMpos 2)
            (pow_le_pow_left₀ hMpos.le (by exact_mod_cast hmM) 2)
        calc 1 / (m : ℝ) ^ 4 = (1 / (m : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by ring
          _ ≤ (1 / (M : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (1 / (M : ℝ) ^ 2) * ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (M : ℝ) ^ 2) * (2 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 / (M : ℝ) ^ 3 := by field_simp

/-- `∑_{m ∈ Icc M N} 1/m ≤ 1 + log N - log M` for `1 ≤ M ≤ N`, the harmonic bound
of `Mathlib.NumberTheory.Harmonic.Bounds` restricted to the range `Icc M N`
(`= Icc 1 N \ Icc 1 (M-1)`). -/
lemma sum_Icc_inv_le_log (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) ≤ 1 + Real.log (N : ℝ) - Real.log (M : ℝ) := by
  have hhar : ∀ n : ℕ, ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ) := by
    intro n
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Rat.cast_inv, Rat.cast_natCast, one_div]
  have hsub : Finset.Icc 1 (M - 1) ⊆ Finset.Icc 1 N := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have hsdiff : Finset.Icc 1 N \ Finset.Icc 1 (M - 1) = Finset.Icc M N := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
  have hs := Finset.sum_sdiff (f := fun i : ℕ => 1 / (i : ℝ)) hsub
  rw [hsdiff] at hs
  have hsum : ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ)
      = ((harmonic N : ℚ) : ℝ) - ((harmonic (M - 1) : ℚ) : ℝ) := by
    rw [hhar N, hhar (M - 1)]
    linarith [hs]
  have h1 : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  have h2 : Real.log (((M - 1) + 1 : ℕ) : ℝ) ≤ ((harmonic (M - 1) : ℚ) : ℝ) :=
    log_add_one_le_harmonic (M - 1)
  have hMcast : (((M - 1) + 1 : ℕ) : ℝ) = (M : ℝ) := by
    rw [Nat.sub_add_cancel hM]
  rw [hMcast] at h2
  rw [hsum]
  linarith

end Work.BoseB7AK.K15R
