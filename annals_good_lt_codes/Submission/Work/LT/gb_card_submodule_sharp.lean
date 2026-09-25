import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_card_subspaces
import Submission.Work.LT.gb_submodule_le_equiv
import Submission.Work.LT.gb_sharp_numprod
import Submission.Work.LT.gb_sharp_factor

namespace Work.LT

/-- **Sharp real product form of the Gaussian binomial bound at `q = 2`.**
For `k ≤ m`,
`∏_{i<k}(2^m - 2^i) ≤ 4 · 2^{k(m-k)} · ∏_{i<k}(2^k - 2^i)`.

This is the sharp constant-`4` version of `gb_gaussian_prod_le` (which has the crude
constant `2^{j+2}`).  It is the analytic heart of `gb_card_submodule_sharp`.

Proof: the termwise identity `gb_sharp_factor` writes each factor of the numerator as
`2^{m-k}(2^k-2^i)(1-2^{i-m})/(1-2^{i-k})`; the denominator product equals
`∏ i, (1-(1/2)^{k-i})`, which is `≥ 1/4` by `gb_sharp_numprod`, and the extra numerators
`1-2^{i-m} ≤ 1` are discarded. -/
theorem gb_sharp_real_prod {m k : ℕ} (hk : k ≤ m) :
    (∏ i : Fin k, ((2 : ℝ) ^ m - (2 : ℝ) ^ (i : ℕ))) ≤
      4 * (2 : ℝ) ^ (k * (m - k)) * ∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) := by
  have hdenpos : ∀ i : Fin k, 0 < 1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)) := by
    intro i
    have hne : k - (i : ℕ) ≠ 0 := by have := i.isLt; omega
    have hlt : (1 / 2 : ℝ) ^ (k - (i : ℕ)) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) hne
    linarith
  -- Termwise sharpening: each factor is at most `2^{m-k}(2^k-2^i)/(1-(1/2)^{k-i})`.
  have hterm : ∀ i : Fin k, ((2 : ℝ) ^ m - (2 : ℝ) ^ (i : ℕ)) ≤
      (2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) *
        (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)))⁻¹ := by
    intro i
    rw [gb_sharp_factor hk i, div_eq_mul_inv]
    have hle1 : 1 - (1 / 2 : ℝ) ^ (m - (i : ℕ)) ≤ 1 := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (m - (i : ℕ)) := by positivity
      linarith
    have hX : 0 ≤ (2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) := by
      apply mul_nonneg (by positivity)
      exact sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt i.isLt))
    have hY : 0 ≤ (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)))⁻¹ := le_of_lt (inv_pos.mpr (hdenpos i))
    calc (2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) *
            (1 - (1 / 2 : ℝ) ^ (m - (i : ℕ))) * (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)))⁻¹
        ≤ (2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) * 1 *
            (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)))⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle1 hX) hY
      _ = (2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) *
            (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)))⁻¹ := by ring
  have hLnn : ∀ i : Fin k, 0 ≤ (2 : ℝ) ^ m - (2 : ℝ) ^ (i : ℕ) := fun i =>
    sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (le_of_lt (lt_of_lt_of_le i.isLt hk)))
  have hprod : (∏ i : Fin k, ((2 : ℝ) ^ m - (2 : ℝ) ^ (i : ℕ))) ≤
      ∏ i : Fin k, ((2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) *
        (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ)))⁻¹) :=
    Finset.prod_le_prod₀ (fun i _ => hLnn i) (fun i _ => hterm i)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [Finset.prod_inv_distrib] at hprod
  have hC : ((2 : ℝ) ^ (m - k)) ^ k = (2 : ℝ) ^ (k * (m - k)) := by
    rw [← pow_mul, Nat.mul_comm]
  have hD : (∏ i : Fin k, (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ))))⁻¹ ≤ 4 := by
    have hpos : 0 < ∏ i : Fin k, (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ))) :=
      Finset.prod_pos (fun i _ => hdenpos i)
    rw [inv_le_iff_one_le_mul₀ hpos]
    have hnum := gb_sharp_numprod k
    linarith
  have hPnn : 0 ≤ ∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) := by
    apply Finset.prod_nonneg; intro i _
    exact sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt i.isLt))
  refine le_trans hprod ?_
  rw [hC]
  calc (2 : ℝ) ^ (k * (m - k)) * (∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ))) *
        (∏ i : Fin k, (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ))))⁻¹
      ≤ (2 : ℝ) ^ (k * (m - k)) * (∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ))) * 4 :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg (by positivity) hPnn)
    _ = 4 * (2 : ℝ) ^ (k * (m - k)) * ∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) := by
        ring

/-- Sharp (Kalachev--Panteleev, Koetter) upper bound for the Gaussian binomial coefficient at `q = 2`: a subspace `U` has at most `4 * 2 ^ (k * (frk U - k))` subspaces of dimension `k`. Mirrors `Work.LT.gb_card_submodule` (crude `2^(k*(m-k)+k+2)`) with the standard sharp constant `4`. Proof: the exact count is `∏_{i<k}(2^m - 2^i)/(2^k - 2^i) = 2^{k(m-k)}·∏_{i<k}(1-2^{i-m})/(1-2^{i-k})` (`GB.gb_card_subspaces`, `GB.card_selfLinearEquiv`); each factor is `≤ 1/(1-2^{i-k})`, and `∏_{j=1}^{k}(1-2^{-j}) ≥ (1-1/2)(1-∑_{j≥2}2^{-j}) = 1/4`. Transport to `U` via `GB.gb_submodule_le_equiv`. -/
theorem gb_card_submodule_sharp {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) (k : ℕ) :
    (Nat.card {W : Submodule (ZMod 2) (Fin D → ZMod 2) // W ≤ U ∧ GB.frk W = k} : ℝ) ≤
      4 * (2 : ℝ) ^ (k * (GB.frk U - k)) := by
  by_cases hk : k ≤ GB.frk U
  · -- the submodules of `U` of dimension `k` are the `k`-dimensional submodules of `V`
    have hcard : Nat.card {W : Submodule (ZMod 2) (Fin D → ZMod 2) // W ≤ U ∧ GB.frk W = k}
        = Nat.card {W' : Submodule (ZMod 2) U // Module.finrank (ZMod 2) W' = k} := by
      simp only [GB.frk]
      exact gb_submodule_le_equiv U k
    rw [hcard]
    -- exact Gaussian-binomial count for the ambient space `U`
    have hcount : Nat.card {W' : Submodule (ZMod 2) U // Module.finrank (ZMod 2) W' = k} *
        (∏ i : Fin k, ((2 : ℕ) ^ k - 2 ^ (i : ℕ))) =
        ∏ i : Fin k, ((2 : ℕ) ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ)) :=
      gb_card_subspaces (V := U) k hk
    have hPn : ∀ i : Fin k, 2 ^ (i : ℕ) ≤ (2 : ℕ) ^ k := fun i =>
      Nat.pow_le_pow_right (by norm_num) (le_of_lt i.isLt)
    have hQn : ∀ i : Fin k, 2 ^ (i : ℕ) ≤ (2 : ℕ) ^ Module.finrank (ZMod 2) U := fun i =>
      Nat.pow_le_pow_right (by norm_num) (le_of_lt (lt_of_lt_of_le i.isLt hk))
    have hPcast : (((∏ i : Fin k, ((2 : ℕ) ^ k - 2 ^ (i : ℕ))) : ℕ) : ℝ) =
        ∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun i _ => by
        rw [Nat.cast_sub (hPn i), Nat.cast_pow, Nat.cast_pow]; norm_num)
    have hQcast : (((∏ i : Fin k, ((2 : ℕ) ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) : ℕ) : ℝ) =
        ∏ i : Fin k, ((2 : ℝ) ^ Module.finrank (ZMod 2) U - (2 : ℝ) ^ (i : ℕ)) := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun i _ => by
        rw [Nat.cast_sub (hQn i), Nat.cast_pow, Nat.cast_pow]; norm_num)
    have hcountR : (Nat.card {W' : Submodule (ZMod 2) U // Module.finrank (ZMod 2) W' = k} : ℝ) *
        (∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ))) =
        (∏ i : Fin k, ((2 : ℝ) ^ Module.finrank (ZMod 2) U - (2 : ℝ) ^ (i : ℕ))) := by
      have h1 : ((Nat.card {W' : Submodule (ZMod 2) U //
              Module.finrank (ZMod 2) W' = k} : ℕ) : ℝ) *
          (((∏ i : Fin k, ((2 : ℕ) ^ k - 2 ^ (i : ℕ))) : ℕ) : ℝ) =
          (((∏ i : Fin k, ((2 : ℕ) ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, hcount]
      rwa [hPcast, hQcast] at h1
    have hPpos : 0 < (∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ))) := by
      apply Finset.prod_pos; intro i _
      exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) i.isLt)
    have hstep : (Nat.card {W' : Submodule (ZMod 2) U // Module.finrank (ZMod 2) W' = k} : ℝ) *
        (∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ))) ≤
        (4 * (2 : ℝ) ^ (k * (Module.finrank (ZMod 2) U - k))) *
          (∏ i : Fin k, ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ))) := by
      rw [hcountR]; exact gb_sharp_real_prod hk
    exact le_of_mul_le_mul_right hstep hPpos
  · -- no `k`-dimensional subspace sits inside `U` when `k > frk U`
    have hE : IsEmpty {W : Submodule (ZMod 2) (Fin D → ZMod 2) // W ≤ U ∧ GB.frk W = k} :=
      ⟨fun W => by
        have hle : GB.frk W ≤ GB.frk U := Submodule.finrank_mono W.2.1
        omega⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hE)]
    simp only [Nat.cast_zero]
    positivity

end Work.LT
