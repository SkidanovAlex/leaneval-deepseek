import Mathlib
import Submission.Work.BourgainPlan.Maximal.lintegral_iSup_sq_le_tsum_sq

namespace Work.BourgainPlan.Maximal

open MeasureTheory

/-- AM-GM in `ℝ≥0∞`: `p * q + q * p ≤ p² + q²` (equivalent to `(p-q)² ≥ 0`). -/
private lemma mul_swap_add_le_sq_add_sq (p q : ENNReal) : p * q + q * p ≤ p ^ 2 + q ^ 2 := by
  rcases eq_or_ne p ⊤ with hp | hp
  · subst hp; simp
  rcases eq_or_ne q ⊤ with hq | hq
  · subst hq; simp
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hp hq, ENNReal.mul_ne_top hq hp⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top hp, ENNReal.pow_ne_top hq⟩
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp hq) (ENNReal.mul_ne_top hq hp),
    ENNReal.toReal_add (ENNReal.pow_ne_top hp) (ENNReal.pow_ne_top hq),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
  nlinarith [sq_nonneg (p.toReal - q.toReal)]

/-- `(p + q)² ≤ 2p² + 2q²` in `ℝ≥0∞`. -/
private lemma add_sq_le_two (p q : ENNReal) :
    (p + q) ^ (2 : ℝ) ≤ 2 * p ^ (2 : ℝ) + 2 * q ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two, pow_two, pow_two, pow_two]
  have h : p * q + q * p ≤ p * p + q * q := by
    simpa [pow_two] using mul_swap_add_le_sq_add_sq p q
  calc (p + q) * (p + q) = p * p + (p * q + q * p) + q * q := by ring
    _ ≤ p * p + (p * p + q * q) + q * q := by
        exact add_le_add (add_le_add le_rfl h) le_rfl
    _ = 2 * (p * p) + 2 * (q * q) := by ring

/-- `(ofReal b²)^(1/2) = ofReal b` for `b ≥ 0`. -/
private lemma ofReal_sq_rpow_half (b : ℝ) (hb : 0 ≤ b) :
    (ENNReal.ofReal (b ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal b := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  rw [← Real.rpow_two b, ← Real.rpow_mul hb 2 (1/2), show (2:ℝ)*(1/2) = 1 by norm_num,
    Real.rpow_one]

/-- **The `ℓ²` maximal inequality from a per-`n` bound (Minkowski + AM-GM).**  Given three families of `ℝ≥0∞`-valued functions on `ℤ` with `A n ≤ B n + D n` pointwise, a per-`n` `ℓ²` bound for `D n`, and a bound on the (summable!) tail sum of the constants, the `ℓ²`-maximal function of `A` over `n ≥ N₀` is dominated by twice the maximal function of `B` plus twice the `ℓ²`-norm of the input:
`∫⁻_x (⨆_{n≥N₀} A n x)² ≤ 2·∫⁻_x (⨆_{n≥N₀} B n x)² + 2·ofReal(C²)·S`.

NOTE (from the review of the previous version): the hypothesis `Summable (fun k => b (N₀+k))` is essential — `tsum` is `0` for a divergent nonneg family, so `tsum (…) ≤ C` alone would be vacuous.

Route: (i) `⨆_{n≥N₀} A n ≤ (⨆_{n≥N₀} B n) + (⨆_{n≥N₀} D n)` pointwise (`iSup_le` + `le_iSup_of_le`, then `add_le_add`); (ii) `(p+q)² ≤ 2p²+2q²` in `ℝ≥0∞` (AM-GM; reduce to the finite case with `ENNReal.toReal`, or use `ENNReal.mul_add_self_le_sq_add_sq`-style helper); (iii) the index shift `⨆_{n≥N₀} f n x = ⨆_k f (N₀+k) x` (`le_iSup_of_le`/`le_iSup` with `N₀ + (n - N₀) = n` via `Nat.add_sub_cancel'`); (iv) `lintegral_iSup_sq_le_tsum_sq` (`Work.BourgainPlan.Maximal.lintegral_iSup_sq_le_tsum_sq`): `∫⁻_x (⨆_k E k x)² ≤ (Σ'_k (∫⁻_x E k x²)^{1/2})²`; (v) from `hpern`, `(∫⁻_x D n x²)^{1/2} ≤ ofReal(b n)·S^{1/2}` using `ENNReal.rpow_le_rpow`, `ENNReal.mul_rpow_of_nonneg (h : 0 ≤ 1/2)`, `ENNReal.ofReal_rpow_of_nonneg`, `Real.rpow_mul` and `(ofReal(b n ^ 2))^(1/2:ℝ) = ofReal(b n)`; (vi) `(Σ'_k ofReal(b k)·S^{1/2})² = (Σ'_k ofReal(b k))²·S` (`ENNReal.tsum_mul_right`, `ENNReal.rpow_mul`, `ENNReal.rpow_one`) `= ofReal((Σ'_k b(N₀+k))²)·S` (`ENNReal.ofReal_tsum_of_nonneg` with `hbsum`), and `(Σ'_k b(N₀+k))² ≤ C²` by `hCsum`, `tsum_nonneg` and monotonicity of squaring. -/
theorem lintegral_iSup_sq_le_of_per_n_bound (A B D : ℕ → ℤ → ENNReal) (N₀ : ℕ) (b : ℕ → ℝ)
    (S : ENNReal) (C : ℝ) (hb : ∀ n : ℕ, 0 ≤ b n) (hC : 0 ≤ C)
    (hbsum : Summable (fun k : ℕ => b (N₀ + k)))
    (hABC : ∀ n : ℕ, ∀ x : ℤ, A n x ≤ B n x + D n x)
    (hpern : ∀ n : ℕ, MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => D n x ^ (2 : ℝ)) ≤ ENNReal.ofReal ((b n) ^ 2) * S)
    (hCsum : (tsum (fun k : ℕ => b (N₀ + k))) ≤ C) :
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
        (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), A n x) ^ (2 : ℝ))
      ≤ 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
          (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)))
        + 2 * ENNReal.ofReal (C ^ 2) * S := by
  -- (i) pointwise domination of the maximals
  have hA_le : ∀ x : ℤ, (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), A n x)
      ≤ (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) + (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) := by
    intro x
    refine iSup_le fun n => iSup_le fun hn => ?_
    calc A n x ≤ B n x + D n x := hABC n x
      _ ≤ (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) + (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) :=
          add_le_add (le_iSup_of_le n (le_iSup_of_le hn le_rfl))
            (le_iSup_of_le n (le_iSup_of_le hn le_rfl))
  -- (ii) AM-GM, pointwise
  have hpt : ∀ x : ℤ, (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), A n x) ^ (2 : ℝ)
      ≤ 2 * (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)
        + 2 * (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ) := by
    intro x
    exact (ENNReal.rpow_le_rpow (hA_le x) (by norm_num)).trans (add_sq_le_two _ _)
  -- split the integral
  have h1 : MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), A n x) ^ (2 : ℝ))
      ≤ 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)))
        + 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ))) := by
    calc MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), A n x) ^ (2 : ℝ))
        ≤ MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
            2 * (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)
              + 2 * (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ)) :=
          MeasureTheory.lintegral_mono hpt
      _ = 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)))
          + 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ))) := by
          rw [MeasureTheory.lintegral_add_left (Measurable.of_discrete),
            MeasureTheory.lintegral_const_mul 2
              (f := fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ))
              (Measurable.of_discrete),
            MeasureTheory.lintegral_const_mul 2
              (f := fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ))
              (Measurable.of_discrete)]
  -- (iii) the index shift `⨆_{n ≥ N₀} f n = ⨆_k f (N₀ + k)`
  have hshift : ∀ x : ℤ, (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) = ⨆ k : ℕ, D (N₀ + k) x := by
    intro x
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => iSup_le fun hn => ?_
      calc D n x = D (N₀ + (n - N₀)) x := by rw [Nat.add_sub_cancel' hn]
        _ ≤ ⨆ k : ℕ, D (N₀ + k) x := le_iSup (fun k : ℕ => D (N₀ + k) x) (n - N₀)
    · refine iSup_le fun k => ?_
      exact le_iSup_of_le (N₀ + k) (le_iSup_of_le (Nat.le_add_right N₀ k) le_rfl)
  -- the `D`-part of the maximal function
  have hMD : MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ))
      ≤ ENNReal.ofReal (C ^ 2) * S := by
    have hshift_lint : MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ))
        = MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ k : ℕ, D (N₀ + k) x) ^ (2 : ℝ)) := by
      apply MeasureTheory.lintegral_congr
      intro x
      rw [hshift x]
    rw [hshift_lint]
    -- (iv) Minkowski for the counted maximal function
    have hMink : MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ k : ℕ, D (N₀ + k) x) ^ (2 : ℝ))
        ≤ (tsum (fun k : ℕ => (MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => D (N₀ + k) x ^ (2 : ℝ))) ^ (1 / 2 : ℝ))) ^ (2 : ℝ) := by
      simpa only [ENNReal.rpow_two] using
        lintegral_iSup_sq_le_tsum_sq (fun k x => D (N₀ + k) x)
    -- (v) the per-`n` bound, after taking square roots
    have hpern' : ∀ k : ℕ, (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => D (N₀ + k) x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (b (N₀ + k)) * S ^ (1 / 2 : ℝ) := by
      intro k
      calc (MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => D (N₀ + k) x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal ((b (N₀ + k)) ^ 2) * S) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (hpern (N₀ + k)) (by norm_num)
        _ = (ENNReal.ofReal ((b (N₀ + k)) ^ 2)) ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ = ENNReal.ofReal (b (N₀ + k)) * S ^ (1 / 2 : ℝ) := by
            rw [ofReal_sq_rpow_half (b (N₀ + k)) (hb _)]
    -- (vi) the arithmetic
    have htail : (tsum (fun k : ℕ => ENNReal.ofReal (b (N₀ + k)) * S ^ (1 / 2 : ℝ))) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (C ^ 2) * S := by
      have hts : (tsum (fun k : ℕ => ENNReal.ofReal (b (N₀ + k)) * S ^ (1 / 2 : ℝ))) ^ (2 : ℝ)
          = (tsum (fun k : ℕ => ENNReal.ofReal (b (N₀ + k)))) ^ (2 : ℝ) * S := by
        rw [ENNReal.tsum_mul_right, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          ← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
      rw [hts]
      have hT : tsum (fun k : ℕ => ENNReal.ofReal (b (N₀ + k)))
          = ENNReal.ofReal (tsum (fun k : ℕ => b (N₀ + k))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => hb (N₀ + k)) hbsum).symm
      rw [hT]
      gcongr
      have h0 : (0 : ℝ) ≤ tsum (fun k : ℕ => b (N₀ + k)) := tsum_nonneg fun k => hb (N₀ + k)
      calc (ENNReal.ofReal (tsum (fun k : ℕ => b (N₀ + k)))) ^ (2 : ℝ)
          = ENNReal.ofReal ((tsum (fun k : ℕ => b (N₀ + k))) ^ (2 : ℝ)) :=
            ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num)
        _ ≤ ENNReal.ofReal (C ^ (2 : ℝ)) :=
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hCsum (by norm_num))
        _ = ENNReal.ofReal (C ^ 2) := by rw [Real.rpow_two]
    calc MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => (⨆ k : ℕ, D (N₀ + k) x) ^ (2 : ℝ))
        ≤ (tsum (fun k : ℕ => (MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => D (N₀ + k) x ^ (2 : ℝ))) ^ (1 / 2 : ℝ))) ^ (2 : ℝ) := hMink
      _ ≤ (tsum (fun k : ℕ => ENNReal.ofReal (b (N₀ + k)) * S ^ (1 / 2 : ℝ))) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum hpern') (by norm_num)
      _ ≤ ENNReal.ofReal (C ^ 2) * S := htail
  calc MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), A n x) ^ (2 : ℝ))
      ≤ 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)))
        + 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), D n x) ^ (2 : ℝ))) := h1
    _ ≤ 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)))
        + 2 * (ENNReal.ofReal (C ^ 2) * S) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hMD (by norm_num))
    _ = 2 * (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (⨆ n : ℕ, ⨆ (_ : N₀ ≤ n), B n x) ^ (2 : ℝ)))
        + 2 * ENNReal.ofReal (C ^ 2) * S := by rw [mul_assoc]

end Work.BourgainPlan.Maximal
