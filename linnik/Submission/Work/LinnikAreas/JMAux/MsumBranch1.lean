import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAux.CellLayerInnerLe
import Submission.Work.LinnikAreas.JMAux.ExpSumLe

/-!
# Branch 1 of the `m`-sum of the far-zero mass (the log-free / Jutila range)

This is the high-`σ` branch `(m+1) ≤ L/5` (i.e. `σ = 1 - (m+1)/L ≥ 4/5`) of the double
`(m,k)`-sum bounding the far-zero mass, where the cell multiplicity is controlled by Jutila's
*log-free* bound with exponent `2 + 1/1000` (no power of `log q` is allowed here, since the
`m`-sum below is `O(1)`).

Two ingredients:

* `CellLayerInnerLe` (a separate lemma): the inner `k`-sum of `(1/4)^k · cellLayer R m k ·
  (q·2^k)^θ`, for `θ ≤ 1/2`, has ratio `2^{θ-2} ≤ 2^{-3/2} < 1`, so the `cellLayer` cutoff
  `R ≤ 2^k` turns it into `≤ 2 · q^θ · R^{-3/2}`.
* `ExpSumLe` (a separate lemma): replacing `q^{θ_m}` by `e^{(2+1/1000)(m+1)}` (using
  `L = log q`), the `m`-weight `e^{-(49/10)m} e^{(2+1/1000)(m+1)}` decays like `e^{-2.899 m}`,
  so the `m`-sum over any finite set is at most `50`.

Their product gives `2 · 50 = 100 · CJ · R^{-3/2}`, exactly the required constant.
-/

namespace Work.LinnikAreas.JMAux

open scoped BigOperators

/-- With `L = log q`, the `q`-power `q^{(2+1/1000)(m+1)/L}` of the branch-1 cell bound is just
`exp((2+1/1000)(m+1))`. -/
lemma qpow_eq_exp (q : ℕ) (hq : 2 ≤ q) {L : ℝ} (hL : L = Real.log (q:ℝ)) (m : ℕ) :
    (q:ℝ)^((2 + 1/1000) * (((m:ℝ)+1)/L)) = Real.exp ((2 + 1/1000) * ((m:ℝ)+1)) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by
    have : (1:ℕ) < q := by omega
    exact_mod_cast this
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hq1
  rw [Real.rpow_def_of_pos hqpos, ← hL]
  congr 1
  field_simp

lemma MsumBranch1 (q : ℕ) (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) (hR1 : 1 ≤ R) {CJ : ℝ} (hCJ : 0 < CJ)
    (Mmax N : ℕ) {s : Finset ℕ} (hs : ∀ m ∈ s, ((m:ℝ)+1) ≤ L/5) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L))))
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) := by
  classical
  have hq1 : 1 ≤ q := by omega
  have hR0 : (0:ℝ) < (R:ℝ) := by positivity
  -- Step 1: for `m ∈ s`, the inner `k`-sum is at most `CJ · 2 · q^{θ_m} · R^{-3/2}`.
  have hstep1 : ∀ m ∈ s, (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L))))
      ≤ CJ * (2 * (q:ℝ) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(3/2:ℝ))) := by
    intro m hm
    have hA : (2 + 1/1000) * (((m:ℝ)+1)/L) ≤ 1/2 := by
      have h1 : ((m:ℝ)+1)/L ≤ 1/5 := by
        rw [div_le_iff₀ hLp]; linarith [hs m hm]
      calc (2 + 1/1000) * (((m:ℝ)+1)/L) ≤ (2 + 1/1000) * (1/5) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ 1/2 := by norm_num
    have hB := CellLayerInnerLe q hq1 R hR1 N m hA
    have heq : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
          * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L))))
        = CJ * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left hB (le_of_lt hCJ)
  -- Step 2: insert the per-`m` bound into the outer sum.
  have hstep2 : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * (CJ * (2 * (q:ℝ) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(3/2:ℝ)))) :=
    Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hstep1 m hm) (Real.exp_nonneg _))
  -- Step 3: pull the constants out of the `m`-sum.
  have hsplit : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * (CJ * (2 * (q:ℝ) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(3/2:ℝ)))))
      = 2 * CJ * (R:ℝ)^(-(3/2:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2 + 1/1000) * (((m:ℝ)+1)/L))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  -- Step 4: rewrite the `q`-power, then bound the geometric `m`-sum.
  have hrew : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2 + 1/1000) * (((m:ℝ)+1)/L)))
      = ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((2 + 1/1000) * ((m:ℝ)+1)) :=
    Finset.sum_congr rfl (fun m _ => by rw [qpow_eq_exp q hq2 hLdef m])
  have hstep3 := ExpSumLe s
  have hnonneg : (0:ℝ) ≤ 2 * CJ * (R:ℝ)^(-(3/2:ℝ)) := by positivity
  -- Step 5: assemble.
  calc (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * (CJ * (2 * (q:ℝ) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(3/2:ℝ)))) := hstep2
    _ = 2 * CJ * (R:ℝ)^(-(3/2:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2 + 1/1000) * (((m:ℝ)+1)/L))) := hsplit
    _ = 2 * CJ * (R:ℝ)^(-(3/2:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((2 + 1/1000) * ((m:ℝ)+1))) := by rw [hrew]
    _ ≤ 2 * CJ * (R:ℝ)^(-(3/2:ℝ)) * 50 := mul_le_mul_of_nonneg_left hstep3 hnonneg
    _ = 100 * CJ / (R:ℝ)^(3/2:ℝ) := by
        rw [div_eq_mul_inv, Real.rpow_neg hR0.le]
        ring

end Work.LinnikAreas.JMAux
