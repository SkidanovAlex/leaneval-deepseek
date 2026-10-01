import Mathlib
import Submission.Work.LinnikAreas.CrudeWideDefs
import Submission.Work.LinnikAreas.FarBoundJM
import Submission.Work.LinnikAreas.JMAux.CellLayerKsum

namespace Work.LinnikAreas

open scoped BigOperators

/-!
# The double `(m,k)`-sum for the two-branch cell bound `cellBoundJMcw`

This module proves `Work.LinnikAreas.MsumBoundJMcw`: the assembly of the double `(m,k)`-sum of
the far-zero argument against the two-branch cell bound `cellBoundJMcw`, with the Montgomery
middle-branch term of `Work.LinnikAreas.msum_boundJMsh` deleted.

The two auxiliary estimates are proved here:

* `MsumExpLeCW`: the `m`-weight `e^{-(49/10)m}·e^{(24/5+1/1000)(m+1)}` has ratio
  `e^{-0.099} ≤ 32/33`, so its sum over any finite set of naturals is at most
  `150·33 = 4950 ≤ 5000`;
* `MsumBranch1cwAux`: the wide low-`λ` branch `(m+1) ≤ (1021/5000)L`: since
  `θ_m = (24/5+1/1000)·(m+1)/L ≤ (24/5+1/1000)·(1021/5000) ≤ 11/10`, the inner `k`-sum is at most
  `4·q^{θ_m}·R^{-9/10}` (`JMAux.CellLayerKsum`) and `q^{θ_m} = e^{(24/5+1/1000)(m+1)}`
  (`L = log q`), giving `4·5000 = 20000`.

The remaining, σ-blind branch `(m+1) > (1021/5000)L` is literally the summand of
`Work.LinnikAreas.msum_branch3sc`.
-/

/-- **The `m`-weight of the wide branch-1 cell bound.**  `e^{-(49/10)m}·e^{(24/5+1/1000)(m+1)}`
`= e^{4.801}·(e^{-0.099})^m`, with `e^{4.801} ≤ 150` and ratio `e^{-0.099} ≤ 32/33 < 1`; hence
the sum over any finite set of naturals is at most `150·33 = 4950 ≤ 5000`. -/
lemma MsumExpLeCW (s : Finset ℕ) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * Real.exp (((24:ℝ)/5 + 1/1000) * ((m:ℝ)+1)))
      ≤ 5000 := by
  set r : ℝ := Real.exp (-(99/1000)) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hconst : Real.exp (((24:ℝ)/5 + 1/1000)) ≤ 150 := by
    calc Real.exp (((24:ℝ)/5 + 1/1000)) ≤ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
      _ = (Real.exp 1)^5 := by
            rw [show (5:ℝ) = ((5:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      _ ≤ (2.7182818286:ℝ)^5 :=
            pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 5
      _ ≤ 150 := by norm_num
  have hrle : r ≤ 32/33 := by
    have h2 : (33/32:ℝ) ≤ Real.exp (99/1000) := by
      have h := Real.add_one_le_exp (99/1000)
      linarith
    have h3 : (Real.exp (99/1000))⁻¹ ≤ ((33/32:ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h2
    have h4 : ((33/32:ℝ))⁻¹ = 32/33 := by norm_num
    rw [hr, Real.exp_neg]
    linarith [h3, h4]
  have hterm : ∀ m : ℕ, Real.exp (-(49/10) * (m:ℝ)) * Real.exp (((24:ℝ)/5 + 1/1000) * ((m:ℝ)+1))
      = Real.exp (((24:ℝ)/5 + 1/1000)) * r^m := by
    intro m
    rw [← Real.exp_add]
    rw [show -(49/10) * (m:ℝ) + ((24:ℝ)/5 + 1/1000) * ((m:ℝ)+1)
        = ((24:ℝ)/5 + 1/1000) + (m:ℝ) * (-(99/1000)) by ring]
    rw [Real.exp_add, Real.exp_nat_mul, ← hr]
  calc ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * Real.exp (((24:ℝ)/5 + 1/1000) * ((m:ℝ)+1))
      = Real.exp (((24:ℝ)/5 + 1/1000)) * ∑ m ∈ s, r^m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => hterm m)
    _ ≤ Real.exp (((24:ℝ)/5 + 1/1000)) * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left (JMAux.geom_finset_le hr0 hr1 s) (le_of_lt (Real.exp_pos _))
    _ ≤ 150 * 33 := by
        have h1r : (1:ℝ)/33 ≤ 1 - r := by linarith
        have hpos : (0:ℝ) < 1 - r := by linarith
        have hinv : (1 - r)⁻¹ ≤ 33 := by
          have h := (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 1/33)).mpr h1r
          rwa [show ((1:ℝ)/33)⁻¹ = 33 by norm_num] at h
        exact mul_le_mul hconst hinv (by positivity) (by norm_num)
    _ ≤ 5000 := by norm_num

/-- **Branch 1 of the `m`-sum of the `cellBoundJMcw` double sum**: the wide low-`λ` range
`(m+1) ≤ (1021/5000)·L`.

Since `θ_m := (24/5 + 1/1000)·(m+1)/L ≤ (24/5+1/1000)·(1021/5000) ≤ 11/10`, `JMAux.CellLayerKsum`
bounds the inner `k`-sum by `4·q^{θ_m}·R^{-9/10}`; with `L = log q`, `q^{θ_m} = e^{θ'_m}` where
`θ'_m = (24/5+1/1000)(m+1)`, and `MsumExpLeCW` bounds the resulting `m`-sum by `5000`.  Hence
`4·5000 = 20000`. -/
lemma MsumBranch1cwAux (q : ℕ) (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) (hR1 : 1 ≤ R) {CJ : ℝ} (hCJ : 0 < CJ)
    (N : ℕ) {s : Finset ℕ} (hs : ∀ m ∈ s, ((m:ℝ)+1) ≤ (1021/5000)*L) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ) + 1)/L))))
      ≤ 20000 * CJ / (R:ℝ)^(9/10:ℝ) := by
  classical
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast (Nat.zero_le q : (0:ℕ) ≤ q)
  have hqpos : (0:ℝ) < (q:ℝ) := by
    have h : 0 < q := by omega
    exact_mod_cast h
  have hR0 : (0:ℝ) < (R:ℝ) := by
    have h : 0 < R := by omega
    exact_mod_cast h
  have hstep : ∀ m ∈ s, (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * (CJ * ((q:ℝ)*(2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L))))
      ≤ CJ * (4 * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1)) * (R:ℝ)^(-(9/10:ℝ))) := by
    intro m hm
    have hθ : ((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L) ≤ 11/10 := by
      have h1 : ((m:ℝ)+1)/L ≤ 1021/5000 := by
        rw [div_le_iff₀ hLp]; linarith [hs m hm]
      calc ((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L) ≤ ((24:ℝ)/5+1/1000) * (1021/5000) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ 11/10 := by norm_num
    have hqpow : (q:ℝ) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L))
        = Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1)) := by
      have hlogne : Real.log (q:ℝ) ≠ 0 := by rw [← hLdef]; exact ne_of_gt hLp
      rw [Real.rpow_def_of_pos hqpos, ← hLdef]
      congr 1
      field_simp
    have hK := JMAux.CellLayerKsum q R N m hR1 (Nat.zero_le q) hθ
    have hK' : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * ((q:ℝ)*(2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L)))
        ≤ 4 * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1)) * (R:ℝ)^(-(9/10:ℝ)) := by
      rw [hqpow] at hK
      exact hK
    have heq : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * (CJ * ((q:ℝ)*(2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L))))
        = CJ * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * ((q:ℝ)*(2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left hK' (le_of_lt hCJ)
  have houter : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CJ * ((q:ℝ)*(2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10)*(m:ℝ))
          * (CJ * (4 * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1)) * (R:ℝ)^(-(9/10:ℝ)))) :=
    Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hstep m hm) (Real.exp_nonneg _))
  have hsplit : (∑ m ∈ s, Real.exp (-(49/10)*(m:ℝ))
        * (CJ * (4 * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1)) * (R:ℝ)^(-(9/10:ℝ)))))
      = 4 * CJ * (R:ℝ)^(-(9/10:ℝ))
          * (∑ m ∈ s, Real.exp (-(49/10)*(m:ℝ))
              * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  calc (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CJ * ((q:ℝ)*(2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ)+1)/L))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10)*(m:ℝ))
          * (CJ * (4 * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1)) * (R:ℝ)^(-(9/10:ℝ)))) := houter
    _ = 4 * CJ * (R:ℝ)^(-(9/10:ℝ))
          * (∑ m ∈ s, Real.exp (-(49/10)*(m:ℝ))
              * Real.exp (((24:ℝ)/5+1/1000)*((m:ℝ)+1))) := hsplit
    _ ≤ 4 * CJ * (R:ℝ)^(-(9/10:ℝ)) * 5000 := by
        refine mul_le_mul_of_nonneg_left (MsumExpLeCW s) ?_
        have : (0:ℝ) ≤ (R:ℝ)^(-(9/10:ℝ)) := Real.rpow_nonneg hR0.le _
        positivity
    _ = 20000 * CJ / (R:ℝ)^(9/10:ℝ) := by
        rw [Real.rpow_neg hR0.le, div_eq_mul_inv]
        ring

/-- **The double `(m,k)`-sum for the two-branch cell bound `cellBoundJMcw`.**  This is
`Work.LinnikAreas.msum_boundJMsh` with the Montgomery middle-branch term `30000*CM/(...)`
deleted.  Proof plan: split `Finset.range Mmax` by the two branches of `cellBoundJMcw`
(`Finset.sum_filter_add_sum_filter_not`, twice as in the reference).
* Branch 1 `(m+1) ≤ (1021/5000)L`: the exponent `θ_m = (24/5 + 1/1000)(m+1)/L` satisfies
  `θ_m ≤ (24/5+1/1000)*(1021/5000) ≤ 11/10`, so `Work.LinnikAreas.JMAux.CellLayerKsum` gives
  the inner `k`-sum `≤ 4·q^{θ_m}·R^{-9/10}`; with `L = log q` one has
  `q^{θ_m} = Real.exp ((24/5+1/1000)(m+1))`, and the `m`-sum is at most `3000`:
  `∑_m e^{-(49/10)m} e^{(24/5+1/1000)(m+1)} = e^{4.801}/(1 - e^{-0.099}) ≈ 1290.5`.  (Bound it
  e.g. by `e^{5} ≤ (2.7182818286)^5 ≤ 150`, ratio `≈ 0.9059`, giving `≤ 150·11 = 1650 ≤ 3000`.)
  Then `4·3000 = 12000 ≤ 20000` produces the first term.
* Branch 2 `(m+1) > (1021/5000)L`: the summand is exactly the summand of
  `Work.LinnikAreas.msum_branch3sc`, whose hypothesis `(1021/5000)L - 1 < m` holds on this
  filter, giving the second term `60000·c0·L/q^{29/50000}` unchanged. -/
lemma MsumBoundJMcw {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (hL1 : 1 ≤ L) (R : ℕ) (hR1 : 1 ≤ R)
    {CJ c0 : ℝ} (hCJ : 0 < CJ) (hc0 : 0 < c0) (Mmax N : ℕ) :
    (∑ m ∈ Finset.range Mmax, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * Work.LinnikAreas.cellBoundJMcw q CJ c0 L m k)
      ≤ 20000 * CJ / (R:ℝ)^(9/10:ℝ) + 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range Mmax)
      (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)
      (fun m => Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMcw q CJ c0 L m k)]
  have hA : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJMcw q CJ c0 L m k)
      ≤ 20000 * CJ / (R:ℝ)^(9/10:ℝ) := by
    have heq : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMcw q CJ c0 L m k)
        = (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ) + 1)/L)))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm1 : ((m:ℝ)+1) ≤ (1021/5000)*L := (Finset.mem_filter.mp hm).2
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJMcw, if_pos hm1])
    rw [heq]
    exact MsumBranch1cwAux q hq2 hLp hLdef R hR1 hCJ N
      (fun m hm => (Finset.mem_filter.mp hm).2)
  have hB : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (1021/5000)*L)),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJMcw q CJ c0 L m k)
      ≤ 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := by
    have heq : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (1021/5000)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMcw q CJ c0 L m k)
        = (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (1021/5000)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k / L)
              * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm2 : ¬ (((m:ℝ)+1) ≤ (1021/5000)*L) := (Finset.mem_filter.mp hm).2
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJMcw, if_neg hm2])
    rw [heq]
    refine msum_branch3sc q hq2 hLp hL1 hLdef R hc0.le N ?_
    intro m hm
    have h2 : (1021/5000)*L < (m:ℝ)+1 := lt_of_not_ge (Finset.mem_filter.mp hm).2
    linarith
  linarith [hA, hB]

end Work.LinnikAreas
