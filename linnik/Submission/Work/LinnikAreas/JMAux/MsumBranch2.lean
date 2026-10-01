import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAux.CellLayerKsum
import Submission.Work.LinnikAreas.JMAux.MsumExpLe

/-!
# Branch 2 of the `m`-sum of the far-zero mass (Montgomery range)

This is the middle branch `L/5 < (m+1) ≤ (5/12)L` of the double `(m,k)`-sum bounding the
far-zero mass: there the cell multiplicity is controlled by Montgomery's density theorem with
exponent `2451/1000`, and the `k`-sum of `(1/4)^k · cellLayer R m k · (q·2^k)^{θ_m}` has ratio
`2^{θ_m-2} ≤ 2^{-9/10}`, while the `cellLayer` cutoff `R ≤ 2^k` produces the factor `R^{-9/10}`.
Rewriting `q^{θ_m} = exp((2451/1000)(m+1))` and using `(m+1) > L/5` turns the `m`-sum into the
geometric tail `e^{49/10}/(1-e^{-2449/1000}) · q^{-2449/5000} ≤ 400 · q^{-19/40}`.
-/

namespace Work.LinnikAreas.JMAux

open scoped BigOperators

lemma MsumBranch2 (q : ℕ) (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) (hR1 : 1 ≤ R) {CM : ℝ} (hCM : 0 < CM)
    (Mmax N : ℕ) {s : Finset ℕ} (hs1 : ∀ m ∈ s, L/5 < (m:ℝ)+1)
    (hs2 : ∀ m ∈ s, (m:ℝ)+1 ≤ (5/12)*L) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L))))
      ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ)) := by
  classical
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hR0 : (0:ℝ) < (R:ℝ) := by positivity
  -- Step 1: for `m ∈ s`, the inner `k`-sum is at most `CM · 4 · q^{θ_m} · R^{-9/10}`.
  have hstep1 : ∀ m ∈ s, (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L))))
      ≤ CM * (4 * (q:ℝ) ^ ((2451/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ))) := by
    intro m hm
    have hθ : (2451/1000) * (((m:ℝ) + 1)/L) ≤ 11/10 := by
      have h1 : ((m:ℝ)+1)/L ≤ 5/12 := by
        rw [div_le_iff₀ hLp]; linarith [hs2 m hm]
      calc (2451/1000)*(((m:ℝ)+1)/L) ≤ (2451/1000)*(5/12) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ 11/10 := by norm_num
    have hA := CellLayerKsum q R N m hR1 (Nat.zero_le q) hθ
    have heq : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
          * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L))))
        = CM * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hCM)
  -- Step 2: insert the per-`m` bound into the outer sum.
  have hstep2 : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L)))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * (CM * (4 * (q:ℝ) ^ ((2451/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ)))) :=
    Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hstep1 m hm) (Real.exp_nonneg _))
  -- Step 3: pull the constants out of the `m`-sum.
  have hsplit : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * (CM * (4 * (q:ℝ) ^ ((2451/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ)))))
      = 4 * CM * (R:ℝ)^(-(9/10:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2451/1000) * (((m:ℝ)+1)/L))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  -- Step 4: the geometric `m`-sum.
  have hstep3 : (∑ m ∈ s, Real.exp (-(49/10)*(m:ℝ)) * (q:ℝ)^((2451/1000)*(((m:ℝ)+1)/L)))
      ≤ 400 * (q:ℝ)^(-(19/40:ℝ)) := MsumExpLe q hq2 hLp hLdef hs1
  have hnonneg : (0:ℝ) ≤ 4 * CM * (R:ℝ)^(-(9/10:ℝ)) := by positivity
  -- Step 5: the final numerical comparison.
  have hfin : 1600 * CM * (R:ℝ)^(-(9/10:ℝ)) * (q:ℝ)^(-(19/40:ℝ))
      ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ)) := by
    have hY : (0:ℝ) ≤ CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(19/40:ℝ))⁻¹ := by positivity
    have e1 : (R:ℝ)^(-(9/10:ℝ)) = ((R:ℝ)^(9/10:ℝ))⁻¹ := Real.rpow_neg hR0.le (9/10)
    have e2 : (q:ℝ)^(-(19/40:ℝ)) = ((q:ℝ)^(19/40:ℝ))⁻¹ := Real.rpow_neg hq0 (19/40)
    have e3 : 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ))
        = 30000 * (CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(19/40:ℝ))⁻¹) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [e1, e2, e3]
    calc 1600 * CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(19/40:ℝ))⁻¹
        = 1600 * (CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(19/40:ℝ))⁻¹) := by ring
      _ ≤ 30000 * (CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(19/40:ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_right (by norm_num) hY
  calc (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * (CM * (4 * (q:ℝ) ^ ((2451/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ)))) := hstep2
    _ = 4 * CM * (R:ℝ)^(-(9/10:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2451/1000) * (((m:ℝ)+1)/L))) := hsplit
    _ ≤ 4 * CM * (R:ℝ)^(-(9/10:ℝ)) * (400 * (q:ℝ)^(-(19/40:ℝ))) :=
        mul_le_mul_of_nonneg_left hstep3 hnonneg
    _ = 1600 * CM * (R:ℝ)^(-(9/10:ℝ)) * (q:ℝ)^(-(19/40:ℝ)) := by ring
    _ ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ)) := hfin

end Work.LinnikAreas.JMAux
