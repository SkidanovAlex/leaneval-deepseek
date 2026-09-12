import Mathlib
import Submission.FeketeLim

/-!
# Step3 scaling infrastructure

Any proof of `Submission.Step3.sym_maximality` (= Dubinin's equal-length
hedgehog bound, sharp constant `4^(-1/s)`) may reduce the general-length
statement to the unit case: the hedgehog `dirStar u L` is the homothetic
image `L · (dirStar u 1)` of the unit hedgehog, and the Fekete numbers
scale by `‖a‖ ^ (n(n-1)/2)` under `K ↦ a • K`.  This module proves that
scaling law at the Vandermonde / Fekete-set / Fekete-number level and the
`limsup_root_scaling` identity, which is exactly the operation the
`Step3.sym_maximality` exponent `2/((n+1)n)` applies.

All statements are elementary (norm_mul, Finset products, csSup scaling);
no `sorry`.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.Step3Scaling

open Submission.FeketeLim
open Set

/-- Homothety of a set: the image by `z ↦ a·z`. -/
def homot (a : ℂ) (K : Set ℂ) : Set ℂ := (fun z : ℂ => a * z) '' K

/-- The Vandermonde product of the `a`-scaled configuration equals
`‖a‖^(n(n-1)/2)` times the Vandermonde product. -/
lemma vdm_scaling (x : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    vdm (fun i => a * x i) n = ‖a‖ ^ (n * (n - 1) / 2) * vdm x n := by
  classical
  unfold vdm
  calc
    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖a * x j - a * x i‖)
        = (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, (‖a‖ * ‖x j - x i‖)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          refine Finset.prod_congr rfl ?_
          intro j hj
          rw [← mul_sub]
          exact Complex.norm_mul a (x j - x i)
    _ = (∏ i ∈ Finset.range n, (∏ j ∈ Finset.range i, ‖a‖) *
            (∏ j ∈ Finset.range i, ‖x j - x i‖)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact Finset.prod_mul_distrib
    _ = (∏ i ∈ Finset.range n, ‖a‖ ^ i) *
        (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖) := by
          calc
            (∏ i ∈ Finset.range n, (∏ j ∈ Finset.range i, ‖a‖) *
                (∏ j ∈ Finset.range i, ‖x j - x i‖))
                = (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖a‖) *
                    (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖) :=
                  Finset.prod_mul_distrib
            _ = (∏ i ∈ Finset.range n, ‖a‖ ^ (Finset.range i).card) *
                (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖) := by
                  congr 1
                  refine Finset.prod_congr rfl ?_
                  intro i hi
                  rw [Finset.prod_const]
            _ = (∏ i ∈ Finset.range n, ‖a‖ ^ i) *
                (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖) := by
                  congr 1
                  refine Finset.prod_congr rfl ?_
                  intro i hi
                  rw [Finset.card_range]
    _ = ‖a‖ ^ (n * (n - 1) / 2) * vdm x n := by
          rw [show (∏ i ∈ Finset.range n, ‖a‖ ^ i) = ‖a‖ ^ (n * (n - 1) / 2) by
            calc
              (∏ i ∈ Finset.range n, ‖a‖ ^ i)
                  = ‖a‖ ^ (∑ i ∈ Finset.range n, i) :=
                    Finset.prod_pow_eq_pow_sum (Finset.range n) (fun i => i) ‖a‖
              _ = ‖a‖ ^ (n * (n - 1) / 2) := by rw [Finset.sum_range_id]]
          rfl

/-- The scaled fekete set is the pointwise-scaled fekete set. -/
lemma feketeSet_scaling (K : Set ℂ) (n : ℕ) (a : ℂ) (hKne : K.Nonempty) :
    feketeSet (homot a K) n = (fun d : ℝ => ‖a‖ ^ (n * (n - 1) / 2) * d) '' feketeSet K n := by
  classical
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    dsimp [homot] at hx
    let y : ℕ → ℂ := fun i => if h : i < n then
        Classical.choose (show x i ∈ (fun z : ℂ => a * z) '' K from hx i h) else 0
    have hy : ∀ i : ℕ, i < n → y i ∈ K := by
      intro i hi
      dsimp [y]
      rw [dif_pos hi]
      exact (Classical.choose_spec (show x i ∈ (fun z : ℂ => a * z) '' K from hx i hi)).1
    have hscale : ∀ i : ℕ, i < n → a * y i = x i := by
      intro i hi
      dsimp [y]
      rw [dif_pos hi]
      exact (Classical.choose_spec (show x i ∈ (fun z : ℂ => a * z) '' K from hx i hi)).2
    refine ⟨vdm y n, ⟨y, hy, rfl⟩, ?_⟩
    calc
      ‖a‖ ^ (n * (n - 1) / 2) * vdm y n = vdm (fun i => a * y i) n := (vdm_scaling y n a).symm
      _ = vdm x n := by
        unfold vdm
        refine Finset.prod_congr rfl ?_
        intro i hi
        refine Finset.prod_congr rfl ?_
        intro j hj
        have hji : j < i := Finset.mem_range.mp hj
        have hin : i < n := Finset.mem_range.mp hi
        have hjn : j < n := lt_trans hji hin
        change ‖a * y j - a * y i‖ = ‖x j - x i‖
        rw [hscale j hjn, hscale i hin]
  · rintro ⟨d₀, hd₀, rfl⟩
    rcases hd₀ with ⟨x, hx, rfl⟩
    dsimp [homot]
    refine ⟨fun i => a * x i, ?_, ?_⟩
    · intro i hi
      refine ⟨x i, hx i hi, rfl⟩
    · exact (vdm_scaling x n a).symm

/-- `sSup` of a nonnegative-scaled set: `sSup (c • S) = c • sSup S` for
`0 ≤ c` and nonempty bounded `S`. -/
lemma csSup_smul_nonneg {S : Set ℝ} (hSne : S.Nonempty) (hbdd : BddAbove S)
    {c : ℝ} (hc : 0 ≤ c) :
    sSup ((fun d : ℝ => c * d) '' S) = c * sSup S := by
  classical
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · rcases hSne with ⟨d, hd⟩
      exact ⟨c * d, d, hd, rfl⟩
    · intro b hb
      rcases hb with ⟨d, hd, rfl⟩
      exact mul_le_mul_of_nonneg_left (le_csSup hbdd hd) hc
  · by_cases hc0 : c = 0
    · rw [hc0, zero_mul]
      have him0 : (fun d : ℝ => 0 * d) '' S = ({0} : Set ℝ) := by
        ext x
        constructor
        · rintro ⟨d, hd, rfl⟩
          simp
        · intro hx
          rcases hSne with ⟨d, hd⟩
          rw [Set.mem_singleton_iff] at hx
          refine ⟨d, hd, ?_⟩
          simp [hx]
      rw [him0, csSup_singleton]
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hbddcS : BddAbove ((fun d : ℝ => c * d) '' S) := ⟨c * sSup S, by
        intro b hb
        rcases hb with ⟨d, hd, rfl⟩
        exact mul_le_mul_of_nonneg_left (le_csSup hbdd hd) hc⟩
      have hle : sSup S ≤ sSup ((fun d : ℝ => c * d) '' S) / c := by
        refine csSup_le hSne ?_
        intro d hd
        rw [le_div_iff₀ hcpos]
        have hmem : c * d ∈ (fun d : ℝ => c * d) '' S := ⟨d, hd, rfl⟩
        simpa [mul_comm] using (le_csSup hbddcS hmem : c * d ≤ sSup ((fun d : ℝ => c * d) '' S))
      calc
        c * sSup S ≤ c * (sSup ((fun d : ℝ => c * d) '' S) / c) := by
          exact mul_le_mul_of_nonneg_left hle (le_of_lt hcpos)
        _ = sSup ((fun d : ℝ => c * d) '' S) := by
          rw [mul_comm c (sSup ((fun d : ℝ => c * d) '' S) / c)]
          exact div_mul_cancel₀ (sSup ((fun d : ℝ => c * d) '' S)) (ne_of_gt hcpos)

/-- Fekete numbers scale by `‖a‖^(n(n-1)/2)` under homothety. -/
lemma feketeNumber_scaling (K : Set ℂ) (n : ℕ) (a : ℂ) (hKne : K.Nonempty)
    (hKb : BddAbove (feketeSet K n)) :
    feketeNumber (homot a K) n = ‖a‖ ^ (n * (n - 1) / 2) * feketeNumber K n := by
  classical
  have hscale := feketeSet_scaling K n a hKne
  have hne : (feketeSet K n).Nonempty := by
    rcases hKne with ⟨k, hk⟩
    refine ⟨vdm (fun _ : ℕ => k) n, fun _ : ℕ => k, ?_, rfl⟩
    intro i hi
    exact hk
  calc
    feketeNumber (homot a K) n
        = sSup (feketeSet (homot a K) n) := by rfl
    _ = sSup ((fun d : ℝ => ‖a‖ ^ (n * (n - 1) / 2) * d) '' feketeSet K n) := by
          rw [← hscale]
    _ = ‖a‖ ^ (n * (n - 1) / 2) * feketeNumber K n := by
          rw [show feketeNumber K n = sSup (feketeSet K n) by rfl]
          exact csSup_smul_nonneg hne hKb (pow_nonneg (norm_nonneg a) _)

/-- Consecutive integers: `2 · ((n+1)·n / 2) = (n+1)·n`. -/
lemma pairs_two_mul (n : ℕ) : 2 * ((n + 1) * n / 2) = (n + 1) * n := by
  have he : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  have hdiv : 2 ∣ (n + 1) * n := by
    rw [mul_comm]
    exact even_iff_two_dvd.mp he
  rcases hdiv with ⟨c, hc⟩
  have hq : (n + 1) * n / 2 = c := by omega
  rw [hq, hc]

/-- The exponent arithmetic behind `feketeRoot_scaling`:
`(number of pairs) · 2/((n+1)·n) = 1` for `n ≥ 1`. -/
lemma pairExp_mul (n : ℕ) (hn : 1 ≤ n) :
    ((((n + 1) * n / 2 : ℕ) : ℝ)) * (2 / (((n + 1 : ℝ)) * (n : ℝ))) = 1 := by
  have h2e : 2 * (((n + 1) * n / 2 : ℕ) : ℝ) = (((n + 1) * n : ℕ) : ℝ) := by
    exact_mod_cast (pairs_two_mul n)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
  have hN : (((n + 1 : ℝ)) * (n : ℝ)) ≠ 0 := by positivity
  calc
    ((((n + 1) * n / 2 : ℕ) : ℝ)) * (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        = ((((n + 1) * n : ℕ) : ℝ) / 2) * (2 / (((n + 1 : ℝ)) * (n : ℝ))) := by
          congr 1
          -- from 2*e = N derive e = N/2
          rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
          -- goal: ↑((n+1)*n/2) * 2 = ↑((n+1)*n)
          rw [mul_comm]
          exact h2e
    _ = 1 := by
          field_simp [hN]
          push_cast
          ring

/-- For `0 ≤ ‖a‖`, the Fekete-root term of order `n+1` of the homothetic
set `a • K` equals `‖a‖` times that of `K` (all `n ≥ 1`; the exponent
`2/((n+1)n)` is exactly the one in `Step3.sym_maximality`). -/
lemma feketeRoot_scaling (K : Set ℂ) (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) (a : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (feketeNumber (homot a K) (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) =
      ‖a‖ * (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) := by
  classical
  let p : ℝ := 2 / (((n + 1 : ℝ)) * (n : ℝ))
  let e : ℕ := (n + 1) * n / 2
  have hF0 : 0 ≤ feketeNumber K (n + 1) := feketeNumber_nonneg hKne hKb (n + 1)
  have hscale : feketeNumber (homot a K) (n + 1) = ‖a‖ ^ e * feketeNumber K (n + 1) := by
    dsimp [e]
    exact feketeNumber_scaling K (n + 1) a hKne (feketeSet_bddAbove_of_bounded hKb (n + 1))
  have hep : (e : ℝ) * p = 1 := by
    dsimp [e, p]
    exact pairExp_mul n hn
  calc
    (feketeNumber (homot a K) (n + 1)) ^ p
        = (‖a‖ ^ e * feketeNumber K (n + 1)) ^ p := by rw [hscale]
    _ = (‖a‖ ^ e) ^ p * (feketeNumber K (n + 1)) ^ p := by
          exact Real.mul_rpow (pow_nonneg (norm_nonneg a) e) hF0
    _ = ‖a‖ * (feketeNumber K (n + 1)) ^ p := by
          -- (‖a‖^e)^p = ‖a‖^((e:ℝ) p) = ‖a‖
          have hpow : (‖a‖ ^ e) ^ p = ‖a‖ := by
            calc
              (‖a‖ ^ e) ^ p = (‖a‖ ^ ((e : ℝ))) ^ p := by
                rw [Real.rpow_natCast]
              _ = ‖a‖ ^ ((e : ℝ) * p) := by
                rw [← Real.rpow_mul (norm_nonneg a)]
              _ = ‖a‖ ^ (1 : ℝ) := by rw [hep]
              _ = ‖a‖ := by rw [Real.rpow_one]
          rw [hpow, mul_comm]
end Submission.Step3Scaling

end
