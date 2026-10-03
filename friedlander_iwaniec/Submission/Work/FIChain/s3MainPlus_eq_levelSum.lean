import Mathlib
import Submission.Work.FIChain.s3MainLevelDefs
import Submission.Work.FIChain.s3MainLevelAux
import Submission.Work.FIChain.s3MPPhi_eq_integral_T
import Submission.Work.FIChain.sum_T_eq_levelSum

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Un-merging the outer index.**  Writing `ℓ = b·e` turns the divisor weight
`Σ_{b | ℓ, sy < b} μ b` into an interval sum over a fresh variable `b`. -/
lemma s3MainPlus_eq_unmerged (lam : ℕ → ℝ) (x : ℕ) (z sy sz : ℝ) (Cm : ℕ) (hz : 1 ≤ z) :
    s3MainPlus lam x z sy sz Cm
      = ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) * ∑ e ∈ Finset.Icc 1 x, s3MPF lam x z sz Cm (b * e) := by
  have hF : ∀ ℓ, x < ℓ → s3MPF lam x z sz Cm ℓ = 0 := by
    intro ℓ hℓ
    rw [s3MPF, if_neg]
    intro hP
    have hlt : (x : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    have hle : (ℓ : ℝ) ≤ (ℓ : ℝ) * z := by
      have := mul_le_mul_of_nonneg_left hz (show (0 : ℝ) ≤ (ℓ : ℝ) by positivity)
      simpa using this
    linarith
  have h1 : s3MainPlus lam x z sy sz Cm
      = ∑ ℓ ∈ Finset.Icc 1 x, (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * s3MPF lam x z sz Cm ℓ := by
    rw [s3MainPlus]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [s3MPF]
    by_cases hP : ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ)
    · rw [if_pos hP, if_pos hP]; ring
    · rw [if_neg hP, if_neg hP, mul_zero]
  rw [h1, sum_divisors_reindex (s3MPF lam x z sz Cm) x sy hF]

/-- **The comparison, Step B.**  For `n ≤ x` the level sum `K(n)` is the `(b,e)`-reindexing of the
`n`-summands `s3MPPhi n b e`. -/
lemma levelSum_eq_sum_Phi (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ)
    (hx : 1 ≤ x) (hCm : 1 ≤ Cm) (hz : 1 ≤ z) (hCmsz : (Cm : ℝ) ≤ sz)
    (hn : n ∈ Finset.Icc 1 x) :
    ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
        ∑ e ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius b : ℝ) * s3MPPhi lam x z sz Cm n b e
      = s3MainLevelSum lam x z sz Cm sy n := by
  have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
  have hszpos : (0 : ℝ) < sz / (Cm : ℝ) := by
    have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast hCm
    have hsz0 : (0 : ℝ) < sz := by linarith
    exact div_pos hsz0 hCmpos
  have hint : ∀ p ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)) ×ˢ Finset.Icc 1 x,
      IntervalIntegrable (fun u : ℝ =>
        (ArithmeticFunction.moebius p.1 : ℝ) * s3MPT lam x z sz Cm n p.1 p.2 u)
        volume (1 : ℝ) (sz / (Cm : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1
    obtain ⟨he1, -⟩ := Finset.mem_Icc.mp hp2
    have hCp : (0 : ℝ) < (p.1 : ℝ) * (p.2 : ℝ) * (Cm : ℝ) := by positivity
    refine (intervalIntegrable_mul_bdd_mul_floorSum_div
      (fun d => (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((p.1 * p.2) * d))
      (fun u : ℝ => if ((p.1 : ℝ) * (p.2 : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then (1 : ℝ) else 0)
      ((ArithmeticFunction.moebius p.1 : ℝ) * (if ((p.1 : ℝ) * (p.2 : ℝ) * z ≤ (x : ℝ)) then 1 else 0)
        * (if ((p.1 : ℝ) * (p.2 : ℝ) * z < (n : ℝ)) then 1 else 0)
        * (if ((n : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) * sz) then 1 else 0)
        * (if (n ≤ x) then 1 else 0) * Submission.ASP.rhoOf lam (p.1 * p.2))
      (1 : ℝ) (sz / (Cm : ℝ)) ?_ ?_ (by norm_num) hszpos).congr (fun u _ => ?_)
    · have hs : MeasurableSet {u : ℝ | (p.1 : ℝ) * (p.2 : ℝ) * (Cm : ℝ) * u < (n : ℝ)} :=
        (continuous_const.mul continuous_id).measurable measurableSet_Iio
      exact Measurable.ite hs measurable_const measurable_const
    · intro u
      by_cases h : ((p.1 : ℝ) * (p.2 : ℝ) * (Cm : ℝ) * u < (n : ℝ)) <;> simp [h]
    · simp only [s3MPT]
      ring
  have hpush : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
        ∑ e ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius b : ℝ) * s3MPPhi lam x z sz Cm n b e)
      = ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
          ∑ e ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius b : ℝ) * s3MPT lam x z sz Cm n b e u := by
    have h1 : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
          ∑ e ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius b : ℝ) * s3MPPhi lam x z sz Cm n b e)
        = ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)), ∑ e ∈ Finset.Icc 1 x,
            ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), (ArithmeticFunction.moebius b : ℝ) *
              s3MPT lam x z sz Cm n b e u := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      refine Finset.sum_congr rfl (fun e he => ?_)
      obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
      obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
      rw [s3MPPhi_eq_integral_T lam x z sz Cm n b e hx hCm hb1 he1 hz hCmsz hnx,
          intervalIntegral.integral_const_mul]
    have hprod : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)), ∑ e ∈ Finset.Icc 1 x,
            ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), (ArithmeticFunction.moebius b : ℝ) *
              s3MPT lam x z sz Cm n b e u)
        = ∑ p ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)) ×ˢ Finset.Icc 1 x,
            ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), (ArithmeticFunction.moebius p.1 : ℝ) *
              s3MPT lam x z sz Cm n p.1 p.2 u := by
      rw [Finset.sum_product]
    rw [h1, hprod, ← intervalIntegral.integral_finsetSum hint]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [Finset.sum_product]
  rw [hpush, s3MainLevelSum_eq_integral]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  refine (Finset.sum_congr rfl (fun b _ => ?_)).trans (sum_T_eq_levelSum lam x z sz Cm sy n u hn)
  rw [Finset.mul_sum]

/-- **Reindexing the `λ⁺`-main half as a level sum.**  With
`K(n) = s3MainLevelSum lam x z sz Cm sy n` (see `Submission.Work.FIChain.s3MainLevelDefs`),
`s3MainPlus lam x z sy sz Cm = Σ_{n ∈ Icc 1 x} ã(n)·K(n)`.

Route: (1) `Work.FIChain.sum_divisors_reindex` un-merges
`Σ_{ℓ ∈ Icc 1 x}(Σ_{b | ℓ, sy < b} μ b)·F ℓ` into `Σ_{b ∈ (Icc 1 x).filter (sy < ·)} μ b ·
Σ_{e ∈ Icc 1 x} F (b*e)` (its support hypothesis holds because `z ≥ 1`, so `ℓ > x` gives
`ℓ·z > x`).  (2) `Ã(m₁) − Ã(m₂) = Σ_{n ∈ Icc (m₂+1) m₁} ã(n)` with
`m₁ = ⌊min (ℓ sz) x⌋₊`, `m₂ = ⌊max (ℓ z) (ℓ Cm u)⌋₊`, using `Work.FIChain.sum_atilc_Icc_eq`
(`Ã(k) = Σ_{n ≤ k} ã(n)`) and `m₂ ≤ m₁` (from `z ≤ sz`, `u ≤ sz/Cm` and `ℓ z ≤ x`).
(3) swap the finite `n`-sum with the `u`-integral
(`intervalIntegral.integral_finsetSum`) and rewrite the `u`-range `[1, U_ℓ]`,
`U_ℓ = min (sz/Cm) (x/(ℓ Cm))`, as `[1, sz/Cm]` subject to the pointwise constraints
`d ≤ ⌊u⌋₊`, `ℓ·Cm·u < n` and `ℓ·Cm·u ≤ x`; the last is implied by `ℓ·Cm·u < n ≤ x`, and for
`u > U_ℓ` the `n`-window is empty (or `⌊u⌋₊ = 0`) so that the two integrals agree. -/
theorem s3MainPlus_eq_levelSum (lam : ℕ → ℝ) (x : ℕ) (z sy sz : ℝ) (Cm : ℕ)
    (hx : 1 ≤ x) (hCm : 1 ≤ Cm) (hz : 1 ≤ z) (hzsz : z ≤ sz)
    (hCmsz : (Cm : ℝ) ≤ sz) (hCmz : (Cm : ℝ) ≤ z) :
    Work.FIChain.s3MainPlus lam x z sy sz Cm
      = ∑ n ∈ Finset.Icc 1 x, Work.FIChain.atilc n
          * Work.FIChain.s3MainLevelSum lam x z sz Cm sy n := by
  rw [s3MainPlus_eq_unmerged lam x z sy sz Cm hz]
  have h2 : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ) * ∑ e ∈ Finset.Icc 1 x, s3MPF lam x z sz Cm (b * e))
      = ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ) *
        ∑ e ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, atilc n * s3MPPhi lam x z sz Cm n b e := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun e he => ?_)
    obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
    exact s3MPF_be_eq_sum_Phi lam x z sz Cm b e hb1 he1 hx hCm hz hzsz hCmsz hCmz
  rw [h2]
  have hswap : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ) *
        ∑ e ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, atilc n * s3MPPhi lam x z sz Cm n b e)
      = ∑ n ∈ Finset.Icc 1 x, atilc n *
          ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
            ∑ e ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius b : ℝ) * s3MPPhi lam x z sz Cm n b e := by
    have L1 : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
          ∑ e ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, atilc n * s3MPPhi lam x z sz Cm n b e)
        = ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
            ∑ e ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
              (ArithmeticFunction.moebius b : ℝ) * (atilc n * s3MPPhi lam x z sz Cm n b e) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.mul_sum]
    have L2 : (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
            ∑ e ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
              (ArithmeticFunction.moebius b : ℝ) * (atilc n * s3MPPhi lam x z sz Cm n b e))
        = ∑ n ∈ Finset.Icc 1 x, ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
            ∑ e ∈ Finset.Icc 1 x,
              (ArithmeticFunction.moebius b : ℝ) * (atilc n * s3MPPhi lam x z sz Cm n b e) := by
      rw [Finset.sum_comm]
      trans ∑ e ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
          ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ) * (atilc n * s3MPPhi lam x z sz Cm n b e)
      · exact Finset.sum_congr rfl (fun e _ => Finset.sum_comm)
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
    have L3 : (∑ n ∈ Finset.Icc 1 x, ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
            ∑ e ∈ Finset.Icc 1 x,
              (ArithmeticFunction.moebius b : ℝ) * (atilc n * s3MPPhi lam x z sz Cm n b e))
        = ∑ n ∈ Finset.Icc 1 x, atilc n *
            ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
              ∑ e ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius b : ℝ) * s3MPPhi lam x z sz Cm n b e := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    exact L1.trans (L2.trans L3)
  rw [hswap]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [levelSum_eq_sum_Phi lam x z sz Cm sy n hx hCm hz hCmsz hn]

end

end Work.FIChain
