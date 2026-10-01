import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3MainTermDefs

/-!
# Elementary estimates for the `S₃` route-A assembly (`JutilaPieces/S3RouteEstimates`)

Two purely elementary (real-analysis) estimates used by the route-A proof of
`S3MainTermClaim`:

* `S3LogSumBound` — `Σ_{r ≤ ⌊x⌋} (1 + log(x/r)) ≤ 3x` for `x ≥ 1`.  This is the bound that turns
  the pointwise floor/bracket estimate `s3floor_pointwise` into an `O(N)` total error: the double
  sum `Σ_{r,t}(1 + log(x/r))(1 + log(x/t))` factors as `(Σ_r(1 + log(x/r)))² ≤ 9x²`.
  Proof: `Σ_{r ≤ m} log(x/r) = m log x − log m!` together with Stirling's lower bound
  `log m! ≥ m log m − m` and `x/m ≤ 2` (since `m = ⌊x⌋`).

* `S3PhiSmall` — for `1 ≤ x < 2` (so `⌊x⌋ = 1`) one has `|Φ(x) − 1| ≤ 1`, `Φ` being the double
  sum of `S3MainTermDefs`.  Needed for the `q`'s with `N/(qz) < 2`, where the asymptotic
  `|Φ − 1| ≤ C/log²` is not available.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

private lemma prod_Icc_id_factorial (m : ℕ) : (∏ r ∈ Finset.Icc 1 m, r) = m.factorial := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 m, Finset.prod_Ico_eq_prod_range]
  rw [show m + 1 - 1 = m from by omega]
  rw [Nat.factorial_eq_prod_range_add_one]
  apply Finset.prod_congr rfl; intro i _; ring

private lemma sum_Icc_log_eq_log_factorial (m : ℕ) :
    (∑ r ∈ Finset.Icc 1 m, Real.log (r : ℝ)) = Real.log (m.factorial : ℝ) := by
  rw [← Real.log_prod (fun r hr => by have := (Finset.mem_Icc.mp hr).1; positivity)]
  congr 1
  rw [← Nat.cast_prod]
  exact_mod_cast prod_Icc_id_factorial m

/-- `Σ_{r ≤ ⌊x⌋} (1 + log(x/r)) ≤ 3x` for `x ≥ 1`. -/
theorem S3LogSumBound (x : ℝ) (hx : 1 ≤ x) :
    (∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (1 + Real.log (x / (r : ℝ)))) ≤ 3 * x := by
  have hm1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hxpos : (0:ℝ) < x := by linarith
  have hmpos : (0:ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hstep1 : (∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (1 + Real.log (x / (r : ℝ))))
      = (⌊x⌋₊ : ℝ) + ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (r : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
    simp
  have hL : (∑ r ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (r : ℝ)))
      = (⌊x⌋₊ : ℝ) * Real.log x - Real.log ((⌊x⌋₊).factorial : ℝ) := by
    have h : ∀ r ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (r:ℝ)) = Real.log x - Real.log (r:ℝ) := by
      intro r hr
      have hrpos : (0:ℝ) < (r:ℝ) := by
        have := (Finset.mem_Icc.mp hr).1; exact_mod_cast (by omega : 0 < r)
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hrpos)]
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
    rw [sum_Icc_log_eq_log_factorial]
    push_cast
    ring
  rw [hstep1, hL]
  have hsterl : (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)
      ≤ Real.log ((⌊x⌋₊).factorial : ℝ) := by
    have h := Stirling.le_log_factorial_stirling (n := ⌊x⌋₊) (by omega)
    have h1 : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
    have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    linarith
  have hxm2 : x / (⌊x⌋₊ : ℝ) < 2 := by
    rw [div_lt_iff₀ hmpos]
    have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have : (1:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hm1
    linarith
  have hlog2 : Real.log (x / (⌊x⌋₊ : ℝ)) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (le_of_lt hxm2)
  have hmlog : (⌊x⌋₊ : ℝ) * Real.log (x / (⌊x⌋₊ : ℝ)) ≤ (⌊x⌋₊ : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 (le_of_lt hmpos)
  have hlogxm : Real.log x - Real.log (⌊x⌋₊ : ℝ) = Real.log (x / (⌊x⌋₊ : ℝ)) :=
    (Real.log_div (ne_of_gt hxpos) (ne_of_gt hmpos)).symm
  have hfloorx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)
    linarith
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hmpos, hfloorx, hmlog, hsterl, hlog2lt, hlog2nn,
    mul_nonneg (le_of_lt hmpos) hlog2nn]

/-- For `1 ≤ x < 2` (so `⌊x⌋ = 1`), `|Φ(x) − 1| ≤ 1`. -/
theorem S3PhiSmall (x : ℝ) (hx : 1 ≤ x) (hx2 : x < 2) : |s3Phi x - 1| ≤ 1 := by
  have hfloor : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith : (0:ℝ) ≤ x)]
    constructor <;> push_cast <;> linarith
  have hs3w1 : s3w 1 = 1 := by
    unfold s3w
    simp
  simp only [s3Phi, hfloor, Finset.Icc_self, Finset.sum_singleton, hs3w1]
  rw [if_pos (by decide : Nat.Coprime 1 1)]
  simp only [mul_one, one_mul, Nat.cast_one, div_one]
  have hpinv : (Real.pi ^ 2 / 6 : ℝ)⁻¹ = 6 / Real.pi ^ 2 := by rw [inv_div]
  rw [hpinv]
  have hb : (0:ℝ) ≤ Real.log x ∧ Real.log x ≤ Real.log 2 :=
    ⟨Real.log_nonneg hx, Real.log_le_log (by linarith) (by linarith)⟩
  have hbx : (Real.log x - 1) * (Real.log x - 1) + 1 ≤ 2 := by
    nlinarith [hb.1, hb.2, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hb0 : (0:ℝ) < 6 / Real.pi ^ 2 := by positivity
  have hb1 : 6 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hle : 6 / Real.pi ^ 2 * ((Real.log x - 1) * (Real.log x - 1) + 1) ≤ 2 := by
    nlinarith [hb0, hb1, hbx, Real.log_nonneg hx]
  have hge : 0 ≤ 6 / Real.pi ^ 2 * ((Real.log x - 1) * (Real.log x - 1) + 1) :=
    mul_nonneg (le_of_lt hb0) (by nlinarith [Real.log_nonneg hx])
  rw [abs_le]; constructor <;> linarith

end

end Work.LinnikAreas.JutilaPieces
