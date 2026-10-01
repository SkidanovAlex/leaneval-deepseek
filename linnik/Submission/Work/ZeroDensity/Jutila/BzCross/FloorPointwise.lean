import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs

namespace Work.ZeroDensity.Jutila.BzCross

/-- `|s3c c| ≤ 1`: the density `s3c c = ζ(2)⁻¹∏_{p | c} p/(p+1)` of the squarefree integers
coprime to `c` has absolute value at most `1` (indeed `0 ≤ s3c c ≤ 1`, as `ζ(2) = π²/6 > 1` and
every factor `p/(p+1)` lies in `(0,1]`). -/
private lemma s3c_abs_le_one (c : ℕ) : |LinnikAreas.Density4.BzS3.s3c c| ≤ 1 := by
  have hnn : (0:ℝ) ≤ LinnikAreas.Density4.BzS3.s3c c := by
    unfold LinnikAreas.Density4.BzS3.s3c
    have h2 : 0 ≤ ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1) :=
      Finset.prod_nonneg (fun p hp => by positivity)
    positivity
  have hle : LinnikAreas.Density4.BzS3.s3c c ≤ 1 := by
    unfold LinnikAreas.Density4.BzS3.s3c
    have hpi : (1:ℝ) < Real.pi ^ 2 / 6 := by
      have h3 := Real.pi_gt_three
      nlinarith [Real.pi_pos]
    have hinv : (Real.pi ^ 2 / 6)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      linarith
    have hprod : ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp; positivity
      · intro p hp
        rw [div_le_one (by positivity)]
        linarith
    have hprod0 : (0:ℝ) ≤ ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1) :=
      Finset.prod_nonneg (fun p hp => by positivity)
    calc (Real.pi ^ 2 / 6)⁻¹ * ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)
        ≤ 1 * 1 := mul_le_mul hinv hprod hprod0 (by norm_num)
      _ = 1 := by norm_num
  rw [abs_of_nonneg hnn]; exact hle

/-- **Floor error of the `log`-quadratic main term, without the density factor.**
For reals `m x α β` with `1 ≤ m ≤ x < m+1` and `u = log x − α ≥ 0`, `v = log x − β ≥ 0`,

  `|x·B(x) − m·B(m)| ≤ 6·(u+1)(v+1)`,  where `B(z) = (log z − α − 1)(log z − β − 1) + 1`.

Writing `δ = x − m ∈ [0,1)` and `ε = log x − log m ≥ 0` (so that `m·ε ≤ δ`, by `log t ≤ t−1`
applied to `t = x/m`, and hence `ε ≤ m·ε ≤ 1`),

  `x·B(x) − m·B(m) = δ·B(x) + m·(B(x) − B(m))` and `B(x) − B(m) = ε·(u + v − ε − 2)`.

Since `B(x) = (u−1)(v−1) + 1` and `B(m) = (u−ε−1)(v−ε−1) + 1`, the two pieces are bounded by
`|B(x)| ≤ (u+1)(v+1) + 1` and `|u+v−ε−2| ≤ |u+v−2| + ε ≤ (u+1)(v+1) + 1 + ε`, and
`ε ≤ 1 ≤ (u+1)(v+1)`, giving the total `≤ 4(u+1)(v+1) + 3 ≤ 6(u+1)(v+1)`. -/
private lemma floor_log_poly_error (m x α β : ℝ) (hm1 : 1 ≤ m) (hmx : m ≤ x)
    (hxm : x < m + 1)
    (hu : 0 ≤ Real.log x - α) (hv : 0 ≤ Real.log x - β) :
    |x * ((Real.log x - α - 1) * (Real.log x - β - 1) + 1)
      - m * ((Real.log m - α - 1) * (Real.log m - β - 1) + 1)|
      ≤ 6 * (Real.log x - α + 1) * (Real.log x - β + 1) := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm1
  have hx0 : 0 < x := lt_of_lt_of_le hm0 hmx
  set u : ℝ := Real.log x - α with hu_def
  set v : ℝ := Real.log x - β with hv_def
  set e : ℝ := Real.log x - Real.log m with he_def
  have hu0 : 0 ≤ u := by rw [hu_def]; exact hu
  have hv0 : 0 ≤ v := by rw [hv_def]; exact hv
  have he0 : 0 ≤ e := by
    rw [he_def]
    exact sub_nonneg.mpr (Real.log_le_log hm0 hmx)
  have hmα : Real.log m - α = u - e := by rw [hu_def, he_def]; ring
  have hmβ : Real.log m - β = v - e := by rw [hv_def, he_def]; ring
  have hme : m * e ≤ x - m := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hm0)
    rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hm0)] at h
    rw [he_def]
    have h2 : m * (x / m - 1) = x - m := by
      rw [mul_sub, mul_div_cancel₀ x (ne_of_gt hm0)]; ring
    nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt hm0), h2]
  have hδl : 0 ≤ x - m := by linarith
  have hδu : x - m < 1 := by linarith
  have he1 : e ≤ 1 := by
    have h1 : e ≤ m * e := by nlinarith [hm1, he0]
    linarith
  have hBx_bound : |(u - 1) * (v - 1) + 1| ≤ (u + 1) * (v + 1) + 1 := by
    rw [abs_le]; constructor <;> nlinarith [hu0, hv0]
  have hsum_bound : |u + v - 2| ≤ (u + 1) * (v + 1) + 1 := by
    rw [abs_le]; constructor <;> nlinarith [hu0, hv0]
  have he_bound : |u + v - e - 2| ≤ |u + v - 2| + e := by
    have h : u + v - e - 2 = (u + v - 2) + (-e) := by ring
    rw [h]
    calc |(u + v - 2) + (-e)| ≤ |u + v - 2| + |-e| := abs_add_le _ _
      _ = |u + v - 2| + e := by rw [abs_neg, abs_of_nonneg he0]
  have huv : 1 ≤ (u + 1) * (v + 1) := by nlinarith [mul_nonneg hu0 hv0]
  have hexp : (m + (x - m)) * ((u - 1) * (v - 1) + 1) - m * ((u - e - 1) * (v - e - 1) + 1)
      = (x - m) * ((u - 1) * (v - 1) + 1) + m * e * (u + v - e - 2) := by ring
  rw [show x = m + (x - m) by ring, hmα, hmβ, hexp]
  calc |(x - m) * ((u - 1) * (v - 1) + 1) + m * e * (u + v - e - 2)|
      ≤ |(x - m) * ((u - 1) * (v - 1) + 1)| + |m * e * (u + v - e - 2)| := abs_add_le _ _
    _ ≤ |(u - 1) * (v - 1) + 1| + |u + v - e - 2| := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg hδl]
          exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
        · rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ m * e)]
          calc (m * e) * |u + v - e - 2| ≤ 1 * |u + v - e - 2| :=
                mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
            _ = |u + v - e - 2| := one_mul _
    _ ≤ 6 * (u + 1) * (v + 1) := by
        nlinarith [hBx_bound, hsum_bound, he_bound, he1, huv]

/-- **Pointwise floor error of the `czMain` main term.**
For real `x ≥ 1` with `m = ⌊x⌋₊`, integer `c`, reals `α β`, and `u = log x − α ≥ 0`,
`v = log x − β ≥ 0`:
`|czMain c α β m − czMain c α β x| ≤ 6·(u+1)(v+1)`,
where `czMain c α β z = s3c c · z · ((log z − α − 1)(log z − β − 1) + 1)`.
ROUTE: `|s3c c| ≤ 1` (`s3c c = (π²/6)⁻¹∏_{p|c} p/(p+1)`, each factor in `(0,1]`). Put
`B(z) = (log z − α − 1)(log z − β − 1) + 1` and `ε = log x − log m ∈ [0, log 2]` (since
`m ≤ x < m+1` and `m ≥ 1` give `1 ≤ x/m ≤ 2`). Then
`x·B(x) − m·B(m) = (x−m)·B(x) + m·(B(x)−B(m))`, with `|x−m| ≤ 1`, `|B(x)| ≤ (u+1)(v+1)+1`,
`B(x) − B(m) = ε·(u+v−2−ε)`, and `m·ε ≤ x − m ≤ 1` (as `log y ≤ y−1` for `y = x/m > 0`).
Hence `|x·B(x) − m·B(m)| ≤ 6(u+1)(v+1)` because `(u+1)(v+1) ≥ 1` and `ε ≤ log 2 ≤ 1`. -/
theorem FloorPointwise (c : ℕ) (α β x : ℝ) (hx : 1 ≤ x)
    (hu : 0 ≤ Real.log x - α) (hv : 0 ≤ Real.log x - β) :
    |czMain c α β ((⌊x⌋₊ : ℕ) : ℝ) - czMain c α β x|
      ≤ 6 * (Real.log x - α + 1) * (Real.log x - β + 1) := by
  set m : ℝ := ((⌊x⌋₊ : ℕ) : ℝ) with hm_def
  have hm1 : 1 ≤ m := by
    rw [hm_def]
    exact_mod_cast (Nat.one_le_floor_iff x).mpr hx
  have hmx : m ≤ x := by
    rw [hm_def]
    exact Nat.floor_le (by linarith)
  have hxm : x < m + 1 := by
    rw [hm_def]
    exact Nat.lt_floor_add_one x
  have hkey := floor_log_poly_error m x α β hm1 hmx hxm hu hv
  have hs3c : |LinnikAreas.Density4.BzS3.s3c c| ≤ 1 := s3c_abs_le_one c
  unfold czMain
  have hfac : LinnikAreas.Density4.BzS3.s3c c * m
        * ((Real.log m - α - 1) * (Real.log m - β - 1) + 1)
      - LinnikAreas.Density4.BzS3.s3c c * x
        * ((Real.log x - α - 1) * (Real.log x - β - 1) + 1)
      = LinnikAreas.Density4.BzS3.s3c c *
        (m * ((Real.log m - α - 1) * (Real.log m - β - 1) + 1)
         - x * ((Real.log x - α - 1) * (Real.log x - β - 1) + 1)) := by ring
  rw [hfac, abs_mul]
  calc |LinnikAreas.Density4.BzS3.s3c c| *
        |m * ((Real.log m - α - 1) * (Real.log m - β - 1) + 1)
         - x * ((Real.log x - α - 1) * (Real.log x - β - 1) + 1)|
      ≤ 1 * (6 * (Real.log x - α + 1) * (Real.log x - β + 1)) := by
        apply mul_le_mul hs3c _ (abs_nonneg _) (by norm_num)
        rw [abs_sub_comm]
        exact hkey
    _ = 6 * (Real.log x - α + 1) * (Real.log x - β + 1) := by ring

end Work.ZeroDensity.Jutila.BzCross
