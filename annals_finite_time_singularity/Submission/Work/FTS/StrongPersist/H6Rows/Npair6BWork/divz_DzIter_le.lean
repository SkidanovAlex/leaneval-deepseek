import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.CoeffF0
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open Set Filter

/-!
# `|D_z^b (z/(1+z))| ≤ 10^6 · z/(1+z)` for `b ≤ 6`

`D_z = z ∂_z` expands in terms of the ordinary derivatives as
`D_z^b φ = ∑_{k ≤ b} S(b,k) z^k ∂_z^k φ` (`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`),
where `S(b,k)` is the Stirling number of the second kind.  For `φ(z) = z/(1+z) = t`
the two ingredients are

* `|z^k ∂_z^k φ| ≤ k! · t` for `k ≤ 6` (the closed form of `∂_z^k φ` is
  `(-1)^{k-1} k! / (1+z)^{k+1}`, so `|z^k ∂_z^k φ| = k! z^k/(1+z)^{k+1} ≤ k! t`),
* `∑_k S(b,k) = bell b ≤ 1000` for `b ≤ 6` (Bell numbers `1,1,2,5,15,52,203`).

Hence `|D_z^b φ| ≤ 1000 · 720 · t ≤ 10^6 · t`.
-/

/-- `z ↦ z/(1+z)` is `C^∞` (in the honest smooth order) on `(0,∞)`. -/
private lemma contDiffOn_divz :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (1 + z)) (Set.Ioi 0) := by
  refine ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
  positivity

/-- `k! · z^k/(1+z)^{k+1} ≤ 720 · z/(1+z)` for `1 ≤ k ≤ 6`, `z > 0`. -/
private lemma fact_div_le (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (z : ℝ) (hz : 0 < z) :
    (k.factorial : ℝ) * z ^ k / (1 + z) ^ (k + 1) ≤ 720 * (z / (1 + z)) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (k.factorial : ℝ) ≤ 720 := by
    have h : k.factorial ≤ 720 := by interval_cases k <;> norm_num
    exact_mod_cast h
  have hzk : z ^ k = z * z ^ (k - 1) := by
    nth_rewrite 1 [show k = (k - 1) + 1 from by omega]
    rw [pow_succ']
  have hzpk : z ^ (k - 1) ≤ (1 + z) ^ k := by
    calc z ^ (k - 1) ≤ (1 + z) ^ (k - 1) := pow_le_pow_left₀ hz.le (by linarith) (k - 1)
      _ ≤ (1 + z) ^ k := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (by omega)
  have hkey : (k.factorial : ℝ) * (z * z ^ (k - 1)) ≤ 720 * (z * (1 + z) ^ k) := by
    calc (k.factorial : ℝ) * (z * z ^ (k - 1)) = z * ((k.factorial : ℝ) * z ^ (k - 1)) := by ring
      _ ≤ z * (720 * (1 + z) ^ k) := by
          refine mul_le_mul_of_nonneg_left ?_ hz.le
          calc (k.factorial : ℝ) * z ^ (k - 1) ≤ 720 * z ^ (k - 1) :=
                mul_le_mul_of_nonneg_right hfac (pow_nonneg hz.le _)
            _ ≤ 720 * (1 + z) ^ k := mul_le_mul_of_nonneg_left hzpk (by norm_num)
      _ = 720 * (z * (1 + z) ^ k) := by ring
  have hpow : (1 + z) ^ (k + 1) = (1 + z) ^ k * (1 + z) := pow_succ _ _
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ (k + 1))]
  rw [show 720 * (z / (1 + z)) * (1 + z) ^ (k + 1) = 720 * (z * (1 + z) ^ k) from by
    rw [hpow]
    field_simp]
  rw [hzk]
  exact hkey

/-- The closed form of `∂_z^k (z/(1+z))`: for `k ≥ 1`,
`∂_z^k (z/(1+z)) = (-1)^{k-1} k!/(1+z)^{k+1}`. -/
private lemma pzIter_divz_closed (k : ℕ) (hk1 : 1 ≤ k) (z θ : ℝ) (hz : 0 < z) :
    Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ
      = (-1 : ℝ) ^ (k - 1) * (k.factorial : ℝ) / (1 + z) ^ (k + 1) := by
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.FTS.NonlinRows.pzIter_radial_fn (fun z => z / (1 + z)) k z θ]
  exact Work.FTS.NonlinRows.iter_deriv_u15_pos k hk1 z hz1

/-- `|z^k ∂_z^k (z/(1+z))| ≤ 720 · z/(1+z)` for `1 ≤ k ≤ 6`, `z > 0`. -/
private lemma pzIter_divz_bound (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (z θ : ℝ) (hz : 0 < z) :
    |z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ| ≤ 720 * (z / (1 + z)) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [pzIter_divz_closed k hk1 z θ hz]
  have habs : |z ^ k * ((-1 : ℝ) ^ (k - 1) * (k.factorial : ℝ) / (1 + z) ^ (k + 1))|
      = (k.factorial : ℝ) * z ^ k / (1 + z) ^ (k + 1) := by
    rw [show z ^ k * ((-1 : ℝ) ^ (k - 1) * (k.factorial : ℝ) / (1 + z) ^ (k + 1))
        = (-1 : ℝ) ^ (k - 1) * ((k.factorial : ℝ) * z ^ k / (1 + z) ^ (k + 1)) from by ring]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (by positivity)
  rw [habs]
  exact fact_div_le k hk1 hk6 z hz

/-- The `k = 0` case of the weighted bound. -/
private lemma pzIter_divz_bound_zero (z θ : ℝ) (hz : 0 < z) :
    |z ^ 0 * Work.Spaces.pzIter 0 (fun z _ => z / (1 + z)) z θ| ≤ 720 * (z / (1 + z)) := by
  have ht : 0 < z / (1 + z) := by positivity
  simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
  rw [abs_of_pos ht]
  linarith

/-- The Bell numbers of the rows `b ≤ 6` are `1,1,2,5,15,52,203`, all `≤ 1000`. -/
private lemma bell_le_1000 (b : ℕ) (hb : b ≤ 6) : Work.Spaces.bell b ≤ 1000 := by
  interval_cases b <;> decide

theorem divz_DzIter_le :
    ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ 1000000 * (z / (1 + z)) := by
  intro b hb z θ hz
  have ht : 0 ≤ z / (1 + z) := by positivity
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' : ℝ => (fun z _ => z / (1 + z)) z' θ) (Set.Ioi 0) := contDiffOn_divz
  rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := fun z _ => z / (1 + z)) (θ := θ)
    hsmooth b z hz]
  have hbound : ∀ k ≤ b,
      |z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ| ≤ 720 * (z / (1 + z)) := by
    intro k hk
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      exact pzIter_divz_bound_zero z θ hz
    · exact pzIter_divz_bound k (Nat.one_le_iff_ne_zero.mpr hk0) (le_trans hk hb) z θ hz
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (720 * (z / (1 + z)))
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ) hbound
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by
    exact_mod_cast bell_le_1000 b hb
  calc |∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * (720 * (z / (1 + z))) := hsum
    _ ≤ 1000 * (720 * (z / (1 + z))) := mul_le_mul_of_nonneg_right hbell (by positivity)
    _ = 720000 * (z / (1 + z)) := by ring
    _ ≤ 1000000 * (z / (1 + z)) := mul_le_mul_of_nonneg_right (by norm_num) ht

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
