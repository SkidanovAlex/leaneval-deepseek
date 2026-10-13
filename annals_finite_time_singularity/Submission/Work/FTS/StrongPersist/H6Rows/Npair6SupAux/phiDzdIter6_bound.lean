import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.NonlinRows.NRow10aux.phiSelfFacts
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.pz_aux
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.CoeffF0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology ContDiff
open Set Filter

/-!
# `|D_z^b (z/(1+z))| ≤ 10000` for `b ≤ 6` on `[0,∞)`

The multiplier `φ(z) = z/(1+z)` is smooth on `(-1,∞)`.  Writing `D_z = z ∂_z` and expanding
`D_z^b` in the Stirling numbers of the second kind,

    D_z^b φ = ∑_{k ≤ b} S(b,k) z^k ∂_z^k φ ,

while `z/(1+z) = 1 - (1+z)⁻¹` gives `∂_z^k φ = ± k! (1+z)^{-(k+1)}` for `k ≥ 1`, hence the
weighted slots obey `|z^k ∂_z^k φ(z)| ≤ k!` on `z ≥ 0`.  Therefore

    |D_z^b φ(z)| ≤ ∑_{k ≤ b} S(b,k) k! ,

and the numerical values of the last sum for `b ≤ 6` are `1, 1, 3, 13, 75, 541, 4683`,
all of them at most `10000`.
-/

/-- `z/(1+z)` is smooth (analytic) on `(-1,∞)`. -/
theorem contDiffOn_div_one_add : ContDiffOn ℝ ⊤ (fun z : ℝ => z / (1 + z)) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi (-1)) := by fun_prop
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => z) (Set.Ioi (-1)) := by fun_prop
  refine ContDiffOn.div hnum hden ?_
  intro z hz
  simp only [Set.mem_Ioi] at hz
  linarith

/-- The Stirling-weighted factorial mass `∑_{k ≤ b} S(b,k) k!` is at most `10000` for `b ≤ 6`
(the values being `1, 1, 3, 13, 75, 541, 4683`). -/
theorem scoef_fact_sum_le (b : ℕ) (hb : b ≤ 6) :
    (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (k.factorial : ℝ)) ≤ 10000 := by
  have hnat : (∑ k ∈ Finset.range (b + 1), Work.Spaces.scoef b k * k.factorial) ≤ 10000 := by
    interval_cases b <;> decide
  exact_mod_cast hnat

/-- The weighted derivative slots of `z/(1+z)`: `|z^k ∂_z^k (z/(1+z))| ≤ k!` for `z ≥ 0`. -/
theorem zpow_iteratedDeriv_div_le (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |z ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z| ≤ (k.factorial : ℝ) := by
  have h1z : 0 < 1 + z := by linarith
  have hge : 0 ≤ z / (1 + z) := div_nonneg hz h1z.le
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have hfac : ((0 : ℕ).factorial : ℝ) = 1 := by norm_num
    rw [iteratedDeriv_zero, pow_zero, one_mul, abs_of_nonneg hge, hfac]
    rw [div_le_one h1z]
    linarith
  · have hz1 : -1 < z := by linarith
    have hw := Work.FTS.PhiStar.StarPkgo2Aux.weighted_iteratedDeriv_div k hk z hz1
    have hzle : |z| ^ k ≤ (z + 1) ^ k := by
      rw [abs_of_nonneg hz]
      exact pow_le_pow_left₀ hz (by linarith) k
    have h2 : |z| ^ k * |iteratedDeriv k (fun z : ℝ => z / (1 + z)) z|
        ≤ (z + 1) ^ k * |iteratedDeriv k (fun z : ℝ => z / (1 + z)) z| :=
      mul_le_mul_of_nonneg_right hzle (abs_nonneg _)
    have h3 : (z + 1) ^ k * |iteratedDeriv k (fun z : ℝ => z / (1 + z)) z|
        = |(z + 1) ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
    have h4 : |(z + 1) ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z|
        = (k.factorial : ℝ) * (1 + z)⁻¹ := by
      rw [hw, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg k.factorial),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z)⁻¹)]
    have h5 : (k.factorial : ℝ) * (1 + z)⁻¹ ≤ (k.factorial : ℝ) := by
      have hle : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ 1 + z)
      have := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg k.factorial : (0 : ℝ) ≤ (k.factorial : ℝ))
      simpa using this
    rw [abs_mul, abs_pow]
    linarith [h2, h3.le, h3.ge, h4.le, h4.ge, h5]

theorem phiDzdIter6_bound (b : ℕ) (hb : b ≤ 6) (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z| ≤ 10000 := by
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have h0 := zpow_iteratedDeriv_div_le 0 z hz
    have h0' : |(fun z : ℝ => z / (1 + z)) z| ≤ 1 := by simpa using h0
    simp only [Work.Elliptic.DzdIter_zero]
    linarith
  · have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have hz' : z ∈ Set.Ioi (-1) := by
      simp only [Set.mem_Ioi]
      linarith
    have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
        ContDiffOn ℝ ⊤ (fun z' => (fun z _ : ℝ => z / (1 + z)) z' θ) (Set.Ioi (-1)) :=
      fun θ _ => contDiffOn_div_one_add
    have hDz : Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z
        = Work.Spaces.DzIter b (fun z _ : ℝ => z / (1 + z)) z 0 :=
      (Work.Elliptic.DzIter_rad (fun z : ℝ => z / (1 + z)) b z 0).symm
    rw [hDz, Work.Spaces.DzIter_eq_sum_scoef hsmooth b z hz' 0 h0I]
    have hterm : ∀ k ∈ Finset.range (b + 1),
        |(Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k
            (fun z _ : ℝ => z / (1 + z)) z 0)|
          ≤ (Work.Spaces.scoef b k : ℝ) * (k.factorial : ℝ) := by
      intro k hk
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef b k))]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (Work.Spaces.scoef b k))
      rw [Work.Spaces.pzIter_eq_iteratedDeriv k (fun z _ : ℝ => z / (1 + z)) z 0]
      exact zpow_iteratedDeriv_div_le k z hz
    calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (z ^ k *
            Work.Spaces.pzIter k (fun z _ : ℝ => z / (1 + z)) z 0)|
        ≤ ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (k.factorial : ℝ) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
      _ ≤ 10000 := scoef_fact_sum_le b hb

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
