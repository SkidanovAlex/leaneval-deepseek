import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.PhiStar.Honesty

/-- A real number is at most its own square plus `1 / 2`:
`x ^ 2 + 1 / 2 - x = (x - 1 / 2) ^ 2 + 1 / 4 ≥ 0`. -/
private lemma self_le_sq_add_half (x : ℝ) : x ≤ x ^ 2 + 1 / 2 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

/-- If `1 ≤ y` then `|x| ^ 2 ≤ (x * y) ^ 2`. -/
private lemma abs_sq_le_mul_sq {x y : ℝ} (hy : 1 ≤ y) : |x| ^ 2 ≤ (x * y) ^ 2 := by
  rw [mul_pow, sq_abs]
  exact le_mul_of_one_le_right (sq_nonneg x) (by nlinarith [hy])

/-- The `i`-th term of the radial part of `HkIntegrand α 1 F` is dominated by the integrand
itself, for `i ≤ 1`. -/
private lemma extract_le_HkIntegrand {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ} {i : ℕ} (hi : i ≤ 1) :
    (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 F z θ := by
  rw [Work.Spaces.HkIntegrand]
  have hnn : 0 ≤ ∑ i ∈ Finset.range (1 + 1), ∑ j ∈ Finset.range (1 + 1),
      (if 1 ≤ i ∧ i + j ≤ 1 then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl _
  refine le_trans ?_ (le_add_of_nonneg_right hnn)
  exact Finset.single_le_sum
    (f := fun k => (Work.Spaces.DzIter k F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun k _ => sq_nonneg _) (by rw [Finset.mem_range]; omega)

theorem slice_pointwise_le {α a t : ℝ} {F : ℝ → ℝ → ℝ} (ha : 0 < a) (hat : a ≤ t) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2 ∧
      |Work.Spaces.pz F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hsinpos : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1]
    · have := Real.pi_pos; linarith [hθ.2]
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hw : 1 ≤ Work.Spaces.w t := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < t ^ 2)]
    nlinarith [sq_nonneg t]
  -- the weight `c = w t / sin(2θ)^(η/2)` occurring in the `HkIntegrand` is at least `1`
  set c : ℝ := Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hcdef
  have hc : 1 ≤ c := by
    rw [hcdef]
    exact (one_le_div hspos).mpr (le_trans hsle hw)
  set A : ℝ := Work.Spaces.HkIntegrand α 1 F t θ with hAdef
  -- the `i = 0` and `i = 1` summands of the `HkIntegrand`
  have hterm0 : (F t θ * c) ^ 2 ≤ A := by
    rw [hcdef, hAdef]
    simpa using extract_le_HkIntegrand (α := α) (F := F) (z := t) (θ := θ) (i := 0) (by norm_num)
  have hterm1 : (t * Work.Spaces.pz F t θ * c) ^ 2 ≤ A := by
    rw [hcdef, hAdef]
    have h := extract_le_HkIntegrand (α := α) (F := F) (z := t) (θ := θ) (i := 1) (by norm_num)
    rw [show Work.Spaces.DzIter 1 F t θ = t * Work.Spaces.pz F t θ from rfl] at h
    exact h
  constructor
  · -- first conjunct: `|F t θ| ≤ F² ≤ HkIntegrand`
    have hsq : |F t θ| ^ 2 ≤ (F t θ * c) ^ 2 := abs_sq_le_mul_sq hc
    have hlin : |F t θ| ≤ |F t θ| ^ 2 + 1 / 2 := self_le_sq_add_half _
    linarith
  · -- second conjunct: `|∂_z F t θ| ≤ (t/a)²·c²·(∂_z F)² ≤ HkIntegrand / a²`
    have hta : 1 ≤ t / a := (one_le_div ha).mpr hat
    have hd : 1 ≤ t / a * c := by nlinarith [hta, hc]
    have heq : (|Work.Spaces.pz F t θ| * (t / a * c)) ^ 2
        = (t * Work.Spaces.pz F t θ * c) ^ 2 / a ^ 2 := by
      simp only [mul_pow, sq_abs]
      rw [div_pow]
      ring
    have h2 : (|Work.Spaces.pz F t θ| * (t / a * c)) ^ 2 ≤ A / a ^ 2 := by
      rw [heq]
      exact div_le_div_of_nonneg_right hterm1 (by positivity)
    have hsq : |Work.Spaces.pz F t θ| ^ 2
        ≤ (|Work.Spaces.pz F t θ| * (t / a * c)) ^ 2 := by
      simpa using abs_sq_le_mul_sq (x := |Work.Spaces.pz F t θ|) hd
    have hlin : |Work.Spaces.pz F t θ| ≤ |Work.Spaces.pz F t θ| ^ 2 + 1 / 2 :=
      self_le_sq_add_half _
    linarith

end Work.FTS.PhiStar.Honesty
