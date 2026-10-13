/-
Copyright: work module for the Elgindi finite-time singularity project.

# A single mixed derivative is dominated by the `ℋ⁶`-integrand

`Work.FTS.StrongEps.LocUnif.mixed_sq_le_HkIntegrand`: for `j + i ≤ 6`, `z > 0` and
`sin(2θ) > 0` the square of the mixed derivative `D_z^j D_θ^i F` is dominated *pointwise*
by the integrand of the `ℋ⁶`-norm,

  `(D_z^j D_θ^i F (z,θ))² ≤ HkIntegrand α 6 F z θ`.

The mechanism is elementary and completely insensitive to `F`: `HkIntegrand α 6 F` is a
sum of squares (`Work.Spaces.HkIntegrand_nonneg`), so it is at least any one of the terms
`Work.Spaces.sq_le_HkIntegrand_z` / `Work.Spaces.sq_le_HkIntegrand_mixed`; and the weight
in front of that term is `≥ 1` on the region `z > 0`, `0 < sin(2θ) ≤ 1`:

* `w(z) = (1+z)²/z² ≥ 1` for `z > 0`;
* `w_θ(θ) = sin(2θ)^{-γ/2} ≥ 1` because `sin(2θ) ∈ (0,1]` and `γ = 1 + α/10 > 0`;
* hence `W = w·w_θ ≥ 1` and `w / sin(2θ)^{η/2} ≥ 1`.

For `i ≥ 1` the relevant atom of `HkIntegrand` is `(mixed j i F · W)²`, for `i = 0` it is
`(D_z^j F · w/sin^{η/2})²` (note `mixed j 0 F = D_z^j F`), and multiplying a real number
by a factor `≥ 1` can only increase its square.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## The weight bounds on the region `z > 0`, `sin(2θ) > 0` -/

/-- `w(z) = (1+z)²/z² ≥ 1` for `z > 0`. -/
private lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : 0 < z ^ 2 := by positivity
  rw [Work.Spaces.w, one_le_div hz2]
  calc z ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
    _ = (1 + z) ^ 2 := rfl

/-- `w_θ(θ) = sin(2θ)^{-γ/2} ≥ 1` for `0 < sin(2θ) ≤ 1` and `γ = gam α ≥ 0`. -/
private lemma one_le_wTheta {α θ : ℝ} (hα : 0 < α) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.wTheta α θ := by
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(Work.Spaces.gam α / 2) ≤ 0 := by
    have h := Work.Spaces.gam_pos hα
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hsin hsin1 hexp
  rwa [Real.rpow_zero] at h

/-- The product weight `W = w·w_θ` is `≥ 1`: both factors are. -/
private lemma one_le_Wt {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) : 1 ≤ Work.Spaces.Wt α z θ := by
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  have h2 : 1 ≤ Work.Spaces.wTheta α θ := one_le_wTheta hα hsin
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Work.Spaces.w z * Work.Spaces.wTheta α θ :=
        mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
    _ = Work.Spaces.Wt α z θ := rfl

/-- The `η`-weight `w(z)/sin(2θ)^{η/2}` is `≥ 1`. -/
private lemma one_le_w_div_sin_eta {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le hs1 (by norm_num [Work.Spaces.eta])
  rw [one_le_div hspos]
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  linarith

/-- If `1 ≤ M` then `A² ≤ (A·M)²`. -/
private lemma sq_le_sq_mul_of_one_le {A M : ℝ} (hM : 1 ≤ M) : A ^ 2 ≤ (A * M) ^ 2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have h : |A| ≤ |A * M| := by
    rw [abs_mul, abs_of_pos hMpos]
    nlinarith [abs_nonneg A]
  exact sq_le_sq.mpr h

/-! ## The lemma -/

theorem mixed_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) (j i : ℕ) (hji : j + i ≤ 6)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed j i F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 F z θ := by
  by_cases hi1 : 1 ≤ i
  · have h1 : 1 ≤ Work.Spaces.Wt α z θ := one_le_Wt hα hz hsin
    have h2 : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 F z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 F z θ i j hi1 (by omega)
    exact le_trans (sq_le_sq_mul_of_one_le h1) h2
  · have hi0 : i = 0 := by omega
    have h3 : (Work.Spaces.DzIter j F z θ) ^ 2
        ≤ (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      sq_le_sq_mul_of_one_le (one_le_w_div_sin_eta hz hsin)
    have h4 : (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 F z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 6 F z θ j (by omega)
    have h5 : Work.Spaces.mixed j i F = Work.Spaces.DzIter j F := by
      rw [hi0]
      simp
    rw [h5]
    exact le_trans h3 h4

end Work.FTS.StrongEps.LocUnif
