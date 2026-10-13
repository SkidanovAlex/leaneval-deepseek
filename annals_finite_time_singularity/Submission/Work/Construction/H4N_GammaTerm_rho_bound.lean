/-
# The radial half of the `ℋ⁴` bound for the `Γ`-term: `|(D_z^j ρ)(z)·w(z)| ≤ M/(1+z)²`

This file proves

`Work.Construction.H4N_GammaTerm_rho_bound`:
`∃ M > 0, ∀ j ≤ 4, ∀ z ≥ 0, |(Zop^[j] ρ)(z)·w(z)| ≤ M/(1+z)²`

where `ρ(z) = z²/(1+z)⁴` (`Work.Construction.rhoR`), `w(z) = (1+z)²/z²`
(`Work.Spaces.w`) and `Zop = D_z` is `z·∂_z` (`Work.Spaces.Zop`).

The mathematical content is the explicit computation of the four `D_z`-iterates of `ρ`,

`(Zop^[j] ρ)(z) = z²·N_j(z)/(1+z)^{4+j}`  (`z ≠ -1`),

with `N_0 = 1`, `N_1 = 2 - 2z`, `N_2 = 4 - 12z + 4z²`, `N_3 = 8 - 52z + 52z² - 8z³`,
`N_4 = 16 - 196z + 416z² - 196z³ + 16z⁴` (proved in the companion modules
`H4N_rhoR_shape12`, `H4N_rhoR_shape3`, `H4N_rhoR_shape4`, obtained by differentiating
`z²N_j(z)/(1+z)^{4+j}` and multiplying by `z`).  Since `N_j` has coefficient `ℓ¹`-norm
`1, 4, 20, 120, 840` and `z^k ≤ (1+z)^j` for `0 ≤ z`, `k ≤ j`, we get
`|N_j(z)| ≤ 840·(1+z)^j` (`H4N_rhoR_numbound`), and therefore, for `z > 0`,

`|(Zop^[j] ρ)(z)·w(z)| = |N_j(z)|/(1+z)^{2+j} ≤ 840/(1+z)²`.

At `z = 0` both sides are `0` (Lean's totalised division gives `w 0 = 0`), so `M = 840`
works; this is the `z`-calculation of the "direct calculation" of the paper
(tex 1398–1402), the companion of `Work.Construction.H4N_GammaTerm_Lop_bound`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.H4N_rhoR_shape12
import Submission.Work.Construction.H4N_rhoR_shape3
import Submission.Work.Construction.H4N_rhoR_shape4
import Submission.Work.Construction.H4N_rhoR_numbound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The five cases `j = 0,1,2,3,4`

For `z = 0` the weight `w` vanishes (`w 0 = 0`), so the bound is trivial; for `z > 0`
we substitute the closed form of the iterate and reduce to the polynomial bound of
`H4N_rhoR_numbound`. -/

private lemma rhoR_w_bound_0 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[0] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [Function.iterate_zero_apply]
    norm_num [rhoR, Work.Spaces.w]
  · have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [Function.iterate_zero_apply, show rhoR = (fun z : ℝ => z^2/(1+z)^4) from rfl,
      Work.Spaces.w]
    have key : (z^2/(1+z)^4) * ((1+z)^2/z^2) = 1/(1+z)^2 := by field_simp
    rw [key, abs_of_pos (by positivity : (0:ℝ) < 1/(1+z)^2)]
    gcongr
    norm_num

private lemma rhoR_w_bound_1 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[1] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape12.1 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape12.1 z (by linarith), Work.Spaces.w]
    have key : (z^2*(2-2*z)/(1+z)^5) * ((1+z)^2/z^2) = (2-2*z)/(1+z)^3 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^3)]
    have key2 : |2 - 2*z| / (1+z)^3 = (|2 - 2*z|/(1+z))/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ h1z]
    linarith [H4N_rhoR_numbound.2.1 z hz]

private lemma rhoR_w_bound_2 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[2] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape12.2 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape12.2 z (by linarith), Work.Spaces.w]
    have key : (z^2*(4-12*z+4*z^2)/(1+z)^6) * ((1+z)^2/z^2)
        = (4-12*z+4*z^2)/(1+z)^4 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^4)]
    have key2 : |4 - 12*z + 4*z^2| / (1+z)^4
        = (|4 - 12*z + 4*z^2|/(1+z)^2)/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+z)^2)]
    linarith [H4N_rhoR_numbound.2.2.1 z hz]

private lemma rhoR_w_bound_3 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[3] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape3 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape3 z (by linarith), Work.Spaces.w]
    have key : (z^2*(8-52*z+52*z^2-8*z^3)/(1+z)^7) * ((1+z)^2/z^2)
        = (8-52*z+52*z^2-8*z^3)/(1+z)^5 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^5)]
    have key2 : |8 - 52*z + 52*z^2 - 8*z^3| / (1+z)^5
        = (|8 - 52*z + 52*z^2 - 8*z^3|/(1+z)^3)/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+z)^3)]
    linarith [H4N_rhoR_numbound.2.2.2.1 z hz]

private lemma rhoR_w_bound_4 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[4] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape4 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape4 z (by linarith), Work.Spaces.w]
    have key : (z^2*(16-196*z+416*z^2-196*z^3+16*z^4)/(1+z)^8) * ((1+z)^2/z^2)
        = (16-196*z+416*z^2-196*z^3+16*z^4)/(1+z)^6 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^6)]
    have key2 : |16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4| / (1+z)^6
        = (|16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4|/(1+z)^4)/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+z)^4)]
    linarith [H4N_rhoR_numbound.2.2.2.2 z hz]

/-! ## The stated bound -/

theorem H4N_GammaTerm_rho_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2 := by
  refine ⟨840, by norm_num, ?_⟩
  intro j hj z hz
  interval_cases j
  · exact rhoR_w_bound_0 z hz
  · exact rhoR_w_bound_1 z hz
  · exact rhoR_w_bound_2 z hz
  · exact rhoR_w_bound_3 z hz
  · exact rhoR_w_bound_4 z hz

end Work.Construction
