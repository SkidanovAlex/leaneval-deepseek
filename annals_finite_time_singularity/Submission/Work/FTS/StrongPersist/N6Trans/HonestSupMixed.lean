import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The honest-class `L^∞`-bound of order `≤ 2` for mixed derivatives.**

For `f` of class `C^∞` on the *open* quadrant with honest `ℋ⁴`-membership (no decay, no
smoothness at the angular boundary, no `𝒲^{l,∞}`-coefficient hypothesis), every mixed
derivative `D_z^bD_θ^a f` with `a + b ≤ 2` is bounded on the open quadrant by
`C/√(γ-1)·|f|_{ℋ⁴}` with a universal `C`.

This is a junction of two proved lemmas:

* `a = 0`, `b ≤ 2`: `Work.FTS.TransportS.sup_dz_le_hk` (pure radial derivatives, honest class);
* `a ≥ 1`: `Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn`, which bounds every mixed
  `D_z^bD_θ^af` with `1 ≤ a`, `a + b ≤ 2` by `√15·|f|_{ℋ⁴}`; since `γ - 1 = α/10 ≤ 1/10`
  one has `1 ≤ 1/√(γ-1)`, so the `1/√(γ-1)` shape covers it. -/
theorem HonestSupMixed : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C1, _, hC1⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨max C0 C1, lt_max_of_lt_left hC0pos, ?_⟩
  intro α f hα hα1 hF hmem b a hab z θ hz hθ hθ2
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1 : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hs1 : Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hγ1
  have hsr : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hγ)]; simpa using hs1
  set s : ℝ := Real.sqrt (Work.Spaces.gam α - 1) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hγ
  set A : ℝ := Work.Spaces.HkNorm α 4 f with hA
  have hA0 : 0 ≤ A := Work.Spaces.HkNorm_nonneg α 4 f
  have hC0nn : 0 ≤ C0 := le_of_lt hC0pos
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    have h := hC0 α f hα hα1 hF hmem b (by omega) z θ hz hθ hθ2
    have h' : |Work.Spaces.mixed b 0 f z θ| ≤ C0 / s * A := by
      simpa only [Work.Spaces.mixed_zero_right, hsdef, hA] using h
    have hle : C0 / s * A ≤ max C0 C1 / s * A := by
      refine mul_le_mul_of_nonneg_right ?_ hA0
      exact div_le_div_of_nonneg_right (le_max_left _ _) hs0.le
    linarith
  · have h := hC1 α f hα hα1 hF hmem b a hapos hab z θ hz hθ hθ2
    have h' : |Work.Spaces.mixed b a f z θ| ≤ C1 * A := by
      simpa only [Work.FTS.Nonlin.Xn, hA] using h
    have hstep : C1 * A ≤ max C0 C1 / s * A := by
      have hmax : C1 ≤ max C0 C1 := le_max_right _ _
      have hmax0 : 0 ≤ max C0 C1 := le_trans hC0nn (le_max_left _ _)
      have h1 : C1 * A ≤ max C0 C1 * A := mul_le_mul_of_nonneg_right hmax hA0
      have h2 : max C0 C1 * A ≤ max C0 C1 * ((1 / s) * A) := by
        refine mul_le_mul_of_nonneg_left ?_ hmax0
        calc A = 1 * A := by ring
          _ ≤ (1 / s) * A := mul_le_mul_of_nonneg_right hsr hA0
      have h3 : max C0 C1 * ((1 / s) * A) = max C0 C1 / s * A := by
        rw [div_eq_mul_inv]; ring
      linarith [h1, h2, h3.le, h3.ge]
    linarith

end Work.FTS.StrongPersist.N6Trans
