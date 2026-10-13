import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Coercivity.sliceEtaAux
import Submission.Work.FTS.H2.mixed_sin_bound
import Submission.Work.FTS.H2.T2SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

/-- Integrability on `Iθ` of the two `θ`-integrands of a mixed slot
`D_θ(D_z^jD_θ^i g)·D_z^jD_θ^i g·sin(2θ)^{-γ}` (`1 ≤ i`, `γ = gam α ∈ (1,2)`), weighted by an
arbitrary smooth `f`: at a fixed `z > 0`, both
`θ ↦ f(z,θ)·D_θ(mixed j i g)(z,θ)·mixed j i g(z,θ)·sin(2θ)^{-γ}` and
`θ ↦ (mixed j i g(z,θ))²·sin(2θ)^{-γ}` are integrable on `Iθ = [0,π/2]`.
Route: for `i ≥ 1` one has `mixed j i g = sin(2θ)·u` with `u = D_z^j(∂_θ D_θ^{i-1}g)` smooth
(`Work.Spaces.DthIter_succ`, `deriv_const_mul_field`, induction — cf. the private lemmas
`DzIter_const_theta_mul`, `mixed_succ_eq_sin_mul` in
`Submission/Work/Coercivity/E2smooth_mixed_sin_bound.lean`), so both integrands equal
`sin(2θ)^{2-γ}` times a function continuous on the compact `Iθ`
(`2 - γ > 0`, `Real.continuous_rpow_const`, `Work.Coercivity.slice_pth_continuousOn`,
`Work.Coercivity.slice_continuousOn`), hence integrable (`ContinuousOn.integrableOn_compact`). -/
theorem T1HardIntMixed (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsmg : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) (hi : 1 ≤ i) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Spaces.Dth (Work.Spaces.mixed j i g) z θ
        * Work.Spaces.mixed j i g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.mixed j i g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) Work.Spaces.Iθ := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  -- smoothness of the two factors exposed by `mixed_eq_sin_mul`
  have hsmw : Work.Spaces.SmoothNbhd (Work.Spaces.mixed j (i' + 1) g) :=
    Work.Spaces.smoothNbhd_mixed hsmg j (i' + 1)
  have hsmX : Work.Spaces.SmoothNbhd
      (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g))) :=
    Work.Spaces.smoothNbhd_DzIter (Work.Spaces.smoothNbhd_DthIter hsmg i').pth j
  -- the exponent `2 - γ` is positive (indeed `γ ≤ 1 + 1/10`)
  have hgam_lt_two : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hexp_nn : (0 : ℝ) ≤ 2 - Work.Spaces.gam α := by linarith
  have hsin : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    (Real.continuous_rpow_const hexp_nn).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  -- continuity of the three angular slices which occur
  have hcont_f : ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ :=
    Work.Coercivity.slice_continuousOn f hsmf hz
  have hcont_pw : ContinuousOn (fun θ => Work.Spaces.pth (Work.Spaces.mixed j (i' + 1) g) z θ)
      Work.Spaces.Iθ :=
    Work.Coercivity.slice_pth_continuousOn (Work.Spaces.mixed j (i' + 1) g) hsmw hz
  have hcont_X : ContinuousOn
      (fun θ => Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ)
      Work.Spaces.Iθ :=
    Work.Coercivity.slice_continuousOn _ hsmX hz
  -- the pointwise rewriting of the two integrands
  have hpt1 : Set.EqOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (f z θ * Work.Spaces.pth (Work.Spaces.mixed j (i' + 1) g) z θ
            * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ))
      (fun θ => f z θ * Work.Spaces.Dth (Work.Spaces.mixed j (i' + 1) g) z θ
        * Work.Spaces.mixed j (i' + 1) g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
      Work.Spaces.Iθ := by
    intro θ hθ
    simp only []
    have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    have hDth : Work.Spaces.Dth (Work.Spaces.mixed j (i' + 1) g) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j (i' + 1) g) z θ := rfl
    rw [hDth, mixed_eq_sin_mul g j i' z θ,
      show f z θ * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j (i' + 1) g) z θ)
            * (Real.sin (2 * θ)
                * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ)
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
          = (Real.sin (2 * θ) * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
            * (f z θ * Work.Spaces.pth (Work.Spaces.mixed j (i' + 1) g) z θ
                * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ) by ring,
      ← sq (Real.sin (2 * θ)),
      sq_mul_rpow_neg (Real.sin (2 * θ)) (Work.Spaces.gam α) hs hgam_lt_two]
  have hpt2 : Set.EqOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ) ^ 2)
      (fun θ => (Work.Spaces.mixed j (i' + 1) g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) Work.Spaces.Iθ := by
    intro θ hθ
    simp only []
    have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    rw [mixed_eq_sin_mul g j i' z θ, mul_pow,
      show Real.sin (2 * θ) ^ 2
            * (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
          = (Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
            * (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ) ^ 2 by ring,
      sq_mul_rpow_neg (Real.sin (2 * θ)) (Work.Spaces.gam α) hs hgam_lt_two]
  constructor
  · exact (ContinuousOn.integrableOn_compact isCompact_Icc
        (hsin.continuousOn.mul ((hcont_f.mul hcont_pw).mul hcont_X))).congr_fun hpt1
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)))
  · exact (ContinuousOn.integrableOn_compact isCompact_Icc
        (hsin.continuousOn.mul (hcont_X.pow 2))).congr_fun hpt2
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)))

end Work.FTS.H2
