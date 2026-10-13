import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_aux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ZTracesAux

/-- The angular integrand `(∂_θ(D_z^bD_θ^af)(s,·))² · sin(2·)^{2-γ}` is integrable on `Iθ`
as soon as `((D_z^bD_θ^{a+1}f)(s,·) · w(s))² sin(2·)^{-γ}` is dominated pointwise by
`HkIntegrand α m f s ·` and `∂_θ(D_z^bD_θ^af)` is identified with
`D_z^bD_θ^{a+1}f / sin(2·)` on the interior: on `(0,π/2)` one has
`(X/c)² c^{2-γ} = ((X·w)² c^{-γ}) / w²`, and the right-hand side is integrable because
`HkIntegrand α m f s ·` is (`hmem`) — the factor `w(s)² > 0` is a constant in `θ`. -/
theorem integrable_pth_sq_sin_gen {α : ℝ} {f : ℝ → ℝ → ℝ} {m : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (b a : ℕ) {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpoint : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α m f s σ)
    (hident : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
        = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) :
    MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hsin_cont : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hu_cont : ContinuousOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont.pow 2).mul (hsin_cont.rpow_const
      (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))))
  have hwne : (Work.Spaces.w s) ^ 2 ≠ 0 := by
    have h := Work.FTS_RegExport.RXT.Slots.w_pos_aux hs
    positivity
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (Work.FTS_RegExport.RXT.Slots.aesm_Iθ_of_continuousOn_Ioo_aux hu_cont) ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)),
    hident σ hσ]
  have hkey : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = ((Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) / (Work.Spaces.w s) ^ 2 := by
    have h1 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    rw [h1, div_pow, mul_pow, eq_div_iff hwne]
    field_simp
  rw [hkey]
  exact div_le_div_of_nonneg_right (hpoint σ hσ) (sq_nonneg _)

end Work.FTS.EpsEngine.ZTracesAux
