import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS.EpsEngine.ZTracesAux.Dth_mixed_eq_gen
import Submission.Work.FTS.EpsEngine.ZTracesAux.slot_le_HkIntegrand_gen
import Submission.Work.FTS.EpsEngine.ZTracesAux.slot_sin_le_HkIntegrand_gen
import Submission.Work.FTS.EpsEngine.ZTracesAux.continuousOn_pth_mixed_slice_gen
import Submission.Work.FTS.EpsEngine.ZTracesAux.integrable_slot_sq_gen
import Submission.Work.FTS.EpsEngine.ZTracesAux.integrable_pth_sq_sin_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `sup_theta_gen` — the uniform angular sup bound for a mixed slot, at every order `m`

For `0 < α ≤ 1` there is a constant `K = K(α) ≥ 0` — the **same** for every `m ≥ 1`, every
datum `f`, and every slot — such that for every mixed slot `D_z^b D_θ^a f` of *total* order
`a + b + 1 ≤ m`

  `(D_z^b D_θ^a f (s,θ) · w(s))² ≤ K · ∫_σ HkIntegrand α m f (s,σ) dσ`

for every `s > 0` and every `θ ∈ (0,π/2)`, where `w(s) = (1+s)²/s²`.

This is the arbitrary-order version of `Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform`
(which is the case `m = 4`, `a + b ≤ 3`), and the proof is the same one: the radial weight `w`
is a function of `s` alone, so the estimate is purely *angular*; the pointwise domination of a
slot by `HkIntegrand` (a summand of the integrand, up to the factor
`sin(2σ)^{±γ} ≤ 1`), the angular Agmon/mean–variation bound
`g(θ)² ≤ (8/π)∫ g² + 2(∫ sin^{γ-2})(∫ g'² sin^{2-γ})` of
`Work.FTS_RegExport.RXT.Slots.angular_meanVar_aux`, and `∫_{Iθ} sin^{γ-2} ≤ 100/(γ-1)` give,
with `g = mixed b a f s ·` and `g' = ∂_θ g = mixed b (a+1) f s · / sin(2·)`,

  `(D_z^bD_θ^af·w)² ≤ (8/π)∫HkIntegrand + 2(∫sin^{γ-2})∫HkIntegrand
     ≤ (8/π + 200/(γ-1))∫HkIntegrand`.

The analytic inputs specific to the general order are the companion lemmas
`Dth_mixed_eq_gen`, `slot_le_HkIntegrand_gen`, `slot_sin_le_HkIntegrand_gen`,
`continuousOn_pth_mixed_slice_gen`, `integrable_slot_sq_gen`, `integrable_pth_sq_sin_gen`
(imported above).
-/

/-- **Uniform angular sup bound for a mixed slot, at every order.** -/
theorem sup_theta_gen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α m f →
      ∀ b a : ℕ, a + b + 1 ≤ m → ∀ s : ℝ, 0 < s → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
        ≤ K * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) := by
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith
  refine ⟨8 / Real.pi + 200 / (Work.Spaces.gam α - 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
    have h2 : (0 : ℝ) ≤ 200 / (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) hγpos.le
    linarith
  intro m hm f hSm hmem b a hab s hs θ hθ0 hθ1
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the finite smoothness needed for the slot
  have hF : ContDiffOn ℝ (a + b + 1) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hSm (a + b + 1)
  have hmixed1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.SmoothOpen.mixed hSm b a).forall 1
  have hslice1 : ContDiffOn ℝ 1 (fun σ => Work.Spaces.mixed b a f s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_t hs hmixed1
  -- the two hypotheses of the angular bound
  have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' => Work.Spaces.mixed b a f s σ')
        (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) σ := by
    intro σ hσ
    exact ((hslice1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hσ)).hasDerivAt
  have hcont1 : ContinuousOn (fun σ => Work.Spaces.mixed b a f s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hslice1.continuousOn
  have hgc : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_pth_mixed_slice_gen hF b a (le_refl _) hs
  have hpoint1 : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2
        ≤ Work.Spaces.HkIntegrand α m f s σ :=
    fun σ hσ => slot_le_HkIntegrand_gen hα b a (by omega) s hσ
  have hpoint2 : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α m f s σ :=
    fun σ hσ => slot_sin_le_HkIntegrand_gen (α := α) b a (by omega) s hσ
  have hident : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
        = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ) := by
    intro σ hσ
    have hD := Dth_mixed_eq_gen (f := f) hF b a (le_refl _) hs hσ
    rw [Work.Spaces.Dth] at hD
    rw [eq_div_iff (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)), mul_comm]
    exact hD
  have hI1 := integrable_slot_sq_gen hmem b a hs hcont1 hpoint1
  have hI2 := integrable_pth_sq_sin_gen hmem b a hs hgc hpoint2 hident
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hang := Work.FTS_RegExport.RXT.Slots.angular_meanVar_aux (γ := Work.Spaces.gam α)
    hγ1 hγ2 hderiv hgc hI1 hI2 θ hθmem
  -- the scalar bounds
  have hAeq : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun σ => by ring)
  have hAle : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ := by
    rw [hAeq]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun σ => sq_nonneg _)
      (hmem.1 s hsI) ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact hpoint1 σ hσ
  have hBeq : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hpth := hident σ hσ
    rw [hpth]
    have h2 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    have e1 : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        = (Work.Spaces.mixed b (a + 1) f s σ) ^ 2 / (Real.sin (2 * σ)) ^ 2 :=
      div_pow _ _ 2
    have hwne : Work.Spaces.w s ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.Slots.w_pos_aux hs)
    rw [e1, h2]
    field_simp <;> ring_nf
  have hBle : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ := by
    rw [hBeq]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 s hsI) ?_
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact hpoint2 σ hσ
  have hGle : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := Work.Spaces.integral_sin_rpow α hα hα1
  have hHnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ :=
    MeasureTheory.integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α m f s σ
  have h3 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
  have h4 : (0 : ℝ) ≤ 2 * (∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)) := by
    refine mul_nonneg (by norm_num) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _
  have h5 : 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 200 / (Work.Spaces.gam α - 1) := by
    have h5a : 2 * (100 / (Work.Spaces.gam α - 1)) = 200 / (Work.Spaces.gam α - 1) := by
      field_simp <;> norm_num
    linarith
  -- assembly
  calc (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
      = (Work.Spaces.mixed b a f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
    _ ≤ ((8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
          + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))
        * (Work.Spaces.w s) ^ 2 := mul_le_mul_of_nonneg_right hang (sq_nonneg _)
    _ = (8 / Real.pi) * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
            * (Work.Spaces.w s) ^ 2)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2) := by
      ring
    _ ≤ (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hAle h3) (mul_le_mul_of_nonneg_left hBle h4)
    _ ≤ (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) := by
      have h6 := mul_le_mul_of_nonneg_right h5 hHnn
      have h7 : (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ)
            + (200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ)
          = (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) := by
        ring
      linarith [h6, h7]

end Work.FTS.EpsEngine.ZTracesAux
