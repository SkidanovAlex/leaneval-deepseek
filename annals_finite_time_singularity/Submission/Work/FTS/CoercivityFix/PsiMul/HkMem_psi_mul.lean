/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ℋ^k`-membership is preserved by a `z`-only multiplier

`Work.Spaces.HkMem α k (fun z θ => ψ z * g z θ)` for `g ∈ ℋ^k` and `ψ` a `C^∞` function of `z`
alone whose `Zop`-iterates `(z ∂_z)^c ψ` are bounded by `K` on `(0,∞)`, `c ≤ k`.

The multiplier estimate `Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform`
controls the `ℋ^k`-integrand of the product *on the open quadrant* `z > 0`, `0 < θ < π/2`.
The transfer of that domination into the two honesty requirements of `HkMem` is done by
`hkMem_of_quad_dominated`: the slices at `z > 0` are integrable because `(0,π/2)` and `[0,π/2]`
differ by the two null endpoints (`MeasureTheory.Ioo_ae_eq_Icc`), the degenerate slice `z = 0`
vanishes (`Work.Spaces.HkIntegrand_zero_z`), and the `θ`-integral is measurable by Fubini
(`AEStronglyMeasurable.integral_prod_right'`) on the open quadrant, where the integrand is
continuous (`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.PsiMul

set_option autoImplicit false

/-- **Membership in `ℋ^k` by a domination on the *open* quadrant.**

If `F` is `C^∞` on the open quadrant (`Work.FTS.LocData.SmoothQuad F`), `g ∈ ℋ^k` and the
`ℋ^k`-integrand of `F` is dominated by `C ·` (the integrand of `g`) at every point of the open
quadrant `z > 0`, `0 < θ < π/2`, then `F ∈ ℋ^k`.

The domination is only needed off the boundary: the open quadrant differs from the domain
`Iz ×ˢ Iθ` by the two null angular endpoints, so the `θ`-slices at `z > 0` are integrable by
`Integrable.mono'` on `(0,π/2)` followed by `IntegrableOn.congr_set_ae`; the slice `z = 0`
vanishes identically; and the `z`-integral of the slices is measurable by Fubini. -/
private theorem hkMem_of_quad_dominated (α : ℝ) (k : ℕ) {F g : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : Work.FTS.LocData.SmoothQuad F) (hm : Work.Spaces.HkMem α k g)
    (hub : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.HkIntegrand α k F z θ ≤ C * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k F := by
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Set.Icc (0 : ℝ) (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k F hF
  constructor
  · -- the angular slices of the integrand are integrable on `Iθ`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero
        (fun θ _ => (Work.Spaces.HkIntegrand_zero_z α k F θ).symm) measurableSet_Icc
    · -- `z > 0`: dominate on the open interval and transfer to `[0,π/2]`
      have hdom : IntegrableOn (fun θ => C * Work.Spaces.HkIntegrand α k g z θ)
          (Set.Ioo (0 : ℝ) (π / 2)) :=
        MeasureTheory.IntegrableOn.congr_set_ae ((hm.1 z hz).const_mul C) hIoo
      have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k F z θ)
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        (Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k F)
          hcont hz0).aestronglyMeasurable measurableSet_Ioo
      have hle : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (π / 2))),
          ‖Work.Spaces.HkIntegrand α k F z θ‖ ≤ C * Work.Spaces.HkIntegrand α k g z θ := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun θ hθ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k F z θ)]
        exact hub z hz0 θ hθ
      exact MeasureTheory.IntegrableOn.congr_set_ae
        (MeasureTheory.Integrable.mono' hdom haesm hle) hIoo.symm
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    have hdom : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        C * Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iz := by
      show MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        C * Work.Spaces.HkIntegrand α k g z θ) (volume.restrict Work.Spaces.Iz)
      simpa only [MeasureTheory.integral_const_mul] using (hm.2).const_mul C
    have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        (volume.restrict Work.Spaces.Iz) := by
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable
          (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k F z θ)
          (volume.restrict (Set.Ioi 0)) := hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable
          (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k F z θ)
          (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k F z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    have hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
        ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ‖
          ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k g z θ := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
        MeasureTheory.integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
        ((hm.1 z hz).const_mul C) ?_
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
      · subst h0
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => ?_
        rw [Work.Spaces.HkIntegrand_zero_z α k F θ]
        exact mul_nonneg hC (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
      · have hioo : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (π / 2))),
            Work.Spaces.HkIntegrand α k F z θ ≤ C * Work.Spaces.HkIntegrand α k g z θ :=
          (MeasureTheory.ae_restrict_iff' (s := Set.Ioo 0 (π / 2)) measurableSet_Ioo).mpr
            (Filter.Eventually.of_forall fun θ hθ => hub z hz0 θ hθ)
        have hmeq : volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
            = volume.restrict Work.Spaces.Iθ :=
          MeasureTheory.Measure.restrict_congr_set hIoo
        rw [← hmeq]
        exact hioo
    exact MeasureTheory.Integrable.mono' hdom haesm hle

theorem HkMem_psi_mul (α : ℝ) (k : ℕ) {ψ : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi (-1)))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g)
    (hm : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => ψ z * g z θ) := by
  obtain ⟨C, hCpos, hCub⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform α k
  have hFquad : Work.FTS.LocData.SmoothQuad (fun z θ => ψ z * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.CoercivityFix.E2Bound.smoothQuad_of_zOnly hsm) hg
  refine hkMem_of_quad_dominated α k (C := C * (1 + K) ^ 2) ?_ hFquad hm ?_
  · exact mul_nonneg hCpos.le (sq_nonneg _)
  · intro z hz θ hθ
    exact hCub ψ K hK hKb hsm g hg z hz θ hθ

end Work.FTS.CoercivityFix.PsiMul
