/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/EpsSq_mul_le_of_sup.lean`

`EpsSq α f = ∫_z ∫_θ (f z θ · epsW α z θ)²` is the weighted `L²`-size of the strong-`ε` space
`X` (`EpsSpace.lean`) and `EpsMem α f` is the honest integrability of the same integrand on
`Iz ×ˢ Iθ`.  This module proves that a profile `f` which is bounded by `M` on the *open* quadrant
(the standing hypothesis of the elliptic layer, where `f` is also `C^∞`) multiplies the space:

  `EpsMem α (f · g)`  and  `EpsSq α (f · g) ≤ M² · EpsSq α g`.

The point is that the weight `epsW α z θ = w z / sin(2θ)^{γ/2}` **vanishes on the boundary of**
`Iz ×ˢ Iθ` (`z = 0`, or `θ ∈ {0, π/2}`): the sup bound is needed only on the open quadrant, and
off it both sides of the pointwise domination collapse to `0`.  What is *not* immediate is the
a.e. strong measurability of the product integrand — `f` is only known to be smooth on the open
quadrant — and that is handled by the fact that the open quadrant is conull for the restricted
product measure, so `volume ∣_{Iz ×ˢ Iθ} = volume ∣_{Quad}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open quadrant inside the closed one -/

/-- The open quadrant `Quad = (0,∞) × (0,π/2)` sits inside `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`. -/
theorem quad_subset_quadrant :
    Work.FTS.StrongEps.Quad ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
  rintro ⟨z, θ⟩ hp
  show 0 ≤ z ∧ 0 ≤ θ ∧ θ ≤ π / 2
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

/-- The open quadrant is measurable. -/
theorem measurableSet_quad : MeasurableSet Work.FTS.StrongEps.Quad :=
  measurableSet_Ioi.prod measurableSet_Ioo

/-- **The two restricted measures agree**: `volume ∣_{Iz ×ˢ Iθ} = volume ∣_{Quad}`.  Indeed the
closed quadrant is the union of the open quadrant and the three boundary lines `z = 0`, `θ = 0`,
`θ = π/2`, which are null for the product measure, and the open quadrant is conull in the closed
one. -/
theorem restrict_prod_eq_restrict_quad :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad := by
  have hP : (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  have hQ : (volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad
      = ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).restrict
          Work.FTS.StrongEps.Quad :=
    (Measure.restrict_restrict_of_subset quad_subset_quadrant).symm
  rw [hQ, ← hP]
  exact (Measure.restrict_eq_self_of_ae_mem ae_mem_quad).symm

/-! ## The pointwise domination -/

/-- **The pointwise domination.**  If `|f| ≤ M` on the *open* quadrant then, at every point of the
*closed* quadrant, the weighted square of `f · g` is dominated by `M²` times the weighted square
of `g`.  Off the open quadrant the weight `epsW α z θ` vanishes (either `z = 0` or `sin(2θ) = 0`),
so both sides are `0` there. -/
theorem mul_sq_le_of_sup {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) {f g : ℝ → ℝ → ℝ}
    (hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ M)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    (f z θ * g z θ * epsW α z θ) ^ 2 ≤ M ^ 2 * (g z θ * epsW α z θ) ^ 2 := by
  by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · obtain ⟨hzpos, hθIoo⟩ := hq
    have hfsq : (f z θ) ^ 2 ≤ M ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hM]
      exact hsup z θ hzpos hθIoo.1 hθIoo.2
    calc (f z θ * g z θ * epsW α z θ) ^ 2
        = (f z θ) ^ 2 * (g z θ * epsW α z θ) ^ 2 := by ring
      _ ≤ M ^ 2 * (g z θ * epsW α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hfsq (sq_nonneg _)
  · have h0 : epsW α z θ = 0 := epsW_eq_zero_of_not_mem_quad hα hz hθ hq
    simp [h0]

/-! ## The target -/

theorem EpsSq_mul_le_of_sup : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → ∀ (f g : Work.FTS.Galerkin.Fn) (M : ℝ),
    0 ≤ M → Work.FTS.EllipticEst.SmoothOpen f →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ M) →
    Work.FTS.StrongEps.EpsMem α g →
    Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ * g z θ) ∧
    Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ * g z θ)
      ≤ C * M ^ 2 * Work.FTS.StrongEps.EpsSq α g := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f g M hM hsm hsup hg
  -- `f` is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.StrongEps.Quad :=
    hsm.continuousOn
  -- (1) the pointwise domination on the closed quadrant
  have hpt : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      (f z θ * g z θ * epsW α z θ) ^ 2 ≤ M ^ 2 * (g z θ * epsW α z θ) ^ 2 :=
    fun z θ hz hθ => mul_sq_le_of_sup hα hM hsup hz hθ
  -- (2) the product integrand is integrable
  have hmem : EpsMem α (fun z θ => f z θ * g z θ) := by
    show MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (f p.1 p.2 * g p.1 p.2 * epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    rw [MeasureTheory.IntegrableOn, restrict_prod_eq_restrict_quad]
    -- on the open quadrant, the integrable factor is `(g · epsW)²` and the bounded factor is `f²`
    have hint : Integrable (fun p : ℝ × ℝ => (g p.1 p.2 * epsW α p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad) :=
      hg.mono_set quad_subset_quadrant
    have hfbd : AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad) :=
      ((hcont.pow 2).aemeasurable measurableSet_quad).aestronglyMeasurable
    have hbound : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad),
        ‖(f p.1 p.2) ^ 2‖ ≤ M ^ 2 := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_quad (fun p hp => ?_)
      have hfsq : (f p.1 p.2) ^ 2 ≤ M ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hM]
        exact hsup p.1 p.2 hp.1 hp.2.1 hp.2.2
      rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine (hint.mul_bdd hfbd hbound).congr (Filter.Eventually.of_forall (fun p => ?_))
    ring
  -- (3) the weighted `L²`-size of the product
  have key : ENNReal.ofReal (EpsSq α (fun z θ => f z θ * g z θ))
      ≤ ENNReal.ofReal (M ^ 2 * EpsSq α g) := by
    rw [Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral hmem]
    calc ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((f z θ * g z θ * epsW α z θ) ^ 2)
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (M ^ 2 * (g z θ * epsW α z θ) ^ 2) := by
          refine MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_))
          refine MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_))
          exact ENNReal.ofReal_le_ofReal (hpt z θ hz hθ)
      _ = ENNReal.ofReal (M ^ 2) *
            ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((g z θ * epsW α z θ) ^ 2) := by
          rw [show (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (M ^ 2 * (g z θ * epsW α z θ) ^ 2))
              = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (M ^ 2) *
                  (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((g z θ * epsW α z θ) ^ 2)) from by
                refine MeasureTheory.lintegral_congr (fun z => ?_)
                rw [show (∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (M ^ 2 * (g z θ * epsW α z θ) ^ 2))
                    = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (M ^ 2) *
                        ENNReal.ofReal ((g z θ * epsW α z θ) ^ 2) from
                    MeasureTheory.lintegral_congr
                      (fun θ => ENNReal.ofReal_mul (sq_nonneg M))]
                exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (EpsSq α g) := by
          rw [← Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral hg]
      _ = ENNReal.ofReal (M ^ 2 * EpsSq α g) := by
          rw [ENNReal.ofReal_mul (sq_nonneg M)]
  refine ⟨hmem, ?_⟩
  have hfin : EpsSq α (fun z θ => f z θ * g z θ) ≤ M ^ 2 * EpsSq α g :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg M) (EpsSq_nonneg α g))).mp key
  calc EpsSq α (fun z θ => f z θ * g z θ) ≤ M ^ 2 * EpsSq α g := hfin
    _ = 1 * M ^ 2 * EpsSq α g := by ring

end Work.FTS.StrongEps.EpsSqTools
