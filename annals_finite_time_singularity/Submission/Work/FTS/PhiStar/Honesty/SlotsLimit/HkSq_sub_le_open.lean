import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.HkMem_sub_of_eqOn_Q0
import Submission.Work.FTS.GalFields.RHS.HkSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Subadditivity of the `ℋ^l`-energy for a *difference*

`Work.Spaces.HkSq α l` is the square of the paper's weighted norm `|·|_{ℋ^l}`, i.e. the iterated
integral of the *nonnegative* integrand `Work.Spaces.HkIntegrand α l`:

`HkSq α l f = ∫_{z ∈ Iz} ∫_{θ ∈ Iθ} HkIntegrand α l f z θ`.

The integrand is a sum of squares of *linear* slot expressions, so on the open quadrant
`Q0 = (0,∞) × (0,π/2)` the pointwise estimate `(a - b)² ≤ 2a² + 2b²` together with the additivity
of the iterated operators `D_z^i` and `D_z^j D_θ^i` for `SmoothOpen` data gives

`HkIntegrand α l (f - g) ≤ 2·HkIntegrand α l f + 2·HkIntegrand α l g`

at every point of the closed quadrant (that pointwise statement is
`Work.FTS.PhiStar.Honesty.EllWeakAux.HkIntegrand_sub_le_open`, from which the boundary lines
`z = 0` and `sin(2θ) = 0` are handled separately).

Integrating that monotone comparison over `θ` and then over `z` — the dominating function
`2·HkIntegrand α l f + 2·HkIntegrand α l g` being integrable precisely by the two membership
hypotheses `HkMem α l f`, `HkMem α l g` — yields the requested

`HkSq α l (f - g) ≤ 2·(HkSq α l f + HkSq α l g)`.

This is the difference-form companion of `Work.FTS.GalFields.RHS.HkSq_add_le_open`; both are
instances of the same "pointwise bound + monotonicity of the integral" pattern
(`MeasureTheory.integral_mono_of_nonneg`, which needs only the *upper* function to be
integrable).  No `α > 0` hypothesis is needed, because the pointwise integrand bound is
`α`-free.
-/

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Subadditivity of `HkSq` for a difference**, on the open smoothness class.

For `f`, `g` smooth on the open quadrant and with honest `ℋ^l`-integrability certificates,

`HkSq α l (f - g) ≤ 2·(HkSq α l f + HkSq α l g)`. -/
theorem HkSq_sub_le_open (α : ℝ) (l : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α l f) (hmg : Work.Spaces.HkMem α l g) :
    Work.Spaces.HkSq α l (fun z θ => f z θ - g z θ)
      ≤ 2 * (Work.Spaces.HkSq α l f + Work.Spaces.HkSq α l g) := by
  -- the pointwise bound on the closed quadrant, from the open-quadrant subadditivity
  have hpt := Work.FTS.PhiStar.Honesty.EllWeakAux.HkIntegrand_sub_le_open (α := α) (k := l) hf hg
  -- inner (angular) monotonicity of the integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
        ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ) := by
    intro z hz
    have hint : Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α l f z θ + Work.Spaces.HkIntegrand α l g z θ)
        (volume.restrict Work.Spaces.Iθ) := (hmf.1 z hz).add (hmg.1 z hz)
    -- regroup `2a + 2b` as `2(a + b)`
    have hptz : ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ
          ≤ 2 * (Work.Spaces.HkIntegrand α l f z θ + Work.Spaces.HkIntegrand α l g z θ) :=
      fun θ hθ => by
        have h := hpt z hz θ hθ
        linarith
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
      (g := fun θ => 2 * (Work.Spaces.HkIntegrand α l f z θ
        + Work.Spaces.HkIntegrand α l g z θ))
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α l (fun z θ => f z θ - g z θ) z θ)
      (hint.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Icc hptz)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  -- outer (radial) monotonicity of the integral
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
      (g := fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ)
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ))
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α l (fun z θ => f z θ - g z θ) z θ)
      ((hmf.2.add hmg.2).const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  -- evaluate the dominating iterated integral
  have hR : (∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α l f z θ)
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ))
      = 2 * (Work.Spaces.HkSq α l f + Work.Spaces.HkSq α l g) := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmg.2]
  exact hmain.trans_eq hR

end Work.FTS.PhiStar.Honesty.SlotsLimit
