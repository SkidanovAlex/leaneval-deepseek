import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Hilbert

open MeasureTheory Set Filter
open scoped Real Topology

/-- **`ℋ^k` is closed under addition.** If `f` and `g` are smooth on a neighbourhood of the closed
quadrant and in `ℋ^k` (i.e. all the weighted derivatives of `Work.Spaces.HkIntegrand` have integrable
iterated slices), then so is `f + g`.

Intended proof: for smooth `f, g` the weighted derivatives are additive
(`DzIter i (f+g) = DzIter i f + DzIter i g`, `mixed j i (f+g) = mixed j i f + mixed j i g`), and
`(a+b)^2 ≤ 2a^2 + 2b^2`, so `HkIntegrand α k (f+g) z θ ≤ 2 * (HkIntegrand α k f z θ + HkIntegrand α k g z θ)`
pointwise; measurability of the integrands follows from `measurable_deriv`, and integrability is
transferred with `Integrable.mono'`. -/
theorem HkMem_add {α : ℝ} {k : ℕ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  -- `f + g` is again smooth on a neighbourhood of the closed quadrant, and the weighted
  -- `ℋ^k` integrand of `f + g` is pointwise dominated by the sum of the integrands of `f` and `g`
  -- (`HkIntegrand_add_le`, proved from the additivity of the iterated operators on `nbhU`).
  have hsm : Work.Spaces.SmoothNbhd (fun z θ => f z θ + g z θ) :=
    show Work.Spaces.SmoothNbhd (fun z θ => f z θ + g z θ) from hf.add hg
  have hslice := Work.Coercivity.aesm_HkIntegrand_slice α k hsm
  have hjoint := Work.Coercivity.aesm_uncurry_HkIntegrand α k hsm
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hpt := HkIntegrand_add_le (α := α) (k := k) (f := f) (g := g) hf hg
  constructor
  · -- every angular slice of the integrand of `f + g` is integrable on `Iθ`
    intro z hz
    refine Integrable.mono' (((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem hmesθ] with θ hθ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ)]
    exact hpt z hz θ hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono' ((hmf.2.add hmg.2).const_mul 2) hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hmono : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) :=
      integral_mono_of_nonneg
        (ae_restrict_of_forall_mem hmesθ
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ))
        (((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2)
        (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hpt z hz θ hθ))
    have hcalc : (∫ θ in Work.Spaces.Iθ,
          2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ))
        = 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) := by
      rw [integral_const_mul, integral_add (hmf.1 z hz) (hmg.1 z hz)]
    exact le_trans hmono hcalc.le

end Work.FTS.Galerkin.Hilbert
