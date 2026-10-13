/-
# `HkMem` transfer from an a.e. angular domination by a sum of two `HkMem` functions

`Work.Spaces.HkMem α k f` asks for the two iterated `H^k`-integrals of `f` to be honest:
every angular slice `θ ↦ HkIntegrand α k f z θ`, `z ∈ Iz`, is integrable on `Iθ`, and the
`z`-integral `z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

Here we record the transfer step used throughout the coercivity chapter: if `h` is smooth on a
neighbourhood of the closed quadrant and its `H^k`-integrand is dominated, on every angular
slice of the domain and for almost every angle, by `2·(integrand of f) + 2·(integrand of g)`
where `f` and `g` are in `ℋ^k`, then `h ∈ ℋ^k`.

Only the *integrals* of the domination are used, so the pointwise hypothesis may be weakened
to an almost-everywhere one: the strong measurability of the integrand of `h` comes for free
from `SmoothNbhd h` (`Work.Coercivity.aesm_HkIntegrand_slice`,
`Work.Coercivity.aesm_uncurry_HkIntegrand`), and the nonnegativity of the integrand
(`Work.Spaces.HkIntegrand_nonneg`) upgrades the domination of the values to a domination of
the norms, both on `Iθ` and after integration over `θ`.  This is exactly the shape in which
the additivity of the weighted `ℋ^k`-integrand in the coercivity step is stated
(`Work.FTS.CoercivityStep.Norm.HkIntegrand_add_le_ae`): with `h = f + g` the lemma below
turns `HkMem α k f` and `HkMem α k g` into `HkMem α k (f + g)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.HkMem_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-- **`HkMem` by a.e. angular domination by a sum.**  If `h` is smooth on a neighbourhood of
the closed quadrant, `f, g ∈ ℋ^k` and the `H^k`-integrand of `h` is, on each angular slice
(with `z ∈ Iz`), dominated almost everywhere in `θ` by `2·HkIntegrand f + 2·HkIntegrand g`,
then `h ∈ ℋ^k`. -/
theorem HkMem_of_add_dominated (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hsmh : Work.Spaces.SmoothNbhd h)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k h z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k h := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hslice := Work.Coercivity.aesm_HkIntegrand_slice α k hsmh
  have hjoint := Work.Coercivity.aesm_uncurry_HkIntegrand α k hsmh
  constructor
  · -- every angular slice of the integrand of `h` is integrable on `Iθ`
    intro z hz
    refine Integrable.mono'
      (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) (hslice z hz) ?_
    filter_upwards [hle z hz] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono'
      (((hf.2).const_mul 2).add ((hg.2).const_mul 2)) hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hmono : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ :=
      integral_mono_of_nonneg
        (ae_restrict_of_forall_mem hmesθ
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
        (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2))
        (hle z hz)
    have hcalc : (∫ θ in Work.Spaces.Iθ,
          2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
      rw [integral_add ((hf.1 z hz).const_mul 2) ((hg.1 z hz).const_mul 2),
        integral_const_mul, integral_const_mul]
    exact le_trans hmono hcalc.le

end Work.FTS.CoercivityStep.Norm
