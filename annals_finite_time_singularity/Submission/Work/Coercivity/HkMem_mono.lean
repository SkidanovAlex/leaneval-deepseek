/-
# `HkMem` is monotone in the order `k`

`Work.Spaces.HkMem α k f` says that the `H^k`-integrand of `f` has honest iterated
integrals: every angular slice `θ ↦ HkIntegrand α k f z θ` is integrable on `Iθ`
(for `z ∈ Iz`) and `z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

Since `HkIntegrand α (k+1) f` is obtained from `HkIntegrand α k f` by adding the extra
(summands of the) finitely many new weighted derivatives — all of them *squares* of
real numbers — the integrand is pointwise monotone in `k`
(`Work.Spaces.HkIntegrand_mono`).  Hence the integrability of the `k+1`-integrand
implies that of the `k`-integrand: the domination argument needs only the a.e. strong
measurability of the smaller integrand, which holds because the integrand of a
`SmoothNbhd` function is continuous on the open quadrant `(0,∞) × (0,π/2)`; the closed
quadrant `[0,∞) × [0,π/2]` differs from the open one by null segments, and on the single
slice `z = 0` the integrand vanishes identically (the radial weight `w` does).

This is the elementary monotonicity that lets every statement proved for `ℋ^{k+1}`
be used at level `k`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkSq_mono
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Measurability of the `H^k`-integrand

`Work.Spaces.continuousOn_HkIntegrand_Qd` gives continuity of `(z,θ) ↦ HkIntegrand α k f z θ`
on the open quadrant as soon as `f` is `C^∞` on the open quadrant `quadU`; and
`SmoothNbhd f` (smoothness on the larger rectangle `(-1,∞) × (-1,π/2+1)`) restricts to
that.  Continuity on the open quadrant together with the vanishing of the integrand on
the slice `z = 0` gives a.e. strong measurability for `volume.restrict Iz`, for
`volume.restrict Iθ` and for their product. -/

/-- `SmoothNbhd` smoothness on the rectangle `(-1,∞) × (-1,π/2+1)` restricts to the open
quadrant `quadU = (-1,∞) × (0,π/2)`. -/
private theorem contDiffOn_uncurry_quadU_of_smoothNbhd {g : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (Function.uncurry g) Spaces.quadU :=
  hsm.mono fun p hp => ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩

/-- The uncurried `H^k`-integrand of a `SmoothNbhd` function is continuous on the open
quadrant. -/
private theorem continuousOn_uncurry_HkIntegrand (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  Spaces.continuousOn_HkIntegrand_Qd α k f (contDiffOn_uncurry_quadU_of_smoothNbhd hsm)

/-- Every angular slice `θ ↦ HkIntegrand α k f z θ`, `z ∈ Iz`, is a.e. strongly
measurable for `volume.restrict Iθ`. -/
theorem aesm_HkIntegrand_slice (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Spaces.HkIntegrand α k f z θ)
        (volume.restrict Spaces.Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
  · -- the slice `z = 0` vanishes identically, hence is measurable
    rw [← h]
    have hzero : (fun θ : ℝ => Spaces.HkIntegrand α k f 0 θ) = fun _ : ℝ => (0 : ℝ) :=
      funext fun θ => Spaces.HkIntegrand_zero_z α k f θ
    rw [hzero]
    exact aestronglyMeasurable_const
  · -- the slice `z > 0` is a slice of a continuous function
    exact Spaces.aesm_slice_of_continuousOn_Qd _
      (continuousOn_uncurry_HkIntegrand α k hsm) h

/-- The uncurried `H^k`-integrand is a.e. strongly measurable for the product of the
restricted measures `volume.restrict Iz` and `volume.restrict Iθ`. -/
theorem aesm_uncurry_HkIntegrand (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
  Spaces.aesm_of_continuousOn_Qd _
    (continuousOn_uncurry_HkIntegrand α k hsm)

/-! ## The monotonicity of `HkMem` in `k` -/

/-- **`HkMem` is monotone in `k`**: a function whose `(k+1)`-st `H`-integrand has honest
iterated integrals also has honest iterated integrals at level `k`. -/
theorem HkMem_mono (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f)
    (h : Spaces.HkMem α (k + 1) f) : Spaces.HkMem α k f := by
  have hjoint := aesm_uncurry_HkIntegrand α k hsm
  have hslice := aesm_HkIntegrand_slice α k hsm
  have hmono : ∀ z θ : ℝ, Spaces.HkIntegrand α k f z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ :=
    fun z θ => Spaces.HkIntegrand_mono α k f z θ
  constructor
  · -- every angular slice of the `k`-integrand is integrable
    intro z hz
    refine Integrable.mono' (h.1 z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)]
      with θ _
    rw [Real.norm_eq_abs, abs_of_nonneg (Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hmono z θ
  · -- the `z`-integral of the `k`-integrand is integrable
    refine Integrable.mono' h.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iz from measurableSet_Ici)]
      with z hz
    have hk : ∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.HkIntegrand α k f z θ :=
      fun θ _ => Spaces.HkIntegrand_nonneg α k f z θ
    have hnn : 0 ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k f z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc hk)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc hk)
      (h.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => hmono z θ))

end Work.Coercivity
