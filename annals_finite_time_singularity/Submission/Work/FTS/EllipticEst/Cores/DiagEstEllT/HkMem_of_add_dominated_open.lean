/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkMem` from an a.e. angular domination, for data smooth on the *open* quadrant

`Work.FTS.CoercivityStep.Norm.HkMem_of_add_dominated` proves that `h ∈ ℋ^k` if `h` is smooth on
a *neighbourhood* of the closed quadrant (`Work.Spaces.SmoothNbhd h`, i.e. real analyticity there
in the frozen vocabulary) and its `H^k`-integrand is dominated, on each angular slice, a.e. in
`θ`, by `2·HkIntegrand f + 2·HkIntegrand g` with `f, g ∈ ℋ^k`.

The analyticity hypothesis is used for exactly one purpose: the a.e. strong measurability of the
integrand of `h` (`Work.Coercivity.aesm_HkIntegrand_slice`, `aesm_uncurry_HkIntegrand`).  On the
*open* quadrant the same measurability is available from continuity alone
(`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` with
`Work.Spaces.aesm_of_continuousOn_Qd` / `aesm_slice_of_continuousOn_Qd`), and the boundary lines
`z = 0`, `θ = 0`, `θ = π/2` of the domain are null sets on which the integrand is `0`
(`Work.Spaces.HkIntegrand_zero_z`, and the rpow factor `sin(2θ)^{-η/2}` vanishes at the two
angular endpoints by Lean's totalised `0^(negative) = 0`).

This is the form in which the honest (finite-smoothness) data of the trace-free class `EllHypT`
consume the lemma: the straightened datum `Ψ + Gsing α F · sin 2θ` is `C^∞` on the open quadrant
but not on any neighbourhood of the closed one, because `Gsing α F` is only finitely smooth.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.CoercivityStep.Norm.HkMem_of_add_dominated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false

/-- **`HkMem` by an a.e. angular domination by a sum, from continuity of the integrand on the
open quadrant.**  The smoothness of `h` is used for exactly one purpose, the a.e. strong
measurability of `HkIntegrand α k h`; taking that as an explicit hypothesis makes the lemma
applicable to data (such as the straightened datum `Ψ + Gsing α F · sin 2θ`) which are honest on
the open quadrant but not `C^∞` there.  The continuity hypothesis is available for every datum
that is `C^k` on the open quadrant
(`Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn`). -/
theorem HkMem_of_add_dominated_cont (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k h z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k h := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k h z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k h z θ) = fun _ => (0 : ℝ) from by
        funext θ; rw [← hz0, Work.Spaces.HkIntegrand_zero_z]]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
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

/-- **`HkMem` by an a.e. angular domination by a sum, from open-quadrant smoothness** (the
specialisation of `HkMem_of_add_dominated_cont` to `SmoothOpen` data). -/
theorem HkMem_of_add_dominated_open (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hsmh : Work.FTS.EllipticEst.SmoothOpen h)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k h z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k h :=
  HkMem_of_add_dominated_cont α k (hsmh.continuousOn_HkIntegrand α k) hf hg hle

end Work.FTS.EllipticEst.Cores.DiagEstEllT
