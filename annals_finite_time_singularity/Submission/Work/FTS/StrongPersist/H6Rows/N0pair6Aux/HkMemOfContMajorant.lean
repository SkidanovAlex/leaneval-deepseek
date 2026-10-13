import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ^k`-membership from a continuous pointwise majorant

If the weighted `ℋ^k`-integrand of `h` is continuous on the open quadrant `Q0`, is dominated on
`Q0` by `K` times that of some `f ∈ ℋ^k`, and `h` is measurable where it matters (which the
continuity supplies), then `h ∈ ℋ^k`.

The point of the lemma is that the domination hypothesis is only required on the *open* quadrant
`(0,∞) × (0,π/2)`: the two angular endpoints `θ = 0, π/2` and the radial endpoint `z = 0` form a
null set, and at `z = 0` the integrand vanishes identically because the radial weight `w` does.
Hence it can be converted into an a.e. statement on the closed quadrant and fed into
`Integrable.mono'` against the (integrable) majorant `K · HkIntegrand α k f`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

theorem HkMemOfContMajorant (α : ℝ) (k : ℕ) {h f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkMem α k h := by
  -- a.e. strong measurability of the angular slices of the integrand of `h`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
        (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- at `z = 0` the radial weight vanishes and the integrand is identically zero
      subst h0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k h 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by
          simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
          simp
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  -- joint a.e. strong measurability of the integrand of `h`
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- the slice majorant is integrable
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => K * Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ :=
    fun z hz => (hmf.1 z hz).const_mul K
  -- so is its `z`-integral
  have hMz : IntegrableOn (fun z => K * ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := hmf.2.const_mul K
  -- the domination, upgraded to an a.e. statement on the closed angular interval
  have hle_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hmeas : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) :=
      (Measure.restrict_congr_set
        (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2)))).symm
    rw [hmeas]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hle z hz θ hθ)
  constructor
  · -- every angular slice of the integrand of `h` is integrable
    intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [hle_ae z hz] with θ hθ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable
    refine Integrable.mono hMz hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ
    have hnnK : 0 ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      mul_nonneg hK (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg hnnK]
    exact (integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
      ((hmf.1 z hz).const_mul K) (hle_ae z hz)).trans (le_of_eq (integral_const_mul K _))

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
