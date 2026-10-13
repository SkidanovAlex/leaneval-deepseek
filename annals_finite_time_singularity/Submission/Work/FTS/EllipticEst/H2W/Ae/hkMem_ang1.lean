import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.HonMemU.honMemPthTan
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Honest.HkSqAssembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `HkMem α 0 (∂_θ(tan θ · u))` in the almost-everywhere class

The angular term `ang1 u = ∂_θ(tan θ · u)` of the level-`0` estimate is honest
(`Work.Spaces.HkMem α 0`) for every datum `AeData α u G` of the almost-everywhere class,
given the honesty of `u` and of `grad u = z ∂_z u`.

## Route

On the open quadrant the equation `bslOp α u = G` rearranges (`scaled_ang1_eq`) to

  `ang1 u = α² z²∂_zz u + G + α(5+α)(z∂_z u) + ∂_θθ u + 6u`,

and each of the five summands is honest: `α² z²∂_zz u` by `AeData.memRad2` and
`HkMem_const_mul`, `G` by `AeData.memG`, `α(5+α)(z∂_z u)` by the hypothesis on `grad u`,
`∂_θθ u` by `AeData.memAng2`, and `6u` by the hypothesis on `u`.  The five-term
Cauchy–Schwarz inequality (`Honest.HkIntegrand_zero_le_five`) turns the pointwise identity
into the domination of the level-`0` integrand of `ang1 u` by `5` times the sum of the five
integrands, and `Work.Blocks.HkMem_of_majorant_aesm` upgrades that to `HkMem` once the
integrability of the majorant (on every angular slice, and of its `z`-integral) and the a.e.
strong measurability of the target integrand are supplied.  The latter follows from the
`C^∞`-regularity of `ang1 u = ∂_θ(tan θ·u)` on the open quadrant (`SmoothOpen`).
-/

/-! ## The rearrangement of the equation -/

/-- **The equation solved for `∂_θ(tan θ · u)`** on the open quadrant. -/
private theorem scaled_ang1_eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ang1 u z θ
      = α ^ 2 * rad2 u z θ + G z θ + α * (5 + α) * grad u z θ + ang2 u z θ
        + 6 * u z θ := by
  have h2 := AeData.eq h z hz θ hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, rad2, grad, ang2, ang1] at h2 ⊢
  linarith

/-- `|a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
private theorem abs_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  have n1 : 0 ≤ |a + b + c + d| := abs_nonneg _
  have n2 : 0 ≤ |a + b + c| := abs_nonneg _
  have n3 : 0 ≤ |a + b| := abs_nonneg _
  have n4 : 0 ≤ |a| := abs_nonneg _
  have n5 : 0 ≤ |b| := abs_nonneg _
  have n6 : 0 ≤ |c| := abs_nonneg _
  have n7 : 0 ≤ |d| := abs_nonneg _
  have n8 : 0 ≤ |e| := abs_nonneg _
  linarith

/-! ## The pointwise majorant and the integrability bookkeeping -/

/-- Integrability on `Iz` of the `θ`-integral of a pointwise sum of two functions, given the
integrability of the angular slices and of the two `θ`-integrals. -/
private theorem integrableOn_integral_add {f g : ℝ → ℝ → ℝ}
    (hf : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ)
    (hg : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => g z θ) Work.Spaces.Iθ)
    (hF : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) Work.Spaces.Iz)
    (hG : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ) Work.Spaces.Iz) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ + g z θ) Work.Spaces.Iz := by
  refine (hF.add hG).congr ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz
  exact (MeasureTheory.integral_add (hf z hz) (hg z hz)).symm

/-- The pointwise majorant of the level-`0` `HkIntegrand` of `∂_θ(tan θ · u)` in the
almost-everywhere class: five times the sum of the `HkIntegrand`s of the five summands of the
rearranged equation `scaled_ang1_eq`. -/
private def Maj (α : ℝ) (G u : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  5 * (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
    + Work.Spaces.HkIntegrand α 0 G z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ
    + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)

/-! ## The main lemma -/

theorem hkMem_ang1 (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u) (hd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u) := by
  -- `ang1 u` is `C^∞` on the open quadrant
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (AeData.smooth h)
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have htanu : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan huS
  have htgt : Work.FTS.EllipticEst.SmoothOpen (ang1 u) :=
    Work.FTS.EllipticEst.SmoothOpen.pth htanu
  have hcont := Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand htgt α 0
  -- the a.e. strong measurability of the integrand of `ang1 u`
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (ang1 u) p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have haesmSlice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 (ang1 u) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 (ang1 u) z θ) = fun θ => (0 : ℝ) from by
        funext θ
        rw [← hz0, Work.Spaces.HkIntegrand_zero_z]]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  have haesmOuter : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (ang1 u) z θ)
      (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
  -- the five summands of the rearranged equation are honest
  have hm1 : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * rad2 u z θ) := by
    simpa only [rad2] using
      (Work.FTS.LocData.HkMem_const_mul α 0 (α ^ 2) (AeData.memRad2 h))
  have hm2 : Work.Spaces.HkMem α 0 G := AeData.memG h
  have hm3 : Work.Spaces.HkMem α 0 (fun z θ => (α * (5 + α)) * grad u z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hd
  have hm4 : Work.Spaces.HkMem α 0 (ang2 u) := by
    simpa only [ang2] using AeData.memAng2 h
  have hm5 : Work.Spaces.HkMem α 0 (fun z θ => 6 * u z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hu
  -- integrability of the angular slices of the majorant
  have hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj α G u z θ) Work.Spaces.Iθ := by
    intro z hz
    simp only [Maj]
    have h12 : Integrable (fun θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ) (volume.restrict Work.Spaces.Iθ) :=
      (hm1.1 z hz).add (hm2.1 z hz)
    have h123 : Integrable (fun θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h12.add (hm3.1 z hz)
    have h1234 : Integrable (fun θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h123.add (hm4.1 z hz)
    have h12345 : Integrable (fun θ => (((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h1234.add (hm5.1 z hz)
    exact h12345.const_mul 5
  -- integrability of the `θ`-integral of the majorant
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Maj α G u z θ) Work.Spaces.Iz := by
    have hs1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (fun z θ => α ^ 2 * rad2 u z θ) z θ) Work.Spaces.Iz := hm1.2
    have hs2 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add
        (f := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 G z θ)
        hm1.1 hm2.1 hm1.2 hm2.2
    have hs3 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ))
        Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        (fun z hz => (hm1.1 z hz).add (hm2.1 z hz)) hm3.1 hs2 hm3.2
    have hs4 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        (fun z hz => ((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)) hm4.1 hs3 hm4.2
    have hs5 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)
        (fun z hz => (((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)).add (hm4.1 z hz))
        hm5.1 hs4 hm5.2
    have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, Maj α G u z θ)
        = fun z => 5 * ∫ θ in Work.Spaces.Iθ,
            ((((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
            + Work.Spaces.HkIntegrand α 0 G z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
            + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ) := by
      funext z
      simp only [Maj]
      exact MeasureTheory.integral_const_mul 5 _
    rw [hkey]
    exact hs5.const_mul 5
  -- the pointwise five-term domination
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (ang1 u) z θ ≤ Maj α G u z θ := by
    have hb := Work.FTS.EllipticEst.Honest.HkIntegrand_zero_le_five (α := α) (u := ang1 u)
      (g1 := fun z θ => α ^ 2 * rad2 u z θ) (g2 := G)
      (g3 := fun z θ => (α * (5 + α)) * grad u z θ) (g4 := ang2 u)
      (g5 := fun z θ => 6 * u z θ)
      (fun z hz θ hθ0 hθ1 => by
        have heq := scaled_ang1_eq h hz hθ0 hθ1
        have e : ang1 u z θ = α ^ 2 * rad2 u z θ + G z θ + (α * (5 + α)) * grad u z θ
            + ang2 u z θ + 6 * u z θ := by
          rw [heq]
        rw [e]
        exact abs_five_le _ _ _ _ _)
    intro z hz θ hθ
    simp only [Maj]
    exact hb z hz θ hθ
  exact Work.Blocks.HkMem_of_majorant_aesm α 0 haesmSlice haesmOuter hMslice hMz hle

end

end Work.FTS.EllipticEst.H2W.Ae
