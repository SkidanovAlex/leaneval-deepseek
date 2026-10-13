import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The level-`0` integrand is the square of the weighted datum

At level `0` both `Finset.range (0 + 1)`-sums of `HkIntegrand` collapse: the first one has the
single summand `i = 0`, and the second one is empty because its condition `1 ≤ i` fails there.
Hence `HkIntegrand α 0 f z θ = (Gaz f z θ)²`, with `Gaz` the weighted datum
`h z θ · w z / sin(2θ)^{η/2}` of `Work.FTS.GalBasis.cc`. -/

/-- **The level-`0` integrand is the square of the weighted datum.** -/
theorem HkIntegrand_zero_eq_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ = (Work.FTS.GalBasis.cc.Gaz f z θ) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.FTS.GalBasis.cc.Gaz, Work.FTS.GalBasis.cc.Sw]

/-! ## The pointwise domination -/

/-- **Pointwise domination of the level-`0` integrand of a difference by the level-`4`
integrands of the two terms.**  Since `Gaz (a - b) = Gaz a - Gaz b` pointwise (the weight
`w z / sin(2θ)^{η/2}` is a common factor), `(x - y)² ≤ 2(x² + y²)`, and the square of each
weighted datum is a single `D_z⁰`-summand of the `ℋ⁴`-integrand
(`Work.FTS.GalBasis.cc.Gaz_sq_le_HkIntegrand`). -/
theorem HkIntegrand_zero_sub_le {α : ℝ} {a b : ℝ → ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α 4 a z θ + Work.Spaces.HkIntegrand α 4 b z θ) := by
  have h0 : Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ
      = (Work.FTS.GalBasis.cc.Gaz a z θ - Work.FTS.GalBasis.cc.Gaz b z θ) ^ 2 := by
    rw [HkIntegrand_zero_eq_sq]
    simp only [Work.FTS.GalBasis.cc.Gaz, Work.FTS.GalBasis.cc.Sw]
    ring
  rw [h0]
  nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Gaz a z θ + Work.FTS.GalBasis.cc.Gaz b z θ),
    Work.FTS.GalBasis.cc.Gaz_sq_le_HkIntegrand α a z θ,
    Work.FTS.GalBasis.cc.Gaz_sq_le_HkIntegrand α b z θ]

/-! ## Continuity on the open quadrant -/

/-- **The level-`0` integrand of a difference of two open-class data is continuous on the
open quadrant.**  This is the only place where the smoothness hypotheses enter: `SmoothOpen`
gives the joint continuity of `a` and of `b` on `Q0`, the weight `w z / sin(2θ)^{η/2}` is
continuous there (`Work.FTS.EllipticEst.continuousOn_wdivsin_Q0`), and continuity is
preserved by subtraction, multiplication and squaring. -/
theorem continuousOn_HkIntegrand_zero_sub {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have ha' : ContinuousOn (fun p : ℝ × ℝ => a p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := ha.continuousOn
  have hb' : ContinuousOn (fun p : ℝ × ℝ => b p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hb.continuousOn
  have hw : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / Work.FTS.GalBasis.cc.Sw p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
  have hfun : (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) p.1 p.2)
      = fun p : ℝ × ℝ => ((a p.1 p.2 - b p.1 p.2)
          * (Work.Spaces.w p.1 / Work.FTS.GalBasis.cc.Sw p.2)) ^ 2 := by
    funext p
    simp [Work.Spaces.HkIntegrand, Work.FTS.GalBasis.cc.Sw]
  rw [hfun]
  exact ((ha'.sub hb').mul hw).pow 2

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `HkMemZeroSub`.
The difference of two open-class `ℋ⁴`-data is `ℋ⁰`, with the `ℋ⁰`-size controlled by the two
`ℋ⁴`-sizes.  With `Gaz h z θ = h z θ · w z / sin(2θ)^{η/2}` one has the pointwise identity
`Work.Spaces.HkIntegrand α 0 h z θ = (Gaz h z θ)²` (the `k = 0` integrand has only the `i = 0`
summand of the first sum and an empty second sum), hence

`HkIntegrand α 0 (a-b) z θ ≤ 2 · (HkIntegrand α 4 a z θ + HkIntegrand α 4 b z θ)`

because `Gaz (a-b) = Gaz a - Gaz b` pointwise and `(x-y)² ≤ 2(x²+y²)`, using
`Work.FTS.GalBasis.cc.Gaz_sq_le_HkIntegrand` for the passage to order `4`.  Membership follows from
`Work.FTS.LocData.HkMem_of_majorant` applied with the majorant
`M z θ := 2 · (HkIntegrand α 4 a z θ + HkIntegrand α 4 b z θ)`: the `θ`-slices and the slice
integral of `M` are integrable by `hma`/`hmb`, and the *continuity* of
`(z,θ) ↦ HkIntegrand α 0 (a-b) z θ = (Gaz (a-b) z θ)²` on the open quadrant (the only place where
`SmoothOpen` is used) follows from `SmoothOpen.continuousOn` of `a` and `b` together with the
continuity of `(z,θ) ↦ w z / sin(2θ)^{η/2}` on the open quadrant
(`Work.FTS.EllipticEst.continuousOn_wdivsin_Q0`).  The `HkSq` bound is then the integral of the
pointwise inequality. -/
theorem HkMemZeroSub {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    Work.Spaces.HkMem α 0 (fun z θ => a z θ - b z θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => a z θ - b z θ)
        ≤ 2 * (Work.Spaces.HkSq α 4 a + Work.Spaces.HkSq α 4 b) := by
  -- the majorant `M` of the statement
  let M : ℝ → ℝ → ℝ := fun z θ =>
    2 * (Work.Spaces.HkIntegrand α 4 a z θ + Work.Spaces.HkIntegrand α 4 b z θ)
  -- the three integrability hypotheses of `HkMem_of_majorant`
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => 2 * (Work.Spaces.HkIntegrand α 4 a z θ
      + Work.Spaces.HkIntegrand α 4 b z θ)) Work.Spaces.Iθ
    exact ((hma.1 z hz).add (hmb.1 z hz)).const_mul 2
  have hMeq : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, M z θ)
      = 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 a z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ) := by
    intro z hz
    rw [show M z = (fun θ => 2 * (Work.Spaces.HkIntegrand α 4 a z θ
        + Work.Spaces.HkIntegrand α 4 b z θ)) from rfl]
    rw [integral_const_mul, integral_add (hma.1 z hz) (hmb.1 z hz)]
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz := by
    refine IntegrableOn.congr_fun (((hma.2.add hmb.2).const_mul 2)) ?_ measurableSet_Ici
    intro z hz
    exact (hMeq z hz).symm
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ ≤ M z θ := by
    intro z hz θ hθ
    simpa only [M] using HkIntegrand_zero_sub_le (α := α) (a := a) (b := b) z θ
  -- membership
  have hmem : Work.Spaces.HkMem α 0 (fun z θ => a z θ - b z θ) :=
    Work.FTS.LocData.HkMem_of_majorant α 0
      (continuousOn_HkIntegrand_zero_sub ha hb) hMslice hMz hle
  refine ⟨hmem, ?_⟩
  -- the size bound: integrate the pointwise domination against the integrable majorant
  have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
    intro z hz
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (hMslice z hz) ?_
    show ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (π / 2))),
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ ≤ M z θ
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall fun θ hθ => hle z hz θ hθ
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 a z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ) := by
    refine integral_mono_ae hmem.2 ((hma.2.add hmb.2).const_mul 2) ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ici (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
        ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 a z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ)
    rw [ae_restrict_iff' measurableSet_Ici]
    exact Eventually.of_forall fun z hz =>
      le_trans (hinner z hz) (le_of_eq (hMeq z hz))
  have hfinal : (∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 a z θ)
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ))
      = 2 * (Work.Spaces.HkSq α 4 a + Work.Spaces.HkSq α 4 b) := by
    rw [integral_const_mul, integral_add hma.2 hmb.2]
    rfl
  rw [Work.Spaces.HkSq]
  exact le_trans houter hfinal.le

end Work.FTS.StrongEps.L12
