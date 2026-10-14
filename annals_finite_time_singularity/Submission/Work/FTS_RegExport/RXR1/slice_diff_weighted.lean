import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_MuLipC.Poly0.n0_poly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_MuLipC.Poly0

/-- **Additivity of `L₁₂` on the open class.**  For two data that are `C^∞` on the open quadrant
and honest in `ℋ⁴`, the integral operator `L₁₂` is additive at every `z ≥ 0`.  This is
`Work.FTS.LocData.L12_add_mul` with its four integrability inputs supplied by the `ℋ⁴`-honesty
(`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`,
`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`). -/
theorem L12_add_of_SmoothOpen_HkMem {α : ℝ} {a b : Work.FTS.Galerkin.Fn}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (fun z θ => a z θ + b z θ) z
        = Work.Construction.L12 a z + Work.Construction.L12 b z := by
  intro z hz
  refine (Work.FTS.LocData.L12_add_mul (c := 0) (a := a) (b := b) (z := z) ?_ ?_ ?_ ?_).1
  · exact fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem ha hma
      (lt_of_le_of_lt hz hs)
  · exact fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hb hmb
      (lt_of_le_of_lt hz hs)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem ha hma).mono_set
      (Set.Ioi_subset_Ioi hz)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hb hmb).mono_set
      (Set.Ioi_subset_Ioi hz)


end Work.FTS_MuLipC.Poly0
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.L12Ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The angular density of a difference is the difference of the angular densities, a.e. in `s`:
at every `s` where both θ-slices are integrable the two integrands differ pointwise, so
`MeasureTheory.integral_sub` applies. -/
theorem L12dens_sub_ae {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun s => Work.Construction.L12dens a s - Work.Construction.L12dens b s) := by
  filter_upwards [h1, h2] with s hs1 hs2
  have hpt : (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s)
      = fun θ => Work.Spaces.K θ * a s θ / s - Work.Spaces.K θ * b s θ / s := by
    funext θ
    ring
  simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  rw [hpt]
  exact MeasureTheory.integral_sub hs1 hs2

/-- The `L₁₂`-density of a difference is integrable as soon as the two densities are integrable
and the two θ-slices are a.e. integrable. -/
theorem integrableOn_L12dens_sub {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    MeasureTheory.IntegrableOn
      (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s) (Set.Ioi z) :=
  (h3.sub h4).congr (L12dens_sub_ae h1 h2).symm

/-- **`L₁₂` is additive on a difference of fields**, in the a.e. form: if the θ-slices of `a`
and `b` are a.e. integrable on `Ioi z` and the densities of `a - b` and `b` are integrable,
then `L₁₂ a z = L₁₂ (a - b) z + L₁₂ b z`.  This is
`Work.FTS.LocData.L12_add_mul` with its (pointwise) slice hypothesis weakened to an a.e. one:
the outer integral only sees a.e. values. -/
theorem L12_ae_sub {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 a z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z + Work.Construction.L12 b z := by
  have hkey : (fun s => Work.Construction.L12dens a s)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s
          + Work.Construction.L12dens b s) := by
    filter_upwards [L12dens_sub_ae h1 h2] with s hs
    rw [hs]
    ring
  have hkey' : ∀ᵐ s ∂(MeasureTheory.volume : Measure ℝ), s ∈ Set.Ioi z →
      Work.FM.L12dens Work.Spaces.K a s
        = Work.FM.L12dens Work.Spaces.K (fun z θ => a z θ - b z θ) s
          + Work.FM.L12dens Work.Spaces.K b s :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hkey
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hkey']
  exact MeasureTheory.integral_add h3 h4

/-- **Homogeneity of `L₁₂` in a constant**, with no hypothesis at all (both sides are the
integral of pointwise equal integrands, and `MeasureTheory.integral_const_mul` is
unconditional). -/
theorem L12_const_mul (c : ℝ) (a : Fn) (z : ℝ) :
    Work.Construction.L12 (fun z θ => c * a z θ) z = c * Work.Construction.L12 a z := by
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s _ => Work.FTS.LocData.L12dens_const_mul Work.Spaces.K c a s)]
  exact MeasureTheory.integral_const_mul c _

/-- **`L₁₂` only sees the values on the open quadrant** (`Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ`,
transported to `Work.Construction.L12`). -/
theorem L12_congrQd {a b : Fn} {z : ℝ} (hz : 0 ≤ z)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → a z θ = b z θ) :
    Work.Construction.L12 a z = Work.Construction.L12 b z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ hz h

/-! ## Congruence and combinations of the slices -/

/-- The angular density only sees the pointwise values of the field. -/
theorem L12dens_congr {X Y : Fn} (h : ∀ z θ : ℝ, X z θ = Y z θ) :
    Work.Construction.L12dens X = Work.Construction.L12dens Y := by
  funext s
  simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [h s θ])

/-- A.e. slice integrability of a difference. -/
theorem slices_sub {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (fun z θ => a z θ - b z θ) s θ / s) Work.Spaces.Iθ := by
  filter_upwards [h1, h2] with s hs1 hs2
  have hpt : (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s)
      = fun θ => Work.Spaces.K θ * a s θ / s - Work.Spaces.K θ * b s θ / s := by
    funext θ
    ring
  rw [hpt]
  exact hs1.sub hs2


/-! ## The linearity statements used by the difference row -/

/-- **`L₁₂` is additive on a difference**, with the density hypotheses carried by the two
fields themselves (the density of the difference is then integrable by
`integrableOn_L12dens_sub`). -/
theorem L12_ae_sub_of_dens {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 a z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z + Work.Construction.L12 b z :=
  L12_ae_sub h1 h2 (integrableOn_L12dens_sub h1 h2 h3 h4) h4

/-- The subtraction form of the a.e. additivity. -/
theorem L12_sub_eq {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 a z - Work.Construction.L12 b z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z := by
  have h := L12_ae_sub_of_dens h1 h2 h3 h4
  rw [h]
  ring


/-- The angular density of the negative is the negative of the density (unconditional). -/
theorem L12dens_neg (b : Fn) :
    Work.Construction.L12dens (fun z θ => -b z θ)
      = fun s => - Work.Construction.L12dens b s := by
  have h1 : (fun z θ => -b z θ) = fun z θ => (-1 : ℝ) * b z θ := by
    funext z θ
    ring
  funext s
  rw [show Work.Construction.L12dens (fun z θ => -b z θ) s
      = Work.FM.L12dens Work.Spaces.K (fun z θ => -b z θ) s from rfl, h1,
    Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-1) b s, neg_one_mul]
  rfl

/-- A.e. slice integrability of the negative. -/
theorem slices_neg {b : Fn} {z : ℝ}
    (h : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (fun z θ => -b z θ) s θ / s) Work.Spaces.Iθ := by
  filter_upwards [h] with s hs
  have hpt : (fun θ => Work.Spaces.K θ * (-b s θ) / s)
      = fun θ => - (Work.Spaces.K θ * b s θ / s) := by
    funext θ
    ring
  rw [hpt]
  exact hs.neg

/-- The density of the negative field is integrable. -/
theorem integrableOn_L12dens_neg {b : Fn} {z : ℝ}
    (h : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (fun z θ => -b z θ))
      (Set.Ioi z) :=
  (L12dens_neg b).symm ▸ h.neg

/-- The addition form of the a.e. additivity. -/
theorem L12_add_eq {a b : Fn} {z : ℝ} (hz : 0 ≤ z)
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => a z θ + b z θ) z
      = Work.Construction.L12 a z + Work.Construction.L12 b z := by
  have hsl_neg := slices_neg (z := z) h2
  have hden_neg : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => -b z θ)) (Set.Ioi z) :=
    integrableOn_L12dens_neg h4
  have hmain := L12_ae_sub h1 hsl_neg (integrableOn_L12dens_sub h1 hsl_neg h3 hden_neg) hden_neg
  have hneg : Work.Construction.L12 (fun z θ => -b z θ) z
      = - Work.Construction.L12 b z := by
    have h1' : (fun z θ => -b z θ) = fun z θ => (-1 : ℝ) * b z θ := by
      funext z θ
      ring
    rw [h1', L12_const_mul]
    ring
  have hbridge : Work.Construction.L12 (fun z θ => a z θ + b z θ) z
      = Work.Construction.L12 (fun z θ => a z θ - (-b z θ)) z :=
    L12_congrQd hz (fun z θ _ _ _ => by ring)
  rw [hbridge, hmain, hneg]
  ring

/-- **`L₁₂` on an alternating four-term sum of fields**: all that the polarization of the
difference row needs. -/
theorem L12_alt4 {A1 A2 A3 A4 : Fn} {z : ℝ} (hz : 0 ≤ z)
    (hs1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A1 s θ / s) Work.Spaces.Iθ)
    (hs2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A2 s θ / s) Work.Spaces.Iθ)
    (hs3 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A3 s θ / s) Work.Spaces.Iθ)
    (hs4 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A4 s θ / s) Work.Spaces.Iθ)
    (hd1 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A1) (Set.Ioi z))
    (hd2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A2) (Set.Ioi z))
    (hd3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A3) (Set.Ioi z))
    (hd4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A4) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => A1 z θ - A2 z θ + A3 z θ - A4 z θ) z
      = Work.Construction.L12 A1 z - Work.Construction.L12 A2 z
        + Work.Construction.L12 A3 z - Work.Construction.L12 A4 z := by
  have hsub12 : Work.Construction.L12 A1 z - Work.Construction.L12 A2 z
      = Work.Construction.L12 (fun z θ => A1 z θ - A2 z θ) z := L12_sub_eq hs1 hs2 hd1 hd2
  have hsub34 : Work.Construction.L12 A3 z - Work.Construction.L12 A4 z
      = Work.Construction.L12 (fun z θ => A3 z θ - A4 z θ) z := L12_sub_eq hs3 hs4 hd3 hd4
  have hden12 : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => A1 z θ - A2 z θ)) (Set.Ioi z) :=
    integrableOn_L12dens_sub hs1 hs2 hd1 hd2
  have hden34 : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => A3 z θ - A4 z θ)) (Set.Ioi z) :=
    integrableOn_L12dens_sub hs3 hs4 hd3 hd4
  have hsl12 := slices_sub hs1 hs2
  have hsl34 := slices_sub hs3 hs4
  have hadd := L12_add_eq hz hsl12 hsl34 hden12 hden34
  have hbridge : Work.Construction.L12 (fun z θ => A1 z θ - A2 z θ + A3 z θ - A4 z θ) z
      = Work.Construction.L12
          (fun z θ => (fun z θ => A1 z θ - A2 z θ) z θ
            + (fun z θ => A3 z θ - A4 z θ) z θ) z :=
    L12_congrQd hz (fun z θ _ _ _ => by ring)
  rw [hbridge, hadd, ← hsub12, ← hsub34]
  ring

end Work.FTS_MuLipC.RowN
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.DiffExpand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN0

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "N0" => Work.Construction.N0
local notation "L12" => Work.Construction.L12
local notation "Fstar" => Work.Construction.Fstar
local notation "Ftot" => Work.Construction.Ftot
local notation "Dz" => Work.Spaces.Dz
local notation "Dth" => Work.Spaces.Dth
local notation "c2m" => Work.Construction.c2m
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Hk" => Work.Spaces.HkIntegrand

/-! ## The pointwise telescoping of the difference -/

/-- **The pointwise telescoping of `Sn0` along the difference `d = f - f'`.**  On the open
quadrant the difference of the two fields splits into three groups of three terms each:
`D₁ = L₁₂(f)(z)·E₁/α`, `D₂ = L₁₂(d)(z)·E₂/α` and `D₃ = L₁₂(d)(z)·E₃/α − c₂·L₁₂(F_*)(z)·D_zd`,
where `E₁ = d + (3/2)D_θd − αc₂D_zd` and `E₂`, `E₃` are the analogues for `f'` and `F_*`. -/
theorem Sn0_sub_expand {α : ℝ} {f f' d : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f')
    (hmd : Work.Spaces.HkMem α 4 d)
    (hddef : ∀ z θ, d z θ = f z θ - f' z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Sn0 α f z θ - Sn0 α f' z θ
        = (L12 f z) * (d z θ / α + (3 / (2 * α)) * Dth d z θ - c2m θ * Dz d z θ)
          + (L12 d z) * (f' z θ / α + (3 / (2 * α)) * Dth f' z θ - c2m θ * Dz f' z θ)
          + (L12 d z) * ((3 / (2 * α)) * Dth (Fstar α) z θ - c2m θ * Dz (Fstar α) z θ)
          - c2m θ * (L12 (Fstar α) z) * Dz d z θ := by
  intro z θ hz h1 h2
  have hF : Work.FTS.EllipticEst.SmoothOpen (Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hL : L12 f z = L12 d z + L12 f' z :=
    Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0 hf hf' hd hmf hmf' hmd hddef hz.le
  have hpth : Work.Spaces.pth (Ftot α f) z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hf hz ⟨h1, h2⟩
  have hpth' : Work.Spaces.pth (Ftot α f') z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth f' z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hf' hz ⟨h1, h2⟩
  have hDz : Dz (Ftot α f) z θ = Dz (Fstar α) z θ + Dz f z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hf hz ⟨h1, h2⟩)
  have hDz' : Dz (Ftot α f') z θ = Dz (Fstar α) z θ + Dz f' z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hf' hz ⟨h1, h2⟩)
  have hpthd : Work.Spaces.pth d z θ = Work.Spaces.pth f z θ - Work.Spaces.pth f' z θ := by
    rw [Work.FTS.PhiStar.CoreAux.pth_congr_Q0 (f := d) (g := fun z θ => f z θ - f' z θ)
      (fun z θ _ _ _ => hddef z θ) z θ hz h1 h2]
    exact Work.FTS.StrongEps.EComparison.pth_sub hf hf' hz h1 h2
  have hpzd : Work.Spaces.pz d z θ = Work.Spaces.pz f z θ - Work.Spaces.pz f' z θ := by
    rw [Work.FTS.GalFields.RHS.Sharp.pz_congr_Q0 (f := d) (g := fun z θ => f z θ - f' z θ)
      (fun z θ _ _ _ => hddef z θ) z θ hz h1 h2]
    exact Work.FTS.StrongEps.EComparison.pz_sub hf hf' hz h1 h2
  have hDzd : Dz d z θ = Dz f z θ - Dz f' z θ := by
    simp only [Work.Spaces.Dz]
    rw [hpzd]
    ring
  simp only [Work.FTS_MuLipC.Sn0, Work.Construction.N0, Work.Construction.Ftot,
    Work.Construction.s2, Work.Spaces.Dth]
  rw [hpth, hpth', hDz, hDz', hL, hpthd, hDzd, hddef z θ]
  ring

/-! ## Elementary bounds -/

/-- The identity `(r/(1+r)²)²·w(r) = (1/(1+r))²` for `r > 0`. -/
theorem sq_div_shape_eq {r : ℝ} (hr : 0 < r) :
    (r / (1 + r) ^ 2) ^ 2 * Work.Spaces.w r = (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- `w(r) ≥ 1` for `r > 0`. -/
theorem one_le_w {r : ℝ} (hr : 0 < r) : 1 ≤ Work.Spaces.w r := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

/-- `w(r) > 0` for `r > 0`. -/
theorem w_pos {r : ℝ} (hr : 0 < r) : 0 < Work.Spaces.w r :=
  lt_of_lt_of_le one_pos (one_le_w hr)

/-- `|cos 2θ - sin²θ| ≤ 2`. -/
theorem abs_c2m_le (θ : ℝ) : |c2m θ| ≤ 2 := by
  have hs1 : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
  rw [Work.Construction.c2m, abs_le]
  constructor
  · nlinarith [Real.neg_one_le_cos (2 * θ), hs1]
  · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]

/-- `|K θ| ≤ 3` on `Iθ`. -/
theorem abs_K_le (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h3 : |Real.cos θ * Real.cos θ| ≤ 1 := by
    nlinarith [h2, abs_nonneg (Real.cos θ), abs_mul (Real.cos θ) (Real.cos θ)]
  have hK : Work.Spaces.K θ = 3 * Real.sin θ * (Real.cos θ * Real.cos θ) := by
    rw [Work.Spaces.K]; ring
  rw [hK, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [h1, h3, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ * Real.cos θ)]

/-- The `θ`-slices of the `L₁₂`-density of a square-integrable slice are integrable. -/
theorem integrableOn_K_mul_div {X : Fn} {r : ℝ} (hr : 0 < r)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun θ => X r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hsq : MeasureTheory.IntegrableOn (fun θ => (X r θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * X r θ / r) Work.Spaces.Iθ := by
  have hK : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have haesm2 : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * X r θ / r) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((((hK.aemeasurable).mul haesm.aemeasurable)).div_const r).aestronglyMeasurable
  have hgint : MeasureTheory.IntegrableOn
      (fun θ => (3 / (2 * r)) * ((X r θ) ^ 2 + 1)) Work.Spaces.Iθ := by
    refine (hsq.add (MeasureTheory.integrableOn_const ?_)).const_mul ((3 : ℝ) / (2 * r))
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono' hgint haesm2 ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  have hK3 := abs_K_le θ
  have h2 : |X r θ| ≤ ((X r θ) ^ 2 + 1) / 2 := by
    nlinarith [abs_nonneg (X r θ), sq_abs (X r θ), sq_nonneg (|X r θ| - 1)]
  have h1 : |Work.Spaces.K θ| * |X r θ| ≤ 3 * (((X r θ) ^ 2 + 1) / 2) :=
    mul_le_mul hK3 h2 (abs_nonneg _) (by norm_num)
  have h3 : (3 / (2 * r)) * ((X r θ) ^ 2 + 1) = 3 * (((X r θ) ^ 2 + 1) / 2) / r := by
    field_simp
  rw [abs_div, abs_mul, abs_of_pos hr, h3]
  exact div_le_div_of_nonneg_right h1 hr.le

end Work.FTS_MuLipC.RowN0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.slice_diff_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.slice_diff_weighted`

The mixed slots of order `≤ 1` of the difference of two slices `slice g τ - slice g τ'` of a
`LimApprox` family decay like the weight `z^{3/2}/(1+z)²`, uniformly on every horizon `[0,T]`,
with a Lipschitz factor `|τ - τ'|` in the fake time.

The proof has three ingredients.

* The approximating families `gn` of the `LimApprox` clause are class-`C` on every slice, and
  `ClassC` is a subspace, so the *difference* `H_n := slice (gn n) τ - slice (gn n) τ'` is again
  class-`C`; `classC_sub_hyp` then supplies `SmoothOpen`, `HkMem β 4` and `BdryTraces β 4` for it,
  so the weighted slot bound `hw` applies at every order `a + b ≤ 2`:
  `|mixed b a H_n| ≤ Cw · SliceW z · |H_n|_{ℋ⁴}`, and `|H_n|_{ℋ⁴} ≤ L|τ - τ'|` is the Lipschitz
  clause of `LimApprox`.
* The `Qd`-jet convergence clause identifies the pointwise limits of `mixed b a H_n` with the
  *difference of the limit slots* `mixed b a (slice g τ) - mixed b a (slice g τ')`: the identity
  `mixed b a (F - G) = mixed b a F - mixed b a G` holds on the open quadrant for the smooth
  approximants (`TTSlot11Aux.mixed_sub_open`).
* At order `≤ 1` the slot of the *limit difference* `mixed b a (slice g τ - slice g τ')` equals the
  difference of the limit slots: for `(b,a) = (0,0)` this is definitional; for `(1,0)` and
  `(0,1)` it is the "derivative of a pointwise limit" statement, which holds because the
  first-order approximant slots are equi-Lipschitz on compacts (`hw` at orders `1` and `2` supply
  the uniform bounds `pzIter_bound_weighted` / `pthIter_le_of_weighted`), so the limit is
  differentiable with the pointwise limit of the derivatives as derivative
  (`hasDerivAt_of_tendsto_deriv`).
-/

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_RegExport.RXR1

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `θ`-derivative of the `θ`-slice** of a function `C^∞` on the open quadrant (companion of
`EllipticEst.SmoothOpen.hasDerivAt_slice`). -/
theorem smoothOpen_hasDerivAt_thslice {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => f z θ') (Work.Spaces.pthIter 1 f z θ) θ :=
  (((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

theorem slice_diff_weighted {β C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hA : Work.FTS.FinalV2.LimApprox β C₀ Φs E g)
    (hw : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem β 4 f →
      Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm β 4 f)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T,
      ∀ b a : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
  obtain ⟨Cw, hCw0, hwraw⟩ := hw
  have hwB : HwBnd β Cw := fun f h1 h2 h3 b a hab z θ hz hθ hθ2 => hwraw f h1 h2 h3 b a hab z θ hz hθ hθ2
  obtain ⟨Kz, hKz0, hzbd⟩ := pzIter_bound_weighted hCw0 hwB
  obtain ⟨Kt, hKt0, htbd⟩ := pthIter_le_of_weighted hCw0 hwB
  obtain ⟨gn, B, L₀, hC, hLip, hjet, hmu⟩ := hA T hT
  refine ⟨Cw * max L₀ 0, mul_nonneg hCw0 (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hL0 : (0 : ℝ) ≤ max L₀ 0 := le_max_right _ _
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  -- ## step 1: the approximant differences are honest class-`C⁴` data
  have hsmH : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) :=
    fun n => (classC_sub_hyp (hC n τ hτ).1 (hC n τ' hτ').1).1
  have hmemH : ∀ n : ℕ, Work.Spaces.HkMem β 4
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) :=
    fun n => (classC_sub_hyp (hC n τ hτ).1 (hC n τ' hτ').1).2.1
  have htrH : ∀ n : ℕ, Work.FTS.Nonlin.BdryTraces β 4
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) :=
    fun n => (classC_sub_hyp (hC n τ hτ).1 (hC n τ' hτ').1).2.2
  have hHk : ∀ n : ℕ, Work.Spaces.HkNorm β 4
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
      ≤ max L₀ 0 * |τ - τ'| := by
    intro n
    exact (hLip n τ hτ τ' hτ').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  -- ## step 2: the uniform weighted bound on the approximant differences, all orders `≤ 2`
  have hmain : ∀ n : ℕ, ∀ b a : ℕ, a + b ≤ 2 →
      |Work.Spaces.mixed b a
        (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
        z θ| ≤ Cw * SliceW z * (max L₀ 0 * |τ - τ'|) := by
    intro n b a hab2
    exact (hwB _ (hsmH n) (hmemH n) (htrH n) b a hab2 z θ hz hθ0 hθ1).trans
      (mul_le_mul_of_nonneg_left (hHk n) (mul_nonneg hCw0 (SliceW_nonneg hz.le)))
  -- ## step 3: the pointwise limit slot
  have hsub : ∀ n : ℕ, Work.Spaces.mixed b a
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ
      = Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ :=
    fun n => Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).1.reg
      (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
  set Lam : ℝ := Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
    - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ with hLam
  have hLamBd : |Lam| ≤ Cw * SliceW z * (max L₀ 0 * |τ - τ'|) := by
    have hconv : Tendsto (fun n : ℕ => Work.Spaces.mixed b a
        (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
        z θ) atTop (𝓝 Lam) := by
      rw [show (fun n : ℕ => Work.Spaces.mixed b a
          (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
          z θ)
        = fun n : ℕ => (Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
            - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ) from
        funext (fun n => hsub n)]
      rw [hLam]
      exact (hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)
    exact le_of_tendsto hconv.abs (Eventually.of_forall (fun n => hmain n b a (by omega)))
  -- ## step 4: the case analysis
  rcases (by omega : b = 0 ∧ a = 0 ∨ b = 1 ∧ a = 0 ∨ b = 0 ∧ a = 1)
    with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `(b,a) = (0,0)`: the slot is the value itself
    have heq : |Work.Spaces.mixed 0 0
        (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| = |Lam| := by
      rw [hLam]
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, Pi.sub_apply]
    rw [heq]
    exact hLamBd.trans (le_of_eq (by ring))
  · -- `(b,a) = (1,0)`
    have hzint : z ∈ Set.Ioo (z / 2) (2 * z + 1) := ⟨by linarith, by linarith⟩
    have hder : ∀ n : ℕ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        HasDerivAt (fun z'' : ℝ => Work.FTS.Galerkin.slice (gn n) τ z'' θ
            - Work.FTS.Galerkin.slice (gn n) τ' z'' θ)
          (Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ) z' :=
      fun n z' hz' => (hsmH n).hasDerivAt_slice hθ (by linarith [hz'.1, hz])
    have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ
        (fun z' : ℝ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ) (Set.Ioo (z / 2) (2 * z + 1)) :=
      fun n z' hz' => ((hsmH n).hasDerivAt_slice_pzIter 1 hθ (by linarith [hz'.1, hz]))
        |>.differentiableAt.differentiableWithinAt
    have hMd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        |Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ| ≤ M := by
      refine ⟨Kz * Real.sqrt (2 * z + 1) * (max L₀ 0 * |τ - τ'|), by positivity, ?_⟩
      intro n z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      refine ((hzbd _ (hsmH n) (hmemH n) (htrH n) z' θ hz'0 hθ0 hθ1).1).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left
        (SliceW_div_le_sqrt hz hz'.1.le hz'.2.le) hKz0)
        (hHk n) (Work.Spaces.HkNorm_nonneg β 4 _) (by positivity)
    have hLd : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        |deriv (fun z'' : ℝ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z'' θ) z'| ≤ L := by
      refine ⟨Kz * (z / 2) ^ (-(1 : ℝ) / 2) * (max L₀ 0 * |τ - τ'|), by positivity, ?_⟩
      intro n z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      have hderiv : deriv (fun z'' : ℝ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z'' θ) z'
          = Work.Spaces.pzIter 2 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ :=
        ((hsmH n).hasDerivAt_slice_pzIter 1 hθ hz'0).deriv
      rw [hderiv]
      refine ((hzbd _ (hsmH n) (hmemH n) (htrH n) z' θ hz'0 hθ0 hθ1).2).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left
        (SliceW_div_sq_le hz hz'.1.le) hKz0)
        (hHk n) (Work.Spaces.HkNorm_nonneg β 4 _) (by positivity)
    have hu : ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        Tendsto (fun n : ℕ => Work.FTS.Galerkin.slice (gn n) τ z' θ
            - Work.FTS.Galerkin.slice (gn n) τ' z' θ) atTop
          (𝓝 (Work.FTS.Galerkin.slice g τ z' θ - Work.FTS.Galerkin.slice g τ' z' θ)) := by
      intro z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      have h1 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ) z' θ)
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z' θ)) :=
        hjet τ hτ 0 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩
      have h2 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ') z' θ)
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ') z' θ)) :=
        hjet τ' hτ' 0 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h1.sub h2
    have hv : ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        Tendsto (fun n : ℕ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ) atTop
          (𝓝 ((Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z' θ
            - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z' θ) / z')) := by
      intro z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      have hconv : Tendsto (fun n : ℕ => Work.Spaces.mixed 1 0
          (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
          z' θ) atTop
          (𝓝 (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z' θ
            - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z' θ)) := by
        rw [show (fun n : ℕ => Work.Spaces.mixed 1 0
            (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
            z' θ)
          = fun n : ℕ => (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice (gn n) τ) z' θ
              - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice (gn n) τ') z' θ) from
          funext (fun n => Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).1.reg
            (hC n τ' hτ').1.reg 1 0 z' θ hz'0 hθ0 hθ1)]
        exact (hjet τ hτ 1 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩).sub
          (hjet τ' hτ' 1 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩)
      exact Filter.Tendsto.congr (fun n => by
        rw [Work.FTS_RegExport.RXR1.mixed_one_zero_eq]
        field_simp) (hconv.div_const z')
    have hlim := hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z + 1) (by linarith)
      (u := fun n z'' => Work.FTS.Galerkin.slice (gn n) τ z'' θ
        - Work.FTS.Galerkin.slice (gn n) τ' z'' θ)
      (v := fun n z'' => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
        - Work.FTS.Galerkin.slice (gn n) τ' z θ) z'' θ)
      (φ := fun z'' => Work.FTS.Galerkin.slice g τ z'' θ - Work.FTS.Galerkin.slice g τ' z'' θ)
      (γ := fun z'' => (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z'' θ
        - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z'' θ) / z'')
      hder hvdiff hMd hLd hu hv z hzint
    have hident : Work.Spaces.mixed 1 0
        (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ = Lam := by
      have hfun : (fun z' : ℝ => (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z' θ)
          = fun z' : ℝ => Work.FTS.Galerkin.slice g τ z' θ - Work.FTS.Galerkin.slice g τ' z' θ := by
        funext z'; rfl
      have hd : deriv (fun z' : ℝ =>
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z' θ) z
          = (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z θ) / z := by
        rw [hfun]; exact hlim.deriv
      rw [hLam]
      rw [show Work.Spaces.mixed 1 0
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ
          = z * deriv (fun z' : ℝ =>
              (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z' θ) z from rfl]
      rw [hd]
      field_simp
    rw [hident]
    exact hLamBd.trans (le_of_eq (by ring))
  · -- `(b,a) = (0,1)`
    -- the neighbourhood of `θ` on which `sin (2θ')` stays above `m := min (sin θ) (cos θ)`
    set m : ℝ := min (Real.sin θ) (Real.cos θ) with hmdef
    have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    have hcosθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    have hm : 0 < m := by rw [hmdef]; exact lt_min hsinθ hcosθ
    have hθin : θ ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) := ⟨by linarith, by linarith⟩
    have h2π : (θ + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
    have hsenv : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        m ≤ Real.sin (2 * θ') := by
      intro θ' hθ'
      have h1 : θ < 2 * θ' := by linarith [hθ'.1]
      have h2 : 2 * θ' < θ + Real.pi / 2 := by linarith [hθ'.2]
      by_cases hle : 2 * θ' ≤ Real.pi / 2
      · refine le_trans (min_le_left _ _) ?_
        exact Real.monotoneOn_sin
          (by constructor <;> linarith [Real.pi_pos])
          (by constructor <;> linarith [Real.pi_pos]) h1.le
      · have hlt : Real.pi / 2 < 2 * θ' := not_le.mp hle
        rw [← Real.sin_pi_sub (2 * θ')]
        refine le_trans (min_le_right _ _) ?_
        have h5 : Real.pi / 2 - θ ≤ Real.pi - 2 * θ' := by linarith
        have h6 : Real.pi - 2 * θ' ≤ Real.pi / 2 := by linarith
        have h7 := Real.monotoneOn_sin
          (by constructor <;> linarith [Real.pi_pos])
          (by constructor <;> linarith [Real.pi_pos]) h5
        rwa [Real.sin_pi_div_two_sub] at h7
    have hθ'pos : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2), 0 < θ' :=
      fun θ' hθ' => by linarith [hθ'.1, hθ0]
    have hθ'lt : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2), θ' < Real.pi / 2 :=
      fun θ' hθ' => by linarith [hθ'.2, hθ1]
    have hdiv : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        SliceW z / Real.sin (2 * θ') ≤ SliceW z / m := by
      intro θ' hθ'
      exact div_le_div_of_nonneg_left (SliceW_nonneg hz.le) hm (hsenv θ' hθ')
    have hdivsq : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        SliceW z / (Real.sin (2 * θ') * Real.sin (2 * θ')) ≤ SliceW z / (m * m) := by
      intro θ' hθ'
      refine div_le_div_of_nonneg_left (SliceW_nonneg hz.le) (by positivity) ?_
      exact mul_le_mul (hsenv θ' hθ') (hsenv θ' hθ') hm.le
        (le_trans hm.le (hsenv θ' hθ'))
    have hder : ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        HasDerivAt (fun θ'' : ℝ => Work.FTS.Galerkin.slice (gn n) τ z θ''
            - Work.FTS.Galerkin.slice (gn n) τ' z θ'')
          (Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ') θ' :=
      fun n θ' hθ' => smoothOpen_hasDerivAt_thslice (hsmH n) hz
        ⟨hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
    have h2deriv : ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        HasDerivAt (fun θ'' : ℝ => Work.Spaces.pthIter 1 (fun z θ =>
            Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'')
          (Work.Spaces.pthIter 2 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ') θ' :=
      fun n θ' hθ' => smoothOpen_hasDerivAt_thslice ((hsmH n).pth) hz
        ⟨hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
    have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ
        (fun θ' : ℝ => Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ')
        (Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2)) :=
      fun n θ' hθ' => (h2deriv n θ' hθ').differentiableAt.differentiableWithinAt
    have hMd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        |Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'| ≤ M := by
      refine ⟨Kt * (SliceW z / m) * (max L₀ 0 * |τ - τ'|),
        mul_nonneg (mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) hm.le)) (by positivity), ?_⟩
      intro n θ' hθ'
      refine ((htbd _ (hsmH n) (hmemH n) (htrH n) z θ' hz (hθ'pos θ' hθ')
        (hθ'lt θ' hθ')).1).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hdiv θ' hθ') hKt0) (hHk n)
        (Work.Spaces.HkNorm_nonneg β 4 _) ?_
      exact mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) hm.le)
    have hLd : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        |deriv (fun θ'' : ℝ => Work.Spaces.pthIter 1 (fun z θ =>
            Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'') θ'|
          ≤ L := by
      refine ⟨Kt * (SliceW z / (m * m)) * (max L₀ 0 * |τ - τ'|),
        mul_nonneg (mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) (by positivity))) (by positivity), ?_⟩
      intro n θ' hθ'
      rw [(h2deriv n θ' hθ').deriv]
      refine ((htbd _ (hsmH n) (hmemH n) (htrH n) z θ' hz (hθ'pos θ' hθ')
        (hθ'lt θ' hθ')).2).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hdivsq θ' hθ') hKt0) (hHk n)
        (Work.Spaces.HkNorm_nonneg β 4 _) ?_
      exact mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) (by positivity))
    have hu : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        Tendsto (fun n : ℕ => Work.FTS.Galerkin.slice (gn n) τ z θ'
            - Work.FTS.Galerkin.slice (gn n) τ' z θ') atTop
          (𝓝 (Work.FTS.Galerkin.slice g τ z θ' - Work.FTS.Galerkin.slice g τ' z θ')) := by
      intro θ' hθ'
      have hmem : (z, θ') ∈ Work.Construction.Qd := ⟨hz, hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
      have h1 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ) z θ')
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ')) :=
        hjet τ hτ 0 0 (by omega) z θ' hmem
      have h2 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ') z θ')
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ') z θ')) :=
        hjet τ' hτ' 0 0 (by omega) z θ' hmem
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h1.sub h2
    have hv : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        Tendsto (fun n : ℕ => Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ') atTop
          (𝓝 ((Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ'
            - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ') / Real.sin (2 * θ'))) := by
      intro θ' hθ'
      have hmem : (z, θ') ∈ Work.Construction.Qd := ⟨hz, hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
      have hsp : Real.sin (2 * θ') ≠ 0 := ne_of_gt (lt_of_lt_of_le hm (hsenv θ' hθ'))
      have hconv : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 1
          (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
          z θ') atTop
          (𝓝 (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ'
            - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ')) := by
        rw [show (fun n : ℕ => Work.Spaces.mixed 0 1
            (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
            z θ')
          = fun n : ℕ => (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice (gn n) τ) z θ'
              - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice (gn n) τ') z θ') from
          funext (fun n => Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).1.reg
            (hC n τ' hτ').1.reg 0 1 z θ' hz (hθ'pos θ' hθ') (hθ'lt θ' hθ'))]
        exact (hjet τ hτ 0 1 (by omega) z θ' hmem).sub (hjet τ' hτ' 0 1 (by omega) z θ' hmem)
      exact Filter.Tendsto.congr (fun n => by
        rw [Work.FTS_RegExport.RXR1.mixed_zero_one_eq]
        field_simp) (hconv.div_const (Real.sin (2 * θ')))
    have hlim := hasDerivAt_of_tendsto_deriv (a := θ / 2) (b := (θ + Real.pi / 2) / 2)
      (by linarith)
      (u := fun n θ'' => Work.FTS.Galerkin.slice (gn n) τ z θ''
        - Work.FTS.Galerkin.slice (gn n) τ' z θ'')
      (v := fun n θ'' => Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
        - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'')
      (φ := fun θ'' => Work.FTS.Galerkin.slice g τ z θ'' - Work.FTS.Galerkin.slice g τ' z θ'')
      (γ := fun θ'' => (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ''
        - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ'') / Real.sin (2 * θ''))
      hder hvdiff hMd hLd hu hv θ hθin
    have hsin2 : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hident : Work.Spaces.mixed 0 1
        (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ = Lam := by
      have hfun : (fun θ' : ℝ => (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ')
          = fun θ' : ℝ => Work.FTS.Galerkin.slice g τ z θ' - Work.FTS.Galerkin.slice g τ' z θ' := by
        funext θ'; rfl
      have hd : deriv (fun θ' : ℝ =>
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ') θ
          = (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ) / Real.sin (2 * θ) := by
        rw [hfun]; exact hlim.deriv
      rw [hLam]
      rw [show Work.Spaces.mixed 0 1
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ
          = Real.sin (2 * θ) * deriv (fun θ' : ℝ =>
              (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ') θ from rfl]
      rw [hd]
      field_simp
    rw [hident]
    exact hLamBd.trans (le_of_eq (by ring))

end Work.FTS_RegExport.RXR1
end
end
