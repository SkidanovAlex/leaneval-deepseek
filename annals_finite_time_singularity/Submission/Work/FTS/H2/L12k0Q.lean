import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.L12k0
import Submission.Work.Elliptic.HardyLeftW
import Submission.Work.Elliptic.HardyRightW
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-- The `k = 0` term of the `ℋ⁴`-norm of `L₁₂(g)`: the weighted Hardy inequality on `(0,1)` and
`(1,∞)` (`HardyLeftW`, `HardyRightW`) applied to `u = L₁₂(g)` with `u(0) = 0` and `u → 0` at
`∞`.  This is *verbatim* `Work.Elliptic.L12k0` with the (in fact unused: the proof body never
mentions it) hypothesis `Work.Spaces.SmoothNbhd g` deleted, so that it applies in the interior
class.  Either copy that proof and drop `hsm` (recommended; the file
`Submission/Work/Elliptic/L12k0.lean` contains the whole proof, and the two Hardy lemmas are
imported unchanged), or call `Work.Elliptic.HardyLeftW`/`HardyRightW` directly. -/
theorem L12k0Q (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0))
    (hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z)
    (hcontd : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0))
    (hcont : ContinuousOn (fun z => Work.Elliptic.L12 g z) (Set.Icc 0 1))
    (htend : Filter.Tendsto (fun z => Work.Elliptic.L12 g z) Filter.atTop (nhds 0))
    (h0 : Work.Elliptic.L12 g 0 = 0)
    (hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  let f : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z
  let U : ℝ → ℝ := fun z => Work.Elliptic.L12 g z
  have hdens : ∀ z : ℝ, Work.Elliptic.L12dens g z = f z / z :=
    fun z => Work.Elliptic.L12dens_eq_Qang_div g z
  have hderivU : ∀ z : ℝ, 0 < z → HasDerivAt U (-(f z / z)) z := by
    intro z hz
    have h := hderiv z hz
    rw [← hdens z]
    exact h
  have hderiv01 : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z :=
    fun z hz => hderivU z hz.1
  have hderiv1 : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt U (-(f z / z)) z :=
    fun z hz => hderivU z (lt_trans one_pos hz)
  have hQIoo : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) :=
    hQint.mono_set (show Set.Ioo (0:ℝ) 1 ⊆ Work.Spaces.Iz from
      fun z hz => show (0:ℝ) ≤ z from le_of_lt hz.1)
  have hQIoi : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) :=
    hQint.mono_set (show Set.Ioi (1:ℝ) ⊆ Work.Spaces.Iz from
      fun z hz => show (0:ℝ) ≤ z from le_of_lt (lt_trans one_pos hz))
  obtain ⟨hIntL, hBoundL⟩ := Work.Elliptic.HardyLeftW f U hderiv01 hcont h0 hQIoo
  obtain ⟨hIntR, hBoundR⟩ := Work.Elliptic.HardyRightW f U hderiv1 htend hQIoi
  have hae : (Set.Ioo (0:ℝ) 1 ∪ Set.Ioi 1) =ᵐ[volume] Work.Spaces.Iz :=
    Work.Elliptic.Ioo_union_Ioi_ae_eq_Iz
  have hvalU : (∫ z in Work.Spaces.Iz, (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0:ℝ) 1, (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + ∫ z in Set.Ioi (1:ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [← MeasureTheory.setIntegral_congr_set hae]
    exact MeasureTheory.setIntegral_union
      (Set.disjoint_left.mpr (fun a ha hb => absurd (lt_trans ha.2 hb) (lt_irrefl a)))
      measurableSet_Ioi hIntL hIntR
  have hvalf : (∫ z in Work.Spaces.Iz, (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0:ℝ) 1, (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + ∫ z in Set.Ioi (1:ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [← MeasureTheory.setIntegral_congr_set hae]
    exact MeasureTheory.setIntegral_union
      (Set.disjoint_left.mpr (fun a ha hb => absurd (lt_trans ha.2 hb) (lt_irrefl a)))
      measurableSet_Ioi hQIoo hQIoi
  have hIntAll : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    show MeasureTheory.IntegrableOn (fun z => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
    exact (MeasureTheory.integrableOn_congr_set_ae hae).mp (hIntL.union hIntR)
  have hbound : (∫ z in Work.Spaces.Iz, (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    show (∫ z in Work.Spaces.Iz, (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (∫ z in Work.Spaces.Iz, (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
    rw [hvalU, hvalf]
    linarith [hBoundL, hBoundR]
  exact ⟨hIntAll, hbound⟩

end Work.FTS.H2
