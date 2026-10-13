/-
# `L₁₂(g) ∈ C⁴((0,∞))` in the localised class (`SmoothQuad` + `ℋ⁵`)

This is the order-`4` companion of `Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn`
(the order-`3` statement).  The fundamental-model operator

  `L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(s,θ)/s dθ ds`

is `C^∞` on `(0,∞)` for analytic data (`Work.Coercivity.L12f_contDiffOn_infty`), but for
the localised data of the route (`Work.FTS.LocData.SmoothQuad` — genuine `C^∞` on the *open*
quadrant — plus `Work.Spaces.HkMem α k g`) the `θ`-integral defining the density is not a
priori differentiable in `s`, and one has to go through the angular moments of
`Work.FTS.H2.QangDiff`.

**The key point of this file is that order `4` costs nothing beyond `HkMem α 4`.**  Writing
`Qang g j z = ∫_θ K(θ)·(D_z^j g)(z,θ) dθ` and `L12dens g = Qang g 0 / z`
(`Work.Elliptic.L12dens_eq_Qang_div`), `QangDiff` gives

* `Qang g j` continuous on `(0,∞)` for `j ≤ 3`, and
* `∂_z (Qang g j) z = Qang g (j+1) z / z` for `j ≤ 2`,

i.e. `ContDiffOn ℝ (3-j) (Qang g j)` for `j ≤ 2`.  Descending in `j`: `Qang g 2 ∈ C¹`,
`Qang g 1 ∈ C²`, `Qang g 0 ∈ C³`, hence `L12dens g = Qang g 0 / z ∈ C³`, hence — since
`L₁₂(g)` is a tail integral of `L12dens g` and `∂_z L₁₂(g) = −L12dens g`
(`Work.FM.hasDerivAt_L12`) — `L₁₂(g) ∈ C⁴`.  The top of the descent chain meets exactly the
`j = 3` continuity of `QangDiff`, so the whole argument runs in `HkMem α 4`.  The requested
statement assumes the stronger `HkMem α 5`, which is reduced to `HkMem α 4` first
(`HkMem_four_of_five_quad` below, the `SmoothQuad` analogue of
`Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five`); the hypothesis `L₁₂ f (0) = 0` is not
needed for this statement (it belongs to the coercivity/`HardyHyp` side).

All constants being existential, the standing `0 < α ≤ 1` of the localised chapter is the
only α-hypothesis (`QangDiff` needs it).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.HkIntegrand_le_succ
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.AuxE2

set_option autoImplicit false
-- `h0 : L₁₂ f 0 = 0` is part of the requested statement (it is used downstream, on the
-- coercivity side) but is not needed for the `C⁴`-regularity proved here.
set_option linter.unusedVariables false

/-- **`ℋ⁵` descends to `ℋ⁴` in the localised class.**  The `ℋ^k`-integrand is pointwise
monotone in `k` (`Work.Coercivity.HkIntegrand_le_succ`), so the honesty of the order-`5`
integrand implies that of the order-`4` one; the measurability input is the continuity of the
order-`4` integrand on the open quadrant, which `SmoothQuad` supplies
(`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`).

This is the `SmoothQuad` analogue of `Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five`
(which is stated with `SmoothQuad` as well but lives behind a much heavier import cone). -/
theorem HkMem_four_of_five_quad (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α 5 f) :
    Work.Spaces.HkMem α 4 f := by
  have hmono : ∀ z θ, Work.Spaces.HkIntegrand α 4 f z θ ≤ Work.Spaces.HkIntegrand α 5 f z θ := by
    intro z θ
    exact Work.Coercivity.HkIntegrand_le_succ α 4 f z θ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsm
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  constructor
  · intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hpos
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
    · have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hpos
      exact (h.1 z hz).mono' haesm (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
        exact hmono z θ)
  · have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
    refine h.2.mono' haesm ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (h.1 z hz) (Filter.Eventually.of_forall fun θ => hmono z θ)

/-- **`L₁₂(g) ∈ C⁴((0,∞))` in the localised class** (`SmoothQuad g` + `HkMem α 5 g`).

Route.  `HkMem α 5 g` descends to `HkMem α 4 g` (`HkMem_four_of_five_quad`), and
`Work.FTS.H2.QangDiff` then gives the primitive/`z`-calculus of the angular moments
`Qang g j = ∫_θ K(θ)·D_z^j g dθ`: continuity for `j ≤ 3` and
`∂_z (Qang g j) z = Qang g (j+1) z / z` for `j ≤ 2`.  Descending in `j`,
`Qang g 2 ∈ C¹`, `Qang g 1 ∈ C²`, `Qang g 0 ∈ C³` on `(0,∞)`; hence the density
`L12dens g = Qang g 0 / z` is `C³` (`Work.Elliptic.L12dens_eq_Qang_div`).  Finally
`L₁₂(g)` is the tail integral of `L12dens g` (`Work.FM.hasDerivAt_L12`, whose hypotheses are
the tail-integrability of the density — `Work.FTS.H2.L12densIntegrable` — and its continuity
at `z`, both available), so `∂_z L₁₂(g) = −L12dens g ∈ C³` and
`contDiffOn_succ_iff_deriv_of_isOpen` gives `L₁₂(g) ∈ C⁴`. -/
theorem L12_contDiffOn_four_of_five (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 5 f) (h0 : Work.Construction.L12 f 0 = 0) :
    ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0) := by
  -- the datum is honest in `ℋ⁴` as well
  have hm4 : Work.Spaces.HkMem α 4 f := HkMem_four_of_five_quad α hsm hmem
  -- the `z`-calculus of the angular moments (`QangDiff`, order `4`)
  obtain ⟨hQderiv, hQcont⟩ := Work.FTS.H2.QangDiff α f hα hα1 hsm hm4
  have hcontQ1 : ContinuousOn (fun z => Work.Elliptic.Qang f 1 z / z) (Set.Ioi 0) :=
    (hQcont 1 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  have hcontQ2 : ContinuousOn (fun z => Work.Elliptic.Qang f 2 z / z) (Set.Ioi 0) :=
    (hQcont 2 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  have hcontQ3 : ContinuousOn (fun z => Work.Elliptic.Qang f 3 z / z) (Set.Ioi 0) :=
    (hQcont 3 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  -- `Qang f 2` is `C¹` (its derivative is `Qang f 3 / z`, continuous)
  have hCd1Q2 : ContDiffOn ℝ 1 (fun z => Work.Elliptic.Qang f 2 z) (Set.Ioi 0) := by
    rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
    refine ⟨fun z hz => (hQderiv 2 (by norm_num) z hz).differentiableAt.differentiableWithinAt, ?_⟩
    refine hcontQ3.congr (fun z hz => ?_)
    rw [derivWithin_of_isOpen isOpen_Ioi hz, (hQderiv 2 (by norm_num) z hz).deriv]
  -- `Qang f 1` is `C²` (its derivative is `Qang f 2 / z`, which is `C¹`)
  have hCd2Q1 : ContDiffOn ℝ 2 (fun z => Work.Elliptic.Qang f 1 z) (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).mpr
      ⟨fun z hz => (hQderiv 1 (by norm_num) z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · refine (hCd1Q2.div contDiffOn_id (fun z hz => ne_of_gt hz)).congr (fun z hz => ?_)
      exact (hQderiv 1 (by norm_num) z hz).deriv
  have hCd2Q1div : ContDiffOn ℝ 2 (fun z => Work.Elliptic.Qang f 1 z / z) (Set.Ioi 0) :=
    hCd2Q1.div contDiffOn_id (fun z hz => ne_of_gt hz)
  -- `Qang f 0` is `C³` (its derivative is `Qang f 1 / z`, which is `C²`)
  have hCd3Q0 : ContDiffOn ℝ 3 (fun z => Work.Elliptic.Qang f 0 z) (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 2) isOpen_Ioi).mpr
      ⟨fun z hz => (hQderiv 0 (by norm_num) z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · refine hCd2Q1div.congr (fun z hz => ?_)
      exact (hQderiv 0 (by norm_num) z hz).deriv
  -- the density is the zero-th angular moment divided by `z`
  have hdens : Work.Elliptic.L12dens f = fun z => Work.Elliptic.Qang f 0 z / z :=
    funext (Work.Elliptic.L12dens_eq_Qang_div f)
  have hCd3dens : ContDiffOn ℝ 3 (Work.Elliptic.L12dens f) (Set.Ioi 0) := by
    rw [hdens]
    exact hCd3Q0.div contDiffOn_id (fun z hz => ne_of_gt hz)
  have hdens_cont : ContinuousOn (Work.Elliptic.L12dens f) (Set.Ioi 0) := by
    rw [hdens]
    exact (hQcont 0 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
  -- `L₁₂(f)` is the tail integral of the density, hence has derivative `−L12dens f`
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Coercivity.L12f f) (-(Work.Elliptic.L12dens f z)) z := by
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi (z / 2)) :=
      (Work.FTS.H2.L12densIntegrable α f hα hα1 hsm hm4).mono_set
        (Set.Ioi_subset_Ioi (by linarith))
    have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
      hdens_cont.continuousAt (isOpen_Ioi.mem_nhds hz)
    exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := z / 2) (ρ := z)
      hint hcont (by linarith)
  -- assemble: `L₁₂(f)` is differentiable with derivative `−L12dens f ∈ C³`
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 3) isOpen_Ioi).mpr ⟨?_, ?_, ?_⟩
  · exact fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  · intro h; exact absurd h (by simp)
  · refine hCd3dens.neg.congr (fun z hz => ?_)
    exact (hderiv z hz).deriv

end Work.FTS.CoercivityFix.Transfer.AuxE2
