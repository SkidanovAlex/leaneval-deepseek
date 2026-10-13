import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Cores.powerHardyNeg
import Submission.Work.FTS.EllSol.hardySinTwoFin
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
import Submission.Work.FTS.EllipticEst.remov.interval_integral_mono_limit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weak-range angular `sin (2θ)`-weighted Hardy inequality

The target `Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak` is the `sin (2θ)`-weighted Hardy
inequality

  `∫_{Iθ} sin(2θ)^{-c} u² ≤ C/(c-1)² ∫_{Iθ} sin(2θ)^{2-c} (u')²`,

for `1 < c ≤ 3/2`, i.e. for the *weak-weight* range where the exponent `2 - c` on the derivative
side is `≥ 0` (all of `Work.FTS.EllSol.hardySinTwoFin`, `hardySinAll`,
`Work.FTS.ClassC.NormPieces.hardy_sinOpen` need the derivative exponent `≤ 0`).

## Route

* Split `(0, π/2)` at `π/4` (`lintegral_split_Ioo_fts`).
* On the left half `(0, π/4)`, `sin(2θ)` is comparable with `θ` in the favourable direction, so
  `Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft` (Jordan's inequality
  `θ ≤ (π/4) sin(2θ)` together with the sharp power-weight Hardy
  `TT.SinHardy.NarrowAlt.powerHardy_open` at the exponent `η = c - 2 ∈ (-1, 0]`) gives the bound
  with the sharp constant `4/(c-1)²`, requiring only `u → 0` at `0⁺`.
* The right half is transported to the left one by the reflection `θ ↦ π/2 - θ`, which preserves
  `sin(2θ)` and turns `deriv` into `-deriv`, and which turns the `(π/2)⁻` limit into a `0⁺` limit
  (`T6CoefAux.lintegral_Ioo_reflect`).
* The `∫⁻` (Lebesgue) inequality on `Iθ`, together with the integrability of the *right* hand
  side, yields integrability of `sin(2θ)^{-c} u²` together with the Bochner-integral inequality
  (`Work.FTS.EllipticEst.remov.integrable_of_lintegral_ofReal_le'`).

The constant produced is `C = 4`.
-/

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas -/

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
private lemma sin2_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Splitting an `∫⁻`-integral on `(0, π/2)` at the midpoint `π/4` (the two halves are disjoint
and their union differs from `(0, π/2)` by the null set `{π/4}`). -/
private theorem lintegral_split_Ioo_fts (F : ℝ → ENNReal) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F θ)
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), F θ)
        + (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ) := by
  have h1 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F θ)
      = ∫⁻ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), F θ :=
    setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc)
  rw [h1, ← Set.Ioc_union_Ioc_eq_Ioc (a := (0 : ℝ)) (b := Real.pi / 4) (c := Real.pi / 2)
    (by positivity) (by linarith [Real.pi_pos])]
  rw [lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := Real.pi / 4)).symm,
      setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := Real.pi / 4) (b := Real.pi / 2)).symm]

/-- **The `∫⁻` form of the weighted Hardy inequality on the open interval `(0, π/2)`**, for
`1 < c ≤ 3/2` and `u` of class `C¹` on `(0, π/2)` with `u → 0` at both endpoints: the form in
which no integrability hypothesis is needed. -/
private theorem lin_hardy_Ioo_fts {c : ℝ} {u : ℝ → ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hu0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hupi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  have hc2' : c ≤ 2 := by linarith
  -- the left half for `u`
  have hu4 : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    hu.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have hleft := Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft c hc1 hc2' hu4 hu0
  -- the reflected function `g θ = u (π/2 - θ)`
  set g : ℝ → ℝ := fun φ => u (Real.pi / 2 - φ) with hgdef
  have hgcont : ContDiffOn ℝ 1 g (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    have hf : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi / 2 - φ) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      (contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id
    have hcomp := hu.comp hf
      (fun φ hφ => ⟨by linarith [hφ.2, Real.pi_pos], by linarith [hφ.1]⟩)
    rw [hgdef]
    exact hcomp
  have hg0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hmap : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhds (0 : ℝ))
            (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
        simpa using h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      · filter_upwards [self_mem_nhdsWithin] with φ hφ
        exact sub_lt_self (Real.pi / 2) hφ
    have h := hupi.comp hmap
    simpa only [hgdef, Function.comp_def] using h
  have hright :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft c hc1 hc2' hgcont hg0
  -- the split and the reflection transport
  have hL1 := lintegral_split_Ioo_fts
    (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
  have hR1 := lintegral_split_Ioo_fts
    (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
  have hL2 : (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = ∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (-c) * (g φ) ^ 2) := by
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
        (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
        (Real.pi / 4) (Real.pi / 2),
      show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    congr 1
    rw [hgdef]
    have hs : Real.sin (2 * (Real.pi / 2 - φ)) = Real.sin (2 * φ) := by
      rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ from by ring, Real.sin_pi_sub]
    rw [hs]
  have hR2 : (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = ∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (2 - c) * (deriv g φ) ^ 2) := by
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
        (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        (Real.pi / 4) (Real.pi / 2),
      show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring]
    rw [hgdef]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    congr 1
    rw [deriv_comp_const_sub]
    have hs : Real.sin (2 * (Real.pi / 2 - φ)) = Real.sin (2 * φ) := by
      rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ from by ring, Real.sin_pi_sub]
    rw [hs, neg_sq]
  have hLR : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (g θ) ^ 2)) :=
    hL1.trans (congrArg (fun t => (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)) + t) hL2)
  have hRR : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv g θ) ^ 2)) :=
    hR1.trans (congrArg (fun t => (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) + t) hR2)
  rw [hLR, hRR]
  calc (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (g θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        + ENNReal.ofReal (4 / (c - 1) ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv g θ) ^ 2)) :=
        add_le_add hleft hright
    _ = ENNReal.ofReal (4 / (c - 1) ^ 2) * ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv g θ) ^ 2))) :=
        (mul_add _ _ _).symm

/-! ## The main theorem -/

/-- **The angular weighted Hardy inequality with the `sin (2θ)`-weight and an exponent
`c ∈ (1,3/2]`, i.e. `c - 2 ∈ (-1,-1/2]` — the weak-weight range** (all of
`Work.FTS.EllSol.hardySinTwoFin`, `hardySinAll`, `Work.FTS.ClassC.NormPieces.hardy_sinOpen`
require the exponent on the *right* to be `≥ 0`):

for `1 < c ≤ 3/2` and `u` of class `C¹` on `(0,π/2)` with `u → 0` at both endpoints
(`0⁺` and `(π/2)⁻`) whose `sin(2θ)^{2-c}`-weighted squared derivative is integrable on
`Iθ = [0,π/2]`, the function `θ ↦ sin(2θ)^{-c} u(θ)²` is integrable on `Iθ` and
`∫_{Iθ} sin(2θ)^{-c} u² ≤ C/(c-1)² ∫_{Iθ} sin(2θ)^{2-c} (u')²`.

`C = 4` is enough.  Route: split `Iθ` at `π/4`; on each half `sin (2θ)` is comparable with the
distance to the corresponding endpoint (`(4/π)θ ≤ sin(2θ) ≤ 2θ` on `[0,π/4]`, and
`sin (2θ) = sin (2(π/2-θ))`), so both comparisons go in the *favourable* direction:
`sin(2θ)^{-c} ≤ θ^{-c}` and `θ^{2-c} ≤ sin(2θ)^{2-c}` (the exponent `2-c > 0` here);
hence the sin-weight inequality on `(0,π/4)` follows from the power-weight Hardy
`Work.FTS.StrongEps.EpsSqTools.powerHardy_negGlobal` with `η = c - 2 ∈ (-1,0)` (being proved in
parallel in a sibling file of the same directory: import it if it is built, otherwise prove the
power statement inside this file — the sharp local form
`Work.FTS.EllipticEst.Cores.powerHardy_at_gen` on `[ε,A]`, valid for every `η > -1`, plus the
truncation/limit argument suffices).  The right half is the reflection `θ ↦ π/2 - θ`, which
preserves both weights and turns the `(π/2)⁻` limit into a `0⁺` limit. -/
theorem hardySinGam_weak : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (u : ℝ → ℝ),
    1 < c → c ≤ 3 / 2 →
    ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)
      ≤ C / (c - 1) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2 := by
  refine ⟨4, by norm_num, ?_⟩
  intro c u hc1 hc2 hu hu0 hupi hG2int
  have hKnn : (0 : ℝ) ≤ 4 / (c - 1) ^ 2 := by positivity
  -- the `∫⁻`-inequality on `(0, π/2)`, transferred to `Iθ = [0, π/2]`
  have hlin2 := lin_hardy_Ioo_fts hc1 hc2 hu hu0 hupi
  have hIθ1 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
      (b := Real.pi / 2))).symm
  have hIθ2 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
      (b := Real.pi / 2))).symm
  have hlinIθ : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [hIθ1, hIθ2]
    exact hlin2
  -- the two weights are nonnegative on `Iθ`
  have hG2ae : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun θ hθ => ?_))
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  have hG2lin : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG2int hG2ae).symm
  have hK : (0 : ℝ) ≤ 4 / (c - 1) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) :=
    mul_nonneg hKnn (integral_nonneg_of_ae hG2ae)
  have hbound : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [hG2lin] at hlinIθ
    refine hlinIθ.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hKnn]
  -- strong measurability and nonnegativity of the left-hand weight
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin2_pos_of_Ioo hθ)))
    exact h1.mul (hu.continuousOn.pow 2)
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      ← Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
        (b := Real.pi / 2))]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * x)) ^ (-c) * (u x) ^ 2 := by
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * x)
      ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  exact Work.FTS.EllipticEst.remov.integrable_of_lintegral_ofReal_le'
    measurableSet_Icc hK haesm hnn hbound

end

end Work.FTS.StrongEps.EpsSqTools
