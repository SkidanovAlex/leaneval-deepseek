/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. radial-slice integrability of a mixed slot against `w²`, for a `C⁴` datum

This is the `C⁴`-version (`ContDiffOn ℝ 4 (Function.uncurry f) Q0`, no analyticity, no
smoothness on the boundary of the quadrant) of
`Work.FTS.StrongEps.SupPort.ae_integrableOn_mixed_sq_w`:

  for `f` of class `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` which is honestly in
  `ℋ⁴` (`Work.Spaces.HkMem α 4 f`), and for every mixed slot `D_z^j D_θ^i f` with `1 ≤ i`
  and `i + j ≤ 4`, the radial function

    `s ↦ (D_z^j D_θ^i f (s, σ))² · w(s)²`      (`w(s) = (1+s)²/s²`)

is integrable on `Iz = [0,∞)` for almost every angle `σ ∈ Iθ = [0,π/2]`.

The proof is the same three-ingredient assembly as in the smooth (`SmoothOpen`) case, with
every occurrence of `C^∞` replaced by `C⁴`:

* **Pointwise domination by the `ℋ⁴`-integrand**
  (`Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand`): at an interior angle
  `σ ∈ (0,π/2)`, `w_θ(σ) = sin(2σ)^{-γ/2} ≥ 1`, so `(D_z^jD_θ^if · w)² ≤ (D_z^jD_θ^if · W)²`,
  which is a summand of `HkIntegrand α 4 f`.  The inequality is pointwise in `s`
  (including `s = 0`, where `w 0 = 0`), so a single `Integrable.mono'` suffices.

* **A.e. strong measurability of the radial slice**
  (`aesm_zslice_mixed_sq_w_C4`): the slot `D_z^jD_θ^if` is continuous on the open quadrant
  (`Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn`, the finite-order form of the
  `D`-calculus), hence at an interior angle its `z`-slice is continuous on `(0,∞)`, and so is
  `w²`; the single point `s = 0` of `Iz` is null.

* **A.e. slice integrability of the `ℋ⁴`-integrand**
  (`ae_integrableOn_HkIntegrand_slice_C4`): `HkIntegrand α 4 f` is nonnegative and continuous
  on the open quadrant (`Work.FTS.StrongEps.continuousOn_HkIntegrand_fin`), hence a.e. strongly
  measurable for the product of the two restricted measures
  (`Work.Spaces.aesm_of_continuousOn_Qd`); the two iterated-integral hypotheses of `HkMem`
  are exactly the inputs of the Tonelli engine `Work.FTS.H2.swap_iterated_integral_of_nonneg`,
  whose third conclusion is the required a.e. slice integrability of the swapped order.

Everything here is fully proved and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.C4

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary a.e. and continuity facts -/

/-- Almost every angle of `Iθ = [0,π/2]` is interior: `Iθ` and `(0,π/2)` differ by the two
endpoints, a null set. -/
theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The square of the radial weight `w` is continuous away from `0`. -/
theorem continuousOn_w_sq :
    ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hnum : ContinuousOn (fun s : ℝ => ((1 + s) ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    ((continuousOn_const.add continuousOn_id).pow 2).pow 2
  have hden : ContinuousOn (fun s : ℝ => (s ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (continuousOn_id.pow 2).pow 2
  refine (hnum.div hden (fun z hz => ?_)).congr (fun z _ => ?_)
  · exact pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
  · show (Work.Spaces.w z) ^ 2 = ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2
    rw [Work.Spaces.w, div_pow]

/-! ## A.e. slice integrability of the `ℋ⁴`-integrand -/

/-- **A.e. radial-slice integrability of the `ℋ⁴`-integrand, for a `C⁴` datum.**

For `f` of class `C⁴` on the open quadrant and honestly in `ℋ⁴`, the radial slice
`s ↦ HkIntegrand α 4 f s σ` is integrable on `Iz` for almost every angle `σ ∈ Iθ`.

This is the third conclusion of `HkSqSwap_C4` (the `C⁴`-analogue of `HkSqSwap`), extracted so
that it can be used without the two integral identities of that statement.  The proof is the
Tonelli engine `Work.FTS.H2.swap_iterated_integral_of_nonneg`, whose three inputs are
nonnegativity of the integrand, a.e. strong measurability (from continuity on the open
quadrant and the nullity of the boundary of the quadrant) and the two iterated-integral
hypotheses contained in `HkMem`. -/
theorem ae_integrableOn_HkIntegrand_slice_C4 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 4 f hF)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  exact (Work.FTS.H2.swap_iterated_integral_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice hmem.2).2.2

/-! ## A.e. strong measurability of the weighted mixed square -/

/-- At an interior angle `σ`, the radial function `s ↦ (D_z^jD_θ^if (s,σ))² w(s)²` is a.e.
strongly measurable for `volume.restrict Iz`: the mixed slot is continuous on the open
quadrant, hence its `z`-slice is continuous on `(0,∞)`, and `w²` is continuous there as well;
the excluded point `s = 0` is null. -/
theorem aesm_zslice_mixed_sq_w_C4 {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (j i : ℕ)
    (hij : i + j ≤ 4) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hmix : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hF hij
  have hslice : ContinuousOn (fun s : ℝ => Work.Spaces.mixed j i f s σ) (Set.Ioi (0 : ℝ)) :=
    (hmix.comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs => ⟨hs, hσ⟩)).congr (fun s _ => rfl)
  have hcont : ContinuousOn
      (fun s : ℝ => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (hslice.pow 2).mul continuousOn_w_sq
  rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-! ## The target -/

theorem ae_integrableOn_mixed_sq_w_C4 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn
        (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  filter_upwards [ae_integrableOn_HkIntegrand_slice_C4 hF hmem, ae_mem_Ioo_of_Iθ] with σ hInt hσ
  refine MeasureTheory.Integrable.mono' hInt (aesm_zslice_mixed_sq_w_C4 hF j i hij hσ) ?_
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand hα j i hi hij hσ

end Work.FTS_RegExport.C4
