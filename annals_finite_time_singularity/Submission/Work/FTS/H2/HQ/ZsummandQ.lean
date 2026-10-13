import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.HQ.ZsummandQDefs
import Submission.Work.FTS.H2.HQ.ZsummandQPtwise
import Submission.Work.FTS.H2.HQ.ZsummandQL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-- **The pure `D_z`-summand of the interior product rule `HProdQ`.**

For `f, g` in the interior class `Work.FTS.Nonlin.RegQ α 4` (`= SmoothQuad ∧ HkMem α 4 ∧
BdryTraces α 4`) and pointwise `L^∞`-bound packages `PwBd α f Cf`, `PwBd α g Cg`
(Corollary `SecondDerivativesBounded` for the interior class, see `HQ/Glue.lean`), the pure
`D_z`-slots of the `ℋ⁴`-integrand of the product `f·g` are square integrable, with
`L2Sq (D_z^i (f g) · w/sin(2θ)^{η/2}) ≤ C/(γ-1)·(Cf+Cg)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}` for `i ≤ 4`.

This is `Work.Spaces.HProductRule_Zsummand` (proved) with the *unusable* class
`Spaces.SmoothNbhd` (analyticity on a neighbourhood of the closed quadrant) replaced by
`RegQ` and with the pointwise `L^∞`-bound of order `≤ 2` supplied abstractly by `PwBd`
(instead of `Work.Spaces.MixedSqPointwiseBound`).  Route: copy the proof of
`Submission/Work/Spaces/HProductRule_Zsummand.lean`, using
* `Work.FTS.H2.HQ.DzIter_mul_quad` (the `D_z`-Leibniz rule for `SmoothQuad`, in `HQ/Glue.lean`)
  in place of `Work.Spaces.DzIter_mul`;
* `Work.FTS.H2.HQ.L2Mem_light_quad`, `Work.FTS.H2.HQ.aesm_light_prod`,
  `Work.FTS.H2.HQ.aesm_light_slice` (in `HQ/Glue.lean`) in place of the corresponding
  `Work.Spaces.HPRZ` lemmas (which need `SmoothNbhd`); note that the latter must be applied to
  `f`, to `g` and to the product `f·g` only through `SmoothQuad` (the `HkMem` hypothesis is not
  available for the product — that is what is being proved), so use
  `Work.FTS.H2.HQ.aesm_light_prod/slice` for the product and `LocData.smoothQuad_mul`;
* the `PwBd` hypothesis for the factor of order `≤ 2` (its `bound` field is stated on the open
  quadrant, `PwBd.nonneg` for nonnegativity);
* the pure lemmas `L2Sq_DzIter_le_HkSq`, `sq_le_HkIntegrand_z` and the `Work.Spaces.HPRZ`
  toolkit for the `L²`-bookkeeping.
Trap: `RegQ` constrains nothing on `θ = 0, π/2` and (for the `PwBd` bound) nothing at `z = 0`,
so all the pointwise estimates must be taken where the weights do not vanish: on
`z = 0` and on `sin(2θ) = 0` both sides of every pointwise inequality used here vanish (the
weights `w z` and `wTheta α θ` are `0` there), and the *integrals* are blind to those lines
(`ae_restrict_mem measurableSet_Ioo`, `MeasureTheory.Ioo_ae_eq_Icc`). -/
theorem ZsummandQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn)
    (Cf Cg : ℝ), 0 < α → α ≤ 1 → Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg → ∀ i ≤ 4,
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ C / (Work.Spaces.gam α - 1) * (Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g Cf Cg hα hα1 hregf hregg hPf hPg i hi
  obtain ⟨hf, hmf, -⟩ := hregf
  obtain ⟨hg, hmg, -⟩ := hregg
  have hγ : 0 < gam α - 1 := gam_sub_one_pos hα
  -- the product of two `SmoothQuad` functions is `SmoothQuad`
  have hfg : SmoothQuad (fun z θ => f z θ * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hf hg
  -- the `L²`-bookkeeping of the majorant, and the interior pointwise majorant
  have hV := ZsummandQL2 α f g Cf Cg hγ hPf.nonneg hPg.nonneg i hi hf hg hmf hmg
  have hint := ZsummandQPtwise α f g Cf Cg i hi hf hg hPf hPg
  -- ## Step 1: the pointwise domination of the slot by the majorant, on the *closed* quadrant.
  -- On the two degenerate lines the light weight vanishes, and the majorant is nonnegative.
  have hdom : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| ≤ |zsVQ α f g Cf Cg i z θ| := by
    intro z hz θ hθ
    have hUnn : 0 ≤ zsVQ α f g Cf Cg i z θ := zsVQ_nonneg α f g Cf Cg i z θ
    rw [abs_of_nonneg hUnn]
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · rcases lt_or_eq_of_le (Set.mem_Icc.mp hθ).1 with hθpos | hθzero
      · rcases lt_or_eq_of_le (Set.mem_Icc.mp hθ).2 with hθlt | hθpi
        · exact hint z hzpos θ hθpos hθlt
        · have hsin : Real.sin (2 * θ) = 0 := by
            rw [hθpi, show 2 * (π / 2) = π by ring, Real.sin_pi]
          rw [light_eq_zero_of_sin hsin, mul_zero, abs_zero]
          exact hUnn
      · have hsin : Real.sin (2 * θ) = 0 := by rw [← hθzero]; simp
        rw [light_eq_zero_of_sin hsin, mul_zero, abs_zero]
        exact hUnn
    · subst hz0
      rw [light_eq_zero_of_z, mul_zero, abs_zero]
      exact hUnn
  -- ## Step 2: the slot is `L2Mem`, by domination by the (measurable) majorant
  have hFs : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) (volume.restrict Iθ) :=
    fun z hz => (aesm_light_slice (fun z θ => f z θ * g z θ) hfg i hz).pow 2
  have hFo : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) :=
    ((aesm_light_prod (fun z θ => f z θ * g z θ) hfg i).pow 2).integral_prod_right'
  have hmem : L2Mem (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) :=
    Work.Spaces.HPRZ.L2Mem_of_abs_le (F := fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) (U := zsVQ α f g Cf Cg i)
      hV.1 hFs hFo hdom
  -- ## Step 3: the squared `L²`-bound
  have hL2 : L2Sq (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ≤ L2Sq (zsVQ α f g Cf Cg i) := by
    rw [L2Sq, L2Sq]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hV.1.2 ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _)) (hV.1.1 z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    have h := pow_le_pow_left₀ (abs_nonneg _) (hdom z hz θ hθ) 2
    simpa only [sq_abs] using h
  exact ⟨hmem, le_trans hL2 hV.2⟩

end Work.FTS.H2.HQ
