/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of a weighted mixed derivative on the product measure,
  for the *open*-quadrant smoothness class

This is the open-quadrant twin of the delivered lemma `Work.Spaces.bt_prod_integrable`
(see `Submission/Work/Spaces/bt_prod_integrable.lean`).  The statement is identical except
that the smoothness hypothesis `Work.Spaces.SmoothNbhd g` (which is *analyticity* on a
neighbourhood of the closed quadrant) is replaced by the honest hypothesis
`Work.FTS.EllipticEst.SmoothOpen f`, i.e. `C^∞` on the open quadrant `(0,∞) × (0,π/2)`,
together with `f ∈ ℋ⁴`.

The proof is the same three-ingredient argument:

* `aesm_mixed_Wt_sq_prod_open`: the integrand `(D_z^j D_θ^i f · W)²` is a.e. strongly
  measurable for `(volume|Iz).prod (volume|Iθ)`, because it is *continuous* on the open
  quadrant `Q0` (smoothness of the mixed derivative from `SmoothOpen.mixed`, continuity of
  the weight away from the singularities) and `Q0` is conull inside `Iz ×ˢ Iθ`; this is
  exactly `Work.Spaces.aesm_of_continuousOn_Qd`;
* pointwise domination by the `ℋ⁴`-integrand of `f`: `(D_z^j D_θ^i f · W)²` is one of the
  summands of `HkIntegrand α 4 f` (`Work.Spaces.sq_le_HkIntegrand_mixed`), so both the
  angular slices and the iterated integral are dominated by the `HkMem α 4 f` data;
* `Work.Spaces.integrable_prod_of_iterated` (Fubini–Tonelli for a nonnegative jointly
  measurable function whose slices and iterated integral are integrable) converts the
  iterated integral into the Bochner integral on the product measure.

The two domination steps use only `hmem`, so they are reused verbatim from the closed case.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.OpenTwins

set_option autoImplicit false

/-! ## The weight is continuous on the open quadrant -/

private theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := hp.2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  refine hw.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-! ## A.e. strong measurability of the integrand -/

private theorem aesm_mixed_Wt_sq_prod_open (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hf.mixed j i).continuousOn.mul (continuousOn_Wt_Q0 α)).pow 2
  exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont

/-! ## Angular slices are integrable, by domination by `HkIntegrand α 4 f` -/

private theorem slice_integrable_aux (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
  filter_upwards [hAE.prodMk_left,
    ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz_meas hz
  refine Integrable.mono' (hmem.1 z hz) hz_meas ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-! ## The iterated integral is integrable, by domination by `hmem.2` -/

private theorem outer_integrable_aux (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    Integrable (fun z => ∫ θ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := by
  refine Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
  exact integral_mono_of_nonneg
    (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => sq_nonneg _))
    (hmem.1 z hz)
    (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij))

/-! ## Assembly -/

theorem bt_prod_integrable_open (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ =>
          (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ MeasureTheory.integral
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (fun p : ℝ × ℝ =>
            (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod_open α f hf j i
  have hslice := slice_integrable_aux α f hmem j i hi hij hAE
  have houter := outer_integrable_aux α f hmem j i hi hij hAE
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated hnn hAE hslice houter
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [Work.Spaces.L2Sq]

end Work.FTS.StrongPersist.N6Trans.OpenTwins
