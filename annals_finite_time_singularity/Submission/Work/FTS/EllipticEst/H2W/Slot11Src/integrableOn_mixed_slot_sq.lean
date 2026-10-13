import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Slot11Src

set_option autoImplicit false

/-- The weight `W = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant
`(0,∞) × (0,π/2)`, where both factors are finite. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    rw [Set.mem_prod] at hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-- **Integrability in `z` of one mixed slot of the `ℋ^k`-integrand.**

For `f` of class `C^∞` on the open quadrant and honestly in `ℋ^k`, the function
`z ↦ ∫_θ (D_z^j D_θ^i f · W)²` is integrable on `Iz = [0,∞)`, for every slot with
`1 ≤ i` and `i + j ≤ k`: the summand is one of the (nonnegative) summands of
`HkIntegrand α k f`, so its `θ`-slice integral is dominated by the `θ`-slice integral of
`HkIntegrand α k f`, whose `z`-integral is integrable by `hmem`.  The only thing needed on
top of the pointwise domination is the a.e. strong measurability of that `z`-integral,
which comes from the continuity of the slot on the open quadrant (the complement of the
quadrant inside `Iz × Iθ` is null for the product measure). -/
theorem integrableOn_mixed_slot_sq (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz := by
  -- The slot square is jointly continuous on the open quadrant.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((hf.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
  -- Hence its `z`-slice integrals are a.e. strongly measurable.
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2
        * Work.Spaces.Wt α p.1 p.2) ^ 2) hcont).integral_prod_right'
  -- Domination by the `ℋ^k`-integrand, whose `z`-slice integral is integrable.
  refine Integrable.mono' hmem.2 haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z hz => ?_)
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    integral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
    (Eventually.of_forall fun θ =>
      Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij)

end Work.FTS.EllipticEst.H2W.Slot11Src
