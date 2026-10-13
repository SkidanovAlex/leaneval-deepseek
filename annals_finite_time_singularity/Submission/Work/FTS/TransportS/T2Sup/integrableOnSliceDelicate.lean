/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/integrableOnSliceDelicate`: the angular slice of the delicate integrand

The companion *slice* statement of the delegated radial-marginal integrability
`Work.FTS.TransportS.T2Sup.delicateMargInt` (and of the bound `delicateBound`): for a fixed
radius `z > 0` the angular function

  `θ ↦ canonW (γ) z θ · |D_z³f(z,θ)| · |D_zD_θg(z,θ)| · |D_z³D_θg(z,θ)|`

is integrable on `Iθ = [0,π/2]`.

## Route

`canonW (γ) z θ = w(z)² sin(2θ)^{-γ}`, and `γ = 1 + α/10 < 2`, so the weight alone is *not*
integrable at the endpoints; the vanishing has to come from the factors.  Three inputs:

1. **The `f`-factor is bounded on the slice.**  `SlotT2.supOpen_slice_bound` (the Agmon
   inequality of `Work.H2.T1Q.SliceSupOpen`, applied to the slice `θ ↦ D_z³f(z,·)`) gives, for
   *every* interior `θ`,
   `(D_z³f(z,θ))² ≤ supOpenBfun α f 3 z`, i.e. `|D_z³f(z,θ)| ≤ K` with
   `K = √(supOpenBfun α f 3 z)` (a constant in `θ`).
2. **The two `g`-factors absorb the weight.**  For each of the slots `(j,i) = (1,1)`, `(3,1)`,
   `SlotT2.mslot_slice_integrable` gives `∫_θ canonW (γ) z θ · (D_z^jD_θ^ig(z,θ))² < ∞`, since
   each slot is a summand of `HkIntegrand α 4 g` and `HkMem α 4 g` supplies its integrability
   on the slice.
3. **Cauchy–Schwarz / AM–GM in `θ`.**  Pointwise a.e. in `θ`,
   `sin(2θ)^{-γ}|A||B||C| = (sin(2θ)^{-γ/2}|A||B|)·(sin(2θ)^{-γ/2}|C|)
     ≤ K·(sin(2θ)^{-γ}B² + sin(2θ)^{-γ}C²)/2`,
   so the slice integrand is dominated by `(K/2)·(canonW (γ)·B² + canonW (γ)·C²)`, which is
   integrable by step 2.

The only nontrivial point is step 1: the `ℋ⁴`-membership of `f` carries the *weighted* second
order control `∫_θ sin(2θ)^{2-γ}(∂_θD_z³f(z,θ))² < ∞` on each slice (the `(3,1)`-slot of `f`),
and the Agmon inequality converts it into a genuine pointwise bound — this is exactly the
mechanism of `supThetaIntOpen`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

theorem integrableOnSliceDelicate {α : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmf : Work.Spaces.HkMem α 4 f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  -- the bound `K` for the `f`-factor, constant in `θ`
  set K : ℝ := Real.sqrt (Work.FTS.TransportS.SlotT2.supOpenBfun α f 3 z) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; exact Real.sqrt_nonneg _
  -- (1) the `f`-factor is dominated by `K` for almost every (indeed every interior) `θ`
  have hAbnd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.DzIter 3 f z θ| ≤ K := by
    rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have h := Work.FTS.TransportS.SlotT2.supOpen_slice_bound (b := 3) hf hmf hα hα1
      (by norm_num) hz θ hθ
    rw [hKdef, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  -- (2) the two `g`-slots are integrable against the full weight `canonW γ`
  have hB : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 1 1 g z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.TransportS.SlotT2.mslot_slice_integrable (Work.Spaces.gam_pos hα) le_rfl hg hmg 1 1
      le_rfl (by norm_num) hzIz
  have hC : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.TransportS.SlotT2.mslot_slice_integrable (Work.Spaces.gam_pos hα) le_rfl hg hmg 3 1
      le_rfl (by norm_num) hzIz
  -- (3) the majorant is integrable
  have hmajint : MeasureTheory.IntegrableOn (fun θ => (K / 2) *
      (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 1 1 g z θ) ^ 2
      + Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2)) Work.Spaces.Iθ :=
    (hB.add hC).const_mul (K / 2)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) p.1 p.2
        * |Work.Spaces.DzIter 3 f p.1 p.2| * |Work.Spaces.mixed 1 1 g p.1 p.2|
        * |Work.Spaces.mixed 3 1 g p.1 p.2|) ?_ hz
    exact (((Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)).mul
      ((hf.DzIter 3).continuousOn.abs)).mul
      ((hg.mixed 1 1).continuousOn.abs)).mul
      ((hg.mixed 3 1).continuousOn.abs)
  refine MeasureTheory.Integrable.mono' hmajint haesm ?_
  filter_upwards [hAbnd, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθA hθI
  have hcw : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
  have hnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
      * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
      * |Work.Spaces.mixed 3 1 g z θ| :=
    mul_nonneg (mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  -- the AM–GM step in `θ`
  have hamgm : |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|
      ≤ ((Work.Spaces.mixed 1 1 g z θ) ^ 2 + (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2 := by
    have h := two_mul_le_add_sq |Work.Spaces.mixed 1 1 g z θ| |Work.Spaces.mixed 3 1 g z θ|
    rw [sq_abs, sq_abs] at h
    linarith
  calc Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ|
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (|Work.Spaces.DzIter 3 f z θ|
          * (|Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|)) := by ring
    _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (K * (((Work.Spaces.mixed 1 1 g z θ) ^ 2
          + (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcw
        exact mul_le_mul hθA hamgm (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hKnn
    _ = (K / 2) * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 1 1 g z θ) ^ 2
      + Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2) := by ring

end Work.FTS.TransportS.T2Sup
