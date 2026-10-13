/-
# `Work.FTS.StrongPersist.N6Trans.T1SixAux.excSlotTerm`

The **exceptional slot term** of the level-six `T1` estimate, in the exact form needed at
`(a,b,i,j) = (1,5,0,5)` of the per-Leibniz-term workhorse: the integral

  `∫_z ∫_θ canonW (gam α) z θ · |D_z⁵ f| · |mixed 0 2 g| · |mixed 5 1 g|`

is bounded by `C α^{-1/2} |f|_{ℋ⁶} |g|_{ℋ⁶}²`, with `C` universal.

This is the *only* case of `t1SlotTermZ` in which the `f`-side slot is the top pure radial
slot `D_z⁵ f`: `HkMem α 6 f` gives no pointwise bound on `D_z⁵ f` (`PwAny6` stops at order
`≤ 4`), so instead of pulling it out as an `L^∞`-factor one pairs it with the *second* angular
slot `mixed 0 2 g` and uses

* the exceptional `L²`-estimate `excDz5Dth2Six` for `D_z⁵ f · D_θ² g · W`,
* the `ℋ⁶`-energy of the slot `mixed 5 1 g` (`L2Sq_mixed_le_HkSq`),
* Cauchy–Schwarz over the quadrant (`L2Mem_prod_le` / `QuadrantCS`),

all three of which are already proved.  The bookkeeping that is *not* in those three is the
`L²`-membership of the weighted mixed slot `mixed j i g · Wt` at level six (needed as the input
of Cauchy–Schwarz): its angular slices come from `integrableOn_mixedSummand` and its radial
marginal is dominated by that of `HkIntegrand α 6 g`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six
import Submission.Work.FTS.H2.T2Easy.QuadrantCS
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.Spaces
open Work.FTS.TransportS.SlotT2 (canonW canonW_gam_eq)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The `L²`-membership of a weighted level-six mixed slot -/

/-- **The weighted level-six mixed slot is square integrable.**  For `g` smooth on the open
quadrant and in `ℋ⁶`, every weighted mixed slot `D_z^jD_θ^i g · W` with `1 ≤ i`, `i + j ≤ 6`
is `L²Mem`.

The angular slices are `integrableOn_mixedSummand`; the radial marginal is dominated by
`z ↦ ∫_θ HkIntegrand α 6 g z θ` (pointwise: `sq_le_HkIntegrand_mixed`), which is integrable
by `HkMem α 6 g`, and it is a.e. strongly measurable as the right marginal of a function
continuous on the open quadrant. -/
theorem L2Mem_mixed_Wt6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (hmem : HkMem α 6 g)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    L2Mem (fun z θ => mixed j i g z θ * Wt α z θ) := by
  constructor
  · intro z hz
    exact Work.FTS.EllipticEst.integrableOn_mixedSummand α 6 hG hmem i j hi hij hz
  · have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (mixed j i g z θ * Wt α z θ) ^ 2)) Work.FTS.EllipticEst.Q0 := by
      show ContinuousOn (fun p : ℝ × ℝ => (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0
      exact (((hG.mixed j i).continuousOn).mul
        (Work.FTS.OpenPkg.ProdOpen.continuousOn_Wt α)).pow 2
    have haesm : AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Iθ, (mixed j i g z θ * Wt α z θ) ^ 2)
        (volume.restrict Iz) :=
      Work.FTS.OpenPkg.ProdOpen.aesm_integral_right
        (F := fun z θ => (mixed j i g z θ * Wt α z θ) ^ 2) hcont
    refine MeasureTheory.Integrable.mono' hmem.2 haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => sq_le_HkIntegrand_mixed α 6 g z θ i j hi hij))

/-! ## The arithmetic of the `α^{-1/2}` rate -/

/-- The elementary arithmetic behind the rate `α^{-1/2}`: for `C1 > 0`, `α > 0` and
`A, B ≥ 0`,

  `√(C1/(γ-1) · A · B) · √B ≤ √(10 C1) · α^{-1/2} · √A · B`,

using `γ - 1 = α/10`. -/
private lemma excArith {C1 α A B : ℝ} (hC1 : 0 < C1) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (C1 / (gam α - 1) * A * B) * Real.sqrt B
      ≤ Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)) * Real.sqrt A * B := by
  have hγeq : gam α - 1 = α / 10 := gam_sub_one α
  have hγpos : 0 < gam α - 1 := by rw [hγeq]; linarith
  have hcnn : 0 ≤ C1 / (gam α - 1) := div_nonneg hC1.le hγpos.le
  have hc : C1 / (gam α - 1) = 10 * C1 / α := by
    rw [hγeq, div_div_eq_mul_div]; ring
  have hAB : 0 ≤ C1 / (gam α - 1) * A := mul_nonneg hcnn hA
  rw [show C1 / (gam α - 1) * A * B = (C1 / (gam α - 1) * A) * B from by ring]
  rw [← Real.sqrt_mul (mul_nonneg hAB hB) B]
  rw [show (C1 / (gam α - 1) * A) * B * B = (C1 / (gam α - 1) * A) * (B * B) from by ring]
  rw [Real.sqrt_mul hAB (B * B), Real.sqrt_mul_self hB]
  rw [Real.sqrt_mul hcnn A, hc]
  rw [Real.sqrt_div (show (0:ℝ) ≤ 10 * C1 by positivity), div_eq_mul_inv]
  rw [Real.sqrt_eq_rpow (10 * C1), Real.sqrt_eq_rpow α, ← Real.rpow_neg hα.le (1 / 2 : ℝ)]

/-! ## The requested term -/

theorem excSlotTerm : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
          * |Work.Spaces.DzIter 5 f z θ| * |Work.Spaces.mixed 0 2 g z θ|
          * |Work.Spaces.mixed 5 1 g z θ|)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six
  refine ⟨Real.sqrt (10 * C1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG
  obtain ⟨hUmem0, hUbd0⟩ := hC1 α f g hα hα1 hF hmemF hG hmemG
  set U : ℝ → ℝ → ℝ := fun z θ => DzIter 5 f z θ * mixed 0 2 g z θ * Wt α z θ with hUdef
  set V : ℝ → ℝ → ℝ := fun z θ => mixed 5 1 g z θ * Wt α z θ with hVdef
  have hUmem : L2Mem U := by simpa only [hUdef] using hUmem0
  have hUbd : L2Sq U ≤ C1 / (gam α - 1) * HkSq α 6 f * HkSq α 6 g := by
    simpa only [hUdef] using hUbd0
  have hVmem : L2Mem V := by
    simpa only [hVdef] using L2Mem_mixed_Wt6 hG hmemG (i := 1) (j := 5)
      (by norm_num) (by norm_num)
  have hVbd : L2Sq V ≤ HkSq α 6 g := by
    simpa only [hVdef] using L2Sq_mixed_le_HkSq α 6 g hmemG 1 5 (by norm_num) (by norm_num)
  -- the pointwise identification of the integrand
  have hpt : ∀ z θ : ℝ, θ ∈ Iθ →
      canonW (gam α) z θ * |DzIter 5 f z θ| * |mixed 0 2 g z θ| * |mixed 5 1 g z θ|
        = |U z θ| * |V z θ| := by
    intro z θ hθ
    rw [canonW_gam_eq α z θ hθ]
    have hWtnn : 0 ≤ Wt α z θ := by
      rw [Wt, wTheta]
      exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
    simp only [hUdef, hVdef, abs_mul, abs_of_nonneg hWtnn]
    ring
  have hIeq : (∫ z in Iz, ∫ θ in Iθ, canonW (gam α) z θ * |DzIter 5 f z θ|
        * |mixed 0 2 g z θ| * |mixed 5 1 g z θ|)
      = ∫ z in Iz, ∫ θ in Iθ, |U z θ| * |V z θ| := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z θ hθ)
  have hCS : (∫ z in Iz, ∫ θ in Iθ, |U z θ| * |V z θ|)
      ≤ Real.sqrt (L2Sq U) * Real.sqrt (L2Sq V) :=
    Work.FTS.H2.T2Easy.L2Mem_prod_le hUmem hVmem
  have hA : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  have hB : 0 ≤ HkSq α 6 g := HkSq_nonneg α 6 g
  calc (∫ z in Iz, ∫ θ in Iθ, canonW (gam α) z θ * |DzIter 5 f z θ|
        * |mixed 0 2 g z θ| * |mixed 5 1 g z θ|)
      = ∫ z in Iz, ∫ θ in Iθ, |U z θ| * |V z θ| := hIeq
    _ ≤ Real.sqrt (L2Sq U) * Real.sqrt (L2Sq V) := hCS
    _ ≤ Real.sqrt (C1 / (gam α - 1) * HkSq α 6 f * HkSq α 6 g) * Real.sqrt (HkSq α 6 g) :=
        mul_le_mul (Real.sqrt_le_sqrt hUbd) (Real.sqrt_le_sqrt hVbd)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)) * Real.sqrt (HkSq α 6 f) * HkSq α 6 g :=
        excArith hC1pos hα hA hB
    _ = Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f * HkSq α 6 g := rfl

end Work.FTS.StrongPersist.N6Trans.T1SixAux
