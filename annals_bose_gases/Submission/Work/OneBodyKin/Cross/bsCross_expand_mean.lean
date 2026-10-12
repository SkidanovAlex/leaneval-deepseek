import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.Cross.bsCross_joint
import Submission.Work.OneBodyKin.Cross.bsCross_slice_pv
import Submission.Work.OneBodyKin.Cross.bsCross_slice_pvs
import Submission.Work.OneBodyKin.Cross.bsCross_slice_uint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin.Cross

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Expand the box mean `bsMf ℓ ψ u = ∫_{s∈acube 1} ψ(ℓ(u+s))` (`OneBodyKin/CrossDefs`) and
exchange the integrals: the `u`-integral of the box mean times the cross form — written with the
`(p,v)`-factor `bsLf ℓ F p v = F ‖p‖ · profHat(ℓ•p) · χ v · cos⟪ℓ•p,v⟫` of the cosine form of the
cross term — equals the four-fold integral over `(p,v,s,u)`.

Intended chain (with `K u p v = bsLf ℓ F p v * ψ (ℓ • (v + u))`):

  `∫_u bsMf u · (∫_p ∫_v K u p v) = ∫_u ∫_p ∫_v (∫_s ψ(ℓ(u+s))) · K u p v` (const-mult, twice)
  `= ∫_u ∫_p ∫_v ∫_s ψ(ℓ(u+s)) · K u p v`                                  (const-mult)
  `= ∫_p ∫_v ∫_s ∫_u K u p v · ψ(ℓ(u+s))`                                  (Fubini)

using `MeasureTheory.integral_mul_const` for the const-mult steps and
`MeasureTheory.integral_integral_swap` / `MeasureTheory.integral_prod` for the exchanges.

**Integrability inputs.**  The joint integrand is dominated by an `L¹` function of `p` times a
bounded function of `(u,v,s)` with compact support in `u,v`:
* `Work.OneBodyKin.bsMf_bound` (in `OneBodyKin/CrossDefs`) gives `C ≥ 0` and a compact `K` with
  `|bsMf ℓ ψ u| ≤ C · 1_K(u)`;
* `Work.OneBodyKin.abs_bsLf_le` gives `|bsLf ℓ F p v| ≤ (∫|χ|)·|F ‖p‖|·|χ v|`;
* `Work.OneBodyKin.exists_bound_of_contDiff_hasCompactSupport` gives `|ψ| ≤ Cψ`.

The pattern for the domination (`Integrable.mul_prod` of a compactly supported bounded function
with `hFi.norm`/`‖χ‖` and `Integrable.mono'`) is in
`Submission/Work/BSKinetic/familyFormUnproj_eq_kernelForm.lean` (see `integrable_bkiFinal` there).
Notice that for fixed `u` the pair `(p,v) ↦ K u p v` is integrable (it is dominated by
`C · ‖F ‖p‖‖ · |χ v|`), and that the joint function on `ℝ³ × (ℝ³ × ℝ³)` is dominated by
`1_K(u) · (‖F ‖p‖‖ · |χ v|)`, a product of an integrable function of `u` and an integrable
function of `(p,v)`. -/
theorem bsCross_expand_mean {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.OneBodyKin.bsMf ℓ ψ u *
          (∫ p : EuclideanSpace ℝ (Fin 3), ∫ v : EuclideanSpace ℝ (Fin 3),
            Work.OneBodyKin.bsLf ℓ F p v * ψ (ℓ • (v + u))))
      = ∫ p : EuclideanSpace ℝ (Fin 3), ∫ v : EuclideanSpace ℝ (Fin 3),
          ∫ s in Submission.BoseGases.acube 1, ∫ u : EuclideanSpace ℝ (Fin 3),
            Work.OneBodyKin.bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)) := by
  set G : ℝ³ → ℝ³ → ℝ³ → ℝ³ → ℝ :=
    fun u p v s => bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)) with hG
  -- the four integrability inputs (independent pieces, each a dominated estimate)
  have hslice1 : ∀ u p : ℝ³, Integrable (fun w : ℝ³ × ℝ³ => G u p w.1 w.2)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) := fun u p =>
    by simpa only [hG] using bsCross_slice_pv hℓ hFi hψ hcs u p
  have hslice2 : ∀ u : ℝ³, Integrable (fun z : ℝ³ × (ℝ³ × ℝ³) => G u z.1 z.2.1 z.2.2)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1)))) := fun u =>
    by simpa only [hG] using bsCross_slice_pvs hℓ hFi hψ hcs u
  have hjoint : Integrable
      (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => G w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) :=
    by simpa only [hG] using bsCross_joint hℓ hFi hψ hcs
  have hslice3 : ∀ p : ℝ³, Integrable
      (fun w : ℝ³ × ℝ³ => ∫ u : ℝ³, G u p w.1 w.2 ∂(volume : Measure ℝ³))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) := fun p =>
    by simpa only [hG] using bsCross_slice_uint hℓ hFi hψ hcs p
  -- Step 1: pull the box mean inside the `(p,v)`-integral and expand it as the `s`-integral
  have hstep1 : ∀ u : ℝ³, bsMf ℓ ψ u *
        (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)))
      = ∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, G u p v s := by
    intro u
    rw [mul_comm (bsMf ℓ ψ u)]
    rw [← MeasureTheory.integral_mul_const]
    congr 1 with p
    rw [← MeasureTheory.integral_mul_const]
    congr 1 with v
    unfold bsMf
    rw [← MeasureTheory.integral_const_mul]
  have hA : (∫ u : ℝ³, bsMf ℓ ψ u *
          (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u))))
      = ∫ u : ℝ³, ∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, G u p v s :=
    integral_congr_ae (Filter.Eventually.of_forall hstep1)
  -- Step 2: fold `(v,s)` into a single product-space variable
  have s1 : (∫ u : ℝ³, ∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, G u p v s)
      = ∫ u : ℝ³, ∫ p : ℝ³, ∫ w : ℝ³ × ℝ³, G u p w.1 w.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact (integral_prod (fun w : ℝ³ × ℝ³ => G u p w.1 w.2) (hslice1 u p)).symm
  -- Step 3: fold `(p,(v,s))` into a single product-space variable
  have s2 : (∫ u : ℝ³, ∫ p : ℝ³, ∫ w : ℝ³ × ℝ³, G u p w.1 w.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))))
      = ∫ u : ℝ³, ∫ z : ℝ³ × (ℝ³ × ℝ³), G u z.1 z.2.1 z.2.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1)))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact (integral_prod (fun z : ℝ³ × (ℝ³ × ℝ³) => G u z.1 z.2.1 z.2.2)
      (hslice2 u)).symm
  have hjoint' : Integrable (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) =>
        G w.1 w.2.1 w.2.2.1 w.2.2.2)
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
          ((volume : Measure ℝ³).restrict (acube 1))))) := hjoint
  -- Step 4: swap the `u`-integral with the block `(p,(v,s))`
  have s3 : (∫ u : ℝ³, ∫ z : ℝ³ × (ℝ³ × ℝ³), G u z.1 z.2.1 z.2.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1)))))
      = ∫ z : ℝ³ × (ℝ³ × ℝ³), ∫ u : ℝ³, G u z.1 z.2.1 z.2.2
          ∂(volume : Measure ℝ³)
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1)))) := by
    have s3a : (∫ u : ℝ³, ∫ z : ℝ³ × (ℝ³ × ℝ³), G u z.1 z.2.1 z.2.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1))))
          ∂(volume : Measure ℝ³))
        = ∫ w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)), G w.1 w.2.1 w.2.2.1 w.2.2.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1))))) :=
      (integral_prod (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => G w.1 w.2.1 w.2.2.1 w.2.2.2)
        hjoint').symm
    have s3b : (∫ w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)), G w.1 w.2.1 w.2.2.1 w.2.2.2
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1))))))
        = ∫ z : ℝ³ × (ℝ³ × ℝ³), ∫ u : ℝ³, G u z.1 z.2.1 z.2.2
          ∂(volume : Measure ℝ³)
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1)))) :=
      integral_prod_symm _ hjoint'
    exact s3a.trans s3b
  -- `(v,s)`-slices of the fully `u`-integrated integrand
  have hfoldz : Integrable
      (fun z : ℝ³ × (ℝ³ × ℝ³) => ∫ u : ℝ³, G u z.1 z.2.1 z.2.2 ∂(volume : Measure ℝ³))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1)))) :=
    Integrable.integral_prod_right (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))
      (f := fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => G w.1 w.2.1 w.2.2.1 w.2.2.2) hjoint'
  -- Step 5: unfold the block `(p,(v,s))`
  have s4 : (∫ z : ℝ³ × (ℝ³ × ℝ³), ∫ u : ℝ³, G u z.1 z.2.1 z.2.2
          ∂(volume : Measure ℝ³)
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
            ((volume : Measure ℝ³).restrict (acube 1)))))
      = ∫ p : ℝ³, ∫ w : ℝ³ × ℝ³, ∫ u : ℝ³, G u p w.1 w.2 ∂(volume : Measure ℝ³)
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) :=
    integral_prod (fun z : ℝ³ × (ℝ³ × ℝ³) =>
      ∫ u : ℝ³, G u z.1 z.2.1 z.2.2 ∂(volume : Measure ℝ³)) hfoldz
  -- Step 6: unfold the block `(v,s)`
  have s5 : (∫ p : ℝ³, ∫ w : ℝ³ × ℝ³, ∫ u : ℝ³, G u p w.1 w.2 ∂(volume : Measure ℝ³)
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))))
      = ∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, ∫ u : ℝ³, G u p v s
          ∂(volume : Measure ℝ³) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact integral_prod (fun w : ℝ³ × ℝ³ => ∫ u : ℝ³, G u p w.1 w.2 ∂(volume : Measure ℝ³))
      (hslice3 p)
  rw [hA, s1, s2, s3, s4, s5]

end Work.OneBodyKin.Cross
