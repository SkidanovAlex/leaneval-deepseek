import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkIntegrand_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **Subadditivity of `HkSq`** on the `SmoothQuad` data of the localisation chapter: if `a` and
`b` are `C^∞` on the open quadrant and both lie in `ℋ^k` *honestly* (`HkMem`), then so does their
sum, with the `2 + 2` bound

`HkSq α k (a+b) ≤ 2·HkSq α k a + 2·HkSq α k b`.

The proof is two monotonicity steps of the iterated integral: the pointwise inequality of the
integrable functions (`HkIntegrand_add_le`) integrated first over `θ ∈ Iθ`, then over `z ∈ Iz`.
The integrability of the dominating function `2·HkIntegrand a + 2·HkIntegrand b` is exactly the
`HkMem` certificates of `a` and `b`; no measurability of `HkIntegrand (a+b)` is needed
(`MeasureTheory.integral_mono_of_nonneg` takes the *larger* function integrable). -/
theorem HkSq_add_le (α : ℝ) (k : ℕ) {a b : ℝ → ℝ → ℝ} (hsa : SmoothQuad a)
    (hsb : SmoothQuad b) (ha : Work.Spaces.HkMem α k a) (hb : Work.Spaces.HkMem α k b) :
    Work.Spaces.HkSq α k (fun z θ => a z θ + b z θ)
      ≤ 2 * Work.Spaces.HkSq α k a + 2 * Work.Spaces.HkSq α k b := by
  -- The inner `θ`-integral, on the domain `Iz`.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k a z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k b z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k a z θ
        + 2 * Work.Spaces.HkIntegrand α k b z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (((ha.1 z hz).const_mul 2).add ((hb.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => HkIntegrand_add_le α k hsa hsb hz hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_add ((ha.1 z hz).const_mul 2)
          ((hb.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k a z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k b z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k _ z θ)
    ((ha.2.const_mul 2).add (hb.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_add (ha.2.const_mul 2) (hb.2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.FTS.LocData
