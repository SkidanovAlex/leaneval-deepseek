import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.Base

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The zero section of the rank-4 bundle `Vk k → S⁴`

`Work.Milnor.VBundleDefs` describes the total space `Vk k` of the rank-4 vector bundle `ξ` over
`S⁴` as a gluing of two copies of `MSpace8 = ℝ⁴ × ℍ` along `{x ≠ 0} × ℍ`.  This file exhibits the
**zero section** of that bundle as an explicit continuous map

`s : S⁴ → Vk k`,  `s (x : S⁴) = ιX (x, 0)` for finite `x`, and `s ∞ = ιY (0, 0)`.

The two descriptions agree on the overlap: for `x ≠ 0` the gluing map sends `(x, 0)` to
`(invBase x, 0)` (the twist fixes the zero of the fibre), so `ιX (x, 0) = ιY (invBase x, 0)`.
Continuity at the finite points is immediate from continuity of `ιX`; continuity at `∞` is the
statement that `ιX (x, 0) = ιY (invBase x, 0)` converges to `ιY (0, 0)` as `‖x‖ → ∞`, which
follows because `‖invBase x‖ = ‖x‖⁻¹ → 0`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set Metric

namespace Work.Milnor

noncomputable section

/-- The zero section of the bundle `Vk k → S⁴`: the finite point `x` of `ℝ⁴ ⊆ S⁴` is sent to the
first chart point `ιX (x, 0)`, and the point at infinity to `ιY (0, 0)`. -/
noncomputable def zeroSection (k : ℤ) : Submission.Milnor.S4 → Submission.Milnor.Vk k :=
  fun z => z.elim ((Submission.Milnor.vData k).ιY (0, 0))
    (fun x => (Submission.Milnor.vData k).ιX (x, 0))

lemma zeroSection_apply_coe (k : ℤ) (x : EuclideanSpace ℝ (Fin 4)) :
    zeroSection k (x : Submission.Milnor.S4) = (Submission.Milnor.vData k).ιX (x, 0) := rfl

lemma zeroSection_apply_infty (k : ℤ) :
    zeroSection k OnePoint.infty = (Submission.Milnor.vData k).ιY (0, 0) := rfl

/-- On the finite part of `S⁴` the zero section is the continuous map `x ↦ ιX (x, 0)`. -/
lemma continuous_zeroSection_coe (k : ℤ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 4) => zeroSection k (x : Submission.Milnor.S4)) := by
  rw [show (fun x : EuclideanSpace ℝ (Fin 4) => zeroSection k (x : Submission.Milnor.S4))
      = (fun x => (Submission.Milnor.vData k).ιX (x, 0)) from rfl]
  exact (Submission.Milnor.vData k).continuous_ιX.comp (continuous_id.prodMk continuous_const)

/-- The zero section is continuous at `∞`.  A neighborhood of `ιY (0, 0)` pulls back to a
neighborhood of `inr (0, 0)` in the second chart; on all sufficiently large `x` the point
`ιX (x, 0) = ιY (invBase x, 0)` lies in it, because `‖invBase x‖ = ‖x‖⁻¹ → 0`. -/
lemma continuousAt_zeroSection_infty (k : ℤ) :
    ContinuousAt (zeroSection k) OnePoint.infty := by
  rw [OnePoint.continuousAt_infty]
  intro U hU
  rw [zeroSection_apply_infty] at hU
  obtain ⟨O, hOU, hOopen, hOmem⟩ := mem_nhds_iff.mp hU
  have hOq : IsOpen ((Submission.Milnor.vData k).q ⁻¹' O) :=
    hOopen.preimage (Submission.Milnor.vData k).continuous_q
  set A : Set Submission.Milnor.MSpace8 :=
    Sum.inr ⁻¹' ((Submission.Milnor.vData k).q ⁻¹' O) with hAdef
  have hAopen : IsOpen A := (isOpen_sum_iff.mp hOq).2
  have hAmem : (0 : Submission.Milnor.MSpace8) ∈ A := by
    show (Submission.Milnor.vData k).q (Sum.inr (0 : Submission.Milnor.MSpace8)) ∈ O
    rw [(Submission.Milnor.vData k).q_inr]
    exact hOmem
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds hAmem)
  refine ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) ε⁻¹, isClosed_closedBall,
    isCompact_closedBall _ _, ?_⟩
  intro x hx
  show zeroSection k (x : Submission.Milnor.S4) ∈ U
  rw [zeroSection_apply_coe]
  have hxnorm : ε⁻¹ < ‖x‖ := by
    have hx' : ¬ (x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) ε⁻¹) := by
      simpa using hx
    rw [Metric.mem_closedBall, not_le, dist_zero_right] at hx'
    exact hx'
  have hxpos : 0 < ‖x‖ := lt_trans (inv_pos.mpr hεpos) hxnorm
  have hxne : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hxpos; exact lt_irrefl 0 hxpos
  have hrel : (Submission.Milnor.vData k).ιX (x, 0)
      = (Submission.Milnor.vData k).ιY (Submission.Milnor.invBase x, 0) := by
    rw [Submission.Glue.Data.ιX_eq_ιY_iff]
    refine ⟨hxne, ?_⟩
    change Submission.Milnor.vMap k (x, 0) = (Submission.Milnor.invBase x, 0)
    simp [Submission.Milnor.vMap, Submission.Milnor.vTwist]
  rw [hrel]
  apply hOU
  have hinvlt : ‖x‖⁻¹ < ε := by
    have h := (inv_lt_inv₀ hxpos (inv_pos.mpr hεpos)).mpr hxnorm
    rwa [inv_inv] at h
  have hdist : dist (((Submission.Milnor.invBase x, 0)) : Submission.Milnor.MSpace8)
      (0 : Submission.Milnor.MSpace8) = ‖x‖⁻¹ := by
    simp [Submission.Milnor.norm_invBase]
  have hballmem : (Submission.Milnor.invBase x, 0) ∈
      Metric.ball (0 : Submission.Milnor.MSpace8) ε := by
    rw [Metric.mem_ball, hdist]; exact hinvlt
  have hA' : (Submission.Milnor.vData k).q (Sum.inr (Submission.Milnor.invBase x, 0)) ∈ O :=
    hball hballmem
  rwa [(Submission.Milnor.vData k).q_inr] at hA'

lemma continuous_zeroSection (k : ℤ) : Continuous (zeroSection k) := by
  rw [OnePoint.continuous_iff]
  exact ⟨OnePoint.continuousAt_infty'.mp (continuousAt_zeroSection_infty k),
    continuous_zeroSection_coe k⟩

theorem exists_zeroSection (k : ℤ) :
    ∃ s : Submission.Milnor.S4 → Submission.Milnor.Vk k,
      Continuous s ∧
      (∀ x : EuclideanSpace ℝ (Fin 4),
        s (x : Submission.Milnor.S4) = (Submission.Milnor.vData k).ιX (x, 0)) ∧
      s OnePoint.infty = (Submission.Milnor.vData k).ιY (0, 0) :=
  ⟨zeroSection k, continuous_zeroSection k, fun x => zeroSection_apply_coe k x,
    zeroSection_apply_infty k⟩

end

end Work.Milnor
