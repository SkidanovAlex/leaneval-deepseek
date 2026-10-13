import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.H2W.aeSliceHonestOfSlots
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.PsiSlices.slotReduction` — the target, reduced to the *slot* honesty of the slices

The target of this directory (`Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable`) is: for a
datum of the weak class `WeakPos2 α F Ψ` and a.e. `z > 0`, the slices `∂_z^mΨ(z,·)`, `m ≤ 4`, are
integrable against `sinθcos²θ` on `Iθ`.

This module records the sharpest available *reduction* of it: **the target follows from the
"slot" honesty of the slices**, namely

* `HkMem α 0 (∂_θ²(∂_z^jΨ))` for `j ≤ 2` (the second angular derivative of the first three
  slices — `aeSliceHonestOfSlots` converts these into the slices themselves, using
  `Honest.slice_bdd_of_sq_mul_sEta`: `∫(u'')²σ < ∞ ⟹ u, u'` bounded, `σ = sin(2θ)^{-η}`), and
* `HkMem α 0 (z²∂_z³Ψ)`, `HkMem α 0 (z²∂_z⁴Ψ)` (the `z²`-weighted square of the two top slices,
  which the AM–GM `abs_mul_sinCos2_le_weighted` absorbs into `sinθcos²θ`).

See `NOTES_pzIterSliceIntegrable_addendum4.md` §4–§6 for why *these* are the slots the whole
chapter funnels into (the moment chain `Endpt/moment_chain_pz` and `H2W.psiMomentChainWeak` need
`HkMem α 0 (z∂_zΨ)`, `HkMem α 0 (z²∂_z²Ψ)`; `aeSliceHonestOfSlots` needs the θ-slots), and §5 for
the new commutation identity `bslOp α (D_θ^iΨ) = D_θ^iF − [D_θ^i, Lzero]Ψ` which is the only
structural handle on them.
-/

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary angular facts -/

private theorem sr_sinCos2_zero_left : Work.Elliptic.sinCos2 0 = 0 := by
  simp [Work.Elliptic.sinCos2]

private theorem sr_sinCos2_zero_right : Work.Elliptic.sinCos2 (Real.pi / 2) = 0 := by
  simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]

private theorem sr_continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

private theorem sr_volume_Iθ_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

private theorem sr_HkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-! ## The AM–GM absorption of the angular weight into the `η`-weighted square -/

/-- **A slice is `sinθcos²θ`-integrable as soon as its `z²`-weighted `η`-square is.**  The
domination is `|u·sinθcos²θ| ≤ (u·w(z)/sin(2θ)^{η/2})² + 1` (`abs_mul_sinCos2_le_weighted`), and
the square is the (`θ`-slice of the) level-`0` `HkIntegrand` of `z²u`. -/
theorem integrableOn_mul_sinCos2_of_HkMem_zsq {α : ℝ} {u : ℝ → ℝ → ℝ} {z : ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * u z θ)) (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  -- the `η`-weighted square of `u` is integrable
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * u z θ) z θ)
      Work.Spaces.Iθ := h.1 z (le_of_lt hz)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * u z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    h1.congr_fun
      (fun θ _ => sr_HkIntegrand_zero α (fun z θ => z ^ 2 * u z θ) z θ) measurableSet_Icc
  have hz4 : ((z : ℝ) ^ 2) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (ne_of_gt hz))
  have h2c : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * u z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * (((z : ℝ) ^ 2) ^ 2)⁻¹) Work.Spaces.Iθ :=
    h2.mul_const (((z : ℝ) ^ 2) ^ 2)⁻¹
  have hW : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    refine h2c.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show ((z ^ 2 * u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * (((z : ℝ) ^ 2) ^ 2)⁻¹
      = (u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    have hstep : ((z ^ 2 * u z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          * (((z : ℝ) ^ 2) ^ 2)⁻¹
        = (u z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          * (((z : ℝ) ^ 2) ^ 2 * (((z : ℝ) ^ 2) ^ 2)⁻¹) := by ring
    rw [hstep, mul_inv_cancel₀ hz4, mul_one]
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
      Work.Spaces.Iθ :=
    hW.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (ne_of_lt sr_volume_Iθ_lt_top))
  rw [MeasureTheory.IntegrableOn]
  refine Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · simpa only [Real.norm_eq_abs] using
        Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted (f := fun θ : ℝ => u z θ) hz hθ
    · rw [h1, sr_sinCos2_zero_right, mul_zero, norm_zero]
      positivity
  · rw [← h0, sr_sinCos2_zero_left, mul_zero, norm_zero]
    positivity

/-! ## The reduction of the target -/

/-- **The target, from the slot honesty of the slices.** -/
theorem pzIterSliceIntegrable_of_slots4 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ)
    (hθ : ∀ j : ℕ, j ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.pzIter j Ψ)))
    (hr3 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ))
    (hr4 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, m ≤ 4 →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ := by
  have h3 := Work.FTS.EllipticEst.H2W.aeSliceHonestOfSlots hα hα4 h hθ hr3
  have hQ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.2.2.2.2.2.2.1
  filter_upwards [h3, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz3 hzmem
  have hz : 0 < z := hzmem
  intro m hm
  have hm4 : m ≤ 3 ∨ m = 4 := by omega
  rcases hm4 with hm3 | rfl
  · exact hz3 m hm3
  · refine integrableOn_mul_sinCos2_of_HkMem_zsq ?_ hr4 hz
    exact (hQ.aesm_slice_pzIter 4 hz).mul
      sr_continuous_sinCos2.measurable.aestronglyMeasurable

end

end Work.FTS.EllipticEst.H2W.PsiSlices
