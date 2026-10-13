import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.shiftReduceDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set

noncomputable section

set_option autoImplicit false

/-! ## Elementary facts about the `Ω`-weight `omegaAux`

`Ω` never vanishes (positivity), which is what allows the *integrable* majorant `(v²σ)·Ω` to
be divided by `Ω`, and it is continuous, which makes the resulting coefficient `e^{2bt}/Ω`
measurable.  Together these produce the a.e. strong measurability of the shifted integrand
`e^{2bt}(v²σ)`, even though nothing is assumed about the measurability of `u`, `v` or `σ`. -/

theorem shiftSq_omegaAux_pos (t : ℝ) : 0 < Work.FTS.EllSol.omegaAux t := by
  simp only [Work.FTS.EllSol.omegaAux]
  positivity

theorem shiftSq_continuous_omegaAux : Continuous (Work.FTS.EllSol.omegaAux) := by
  unfold Work.FTS.EllSol.omegaAux
  exact ((continuous_const.add Real.continuous_exp).pow 4).mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))

/-- On the closed strip `Iθ` the only points which are not interior are the two endpoints
`0` and `π/2`; this is what makes the passage from the open strip (where the identity
`u = e^{bt} v` is available) to `univ ×ˢ Iθ` harmless. -/
theorem shiftSq_Iθ_diff_Ioo_eq_endpoints {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hθ' : θ ∉ Set.Ioo 0 (Real.pi / 2)) : θ = 0 ∨ θ = Real.pi / 2 := by
  have hIcc : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
  rcases eq_or_lt_of_le hIcc.1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hIcc.2 (le_of_not_gt fun hlt => hθ' ⟨h, hlt⟩))

/-- The set of non-interior points of the strip is null. -/
theorem shiftSq_volume_prod_endpoints :
    (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({0, Real.pi / 2} : Set ℝ)) = 0 := by
  have h : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [Set.insert_eq]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton _)
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h, mul_zero]

/-- Transfer of `σ`-weighted square integrability under the exponential shift `u = e^{bt} v`:
if the `Ω`-weighted square of `v` is integrable on the strip `univ ×ˢ Iθ` (with `Ω` dominating
`e^{2bt}`), and `u = e^{bt}·v` on the open strip `0 < θ < π/2`, then the `σ`-weighted square of
`u` is integrable on the strip.  No measurability of `u`, `v`, `σ` is assumed: it is produced
from the integrability of the majorant. -/
theorem integrableOn_shift_sq {b : ℝ} {u v : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hexp : ∀ t : ℝ, Real.exp (2 * b * t) ≤ Work.FTS.EllSol.omegaAux t)
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hv : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hid : ∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      u t θ = Real.exp (b * t) * v t θ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * σ p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
  set S : Set (ℝ × ℝ) := Set.univ ×ˢ Work.Spaces.Iθ with hS
  set G : ℝ × ℝ → ℝ := fun p => (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2
    with hGdef
  set G0 : ℝ × ℝ → ℝ := fun p => (v p.1 p.2) ^ 2 * σ p.2 with hG0def
  set f0 : ℝ × ℝ → ℝ := fun p => Real.exp (2 * b * p.1) * G0 p with hf0def
  have hSmeas : MeasurableSet S := by
    rw [hS]; exact MeasurableSet.univ.prod measurableSet_Icc
  -- the majorant `G` is integrable on the (restricted) strip
  have hGint : Integrable G (volume.restrict S) := by
    rw [hS, hGdef]
    exact hv
  -- `f0` is a.e. strongly measurable: it is `(e^{2bt}/Ω)·G` and `Ω` never vanishes
  have hf0_eq : f0 = fun p : ℝ × ℝ =>
      (Real.exp (2 * b * p.1) / Work.FTS.EllSol.omegaAux p.1) * G p := by
    funext p
    have hω : Work.FTS.EllSol.omegaAux p.1 ≠ 0 :=
      ne_of_gt (shiftSq_omegaAux_pos p.1)
    simp only [hf0def, hGdef, hG0def]
    field_simp
  have hf0_aesm : AEStronglyMeasurable f0 (volume.restrict S) := by
    rw [hf0_eq]
    have hc : Measurable (fun p : ℝ × ℝ =>
        Real.exp (2 * b * p.1) / Work.FTS.EllSol.omegaAux p.1) :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).div
        (shiftSq_continuous_omegaAux.measurable.comp measurable_fst)
    exact hc.aestronglyMeasurable.mul hGint.aestronglyMeasurable
  -- a.e. domination: on the strip `σ ≥ 0` and `e^{2bt} ≤ Ω`
  have hmono : ∀ᵐ p ∂(volume.restrict S), ‖f0 p‖ ≤ G p := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with p hp
    have hpIθ : p.2 ∈ Work.Spaces.Iθ := by
      simpa only [hS, Set.mem_prod, Set.mem_univ, true_and] using hp
    have hσp : 0 ≤ σ p.2 := hσ p.2 hpIθ
    have hf0unf : f0 p = Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2) := rfl
    have hGunf : G p = (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 := rfl
    have hωnn : 0 ≤ Work.FTS.EllSol.omegaAux p.1 :=
      le_of_lt (shiftSq_omegaAux_pos p.1)
    have hG0nn : 0 ≤ (v p.1 p.2) ^ 2 * σ p.2 := mul_nonneg (sq_nonneg _) hσp
    have hf0nn : 0 ≤ Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2) :=
      mul_nonneg (Real.exp_nonneg _) hG0nn
    have hGnn : 0 ≤ (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hωnn) hσp
    have hmain : Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2)
        ≤ (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 := by
      calc Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2)
          ≤ Work.FTS.EllSol.omegaAux p.1 * ((v p.1 p.2) ^ 2 * σ p.2) :=
            mul_le_mul_of_nonneg_right (hexp p.1) hG0nn
        _ = (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 := by ring
    have hf0abs : ‖f0 p‖ = Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2) := by
      rw [hf0unf, Real.norm_eq_abs, abs_of_nonneg hf0nn]
    rw [hf0abs, hGunf]
    exact hmain
  -- the only points of `S` where the identity `u = e^{bt}v` may fail are the endpoints
  have haeIoo : ∀ᵐ p ∂(volume.restrict S), p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' hSmeas, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ shiftSq_volume_prod_endpoints
    intro p hp
    simp only [Set.mem_ofPred_eq, not_imp] at hp
    have hpIθ : p.2 ∈ Work.Spaces.Iθ := by
      simpa only [hS, Set.mem_prod, Set.mem_univ, true_and] using hp.1
    have hmem : p.2 = 0 ∨ p.2 = Real.pi / 2 := shiftSq_Iθ_diff_Ioo_eq_endpoints hpIθ hp.2
    refine ⟨Set.mem_univ _, ?_⟩
    rcases hmem with h0 | hpi
    · rw [Set.mem_insert_iff]; exact Or.inl h0
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr hpi
  have hFint : Integrable (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * σ p.2)
      (volume.restrict S) := by
    refine (hGint.mono' hf0_aesm hmono).congr ?_
    filter_upwards [haeIoo] with p hp
    have hG0unf : G0 p = (v p.1 p.2) ^ 2 * σ p.2 := rfl
    have hf0unf : f0 p = Real.exp (2 * b * p.1) * G0 p := rfl
    rw [hf0unf, hG0unf, hid p.1 p.2 hp]
    have hexp2 : Real.exp (2 * b * p.1) = Real.exp (b * p.1) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hexp2, mul_pow]
    ring
  exact hFint

end

end Work.FTS.EllSol.Shift2Flat
