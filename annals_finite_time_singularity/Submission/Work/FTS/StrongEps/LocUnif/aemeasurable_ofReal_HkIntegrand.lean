/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. measurability of the `ofReal` of the `H^k`-integrand on a rectangle

`HkIntegrand α k g z θ` is a finite sum of squares

* `(D_z^i g · w(z)/sin(2θ)^{η/2})²`, `0 ≤ i ≤ k`, and
* `(D_z^j D_θ^i g · W(z,θ))²`, `0 ≤ i, j ≤ k`, `1 ≤ i`, `i + j ≤ k`,

where the weights `w` and `W = w · sin(2θ)^{-γ/2}` are Borel measurable *functions of `(z,θ)`
alone* (no positivity of `sin(2θ)` or of `z` is needed for measurability).  Hence
`p ↦ ofReal (HkIntegrand α k g p.1 p.2)` is a.e. measurable on a rectangle `[a,b] × [c,d]` as
soon as each slot `D_z^j D_θ^i g` is `ContinuousOn` that rectangle, which is exactly the
hypothesis `hslots` (the `D_z^i g` are the slots `D_z^i D_θ^0 g`).

This mirrors the private lemma `aemeasurable_ofReal_HkIntegrand_five` of
`Submission/Work/FTS/StrongEps/LocUnif/lintegral_HkIntegrand_five_le_liminf.lean`, with the
level `5` replaced by an arbitrary `k`.

(Note `open scoped Real` below: without it the `π` in the statement is not the notation for
`Real.pi`, and with `autoImplicit = false` the statement does not even elaborate.)
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

theorem aemeasurable_ofReal_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hslots : ∀ (j i : ℕ), ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  -- The three positivity hypotheses are not needed for measurability itself: they are what
  -- places the rectangle inside the open quadrant, i.e. they are what makes the slots
  -- `ContinuousOn` on it in the applications of this lemma.
  have hquad : ∀ (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d →
      0 < z ∧ 0 < θ ∧ θ < π / 2 := by
    intro z θ hz hθ
    exact ⟨by linarith [hz.1, ha], by linarith [hθ.1, hc], by linarith [hθ.2, hd]⟩
  have hs : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hslot : ∀ j i : ℕ, AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun j i => (hslots j i).aemeasurable hs
  -- the radial weight `w z / sin(2θ)^{η/2}` is Borel measurable
  have hw : AEMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    ((((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)).div
      ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow
        measurable_const)).aemeasurable
  -- the full weight `W = w · sin(2θ)^{-γ/2}` is Borel measurable
  have hWt : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    have h : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [h]
    exact ((((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)).mul
      ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow
        measurable_const)).aemeasurable
  -- the `D_z`-block: `DzIter i g = mixed i 0 g`
  have hsum1 : AEMeasurable
      (∑ i ∈ Finset.range (k + 1), fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter i g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    Finset.aemeasurable_sum _ (fun i _ => ((hslot i 0).mul hw).pow_const 2)
  -- the mixed block
  have hsum2 : AEMeasurable
      (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), fun p : ℝ × ℝ =>
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    Finset.aemeasurable_sum _ (fun i _ => Finset.aemeasurable_sum _ (fun j _ => by
      by_cases hc' : 1 ≤ i ∧ i + j ≤ k
      · simp only [ite_eq_left hc']
        exact ((hslot j i).mul hWt).pow_const 2
      · simp only [ite_eq_right hc']
        exact aemeasurable_zero))
  have hpoly : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    (hsum1.add hsum2).congr (by
      filter_upwards with p
      simp only [Pi.add_apply, Finset.sum_apply]
      rfl)
  exact ENNReal.measurable_ofReal.comp_aemeasurable hpoly

end Work.FTS.StrongEps.LocUnif
