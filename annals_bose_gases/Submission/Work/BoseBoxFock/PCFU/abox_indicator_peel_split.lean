import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chCslot_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.abox_indicator_peel_split`

The *indicator-split* companion of `chCcfg_integral_peel_real` (`PCFU/chCslot_peel.lean`).

The generic slot peel rewrites an integral over `X n` as the triple iterated integral over the
remaining coordinates `x'` and the two slots `w, w'`:

    ∫_x F x = ∫_{x'} ∫_w ∫_{w'} F (chCcfg i j w w' x') .

Here `F` is the box-restricted integrand `F = 1_{abox n ℓ} · f`.  Since
`chCcfg i j w w' x' ∈ abox n ℓ ↔ w ∈ acube ℓ ∧ w' ∈ acube ℓ ∧ ∀ k, x' k ∈ acube ℓ`
(`chCcfg_mem_abox_iff`), the box indicator factors *exactly* into the three indicators of the
three integration variables:

    1_{abox n ℓ}(chCcfg i j w w' x') = 1_{acube ℓ}(w) · (1_{acube ℓ}(w') · 1_{Π acube ℓ}(x')) .

So the peel of the box integral becomes the identity stated below: the naive integration of `f`
over the box equals the integration of the fully windowed integrand over the *unrestricted*
`(w, w', x')`-space.  The pointwise factorisation is proved by case analysis on the three
membership predicates; the integral identity is then the generic peel plus three
`integral_congr_ae` rewrites (the equality holds everywhere, not merely a.e.).
-/

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The indicator split of the box peel.**  For `i ≠ j` and `f` whose box restriction is
integrable, the integral of `f` over the centred box is the iterated integral over the two peeled
slots `w, w'` and the remaining coordinates `x'` of the product of the three cube-indicators with
`f : X n → ℝ`, and `f` evaluated at `chCcfg i j w w' x'`. -/
theorem abox_indicator_peel_split {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ℓ : ℝ}
    {f : Submission.BoseGases.X n → ℝ}
    (hf : MeasureTheory.Integrable
      (fun x => (Submission.BoseGases.abox n ℓ).indicator f x)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :
    (∫ x : Submission.BoseGases.X n, (Submission.BoseGases.abox n ℓ).indicator f x)
      = ∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → EuclideanSpace ℝ (Fin 3)),
          ∫ w : EuclideanSpace ℝ (Fin 3), ∫ w' : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w
              * ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w'
                * ((Set.univ.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} =>
                    Submission.BoseGases.acube ℓ)).indicator (fun _ => (1 : ℝ)) x'
                  * f (Work.BoseBoxFock.PCFU.chCcfg i j w w' x'))) := by
  classical
  -- The pointwise factorisation of the box indicator along the slot map.
  have hpt : ∀ (w w' : E3) (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3),
      (Submission.BoseGases.abox n ℓ).indicator f
          (Work.BoseBoxFock.PCFU.chCcfg i j w w' x')
        = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w
          * ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w'
            * ((Set.univ.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} =>
                Submission.BoseGases.acube ℓ)).indicator (fun _ => (1 : ℝ)) x'
              * f (Work.BoseBoxFock.PCFU.chCcfg i j w w' x'))) := by
    intro w w' x'
    have hmem := Work.BoseBoxFock.PCFU.chCcfg_mem_abox_iff (i := i) (j := j) hij w w' ℓ x'
    by_cases hw : w ∈ Submission.BoseGases.acube ℓ
    · by_cases hw' : w' ∈ Submission.BoseGases.acube ℓ
      · by_cases hx : x' ∈ Set.univ.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} =>
            Submission.BoseGases.acube ℓ)
        · have hy : Work.BoseBoxFock.PCFU.chCcfg i j w w' x' ∈ Submission.BoseGases.abox n ℓ :=
            hmem.mpr ⟨hw, hw', fun k => Set.mem_univ_pi.mp hx k⟩
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hw, Set.indicator_of_mem hw',
            Set.indicator_of_mem hx]
          simp
        · have hy : Work.BoseBoxFock.PCFU.chCcfg i j w w' x' ∉ Submission.BoseGases.abox n ℓ :=
            fun h => hx (Set.mem_univ_pi.mpr (hmem.mp h).2.2)
          rw [Set.indicator_of_notMem hy, Set.indicator_of_mem hw, Set.indicator_of_mem hw',
            Set.indicator_of_notMem hx]
          simp
      · have hy : Work.BoseBoxFock.PCFU.chCcfg i j w w' x' ∉ Submission.BoseGases.abox n ℓ :=
          fun h => hw' (hmem.mp h).2.1
        rw [Set.indicator_of_notMem hy, Set.indicator_of_mem hw, Set.indicator_of_notMem hw']
        simp
    · have hy : Work.BoseBoxFock.PCFU.chCcfg i j w w' x' ∉ Submission.BoseGases.abox n ℓ :=
        fun h => hw (hmem.mp h).1
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hw]
      simp
  -- The generic slot peel, then the pointwise factorisation at each of the three levels.
  rw [Work.BoseBoxFock.PCFU.chCcfg_integral_peel_real (n := n) (i := i) (j := j) hij hf]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
  exact hpt w w' x'

end Work.BoseBoxFock.PCFU
