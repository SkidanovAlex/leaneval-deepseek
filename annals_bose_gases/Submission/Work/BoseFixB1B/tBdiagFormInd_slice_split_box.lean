import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.tBdiagFormInd_blockIntegrand_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.tBdiagFormInd_slice_split_box` — the repaired block split of `tBdiagFormInd`

`Work.UBBInputs8.tBdiagFormInd a A V χ F Φ` is a sum of *one-slot* Bochner integrals

```
∑ i, (2π)⁻³ ∫_p F‖p‖ · ((a³)⁻¹ ∫_{abox N a} ‖tBamp χ p (Q_{A,i}Φ) i x‖²),
```

so the block decomposition `N = N₁ + N₂` of the particle number splits it into the first-block
slots (integrated over the *second* block `w`) plus the second-block slots (integrated over the
*first* block `y`).  The delegated statement
`Work.BoseFixB1B.tBdiagFormInd_slice_split` asks for this **without** the standing hypotheses on
the box `A` / the window `χ`, and with only the *Bochner-value* hypothesis `hint`; that version is
**not provable**: it needs the joint `(p,w)`-integrability of the amplitude integrand, which `hint`
cannot supply because a non-`L¹` integrand contributes the junk value `0` to a Bochner integral
(`integral_undef`).  See
`Submission/Work/BoseFixB1B/FINDING_tBdiagFormInd_slice_split_missing_joint_integrability.md`.

This file proves the repaired statement, in the regime of the FS application
(`A = dlBox ℓ d u` bounded and measurable, `support (chiB ℓ d u) ⊆ dlBox ℓ d u`, and the symbol
`F = fsKinCoeff c` a polynomial of degree `2 < 3`):

* `Work.BoseFixB1B.tBamp_boxQInd_merge_loc` — the *pointwise* fibre identity: the amplitude of a
  block-slot at a merged configuration is the amplitude of the corresponding slot of the slice;
* `Work.BoseFixB1B.tBamp_boxQInd_uniform_decay` — with `A ⊆ acube a`, `MeasurableSet A` and
  `support χ ⊆ A`, the box projection is bounded on the box and the amplitude decays uniformly:
  `‖tBamp χ p (Q_{A,i}Φ) i x‖ ≤ C(1+‖p‖)⁻³` for `x` in the box, *in particular* on the merged
  configurations `mergeBlock (u,w)` — which is what makes the sliced integrand bounded uniformly in
  the slice parameter `w`, hence jointly integrable;
* `Work.BoseFixB1B.tBamp_amplitude_box_fubini` — the per-slot box split under the honest
  `IntegrableOn` hypothesis;
* `Work.BoseFixB1B.tBdiagFormInd_blockIntegrand_integrable` — the joint `(p,w)`-integrability
  supplied by the two previous items and the growth bound on `F`.

The assembly below is then: unfold, `Fin.sum_univ_add`, the per-slot box split, the `p ↔ w`
exchange (`integral_integral_swap`), the finite slot sums (`integral_finsetSum`), and the
definitional rewrite of `tBdiagFormInd` at the slices.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem tBdiagFormInd_slice_split_box {N1 N2 : ℕ} {a V : ℝ} (ha : 0 < a)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : E3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχA : ∀ z : E3, z ∉ A → χ z = 0)
    {F : ℝ → ℝ} (hFm : Measurable F) {K d : ℝ} (hK : 0 ≤ K) (hd : d < 3)
    (hFd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ d)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.UBBInputs8.tBdiagFormInd a A V χ F Φ
      = (∫ w in Submission.BoseGases.abox N2 a,
            Work.UBBInputs8.tBdiagFormInd a A V χ F
              (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))))
        + (∫ y in Submission.BoseGases.abox N1 a,
            Work.UBBInputs8.tBdiagFormInd a A V χ F
              (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) := by
  classical
  -- ## 0. finite measures on the two blocks
  haveI hfin2 : IsFiniteMeasure ((volume : Measure (X N2)).restrict (abox N2 a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top N2 a ha.le⟩
  haveI hfin1 : IsFiniteMeasure ((volume : Measure (X N1)).restrict (abox N1 a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top N1 a ha.le⟩
  -- ## 1. the sup-bound of `Φ` on the box, and the uniform amplitude decay
  obtain ⟨B, hB⟩ := (abox_compact (N1 + N2) ha).exists_bound_of_continuousOn (f := Φ)
    hΦ.continuous.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (Φ (0 : X (N1 + N2)))) (hB _ (zero_mem_abox ha.le))
  have hΦb : ∀ x ∈ abox (N1 + N2) a, |Φ x| ≤ B :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  have hχsupp : Function.support χ ⊆ A := fun z hz => by_contra fun hzA => hz (hχA z hzA)
  obtain ⟨C, hC0, hCd⟩ := tBamp_boxQInd_uniform_decay (N := N1 + N2) (a := a) (volA := V) (B := B)
    ha hB0 hA hAc hχ hχs hχsupp hΦ hΦb
  -- ## 2. the per-slot amplitude squared is integrable on the big box
  have hmeas : ∀ (i : Fin (N1 + N2)) (p : E3),
      AEStronglyMeasurable (fun x : X (N1 + N2) =>
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2)
        ((volume : Measure (X (N1 + N2))).restrict (abox (N1 + N2) a)) := by
    intro i p
    exact ((Work.BoseFixB1.measurable_tBamp_boxQInd_pair (n := N1 + N2) (A := A) (χ := χ)
        (volA := V) (Ψ := Φ) hA hχ.continuous hΦ.continuous.measurable i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hInt : ∀ (i : Fin (N1 + N2)) (p : E3),
      IntegrableOn (fun x : X (N1 + N2) =>
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Φ) i x‖ ^ 2)
        (abox (N1 + N2) a) := by
    intro i p
    refine IntegrableOn.of_bound (abox_lt_top (N1 + N2) a ha.le) (hmeas i p)
      ((C / (1 + ‖p‖) ^ 3) ^ 2) ?_
    filter_upwards [ae_restrict_mem (abox_measurable (N1 + N2) a)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCd x hx i p) 2
  -- ## 3. the per-slot box split
  have hsplit1 : ∀ (j : Fin N1) (p : E3),
      (∫ x in abox (N1 + N2) a,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ) (Fin.castAdd N2 j) x‖ ^ 2)
        = ∫ w in abox N2 a, ∫ u in abox N1 a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A j
                (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2 :=
    fun j p => (tBamp_amplitude_box_fubini (N1 := N1) (N2 := N2) (a := a) (V := V) (A := A)
      (χ := χ) (Φ := Φ) p).1 j (hInt (Fin.castAdd N2 j) p)
  have hsplit2 : ∀ (j : Fin N2) (p : E3),
      (∫ x in abox (N1 + N2) a,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ) (Fin.natAdd N1 j) x‖ ^ 2)
        = ∫ u in abox N1 a, ∫ w in abox N2 a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A j
                (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2 :=
    fun j p => (tBamp_amplitude_box_fubini (N1 := N1) (N2 := N2) (a := a) (V := V) (A := A)
      (χ := χ) (Φ := Φ) p).2 j (hInt (Fin.natAdd N1 j) p)
  -- ## 4. the joint `(p,w)`-integrability
  have hJ1 : ∀ j : Fin N1,
      Integrable (fun q : E3 × X N2 => F ‖q.1‖ * ((a ^ 3)⁻¹ *
          (∫ u in abox N1 a,
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd V A j
                (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, q.2)))) j u‖ ^ 2)))
        ((volume : Measure E3).prod ((volume : Measure (X N2)).restrict (abox N2 a))) :=
    (tBdiagFormInd_blockIntegrand_integrable (N1 := N1) (N2 := N2) ha hA hAc hχ hχs hχA hΦ
      hFm hK hd hFd).1
  have hJ2 : ∀ j : Fin N2,
      Integrable (fun q : E3 × X N1 => F ‖q.1‖ * ((a ^ 3)⁻¹ *
          (∫ w in abox N2 a,
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd V A j
                (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (q.2, y)))) j w‖ ^ 2)))
        ((volume : Measure E3).prod ((volume : Measure (X N1)).restrict (abox N1 a))) :=
    (tBdiagFormInd_blockIntegrand_integrable (N1 := N1) (N2 := N2) ha hA hAc hχ hχs hχA hΦ
      hFm hK hd hFd).2
  -- ## 5. the `p ↔ w` exchange at each slot
  have hswap1 : ∀ j : Fin N1,
      (∫ p : E3, ∫ w in abox N2 a, F ‖p‖ * ((a ^ 3)⁻¹ *
          (∫ u in abox N1 a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A j
                (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)))
        = ∫ w in abox N2 a, ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ u in abox N1 a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A j
                  (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)) :=
    fun j => integral_integral_swap (hJ1 j)
  have hswap2 : ∀ j : Fin N2,
      (∫ p : E3, ∫ u in abox N1 a, F ‖p‖ * ((a ^ 3)⁻¹ *
          (∫ w in abox N2 a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A j
                (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)))
        = ∫ u in abox N1 a, ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ w in abox N2 a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A j
                  (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)) :=
    fun j => integral_integral_swap (hJ2 j)
  -- ## 6. the first-block half
  have hfirst :
      (∑ j : Fin N1, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
          (∫ x in abox (N1 + N2) a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ) (Fin.castAdd N2 j) x‖ ^ 2))))
        = ∫ w in abox N2 a, ∑ j : Fin N1, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2))) := by
    have hstep : ∀ j : Fin N1,
        ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ x in abox (N1 + N2) a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ) (Fin.castAdd N2 j) x‖ ^ 2)))
          = ∫ w in abox N2 a, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2))) := by
      intro j
      -- (a) replace the `x`-integral by the sliced double integral
      have ha1 : (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ x in abox (N1 + N2) a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ) (Fin.castAdd N2 j) x‖ ^ 2)))
          = ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ * (∫ w in abox N2 a, ∫ u in abox N1 a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A j
                  (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        rw [hsplit1 j p]
      rw [ha1]
      -- (b) move the constants inside the `w`-integral
      have hb1 : (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ * (∫ w in abox N2 a, ∫ u in abox N1 a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A j
                  (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)))
          = ∫ p : E3, ∫ w in abox N2 a, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        have h1 : (∫ w in abox N2 a, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)))
            = F ‖p‖ * (∫ w in abox N2 a, ((a ^ 3)⁻¹ *
                (∫ u in abox N1 a,
                  ‖Work.SmallBoxTBWord.tBamp χ p
                    (Work.UBBInputs8.boxQInd V A j
                      (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2))) :=
          integral_const_mul (μ := (volume : Measure (X N2)).restrict (abox N2 a)) (F ‖p‖) _
        have h2 : (∫ w in abox N2 a, ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)))
            = (a ^ 3)⁻¹ * (∫ w in abox N2 a, (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2)) :=
          integral_const_mul (μ := (volume : Measure (X N2)).restrict (abox N2 a)) ((a ^ 3)⁻¹) _
        exact (h1.trans (by rw [h2])).symm
      rw [hb1]
      -- (c) the `p ↔ w` exchange
      rw [hswap1 j]
      -- (d) pull `(2π)⁻³` inside
      rw [← integral_const_mul]
    calc (∑ j : Fin N1, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ x in abox (N1 + N2) a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ) (Fin.castAdd N2 j) x‖ ^ 2))))
        = ∑ j : Fin N1, ∫ w in abox N2 a, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2))) :=
          Finset.sum_congr rfl fun j _ => hstep j
      _ = ∫ w in abox N2 a, ∑ j : Fin N1, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ u in abox N1 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) j u‖ ^ 2))) := by
          refine (integral_finsetSum Finset.univ fun j _ => ?_).symm
          exact ((hJ1 j).integral_prod_right).const_mul ((2 * π) ^ 3)⁻¹
  -- ## 7. the second-block half
  have hsecond :
      (∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
          (∫ x in abox (N1 + N2) a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ) (Fin.natAdd N1 j) x‖ ^ 2))))
        = ∫ y in abox N1 a, ∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w')))) j w‖ ^ 2))) := by
    have hstep : ∀ j : Fin N2,
        ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ x in abox (N1 + N2) a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ) (Fin.natAdd N1 j) x‖ ^ 2)))
          = ∫ y in abox N1 a, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w')))) j w‖ ^ 2))) := by
      intro j
      have ha1 : (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ x in abox (N1 + N2) a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ) (Fin.natAdd N1 j) x‖ ^ 2)))
          = ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ * (∫ u in abox N1 a, ∫ w in abox N2 a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A j
                  (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        rw [hsplit2 j p]
      rw [ha1]
      have hb1 : (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ * (∫ u in abox N1 a, ∫ w in abox N2 a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A j
                  (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)))
          = ∫ p : E3, ∫ u in abox N1 a, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        have h1 : (∫ u in abox N1 a, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)))
            = F ‖p‖ * (∫ u in abox N1 a, ((a ^ 3)⁻¹ *
                (∫ w in abox N2 a,
                  ‖Work.SmallBoxTBWord.tBamp χ p
                    (Work.UBBInputs8.boxQInd V A j
                      (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2))) :=
          integral_const_mul (μ := (volume : Measure (X N1)).restrict (abox N1 a)) (F ‖p‖) _
        have h2 : (∫ u in abox N1 a, ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)))
            = (a ^ 3)⁻¹ * (∫ u in abox N1 a, (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w')))) j w‖ ^ 2)) :=
          integral_const_mul (μ := (volume : Measure (X N1)).restrict (abox N1 a)) ((a ^ 3)⁻¹) _
        exact (h1.trans (by rw [h2])).symm
      rw [hb1]
      rw [hswap2 j]
      rw [← integral_const_mul]
    calc (∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
            (∫ x in abox (N1 + N2) a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ) (Fin.natAdd N1 j) x‖ ^ 2))))
        = ∑ j : Fin N2, ∫ y in abox N1 a, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w')))) j w‖ ^ 2))) :=
          Finset.sum_congr rfl fun j _ => hstep j
      _ = ∫ y in abox N1 a, ∑ j : Fin N2, ((2 * π) ^ 3)⁻¹ * (∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
              (∫ w in abox N2 a,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd V A j
                    (fun w' => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w')))) j w‖ ^ 2))) := by
          refine (integral_finsetSum Finset.univ fun j _ => ?_).symm
          exact ((hJ2 j).integral_prod_right).const_mul ((2 * π) ^ 3)⁻¹
  -- ## 8. assemble
  rw [Work.UBBInputs8.tBdiagFormInd, Fin.sum_univ_add, hfirst, hsecond]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Work.UBBInputs8.tBdiagFormInd]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Work.UBBInputs8.tBdiagFormInd]

end Work.BoseFixB1B
