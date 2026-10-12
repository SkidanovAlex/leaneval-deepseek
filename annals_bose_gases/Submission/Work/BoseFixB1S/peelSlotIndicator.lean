import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.peelSlotIndicator`

Peeling the `i`-th position slot out of a centred box integral against a bounded kernel:

  `∫_{abox (n+1) ℓ} 1_A(x i)·g(x i)·K x = ∫_{t ∈ A} g t · ∫_{abox n ℓ} K (kcInsN n i (t,r))`

for a measurable `A ⊆ acube ℓ`, an integrable `1_A·g` on the cube and a kernel `K` that is
a.e. strongly measurable and bounded by `C` on the `(n+1)`-particle box.

The three ingredients are

* the measure-preserving change of variables `abox_peel_transport` (`kcInsN` identifies the
  box integral with the integral against the product measure on `acube ℓ × abox n ℓ`),
* Fubini (`integral_prod`) with integrability supplied by the pointwise domination
  `‖1_A(t)g(t)·K(kcInsN n i (t,r))‖ ≤ ‖1_A(t)g(t)‖·C`,
* the identification `∫_{acube ℓ} 1_A·g·ψ = ∫_{A} g·ψ` for `A ⊆ acube ℓ`.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open Submission.BoseGases

set_option maxHeartbeats 1000000

theorem peelSlotIndicator {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : MeasureTheory.Integrable (fun t => A.indicator (fun _ => (1 : ℝ)) t * g t)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {K : Submission.BoseGases.X (n + 1) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hKm : MeasureTheory.AEStronglyMeasurable K
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)))
    (hKb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |K x| ≤ C) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        A.indicator (fun _ => (1 : ℝ)) (x i) * g (x i) * K x)
      = ∫ t in A, g t * (∫ r in Submission.BoseGases.abox n ℓ,
          K (Submission.BoseGases.kcInsN n i (t, r))) := by
  -- finiteness of the two restricted measures (for `SFinite`/`IsFiniteMeasure` instances)
  haveI : IsFiniteMeasure ((volume : Measure kcE3).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ.le⟩
  -- (1) change of variables: peel the `i`-th slot out of the box integral
  rw [Q0C.abox_peel_transport (n := n) (ℓ := ℓ) i
    (fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * g (x i) * K x)]
  -- (2) the peeled coordinate is the first component of the pair
  have hpoint : ∀ q : kcE3 × X n,
      A.indicator (fun _ => (1 : ℝ)) ((kcInsN n i q) i) * g ((kcInsN n i q) i)
          * K (kcInsN n i q)
        = (A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1) * K (kcInsN n i q) := by
    rintro ⟨t, r⟩
    simp only [kc_insN_apply_same]
  simp only [hpoint]
  -- (3) a.e. the pair lies in the boxes
  have hmems : ∀ᵐ q ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))),
      q.1 ∈ acube ℓ ∧ q.2 ∈ abox n ℓ := by
    have hmem : ∀ᵐ q ∂(volume : Measure (kcE3 × X n)).restrict (acube ℓ ×ˢ abox n ℓ),
        q ∈ acube ℓ ×ˢ abox n ℓ :=
      self_mem_ae_restrict ((acube_measurable ℓ).prod (abox_measurable n ℓ))
    rw [← Q0C.prod_restrict_acube n ℓ] at hmem
    simpa [Set.mem_prod] using hmem
  -- (4) the dominating integrable function
  have hconst : Integrable (fun _ : X n => C) ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    integrable_const C
  have hdom : Integrable (fun q : kcE3 × X n =>
      ‖A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1‖ * C)
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    Integrable.mul_prod (f := fun t : kcE3 => ‖A.indicator (fun _ => (1 : ℝ)) t * g t‖)
      (g := fun _ : X n => C) hg.norm hconst
  -- (5) a.e. strong measurability of the joint integrand
  have hmp : MeasurePreserving (⇑(kcInsN n i))
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ)))
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => kcE3) i))
      (abox_peel_mp (n := n) ℓ i)
    simpa [kcInsN] using h
  have hmeasφ : AEStronglyMeasurable (fun q : kcE3 × X n =>
      A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1)
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    hg.aestronglyMeasurable.comp_fst
  have hmeasK : AEStronglyMeasurable (fun q : kcE3 × X n => K (kcInsN n i q))
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    hKm.comp_measurePreserving hmp
  have hmeas : AEStronglyMeasurable (fun q : kcE3 × X n =>
      A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1 * K (kcInsN n i q))
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    hmeasφ.mul hmeasK
  -- (6) the pointwise domination
  have hbnd : ∀ᵐ q ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))),
      ‖A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1 * K (kcInsN n i q)‖
        ≤ ‖A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1‖ * C := by
    filter_upwards [hmems] with q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hK : |K (kcInsN n i q)| ≤ C :=
      hKb _ (Q0C.kcInsN_mem_abox (A := acube ℓ) (Set.Subset.refl _) i hq1 hq2)
    have hK' : ‖K (kcInsN n i q)‖ ≤ C := by simpa [Real.norm_eq_abs] using hK
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hK' (norm_nonneg _)
  -- (7) integrability of the joint integrand
  have hprod : Integrable (fun q : kcE3 × X n =>
      A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1 * K (kcInsN n i q))
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    Integrable.mono' hdom hmeas hbnd
  -- (8) Fubini
  rw [integral_prod _ hprod]
  dsimp only
  -- (9) the inner integral of a constant times `K`
  have hstep : (∫ t in acube ℓ, ∫ r in abox n ℓ,
        (A.indicator (fun _ => (1 : ℝ)) t * g t) * K (kcInsN n i (t, r)))
      = ∫ t in acube ℓ, (A.indicator (fun _ => (1 : ℝ)) t * g t)
          * (∫ r in abox n ℓ, K (kcInsN n i (t, r))) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [integral_const_mul]
  rw [hstep]
  -- (10) the cube integral of the indicator is the integral over `A`
  have hlast : (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t * g t
        * (∫ r in abox n ℓ, K (kcInsN n i (t, r))))
      = ∫ t in A, g t * (∫ r in abox n ℓ, K (kcInsN n i (t, r))) := by
    have hEq : (fun t : kcE3 => A.indicator (fun _ => (1 : ℝ)) t * g t
          * (∫ r in abox n ℓ, K (kcInsN n i (t, r))))
        = A.indicator (fun t : kcE3 => g t
            * (∫ r in abox n ℓ, K (kcInsN n i (t, r)))) := by
      funext t
      by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
    rw [hEq, MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hAc]
  rw [hlast]

end Work.BoseFixB1S
