import Mathlib

/-!
# Almost every slice of a null set is null

For a Lebesgue-null set `N ⊆ ℝ^{n+1}` we show that, for almost every `y : ℝ^n`,
the fibre `{t : ℝ | Fin.snoc y t ∈ N}` is Lebesgue-null in `ℝ`.

This is the "a.e. form" of Fubini/Tonelli for the product decomposition
`ℝ^{n+1} ≃ ℝ^n × ℝ`, `(y, t) ↦ Fin.snoc y t`, obtained from
`Measure.measure_ae_null_of_prod_null`.

It is the `∀ᵐ` strengthening of the pointwise statement
`Work.WilE2.slice_null` (`∃ y, volume {t | Fin.snoc y t ∈ N} = 0`).
-/

namespace Work.WilE2

open MeasureTheory

/-- The measurable equivalence `(y, t) ↦ Fin.snoc y t` between
`(Fin n → ℝ) × ℝ` and `Fin (n + 1) → ℝ`, built by splitting off the last
coordinate (`piFinSuccAbove`) and swapping the factors. -/
private noncomputable def sliceEquiv (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm

private lemma sliceEquiv_apply (n : ℕ) (y : Fin n → ℝ) (t : ℝ) :
    sliceEquiv n (y, t) = Fin.snoc y t := by
  have h : sliceEquiv n (y, t)
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
          (t, y) :=
    rfl
  rw [h]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last, Fin.snocEquiv]

/-- `(y, t) ↦ Fin.snoc y t` preserves Lebesgue measure. -/
private lemma sliceEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (sliceEquiv n) volume volume := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodComm : (Fin n → ℝ) × ℝ ≃ᵐ ℝ × (Fin n → ℝ)) volume volume :=
    Measure.measurePreserving_swap
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
      volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have h := h2.comp h1
  simpa [sliceEquiv, MeasurableEquiv.coe_trans, Function.comp_def] using h

theorem slice_null_ae {n : ℕ} {N : Set (Fin (n + 1) → ℝ)} (hN : MeasureTheory.volume N = 0) : MeasureTheory.volume {y : Fin n → ℝ | MeasureTheory.volume {t : ℝ | Fin.snoc y t ∈ N} ≠ 0} = 0 := by
  -- Replace `N` by a measurable null superset `N'`.
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  -- Its preimage under `(y, t) ↦ Fin.snoc y t` is a null set of the product.
  have hpre : (volume : Measure ((Fin n → ℝ) × ℝ)) (sliceEquiv n ⁻¹' N') = 0 := by
    rw [← Measure.map_apply (sliceEquiv n).measurable hN'm,
      (sliceEquiv_measurePreserving n).map_eq, hN'0]
  -- Fubini: almost every `y` has a null fibre.
  have h_ae : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      (volume : Measure ℝ) (Prod.mk y ⁻¹' (sliceEquiv n ⁻¹' N')) = 0 :=
    Measure.measure_ae_null_of_prod_null hpre
  -- Rewrite the fibre as a `Fin.snoc` fibre.
  have h_ae' : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      (volume : Measure ℝ) {t : ℝ | Fin.snoc y t ∈ N'} = 0 := by
    filter_upwards [h_ae] with y hy
    rwa [show Prod.mk y ⁻¹' (sliceEquiv n ⁻¹' N') = {t : ℝ | Fin.snoc y t ∈ N'} by
      ext t; simp [sliceEquiv_apply]] at hy
  -- The set of `y` whose `N'`-fibre is non-null is null.
  have hbad' : (volume : Measure (Fin n → ℝ))
      {y : Fin n → ℝ | ¬ ((volume : Measure ℝ) {t : ℝ | Fin.snoc y t ∈ N'} = 0)} = 0 :=
    (MeasureTheory.ae_iff (μ := (volume : Measure (Fin n → ℝ)))).mp h_ae'
  -- And the analogous set for `N` is contained in it, since `N ⊆ N'`.
  refine measure_mono_null (fun y hy => ?_) hbad'
  exact fun hzero => hy (measure_mono_null (fun t ht => hNN' ht) hzero)

end Work.WilE2
