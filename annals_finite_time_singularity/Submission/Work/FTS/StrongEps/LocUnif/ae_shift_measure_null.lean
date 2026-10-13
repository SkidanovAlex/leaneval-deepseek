import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set

/-- Fubini + translation invariance: if a measurable set `B` meets the rectangle
`Icc a b ×ˢ Icc c d` in a null set, then for almost every `p` in the shifted
(and thinner) rectangle `Icc a' b' ×ˢ Icc c d`, the set of shifts `s ∈ (0, h]`
with `(p.1 - s, p.2) ∈ B` is null.  The hypotheses `h < a' - a` and `b' < b`
guarantee that for `p` in the small rectangle and `s ∈ (0, h]` the point
`(p.1 - s, p.2)` automatically lies in the *large* rectangle, so the null set
condition for `B ∩ (Icc a b ×ˢ Icc c d)` applies. -/
theorem ae_shift_measure_null {a b a' b' c d h : ℝ} (haa' : a < a') (hb'b : b' < b)
    (hh : 0 < h) (hah : h < a' - a) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hBnull : (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) B = 0) :
    ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      (MeasureTheory.volume.restrict (Set.Ioc 0 h)) {s : ℝ | (p.1 - s, p.2) ∈ B} = 0 := by
  -- Work with the piece of `B` inside the large rectangle: it is null.
  set W : Set (ℝ × ℝ) := B ∩ (Set.Icc a b ×ˢ Set.Icc c d) with hW
  have hWmeas : MeasurableSet W := hB.inter (measurableSet_Icc.prod measurableSet_Icc)
  have hWnull : (MeasureTheory.volume : Measure (ℝ × ℝ)) W = 0 := by
    rw [hW, ← Measure.restrict_apply hB]
    exact hBnull
  -- Fubini: almost every vertical slice of `W` is null.
  have hslice : ∀ᵐ y ∂(MeasureTheory.volume : Measure ℝ),
      (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, y) ∈ W} = 0 := by
    have h1 : ∫⁻ y, (MeasureTheory.volume : Measure ℝ) ((fun x : ℝ => (x, y)) ⁻¹' W)
        ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
      rw [← Measure.prod_apply_symm hWmeas]
      rw [← Measure.volume_eq_prod]
      exact hWnull
    exact (MeasureTheory.lintegral_eq_zero_iff
      (measurable_measure_prodMk_right hWmeas)).mp h1
  -- Restrict the `y`-variable to `Icc c d` and pull back through the product measure.
  have hD : ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc a' b')).prod
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc c d)),
      (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} = 0 := by
    have hTae : ∀ᵐ y ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Icc c d),
        (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, y) ∈ W} = 0 :=
      MeasureTheory.ae_restrict_of_ae hslice
    refine (Measure.ae_prod_iff_ae_ae ?_).mpr ?_
    · exact (measurableSet_singleton (0 : ENNReal)).preimage
        ((measurable_measure_prodMk_right hWmeas).comp measurable_snd)
    · exact Filter.Eventually.of_forall fun x => by simpa using hTae
  -- Rewrite the product of restricted measures as a restricted product measure.
  have hD' : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} = 0 := by
    have h := hD
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
    exact h
  have hbox : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      p ∈ Set.Icc a' b' ×ˢ Set.Icc c d :=
    MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [hD', hbox] with p hp hpmem
  rw [Set.mem_prod] at hpmem
  -- For `p` in the small rectangle and `s ∈ (0, h]`, the point `(p.1 - s, p.2)` lies
  -- in the large rectangle, so membership in `B` is membership in `W`.
  have hsub : {s : ℝ | (p.1 - s, p.2) ∈ B} ∩ Set.Ioc 0 h
      ⊆ {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}} := by
    intro s hs
    have h1 : a < p.1 - s := by
      have hh1 : a' ≤ p.1 := (Set.mem_Icc.mp hpmem.1).1
      linarith [hs.2.2]
    have h2 : p.1 - s < b := by
      have hh1 : p.1 ≤ b' := (Set.mem_Icc.mp hpmem.1).2
      linarith [hs.2.1]
    show (p.1 - s, p.2) ∈ W
    rw [hW]
    exact ⟨hs.1, ⟨le_of_lt h1, le_of_lt h2⟩, hpmem.2⟩
  -- Translation invariance of Lebesgue measure on `ℝ`.
  have htrans : (MeasureTheory.volume : Measure ℝ)
        {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}}
      = (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} := by
    have key : {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}}
        = (fun s : ℝ => -s) ⁻¹' ((fun t : ℝ => p.1 + t) ⁻¹' {x : ℝ | (x, p.2) ∈ W}) := by
      ext s; simp [sub_eq_add_neg]
    rw [key, MeasureTheory.Measure.measure_preimage_neg, MeasureTheory.measure_preimage_add]
  have hSp_meas : MeasurableSet {s : ℝ | (p.1 - s, p.2) ∈ B} :=
    hB.preimage ((measurable_const.sub measurable_id).prodMk measurable_const)
  rw [Measure.restrict_apply hSp_meas]
  refine le_antisymm ?_ zero_le
  calc (MeasureTheory.volume : Measure ℝ) ({s : ℝ | (p.1 - s, p.2) ∈ B} ∩ Set.Ioc 0 h)
      ≤ (MeasureTheory.volume : Measure ℝ) {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}} :=
        measure_mono hsub
    _ = (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} := htrans
    _ = 0 := hp

end Work.FTS.StrongEps.LocUnif
