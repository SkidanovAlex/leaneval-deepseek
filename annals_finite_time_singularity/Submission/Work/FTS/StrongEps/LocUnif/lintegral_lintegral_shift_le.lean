import Mathlib.Analysis.SpecialFunctions.PolarCoord

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.LocUnif.lintegral_lintegral_shift_le`

A pure measure-theoretic shifting estimate used by the local-uniformity extraction of
`Submission/Work/FTS/StrongEps/exists_locUnif_subseq_of_uniform_H6.lean`.

**Statement.**  For `a < a'`, `b' < b`, `0 < h` and `h < a' - a`, and for a measurable
`G' : ℝ × ℝ → ℝ≥0∞`,

`∫⁻ p in [a',b'] × [c,d], ∫⁻ s in (0,h], G' (p.1 - s, p.2) ≤ h · ∫⁻ q in [a,b] × [c,d], G' q`.

**Why it is true.**  Tonelli swaps the two integrations; for a fixed `s ∈ (0,h]` the map
`p ↦ (p.1 - s, p.2)` translates the box `[a',b'] × [c,d]` *into* `[a,b] × [c,d]` (because
`a < a' - h ≤ a' - s` and `b' - s ≤ b' < b`), so the inner integral is at most the full
integral over `[a,b] × [c,d]`.  Integrating the resulting constant over `(0,h]` contributes
exactly `volume (Ioc 0 h) = ofReal h`.

The helper below isolates the per-`s` step: it is the image-measure form
`map (· - (s,0)) (volume.restrict A) ≤ volume.restrict C` of the shift, transported to
integrals with `lintegral_map`.
-/

open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

/-- **Per-`s` shift bound.**  If `a ≤ a' - s`, `b' ≤ b` and `0 ≤ s`, then translating the box
`[a',b'] × [c,d]` by `(s,0)` to the left does not increase the integral of a nonegative
measurable function against Lebesgue measure on `[a,b] × [c,d]`. -/
lemma setLIntegral_shift_le {a b a' b' c d s : ℝ} (ha : a ≤ a' - s) (hbb' : b' ≤ b)
    (hs0 : 0 ≤ s) {G' : ℝ × ℝ → ENNReal} (hG' : Measurable G') :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)
      ≤ ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
  have hCmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- the shift maps the source box into the target box
  have hsub : Set.Icc a' b' ×ˢ Set.Icc c d ⊆
      (fun p : ℝ × ℝ => (p.1 - s, p.2)) ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d) := by
    rintro p ⟨hp1, hp2⟩
    have h1 : a ≤ p.1 - s := by linarith [ha, hp1.1]
    have h2 : p.1 - s ≤ b := by linarith [hbb', hp1.2, hs0]
    exact ⟨⟨h1, h2⟩, hp2⟩
  have hTmeas : Measurable (fun p : ℝ × ℝ => (p.1 - s, p.2)) := by fun_prop
  -- the shift preserves Lebesgue measure on `ℝ × ℝ`
  have hmap : Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2)) volume = volume := by
    have heq : (fun p : ℝ × ℝ => (p.1 - s, p.2)) = fun p : ℝ × ℝ => p + (-s, 0) := by
      funext p; ext <;> simp [sub_eq_add_neg]
    rw [heq, Measure.IsAddRightInvariant.map_add_right_eq_self]
  have hmono : Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
        (volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
      ≤ volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := by
    calc Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
          (volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
        ≤ Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
            (volume.restrict ((fun p : ℝ × ℝ => (p.1 - s, p.2)) ⁻¹'
              (Set.Icc a b ×ˢ Set.Icc c d))) :=
          Measure.map_mono (Measure.restrict_mono hsub le_rfl) hTmeas
      _ = (Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2)) volume).restrict
            (Set.Icc a b ×ˢ Set.Icc c d) :=
          (Measure.restrict_map hTmeas hCmeas).symm
      _ = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := by rw [hmap]
  calc ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)
      = ∫⁻ q, G' q ∂(Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
            (volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))) :=
        (lintegral_map (μ := volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
          (f := G') (g := fun p : ℝ × ℝ => (p.1 - s, p.2)) hG' hTmeas).symm
    _ ≤ ∫⁻ q, G' q ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        lintegral_mono' hmono le_rfl
    _ = ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := rfl

set_option linter.unusedVariables false

/-- The assumption `a < a'` is not needed (only `h < a' - a` is), and neither is `0 < h`
(the bound is also valid, and trivial, for `h ≤ 0`); they are kept because they are part of the
requested statement. -/
theorem lintegral_lintegral_shift_le {a b a' b' c d h : ℝ} (haa' : a < a') (hb'b : b' < b)
    (hh : 0 < h) (hah : h < a' - a) {G' : ℝ × ℝ → ENNReal} (hG' : Measurable G') :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
      ≤ ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
  -- Tonelli: swap the order of integration.
  have hswap :
      ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
        = ∫⁻ s in Set.Ioc 0 h, ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2) :=
    lintegral_lintegral_swap (μ := volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
      (ν := volume.restrict (Set.Ioc 0 h)) (f := fun p s => G' (p.1 - s, p.2)) (by fun_prop)
  rw [hswap]
  -- For every `s ∈ (0,h]` the inner integral is bounded by the full integral over the target box.
  have hpt : ∀ s ∈ Set.Ioc 0 h,
      ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)
        ≤ ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hsle : s ≤ h := hs.2
    have ha : a ≤ a' - s := by linarith [hah, haa', hh]
    exact setLIntegral_shift_le ha (le_of_lt hb'b) hs0 hG'
  calc ∫⁻ s in Set.Ioc 0 h,
        (fun s => ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)) s
      ≤ ∫⁻ s in Set.Ioc 0 h,
        (fun _ => ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) s :=
        setLIntegral_mono measurable_const hpt
    _ = (∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) * volume (Set.Ioc 0 h) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
        rw [Real.volume_Ioc, sub_zero, mul_comm]

end Work.FTS.StrongEps.LocUnif
