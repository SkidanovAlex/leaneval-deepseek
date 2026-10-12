import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.meanSq3d` — the three-dimensional sliding-box mean-square bound

For `0 < h ≤ ℓ` and a measurable `F : (Fin 3 → ℝ) → ℝ≥0∞`, with the sliding box
`slBox ℓ h u = ∏_j slI ℓ h (u j)` and the cube `slBig ℓ`:

  `∫⁻_u ( (∫⁻_{y ∈ slBox ℓ h u} F y) / |slBox ℓ h u| )² du  ≤  (30/h)³ ∫⁻_{y ∈ slBig ℓ} F y² dy`.

The proof tensorises the one-dimensional bound `Work.BoseFixB1.Core.oneDimMeanSq`: the box mean is
the threefold iterated one-dimensional window mean (`Box3.lintegral_slBox` for the box integral,
`Box3.volume_slBox` for the normalising volume), the `u`-integral is peeled in the coordinate order
`(2,1,0)` (`lintegralPi3_peel_rev`) so that the innermost sliding variable is paired with the
outermost box integration variable, and the one-dimensional bound is applied once per coordinate,
each time pointwise in the remaining parameters.  The three intermediate reorderings use
`lintegral_lintegral_swap`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1.Core

open Work.BoseFixB1S

variable {ℓ h : ℝ}

/-- **Set-integral version of `lintegral_const_mul`**, valid for all constants including `⊤`. -/
lemma setLIntegral_const_mul {s : Set ℝ} (hs : MeasurableSet s) (c : ℝ≥0∞) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x in s, c * f x = c * ∫⁻ x in s, f x := by
  rw [← lintegral_indicator hs (fun x => c * f x), ← lintegral_indicator hs f]
  have hpt : (fun x => s.indicator (fun x => c * f x) x) = fun x => c * s.indicator f x := by
    funext x
    by_cases hx : x ∈ s <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hpt]
  exact lintegral_const_mul c (hf.indicator hs)

set_option maxHeartbeats 1600000 in
/-- Peel the coordinates of `Fin 3 → ℝ` in the order `(2,1,0)`. -/
theorem lintegralPi3_peel_rev (G : (Fin 3 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u : Fin 3 → ℝ, G u = ∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ a : ℝ, G ![a, b, c] := by
  set e1 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3) with he1
  set e2 : (Fin 2 → ℝ) ≃ᵐ ℝ × (Fin 1 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) (1 : Fin 2) with he2
  set e3 : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ with he3
  have hmp1 : MeasurePreserving e1.symm (volume : Measure (ℝ × (Fin 2 → ℝ))) volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)).symm
  have hmp2 : MeasurePreserving e2.symm (volume : Measure (ℝ × (Fin 1 → ℝ))) volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) (1 : Fin 2)).symm
  have hmp3 : MeasurePreserving e3.symm (volume : Measure ℝ) volume :=
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have h1 : (∫⁻ p : ℝ × (Fin 2 → ℝ), G (e1.symm p)) = ∫⁻ u : Fin 3 → ℝ, G u :=
    hmp1.lintegral_comp hG
  rw [← h1]
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) = volume.prod volume from rfl]
  have hprod1 : (∫⁻ p : ℝ × (Fin 2 → ℝ), G (e1.symm p)
        ∂(volume.prod (volume : Measure (Fin 2 → ℝ))))
      = ∫⁻ c : ℝ, ∫⁻ q : Fin 2 → ℝ, G (e1.symm (c, q)) :=
    MeasureTheory.lintegral_prod (μ := volume) (ν := (volume : Measure (Fin 2 → ℝ)))
      (f := fun p : ℝ × (Fin 2 → ℝ) => G (e1.symm p))
      (hG.comp (MeasurableEquiv.measurable e1.symm)).aemeasurable
  rw [hprod1]
  have hstep2 : ∀ c : ℝ, (∫⁻ q : Fin 2 → ℝ, G (e1.symm (c, q)))
      = ∫⁻ b : ℝ, ∫⁻ r : Fin 1 → ℝ, G (e1.symm (c, e2.symm (b, r))) := by
    intro c
    have hf : Measurable (fun q : Fin 2 → ℝ => G (e1.symm (c, q))) := by fun_prop
    have h2 : (∫⁻ p : ℝ × (Fin 1 → ℝ), G (e1.symm (c, e2.symm p)))
        = ∫⁻ q : Fin 2 → ℝ, G (e1.symm (c, q)) :=
      hmp2.lintegral_comp (f := fun q : Fin 2 → ℝ => G (e1.symm (c, q))) hf
    rw [← h2]
    rw [show (volume : Measure (ℝ × (Fin 1 → ℝ))) = volume.prod volume from rfl]
    exact MeasureTheory.lintegral_prod (μ := volume) (ν := (volume : Measure (Fin 1 → ℝ)))
      (f := fun p : ℝ × (Fin 1 → ℝ) => G (e1.symm (c, e2.symm p))) (by fun_prop)
  simp only [hstep2]
  have hstep3 : ∀ (c b : ℝ), (∫⁻ r : Fin 1 → ℝ, G (e1.symm (c, e2.symm (b, r))))
      = ∫⁻ a : ℝ, G (e1.symm (c, e2.symm (b, e3.symm a))) := by
    intro c b
    have hf : Measurable (fun r : Fin 1 → ℝ => G (e1.symm (c, e2.symm (b, r)))) := by fun_prop
    exact (hmp3.lintegral_comp (f := fun r : Fin 1 → ℝ => G (e1.symm (c, e2.symm (b, r))))
      hf).symm
  simp only [hstep3]
  have hcoord : ∀ a b c : ℝ, G (e1.symm (c, e2.symm (b, e3.symm a))) = G ![a, b, c] := by
    intro a b c
    congr 1
    funext i
    fin_cases i <;>
      simp [he1, he2, he3, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
        MeasurableEquiv.funUnique, Fin.insertNth, Fin.insertNth_apply_below, Matrix.cons_val_zero,
        Matrix.cons_val_one]
  simp only [hcoord]

/-! ## The window means -/

/-- The Lebesgue volume of the one-dimensional window `slI ℓ h x`. -/
noncomputable def wv (ℓ h x : ℝ) : ℝ≥0∞ := volume (Work.BoseFixB1S.slI ℓ h x)

/-- The innermost window mean (mean over the third-coordinate window). -/
noncomputable def wM2 (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h c y₀ y₁ : ℝ) : ℝ≥0∞ :=
  (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) / wv ℓ h c

/-- The middle window mean. -/
noncomputable def wM1 (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h b c y₀ : ℝ) : ℝ≥0∞ :=
  (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, wM2 F ℓ h c y₀ y₁) / wv ℓ h b

/-- The threefold iterated window mean. -/
noncomputable def wM0 (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h a b c : ℝ) : ℝ≥0∞ :=
  (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, wM1 F ℓ h b c y₀) / wv ℓ h a

/-- The box mean. -/
noncomputable def wMean (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h a b c : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
    / volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c])

/-- **Set-integral const-pull.**  For a finite constant, or when the function vanishes
identically, a constant can be pulled out of a set integral. -/
lemma setLIntegral_const_mul_of {s : Set ℝ} (c : ℝ≥0∞) {f : ℝ → ℝ≥0∞}
    (h : c ≠ ⊤ ∨ ∀ x, f x = 0) : ∫⁻ x in s, c * f x = c * ∫⁻ x in s, f x := by
  rcases h with hc | hf
  · exact lintegral_const_mul' c f hc
  · have h1 : (fun x => c * f x) = fun _ => (0 : ℝ≥0∞) := by
      funext x
      rw [hf x, mul_zero]
    have h2 : f = fun _ => (0 : ℝ≥0∞) := funext hf
    rw [h1, h2, lintegral_zero, mul_zero]

/-- The volume of the sliding box is the product of the one-dimensional window volumes. -/
lemma volume_slBox_vec (a b c : ℝ) :
    volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c]) = wv ℓ h a * wv ℓ h b * wv ℓ h c := by
  have e0 : (![a, b, c] : Fin 3 → ℝ) 0 = a := rfl
  have e1 : (![a, b, c] : Fin 3 → ℝ) 1 = b := rfl
  have e2 : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl
  rw [Work.BoseFixB1S.volume_slBox, Fin.prod_univ_three, e0, e1, e2]
  rfl

/-- The one-dimensional window volume is finite. -/
lemma wv_ne_top (x : ℝ) : wv ℓ h x ≠ ⊤ := Work.BoseFixB1S.volume_slI_ne_top ℓ h x

/-- The arithmetic of the normalising constants. -/
lemma inv_prod_eq (a b c : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) :
    (a * b * c)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ := by
  rw [ENNReal.mul_inv (Or.inr hc) (Or.inl (ENNReal.mul_ne_top ha hb)),
    ENNReal.mul_inv (Or.inr hb) (Or.inl ha)]

/-- **The box mean is the threefold iterated window mean.** -/
lemma wMean_eq_wM0 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (a b c : ℝ) :
    wMean F ℓ h a b c = wM0 F ℓ h a b c := by
  have e0 : (![a, b, c] : Fin 3 → ℝ) 0 = a := rfl
  have e1 : (![a, b, c] : Fin 3 → ℝ) 1 = b := rfl
  have e2 : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl
  have hLHS : wMean F ℓ h a b c
      = (wv ℓ h a * wv ℓ h b * wv ℓ h c)⁻¹ *
          ∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂] := by
    rw [wMean, Work.BoseFixB1S.lintegral_slBox _ hF, volume_slBox_vec,
      ENNReal.div_eq_inv_mul]
    simp only [e0, e1, e2]
  -- the pull of `(wv c)⁻¹` out of the `y₁`-integral, pointwise in `y₀`
  have hinner : ∀ y₀ : ℝ, (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
        (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) / wv ℓ h c) / wv ℓ h b
      = (wv ℓ h b)⁻¹ * ((wv ℓ h c)⁻¹ * ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
          ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) := by
    intro y₀
    have hA : (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
          (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) / wv ℓ h c)
        = ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            (wv ℓ h c)⁻¹ * (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) :=
      lintegral_congr fun y₁ => ENNReal.div_eq_inv_mul
    have hc : (wv ℓ h c)⁻¹ ≠ ⊤ ∨ ∀ y₁ : ℝ,
        (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) = 0 := by
      by_cases h0 : wv ℓ h c = 0
      · exact Or.inr fun y₁ => setLIntegral_measure_zero _ _ h0
      · exact Or.inl (ENNReal.inv_ne_top.mpr h0)
    rw [hA, setLIntegral_const_mul_of _ hc, ENNReal.div_eq_inv_mul]
  have houter : (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, (wv ℓ h b)⁻¹ * ((wv ℓ h c)⁻¹ *
        ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c,
          F ![y₀, y₁, y₂])) / wv ℓ h a
      = (wv ℓ h a)⁻¹ * ((wv ℓ h b)⁻¹ * ((wv ℓ h c)⁻¹ *
          ∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])) := by
    have hb : (wv ℓ h b)⁻¹ ≠ ⊤ ∨ ∀ y₀ : ℝ, (wv ℓ h c)⁻¹ *
        (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
          ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) = 0 := by
      by_cases h0 : wv ℓ h b = 0
      · refine Or.inr fun y₀ => ?_
        have hz : (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) = 0 :=
          setLIntegral_measure_zero _ _ h0
        rw [hz, mul_zero]
      · exact Or.inl (ENNReal.inv_ne_top.mpr h0)
    have hb2 : (wv ℓ h c)⁻¹ ≠ ⊤ ∨ ∀ y₀ : ℝ,
        (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c,
          F ![y₀, y₁, y₂]) = 0 := by
      by_cases h0 : wv ℓ h c = 0
      · refine Or.inr fun y₀ => ?_
        rw [show (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
            = ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, (0 : ℝ≥0∞) from
          lintegral_congr fun y₁ => setLIntegral_measure_zero _ _ h0, lintegral_zero]
      · exact Or.inl (ENNReal.inv_ne_top.mpr h0)
    rw [setLIntegral_const_mul_of _ hb, setLIntegral_const_mul_of _ hb2,
      ENNReal.div_eq_inv_mul]
  have hMid : (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
        (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) / wv ℓ h c) / wv ℓ h b)
        / wv ℓ h a
      = (wv ℓ h a)⁻¹ * ((wv ℓ h b)⁻¹ * ((wv ℓ h c)⁻¹ *
          ∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])) := by
    rw [lintegral_congr hinner]
    exact houter
  rw [hLHS]
  simp only [wM0, wM1, wM2]
  rw [hMid]
  rw [inv_prod_eq _ _ _ (wv_ne_top a) (wv_ne_top b) (wv_ne_top c)]
  ring

/-! ## Measurability of the window means -/

/-- Joint measurability of the one-dimensional window membership. -/
lemma measurableSet_slI_pair :
    MeasurableSet {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1} := by
  have hmem : ∀ q : ℝ × ℝ, q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1 ↔
      max (-ℓ / 2) (h * q.1 - h / 2) ≤ q.2 ∧ q.2 ≤ min (ℓ / 2) (h * q.1 + h / 2) := by
    intro q
    simp only [Work.BoseFixB1S.slI, Set.mem_Icc]
  have hset : {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1}
      = {q : ℝ × ℝ | max (-ℓ / 2) (h * q.1 - h / 2) ≤ q.2}
        ∩ {q : ℝ × ℝ | q.2 ≤ min (ℓ / 2) (h * q.1 + h / 2)} := by
    ext q
    simpa only [Set.mem_setOf_eq, Set.mem_inter_iff] using hmem q
  rw [hset]
  exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet.inter
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet

/-- Measurability of the window volume. -/
lemma measurable_wv : Measurable (fun c : ℝ => wv ℓ h c) := by
  have hw : (fun c : ℝ => wv ℓ h c) = fun c => ENNReal.ofReal
      (min (ℓ / 2) (h * c + h / 2) - max (-ℓ / 2) (h * c - h / 2)) := by
    funext c
    rw [wv, Work.BoseFixB1S.slI, Real.volume_Icc]
  rw [hw]
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-- The innermost window mean, jointly measurable in its parameters. -/
lemma measurable_wM2 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => wM2 F ℓ h p.1 p.2.1 p.2.2) := by
  have hpair : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1} :=
    measurableSet_slI_pair (ℓ := ℓ) (h := h)
  have hbase : Measurable (fun q : (ℝ × (ℝ × ℝ)) × ℝ => F ![q.1.2.1, q.1.2.2, q.2]) :=
    hF.comp (by fun_prop)
  have hset : MeasurableSet {q : (ℝ × (ℝ × ℝ)) × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1} :=
    hpair.preimage (f := fun q : (ℝ × (ℝ × ℝ)) × ℝ => (q.1.1, q.2)) (by fun_prop)
  have hjoint : Measurable (Function.uncurry (fun (p : ℝ × (ℝ × ℝ)) (y₂ : ℝ) =>
      (Work.BoseFixB1S.slI ℓ h p.1).indicator (fun y₂ => F ![p.2.1, p.2.2, y₂]) y₂)) := by
    have heq : Function.uncurry (fun (p : ℝ × (ℝ × ℝ)) (y₂ : ℝ) =>
        (Work.BoseFixB1S.slI ℓ h p.1).indicator (fun y₂ => F ![p.2.1, p.2.2, y₂]) y₂)
        = {q : (ℝ × (ℝ × ℝ)) × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1}.indicator
            (fun q => F ![q.1.2.1, q.1.2.2, q.2]) := by
      funext q
      obtain ⟨p, y₂⟩ := q
      simp only [Function.uncurry_apply_pair]
      by_cases hq : y₂ ∈ Work.BoseFixB1S.slI ℓ h p.1
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show (p, y₂) ∈ {q : (ℝ × (ℝ × ℝ)) × ℝ |
            q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show (p, y₂) ∉ {q : (ℝ × (ℝ × ℝ)) × ℝ |
            q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1} from hq)]
    rw [heq]
    exact hbase.indicator hset
  have hnum : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h p.1, F ![p.2.1, p.2.2, y₂]) := by
    have hint := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hjoint
    convert hint using 2 with p
    exact (MeasureTheory.lintegral_indicator (Work.BoseFixB1S.measurableSet_slI ℓ h p.1)
      (fun y₂ => F ![p.2.1, p.2.2, y₂])).symm
  have hden : Measurable (fun p : ℝ × (ℝ × ℝ) => wv ℓ h p.1) := measurable_wv.comp (by fun_prop)
  exact hnum.div hden

/-- The middle window mean, jointly measurable in its parameters. -/
lemma measurable_wM1 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => wM1 F ℓ h p.1.1 p.1.2 p.2) := by
  have hM2 : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      wM2 F ℓ h q.1.1.2 q.1.2 q.2) :=
    (measurable_wM2 (ℓ := ℓ) (h := h) hF).comp (by fun_prop :
      Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ => (q.1.1.2, (q.1.2, q.2)))
  have hpair : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1} :=
    measurableSet_slI_pair (ℓ := ℓ) (h := h)
  have hset : MeasurableSet {q : ((ℝ × ℝ) × ℝ) × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1.1} :=
    hpair.preimage (f := fun q : ((ℝ × ℝ) × ℝ) × ℝ => (q.1.1.1, q.2)) (by fun_prop)
  have hjoint : Measurable (Function.uncurry (fun (p : (ℝ × ℝ) × ℝ) (y₁ : ℝ) =>
      (Work.BoseFixB1S.slI ℓ h p.1.1).indicator
        (fun y₁ => wM2 F ℓ h p.1.2 p.2 y₁) y₁)) := by
    have heq : Function.uncurry (fun (p : (ℝ × ℝ) × ℝ) (y₁ : ℝ) =>
        (Work.BoseFixB1S.slI ℓ h p.1.1).indicator
          (fun y₁ => wM2 F ℓ h p.1.2 p.2 y₁) y₁)
        = {q : ((ℝ × ℝ) × ℝ) × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1.1}.indicator
            (fun q => wM2 F ℓ h q.1.1.2 q.1.2 q.2) := by
      funext q
      obtain ⟨p, y₁⟩ := q
      simp only [Function.uncurry_apply_pair]
      by_cases hq : y₁ ∈ Work.BoseFixB1S.slI ℓ h p.1.1
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show (p, y₁) ∈ {q : ((ℝ × ℝ) × ℝ) × ℝ |
            q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1.1} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show (p, y₁) ∉ {q : ((ℝ × ℝ) × ℝ) × ℝ |
            q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.1.1} from hq)]
    rw [heq]
    exact hM2.indicator hset
  have hnum : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h p.1.1, wM2 F ℓ h p.1.2 p.2 y₁) := by
    have hint := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hjoint
    convert hint using 2 with p
    exact (MeasureTheory.lintegral_indicator (Work.BoseFixB1S.measurableSet_slI ℓ h p.1.1)
      (fun y₁ => wM2 F ℓ h p.1.2 p.2 y₁)).symm
  have hden : Measurable (fun p : (ℝ × ℝ) × ℝ => wv ℓ h p.1.1) :=
    measurable_wv.comp (by fun_prop)
  exact hnum.div hden

/-- Measurability of the box mean of `F`. -/
lemma measurable_wMean {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun u : Fin 3 → ℝ => (∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
      / (volume (Work.BoseFixB1S.slBox ℓ h u))) := by
  have hpair : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1} :=
    measurableSet_slI_pair (ℓ := ℓ) (h := h)
  have hset : MeasurableSet
      {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} := by
    have h2 : {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1}
        = ⋂ j : Fin 3, {p | (p.1 j, p.2 j) ∈ {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1}} := by
      ext p
      simp [Work.BoseFixB1S.mem_slBox]
    rw [h2]
    exact MeasurableSet.iInter fun j =>
      hpair.preimage (f := fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (p.1 j, p.2 j)) (by fun_prop)
  have hjoint : Measurable (Function.uncurry (fun (u : Fin 3 → ℝ) (y : Fin 3 → ℝ) =>
      (Work.BoseFixB1S.slBox ℓ h u).indicator F y)) := by
    have heq : Function.uncurry (fun (u : Fin 3 → ℝ) (y : Fin 3 → ℝ) =>
        (Work.BoseFixB1S.slBox ℓ h u).indicator F y)
        = {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1}.indicator
            (fun p => F p.2) := by
      funext p
      obtain ⟨u, y⟩ := p
      simp only [Function.uncurry_apply_pair, Set.mem_setOf_eq]
      by_cases hy : y ∈ Work.BoseFixB1S.slBox ℓ h u
      · rw [Set.indicator_of_mem hy,
          Set.indicator_of_mem (show (u, y) ∈ {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
            p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} from hy)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (show (u, y) ∉ {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
            p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} from hy)]
    rw [heq]
    exact (hF.comp measurable_snd).indicator hset
  have hnum : Measurable (fun u : Fin 3 → ℝ => ∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y) := by
    have hint := Measurable.lintegral_prod_right (ν := (volume : Measure (Fin 3 → ℝ))) hjoint
    convert hint using 2 with u
    exact (MeasureTheory.lintegral_indicator (Work.BoseFixB1S.measurableSet_slBox ℓ h u) F).symm
  have hvol : Measurable (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slBox ℓ h u)) := by
    rw [show (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slBox ℓ h u))
        = fun u => ∏ j, volume (Work.BoseFixB1S.slI ℓ h (u j)) from
      funext fun u => Work.BoseFixB1S.volume_slBox ℓ h u]
    refine Finset.measurable_prod _ fun j _ => ?_
    have hw : (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slI ℓ h (u j)))
        = fun u => ENNReal.ofReal
            (min (ℓ / 2) (h * u j + h / 2) - max (-ℓ / 2) (h * u j - h / 2)) := by
      funext u
      rw [Work.BoseFixB1S.slI, Real.volume_Icc]
    rw [hw]
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  exact hnum.div hvol

/-! ## The tensorisation -/

/-- Swap a Lebesgue integral with an integral over a set. -/
lemma lintegral_swap_set {s : Set ℝ} {K : ℝ → ℝ → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) :
    ∫⁻ b, ∫⁻ x in s, K b x = ∫⁻ x in s, ∫⁻ b, K b x :=
  MeasureTheory.lintegral_lintegral_swap (μ := volume) (ν := volume.restrict s) hK.aemeasurable

/-- Pull a constant out of the two outer integrals. -/
lemma pull_const2 (C : ℝ≥0∞) (hC : C ≠ ⊤) (g : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ c : ℝ, ∫⁻ b : ℝ, C * g b c) = C * ∫⁻ c : ℝ, ∫⁻ b : ℝ, g b c := by
  have h1 : (∫⁻ c : ℝ, ∫⁻ b : ℝ, C * g b c) = ∫⁻ c : ℝ, C * (∫⁻ b : ℝ, g b c) :=
    lintegral_congr fun c => lintegral_const_mul' C (fun b => g b c) hC
  rw [h1]
  exact lintegral_const_mul' C (fun c => ∫⁻ b : ℝ, g b c) hC

/-- Pull a constant out of two nested integrals over a set. -/
lemma pull_const_Icc2 (C : ℝ≥0∞) (hC : C ≠ ⊤) (K : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ c in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), C * K c x)
      = C * ∫⁻ c in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), K c x := by
  have h1 : (∫⁻ c in Set.Icc (-ℓ / 2) (ℓ / 2),
        ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), C * K c x)
      = ∫⁻ c in Set.Icc (-ℓ / 2) (ℓ / 2),
          C * (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), K c x) :=
    lintegral_congr fun c => lintegral_const_mul' C (fun x => K c x) hC
  rw [h1]
  exact lintegral_const_mul' C (fun c => ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), K c x) hC

/-- Pull a constant out of the integrals over a set. -/
lemma pull_const_Icc (C : ℝ≥0∞) (hC : C ≠ ⊤) (K : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), C * K c x)
      = C * ∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), K c x := by
  have h1 : (∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), C * K c x)
      = ∫⁻ c : ℝ, C * (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), K c x) :=
    lintegral_congr fun c => lintegral_const_mul' C (fun x => K c x) hC
  rw [h1]
  exact lintegral_const_mul' C (fun c => ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), K c x) hC

/-- **The three-dimensional sliding-box mean-square bound**, given the one-dimensional input
`H1` (the sliding-window mean-square bound of `Work.BoseFixB1.Core.oneDimMeanSq`).

Step 1: the innermost coordinate. -/
lemma meanSq3d_step1
    (H1 : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ Φ : ℝ → ℝ≥0∞, AEMeasurable Φ (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, Φ x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (Φ x) ^ 2)
    (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (b c : ℝ) :
    (∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2 := by
  have hm : AEMeasurable (fun x : ℝ => wM1 F ℓ h b c x) (volume : Measure ℝ) :=
    ((measurable_wM1 (ℓ := ℓ) (h := h) hF).comp
      (by fun_prop : Measurable fun x : ℝ => ((b, c), x))).aemeasurable
  have h1d := H1 (ℓ := ℓ) (h := h) hh hhℓ (wM1 F ℓ h b c) hm
  simpa only [wM0, wv] using h1d

/-- Step 2: the middle coordinate. -/
lemma meanSq3d_step2
    (H1 : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ Φ : ℝ → ℝ≥0∞, AEMeasurable Φ (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, Φ x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (Φ x) ^ 2)
    (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (c x : ℝ) :
    (∫⁻ b : ℝ, (wM1 F ℓ h b c x) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2 := by
  have hm : AEMeasurable (fun y : ℝ => wM2 F ℓ h c x y) (volume : Measure ℝ) :=
    ((measurable_wM2 (ℓ := ℓ) (h := h) hF).comp
      (by fun_prop : Measurable fun y : ℝ => (c, (x, y)))).aemeasurable
  have h1d := H1 (ℓ := ℓ) (h := h) hh hhℓ (wM2 F ℓ h c x) hm
  simpa only [wM1, wM2, wv] using h1d

/-- Step 3: the outermost coordinate. -/
lemma meanSq3d_step3
    (H1 : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ Φ : ℝ → ℝ≥0∞, AEMeasurable Φ (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, Φ x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (Φ x) ^ 2)
    (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (x y : ℝ) :
    (∫⁻ c : ℝ, (wM2 F ℓ h c x y) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2 := by
  have hslice : Measurable (fun z : ℝ => F ![x, y, z]) := hF.comp (by fun_prop)
  have h1d := H1 (ℓ := ℓ) (h := h) hh hhℓ (fun z : ℝ => F ![x, y, z]) hslice.aemeasurable
  simpa only [wM2, wv] using h1d

set_option maxHeartbeats 3200000 in
/-- The final identification of the triple window integral with the box integral. -/
lemma meanSq3d_tail {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
        ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2)
      = ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 :=
  (Work.BoseFixB1S.lintegral_slBig (ℓ := ℓ) (F := fun y => (F y) ^ 2)
    (hF.pow_const 2)).symm

set_option maxHeartbeats 8000000 in
/-- The peeling of the `u`-integral and the identification of the peeled integrand with the
square of the iterated window mean. -/
lemma meanSq3d_peel {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2)
      = ∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2 := by
  have hφm : Measurable (fun u : Fin 3 → ℝ => ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
      / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2) :=
    (measurable_wMean (ℓ := ℓ) (h := h) hF).pow_const 2
  have hpeel : (∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
      / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2)
      = ∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ a : ℝ,
          ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
            / (volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c]))) ^ 2 :=
    lintegralPi3_peel_rev (G := fun u : Fin 3 → ℝ =>
      ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2) hφm
  rw [hpeel]
  refine lintegral_congr fun c => lintegral_congr fun b => lintegral_congr fun a => ?_
  have hwt := wMean_eq_wM0 (ℓ := ℓ) (h := h) hF a b c
  rw [show ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
      / volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c])) = wMean F ℓ h a b c from rfl, hwt]

set_option maxHeartbeats 8000000 in
/-- The three one-dimensional steps in the tensorisation, combined. -/
lemma meanSq3d_mid
    (H1 : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ Φ : ℝ → ℝ≥0∞, AEMeasurable Φ (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, Φ x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (Φ x) ^ 2)
    (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2)
      ≤ (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2 := by
  have hsw1 : ∀ c : ℝ, Measurable (Function.uncurry (fun b x : ℝ => (wM1 F ℓ h b c x) ^ 2)) :=
    fun c => ((measurable_wM1 (ℓ := ℓ) (h := h) hF).comp
      (by fun_prop : Measurable fun p : ℝ × ℝ => ((p.1, c), p.2))).pow_const 2
  have hsw2 : Measurable (Function.uncurry
      (fun c y₀ : ℝ => ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c y₀ y₁) ^ 2)) := by
    have hb : Measurable (fun q : (ℝ × ℝ) × ℝ => (wM2 F ℓ h q.1.1 q.1.2 q.2) ^ 2) :=
      ((measurable_wM2 (ℓ := ℓ) (h := h) hF).comp
        (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.1, (q.1.2, q.2)))).pow_const 2
    have hs : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} :=
      measurableSet_Icc.preimage measurable_snd
    have hjoint : Measurable (Function.uncurry (fun (p : ℝ × ℝ) (y₁ : ℝ) =>
        (Set.Icc (-ℓ / 2) (ℓ / 2)).indicator (fun y₁ => (wM2 F ℓ h p.1 p.2 y₁) ^ 2) y₁)) := by
      have heq : Function.uncurry (fun (p : ℝ × ℝ) (y₁ : ℝ) =>
          (Set.Icc (-ℓ / 2) (ℓ / 2)).indicator (fun y₁ => (wM2 F ℓ h p.1 p.2 y₁) ^ 2) y₁)
          = {q : (ℝ × ℝ) × ℝ | q.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}.indicator
              (fun q => (wM2 F ℓ h q.1.1 q.1.2 q.2) ^ 2) := by
        funext q
        obtain ⟨p, y₁⟩ := q
        simp only [Function.uncurry_apply_pair, Set.mem_setOf_eq]
        by_cases hq : y₁ ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
        · rw [Set.indicator_of_mem hq,
            Set.indicator_of_mem (show (p, y₁) ∈ {q : (ℝ × ℝ) × ℝ |
              q.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} from hq)]
        · rw [Set.indicator_of_notMem hq,
            Set.indicator_of_notMem (show (p, y₁) ∉ {q : (ℝ × ℝ) × ℝ |
              q.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} from hq)]
      rw [heq]
      exact hb.indicator hs
    have hint := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hjoint
    convert hint using 2 with p
    exact (MeasureTheory.lintegral_indicator (s := Set.Icc (-ℓ / 2) (ℓ / 2)) measurableSet_Icc
      (fun y₁ => (wM2 F ℓ h p.1 p.2 y₁) ^ 2)).symm
  have hsw3 : ∀ y₀ : ℝ, Measurable (Function.uncurry
      (fun c y₁ : ℝ => (wM2 F ℓ h c y₀ y₁) ^ 2)) := by
    intro y₀
    have hmeas : Measurable (fun p : ℝ × ℝ => (wM2 F ℓ h p.1 y₀ p.2) ^ 2) :=
      ((measurable_wM2 (ℓ := ℓ) (h := h) hF).comp
        (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1, (y₀, p.2)))).pow_const 2
    exact hmeas
  calc ∫⁻ c, ∫⁻ b, ∫⁻ a, (wM0 F ℓ h a b c) ^ 2
      ≤ ∫⁻ c, ∫⁻ b, ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2),
          (wM1 F ℓ h b c x) ^ 2 :=
        lintegral_mono fun c => lintegral_mono fun b => meanSq3d_step1 H1 hh hhℓ hF b c
    _ = ENNReal.ofReal (30 / h) * ∫⁻ c, ∫⁻ b, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2),
          (wM1 F ℓ h b c x) ^ 2 := by
        exact pull_const2 (ENNReal.ofReal (30 / h)) ENNReal.ofReal_ne_top
          (fun b c => ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2)
    _ = ENNReal.ofReal (30 / h) * ∫⁻ c, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ b,
          (wM1 F ℓ h b c x) ^ 2 := by
        congr 1
        exact lintegral_congr fun c => lintegral_swap_set (hsw1 c)
    _ ≤ ENNReal.ofReal (30 / h) * ∫⁻ c, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2),
          ENNReal.ofReal (30 / h) * ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
            (wM2 F ℓ h c x y) ^ 2 :=
        mul_le_mul_right (lintegral_mono fun c =>
          lintegral_mono fun x => meanSq3d_step2 H1 hh hhℓ hF c x)
          (ENNReal.ofReal (30 / h))
    _ = (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)) *
          ∫⁻ c, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
            (wM2 F ℓ h c x y) ^ 2 := by
        rw [pull_const_Icc (ENNReal.ofReal (30 / h)) ENNReal.ofReal_ne_top
          (fun c x => ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2),
          mul_assoc (ENNReal.ofReal (30 / h)) (ENNReal.ofReal (30 / h))]
    _ = (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ c,
            (wM2 F ℓ h c x y) ^ 2 := by
        congr 1
        rw [lintegral_swap_set hsw2]
        exact lintegral_congr fun x => lintegral_swap_set (hsw3 x)
    _ ≤ (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
            ENNReal.ofReal (30 / h) * ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2),
              (F ![x, y, z]) ^ 2 :=
        mul_le_mul_right (lintegral_mono fun x =>
          lintegral_mono fun y => meanSq3d_step3 H1 hh hhℓ hF x y)
          (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h))
    _ = (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2 := by
        rw [pull_const_Icc2 (ENNReal.ofReal (30 / h)) ENNReal.ofReal_ne_top
          (fun x y => ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2),
          mul_assoc (ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h))
            (ENNReal.ofReal (30 / h))]

set_option maxHeartbeats 3200000 in
/-- **The three-dimensional sliding-box mean-square bound**, given the one-dimensional input. -/
theorem meanSq3d
    (H1 : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ Φ : ℝ → ℝ≥0∞, AEMeasurable Φ (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, Φ x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (30 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (Φ x) ^ 2)
    (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
      ≤ ENNReal.ofReal ((30 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := by
  have hC : (0 : ℝ) ≤ 30 / h := by positivity
  rw [meanSq3d_peel (ℓ := ℓ) (h := h) hF]
  refine le_trans (meanSq3d_mid H1 hh hhℓ hF) ?_
  rw [meanSq3d_tail (ℓ := ℓ) hF]
  have hconst : ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)
      = ENNReal.ofReal ((30 / h) ^ 3) := by
    rw [show ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h) * ENNReal.ofReal (30 / h)
        = (ENNReal.ofReal (30 / h)) ^ 3 from by ring,
      ENNReal.ofReal_pow hC 3]
  rw [hconst]

end Work.BoseFixB1.Core
