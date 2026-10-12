import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.MM.threeDimL` — the three-dimensional sliding-box mean-square bound
from the one-dimensional input

For `0 < h ≤ ℓ` and a measurable `F : (Fin 3 → ℝ) → ℝ≥0∞`, *given* the one-dimensional bound `H1`
(same window `slI`, same constant `30/h'`) for **every** pair `0 < h' ≤ ℓ'`:

  `∫⁻_u ( (∫⁻_{y ∈ slBox ℓ h u} F y) / |slBox ℓ h u| )² du  ≤  (30/h)³ ∫⁻_{y ∈ slBig ℓ} F y² dy`.

The proof tensorises `H1` in the three coordinates:

* `Work.BoseFixB1S.lintegral_slBox` writes the box integral as the iterated window integral
  `∫_{y₀ ∈ slI(u₀)} ∫_{y₁ ∈ slI(u₁)} ∫_{y₂ ∈ slI(u₂)} F ![y₀,y₁,y₂]` and `volume_slBox` writes the
  normalising volume as the product `∏_j |slI(u_j)|`; hence the box mean is the threefold iterated
  window mean `wM0` (`wMean_eq_wM0`), whose outer sliding average is over the *outermost* coordinate
  `y₀` of a function that does not depend on the sliding variable `u₀`;
* `lintegralPi3_peel_rev` peels the `u`-integral in the order `(2,1,0)`, so that the innermost
  `u`-integral is over the coordinate `u₀` of the outermost window mean;
* `H1` is applied once per coordinate (each time pointwise in the remaining parameters), and the
  three intermediate reorderings are Tonelli swaps `lintegral_lintegral_swap` (everything is
  nonnegative, so there are no integrability side conditions);
* `Work.BoseFixB1S.lintegral_slBig` peels the `y`-integral back.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1.Core.MM

open Work.BoseFixB1S

variable {ℓ h : ℝ}

/-- **Set-integral version of `lintegral_const_mul`**, valid for all constants including `⊤`. -/
private lemma setLIntegral_const_mul {s : Set ℝ} (hs : MeasurableSet s) (c : ℝ≥0∞) {f : ℝ → ℝ≥0∞}
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
private theorem lintegralPi3_peel_rev (G : (Fin 3 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
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
private noncomputable def wv (ℓ h x : ℝ) : ℝ≥0∞ := volume (Work.BoseFixB1S.slI ℓ h x)

/-- The innermost window mean (mean over the third-coordinate window). -/
private noncomputable def wM2 (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h c y₀ y₁ : ℝ) : ℝ≥0∞ :=
  (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) / wv ℓ h c

/-- The middle window mean. -/
private noncomputable def wM1 (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h b c y₀ : ℝ) : ℝ≥0∞ :=
  (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, wM2 F ℓ h c y₀ y₁) / wv ℓ h b

/-- The threefold iterated window mean. -/
private noncomputable def wM0 (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h a b c : ℝ) : ℝ≥0∞ :=
  (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a, wM1 F ℓ h b c y₀) / wv ℓ h a

/-- The box mean. -/
private noncomputable def wMean (F : (Fin 3 → ℝ) → ℝ≥0∞) (ℓ h a b c : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
    / volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c])

/-- **Set-integral const-pull.**  For a finite constant, or when the function vanishes
identically, a constant can be pulled out of a set integral. -/
private lemma setLIntegral_const_mul_of {s : Set ℝ} (c : ℝ≥0∞) {f : ℝ → ℝ≥0∞}
    (h : c ≠ ⊤ ∨ ∀ x, f x = 0) : ∫⁻ x in s, c * f x = c * ∫⁻ x in s, f x := by
  rcases h with hc | hf
  · exact lintegral_const_mul' c f hc
  · have h1 : (fun x => c * f x) = fun _ => (0 : ℝ≥0∞) := by
      funext x
      rw [hf x, mul_zero]
    have h2 : f = fun _ => (0 : ℝ≥0∞) := funext hf
    rw [h1, h2, lintegral_zero, mul_zero]

/-- The volume of the sliding box is the product of the one-dimensional window volumes. -/
private lemma volume_slBox_vec (a b c : ℝ) :
    volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c]) = wv ℓ h a * wv ℓ h b * wv ℓ h c := by
  have e0 : (![a, b, c] : Fin 3 → ℝ) 0 = a := rfl
  have e1 : (![a, b, c] : Fin 3 → ℝ) 1 = b := rfl
  have e2 : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl
  rw [Work.BoseFixB1S.volume_slBox, Fin.prod_univ_three, e0, e1, e2]
  rfl

/-- The one-dimensional window volume is finite. -/
private lemma wv_ne_top (x : ℝ) : wv ℓ h x ≠ ⊤ := Work.BoseFixB1S.volume_slI_ne_top ℓ h x

/-- The arithmetic of the normalising constants. -/
private lemma inv_prod_eq (a b c : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) :
    (a * b * c)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ := by
  rw [ENNReal.mul_inv (Or.inr hc) (Or.inl (ENNReal.mul_ne_top ha hb)),
    ENNReal.mul_inv (Or.inr hb) (Or.inl ha)]

/-- **The box mean is the threefold iterated window mean.** -/
private lemma wMean_eq_wM0 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (a b c : ℝ) :
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
private lemma measurableSet_slI_pair :
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
private lemma measurable_wv : Measurable (fun c : ℝ => wv ℓ h c) := by
  have hw : (fun c : ℝ => wv ℓ h c) = fun c => ENNReal.ofReal
      (min (ℓ / 2) (h * c + h / 2) - max (-ℓ / 2) (h * c - h / 2)) := by
    funext c
    rw [wv, Work.BoseFixB1S.slI, Real.volume_Icc]
  rw [hw]
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-- The innermost window mean, jointly measurable in its parameters. -/
private lemma measurable_wM2 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
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
private lemma measurable_wM1 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
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
private lemma measurable_wMean {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
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
private lemma lintegral_swap_set {s : Set ℝ} {K : ℝ → ℝ → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) :
    ∫⁻ b, ∫⁻ x in s, K b x = ∫⁻ x in s, ∫⁻ b, K b x :=
  MeasureTheory.lintegral_lintegral_swap (μ := volume) (ν := volume.restrict s) hK.aemeasurable

/-! ### The one-dimensional input and const-pull helpers -/

/-- The one-dimensional bound of the statement, as a `Prop` (so that the auxiliary lemmas below
can take it as a hypothesis without repeating its body). -/
private def OneDimHyp : Prop :=
  ∀ {ℓ' h' : ℝ}, 0 < h' → h' ≤ ℓ' → ∀ G : ℝ → ℝ≥0∞,
    AEMeasurable G (volume : Measure ℝ) →
    ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ' h' u, G x)
        / (volume (Work.BoseFixB1S.slI ℓ' h' u))) ^ 2
      ≤ ENNReal.ofReal (30 / h') * ∫⁻ x in Set.Icc (-ℓ' / 2) (ℓ' / 2), (G x) ^ 2

/-- Pull a finite constant out of a double integral. -/
private lemma pull_out2 (r : ℝ≥0∞) (hr : r ≠ ⊤) (f : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ c, ∫⁻ b, r * f c b = r * ∫⁻ c, ∫⁻ b, f c b := by
  have h : (∫⁻ c, ∫⁻ b, r * f c b) = ∫⁻ c, r * (∫⁻ b, f c b) :=
    lintegral_congr fun c => lintegral_const_mul' r (f c) hr
  rw [h, lintegral_const_mul' r (fun c => ∫⁻ b, f c b) hr]

/-- Pull a finite constant out of an integral followed by a set integral. -/
private lemma pull_out_set2 (r : ℝ≥0∞) (hr : r ≠ ⊤) (f : ℝ → ℝ → ℝ≥0∞) (s : Set ℝ) :
    ∫⁻ c, ∫⁻ x in s, r * f c x = r * ∫⁻ c, ∫⁻ x in s, f c x := by
  have h : (∫⁻ c, ∫⁻ x in s, r * f c x) = ∫⁻ c, r * (∫⁻ x in s, f c x) :=
    lintegral_congr fun c => lintegral_const_mul' r (f c) hr
  rw [h, lintegral_const_mul' r (fun c => ∫⁻ x in s, f c x) hr]

/-- Pull a finite constant out of a double set integral. -/
private lemma pull_out_set_set (r : ℝ≥0∞) (hr : r ≠ ⊤) (f : ℝ → ℝ → ℝ≥0∞) (s : Set ℝ) :
    ∫⁻ x in s, ∫⁻ y in s, r * f x y = r * ∫⁻ x in s, ∫⁻ y in s, f x y := by
  have h : (∫⁻ x in s, ∫⁻ y in s, r * f x y) = ∫⁻ x in s, r * (∫⁻ y in s, f x y) :=
    lintegral_congr fun x => lintegral_const_mul' r (f x) hr
  rw [h, lintegral_const_mul' r (fun x => ∫⁻ y in s, f x y) hr]

/-! ### The box mean is the iterated window mean -/

/-- Pointwise: the squared box mean of `F` at `![a,b,c]` is the square of the threefold
iterated window mean. -/
private lemma tdl_boxPt {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (a b c : ℝ) :
    ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
        / (volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c]))) ^ 2 = (wM0 F ℓ h a b c) ^ 2 := by
  rw [show ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
      / (volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c]))) = wMean F ℓ h a b c from rfl,
    wMean_eq_wM0 (ℓ := ℓ) (h := h) hF a b c]

/-- Peel the `u`-integral of the squared box mean into the threefold iterated window mean. -/
private lemma tdl_peel {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
      = ∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2 := by
  have hφm : Measurable (fun u : Fin 3 → ℝ => ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
      / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2) :=
    (measurable_wMean (ℓ := ℓ) (h := h) hF).pow_const 2
  rw [lintegralPi3_peel_rev (G := fun u : Fin 3 → ℝ => ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u,
    F y) / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2) hφm]
  exact lintegral_congr fun c => lintegral_congr fun b => lintegral_congr fun a =>
    tdl_boxPt (ℓ := ℓ) (h := h) hF a b c

/-! ### The three one-dimensional applications -/

/-- The one-dimensional bound in the outermost coordinate `a`. -/
private lemma tdl_step1 (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (H1 : OneDimHyp) (b c : ℝ) :
    (∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2 := by
  have hg : Measurable (fun x : ℝ => ((b, c), x)) :=
    ((measurable_const (a := b)).prodMk (measurable_const (a := c))).prodMk measurable_id
  have hm : AEMeasurable (fun x : ℝ => wM1 F ℓ h b c x) (volume : Measure ℝ) :=
    ((measurable_wM1 (ℓ := ℓ) (h := h) hF).comp hg).aemeasurable
  have h1d := H1 (ℓ' := ℓ) (h' := h) hh hhℓ (fun x : ℝ => wM1 F ℓ h b c x) hm
  simpa only [wM0, wv] using h1d

/-- The one-dimensional bound in the middle coordinate `b`. -/
private lemma tdl_step2 (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (H1 : OneDimHyp) (c x : ℝ) :
    (∫⁻ b : ℝ, (wM1 F ℓ h b c x) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2 := by
  have hg : Measurable (fun y : ℝ => (c, (x, y))) :=
    (measurable_const (a := c)).prodMk
      ((measurable_const (a := x)).prodMk measurable_id)
  have hm : AEMeasurable (fun y : ℝ => wM2 F ℓ h c x y) (volume : Measure ℝ) :=
    ((measurable_wM2 (ℓ := ℓ) (h := h) hF).comp hg).aemeasurable
  have h1d := H1 (ℓ' := ℓ) (h' := h) hh hhℓ (fun y : ℝ => wM2 F ℓ h c x y) hm
  simpa only [wM1, wM2, wv] using h1d

/-- The one-dimensional bound in the innermost coordinate `c`. -/
private lemma tdl_step3 (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (H1 : OneDimHyp) (x y : ℝ) :
    (∫⁻ c : ℝ, (wM2 F ℓ h c x y) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2 := by
  have hslice : Measurable (fun z : ℝ => (![x, y, z] : Fin 3 → ℝ)) := by fun_prop
  have h1d := H1 (ℓ' := ℓ) (h' := h) hh hhℓ (fun z : ℝ => F ![x, y, z])
    (hF.comp hslice).aemeasurable
  simpa only [wM2, wv] using h1d

/-! ### Measurability certificates for the Tonelli swaps -/

/-- Measurability certificate for the first swap (`b` against `x`). -/
private lemma tdl_meas1 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (c : ℝ) :
    Measurable (Function.uncurry (fun b x : ℝ => (wM1 F ℓ h b c x) ^ 2)) := by
  have hg : Measurable (fun q : ℝ × ℝ => ((q.1, c), q.2)) :=
    (measurable_fst.prodMk (measurable_const (a := c))).prodMk measurable_snd
  exact ((measurable_wM1 (ℓ := ℓ) (h := h) hF).comp hg).pow_const 2

/-- Measurability certificate for the second swap (`c` against `x`): the inner `y`-integral is
jointly measurable in `(c, x)`. -/
private lemma tdl_meas2 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (Function.uncurry (fun c x : ℝ =>
      ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2)) := by
  have hg1 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.1.1) := measurable_fst.fst
  have hg2 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.1.2) := measurable_fst.snd
  have hg0 : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1.1, (q.1.2, q.2))) :=
    hg1.prodMk (hg2.prodMk measurable_snd)
  have hM2 : Measurable (fun q : (ℝ × ℝ) × ℝ => (wM2 F ℓ h q.1.1 q.1.2 q.2) ^ 2) :=
    ((measurable_wM2 (ℓ := ℓ) (h := h) hF).comp hg0).pow_const 2
  have hset : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} :=
    measurableSet_Icc.preimage measurable_snd
  have hjoint : Measurable (Function.uncurry (fun (p : ℝ × ℝ) (y : ℝ) =>
      {r : (ℝ × ℝ) × ℝ | r.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}.indicator
        (fun r => (wM2 F ℓ h r.1.1 r.1.2 r.2) ^ 2) (p, y))) := by
    have heq : Function.uncurry (fun (p : ℝ × ℝ) (y : ℝ) =>
        {r : (ℝ × ℝ) × ℝ | r.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}.indicator
          (fun r => (wM2 F ℓ h r.1.1 r.1.2 r.2) ^ 2) (p, y))
        = fun q : (ℝ × ℝ) × ℝ =>
            {r : (ℝ × ℝ) × ℝ | r.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}.indicator
              (fun r => (wM2 F ℓ h r.1.1 r.1.2 r.2) ^ 2) q := rfl
    rw [heq]
    exact hM2.indicator hset
  have hint := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hjoint
  have hfun : (fun p : ℝ × ℝ => ∫⁻ y, {r : (ℝ × ℝ) × ℝ | r.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}.indicator
        (fun r => (wM2 F ℓ h r.1.1 r.1.2 r.2) ^ 2) (p, y))
      = (fun p : ℝ × ℝ => ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h p.1 p.2 y) ^ 2) := by
    funext p
    rw [← lintegral_indicator measurableSet_Icc (fun y => (wM2 F ℓ h p.1 p.2 y) ^ 2)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_mem (show (p, y) ∈ {r : (ℝ × ℝ) × ℝ |
          r.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} from hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show (p, y) ∉ {r : (ℝ × ℝ) × ℝ |
          r.2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} from hy)]
  rw [hfun] at hint
  exact hint

/-- Measurability certificate for the second swap (`c` against `y`). -/
private lemma tdl_meas3 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (x : ℝ) :
    Measurable (Function.uncurry (fun c y : ℝ => (wM2 F ℓ h c x y) ^ 2)) := by
  have hg : Measurable (fun q : ℝ × ℝ => (q.1, (x, q.2))) :=
    measurable_fst.prodMk ((measurable_const (a := x)).prodMk measurable_snd)
  exact ((measurable_wM2 (ℓ := ℓ) (h := h) hF).comp hg).pow_const 2

/-! ### The Tonelli swaps and the final identification -/

/-- Swap `b` with `x` in the middle expression. -/
private lemma tdl_swap1 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (c : ℝ) :
    ∫⁻ b : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2
      = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ b : ℝ, (wM1 F ℓ h b c x) ^ 2 :=
  lintegral_swap_set (K := fun b x : ℝ => (wM1 F ℓ h b c x) ^ 2) (tdl_meas1 (ℓ := ℓ) (h := h) hF c)

/-- Swap `c` with `x` and then with `y`. -/
private lemma tdl_swap2 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
        (wM2 F ℓ h c x y) ^ 2
      = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ c : ℝ, (wM2 F ℓ h c x y) ^ 2 := by
  rw [lintegral_swap_set (K := fun c x : ℝ =>
    ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2)
    (tdl_meas2 (ℓ := ℓ) (h := h) hF)]
  refine lintegral_congr fun x => ?_
  exact lintegral_swap_set (K := fun c y : ℝ => (wM2 F ℓ h c x y) ^ 2)
    (tdl_meas3 (ℓ := ℓ) (h := h) hF x)

/-- The triple integral over the cube in coordinates is the integral over `slBig ℓ`. -/
private lemma tdl_tail {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
        ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2
      = ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 :=
  (Work.BoseFixB1S.lintegral_slBig (ℓ := ℓ) (F := fun y => (F y) ^ 2) (hF.pow_const 2)).symm

set_option maxHeartbeats 1600000 in
/-- **The three-dimensional sliding-box mean-square bound** (from the one-dimensional input). -/
theorem threeDimL {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (H1 : ∀ {ℓ' h' : ℝ}, 0 < h' → h' ≤ ℓ' → ∀ G : ℝ → ℝ≥0∞,
      AEMeasurable G (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ' h' u, G x)
          / (volume (Work.BoseFixB1S.slI ℓ' h' u))) ^ 2
        ≤ ENNReal.ofReal (30 / h') * ∫⁻ x in Set.Icc (-ℓ' / 2) (ℓ' / 2), (G x) ^ 2) :
    ∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
      ≤ ENNReal.ofReal ((30 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := by
  have hC : (0 : ℝ) ≤ 30 / h := by positivity
  have h1 : OneDimHyp := H1
  have hs1 : ∀ b c : ℝ, (∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2 :=
    fun b c => tdl_step1 (ℓ := ℓ) (h := h) hh hhℓ hF h1 b c
  have hs2 : ∀ c x : ℝ, (∫⁻ b : ℝ, (wM1 F ℓ h b c x) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2 :=
    fun c x => tdl_step2 (ℓ := ℓ) (h := h) hh hhℓ hF h1 c x
  have hs3 : ∀ x y : ℝ, (∫⁻ c : ℝ, (wM2 F ℓ h c x y) ^ 2)
      ≤ ENNReal.ofReal (30 / h) *
          ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2 :=
    fun x y => tdl_step3 (ℓ := ℓ) (h := h) hh hhℓ hF h1 x y
  rw [tdl_peel (ℓ := ℓ) (h := h) hF]
  calc ∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ a : ℝ, (wM0 F ℓ h a b c) ^ 2
      ≤ ∫⁻ c : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (30 / h) *
          ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2 :=
        lintegral_mono fun c => lintegral_mono fun b => hs1 b c
    _ = ENNReal.ofReal (30 / h) *
          (∫⁻ c : ℝ, ∫⁻ b : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2),
            (wM1 F ℓ h b c x) ^ 2) :=
        pull_out2 (ENNReal.ofReal (30 / h)) ENNReal.ofReal_ne_top
          (fun c b => ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (wM1 F ℓ h b c x) ^ 2)
    _ = ENNReal.ofReal (30 / h) *
          (∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ b : ℝ,
            (wM1 F ℓ h b c x) ^ 2) := by
        congr 1
        exact lintegral_congr fun c => tdl_swap1 (ℓ := ℓ) (h := h) hF c
    _ ≤ ENNReal.ofReal (30 / h) *
          (∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ENNReal.ofReal (30 / h) *
            ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (lintegral_mono fun c => lintegral_mono fun x => hs2 c x) zero_le
    _ = ENNReal.ofReal (30 / h) *
          (ENNReal.ofReal (30 / h) *
            (∫⁻ c : ℝ, ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in
              Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2)) := by
        congr 1
        exact pull_out_set2 (ENNReal.ofReal (30 / h)) ENNReal.ofReal_ne_top
          (fun c x => ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), (wM2 F ℓ h c x y) ^ 2)
          (Set.Icc (-ℓ / 2) (ℓ / 2))
    _ = ENNReal.ofReal (30 / h) *
          (ENNReal.ofReal (30 / h) *
            (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
              ∫⁻ c : ℝ, (wM2 F ℓ h c x y) ^ 2)) := by
        congr 1
        congr 1
        exact tdl_swap2 (ℓ := ℓ) (h := h) hF
    _ ≤ ENNReal.ofReal (30 / h) *
          (ENNReal.ofReal (30 / h) *
            (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
              ENNReal.ofReal (30 / h) *
                ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (lintegral_mono fun x => lintegral_mono fun y => hs3 x y) zero_le)
          zero_le
    _ = ENNReal.ofReal (30 / h) *
          (ENNReal.ofReal (30 / h) *
            (ENNReal.ofReal (30 / h) *
              (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2),
                ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2))) := by
        congr 1
        congr 1
        exact pull_out_set_set (ENNReal.ofReal (30 / h)) ENNReal.ofReal_ne_top
          (fun x y => ∫⁻ z in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![x, y, z]) ^ 2)
          (Set.Icc (-ℓ / 2) (ℓ / 2))
    _ = ENNReal.ofReal (30 / h) *
          (ENNReal.ofReal (30 / h) *
            (ENNReal.ofReal (30 / h) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2)) := by
        congr 1
        congr 1
        congr 1
        exact tdl_tail (ℓ := ℓ) hF
    _ = ENNReal.ofReal ((30 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := by
        rw [ENNReal.ofReal_pow hC 3]
        ring

end Work.BoseFixB1.Core.MM
