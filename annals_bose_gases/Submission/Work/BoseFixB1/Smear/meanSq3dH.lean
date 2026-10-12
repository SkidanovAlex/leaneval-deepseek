import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1.Smear.MeanSq3dAux
import Submission.Work.BoseFixB1S.MeanSq.Sliced3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.BoseFixB1.Smear

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The normalised average of `F` over the sliding box `slBox ℓ h u`. -/
def bAvg (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (u : Fin 3 → ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y) / volume (Work.BoseFixB1S.slBox ℓ h u)

/-- Innermost sliced average: free integration variable `c`. -/
def slL (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (y₀ y₁ c : ℝ) : ℝ≥0∞ :=
  avg1 ℓ h (fun y₂ => F ![y₀, y₁, y₂]) c

/-- Middle sliced average: free integration variable `b`, with `(y₀, c)` frozen. -/
def slM (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (y₀ b c : ℝ) : ℝ≥0∞ :=
  avg1 ℓ h (fun y₁ => slL ℓ h F y₀ y₁ c) b

/-- Outer sliced average: free integration variable `a`, with `(b, c)` frozen. -/
def slN (ℓ h : ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) (a b c : ℝ) : ℝ≥0∞ :=
  avg1 ℓ h (fun y₀ => slM ℓ h F y₀ b c) a

/-! ## Measurability toolbox -/

/-- Measurability of `x ↦ ![a x, b x, c x]`. -/
lemma measurable_vec3 {α : Type*} [MeasurableSpace α] {a b c : α → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun x => (![a x, b x, c x] : Fin 3 → ℝ) := by
  rw [measurable_pi_iff]
  intro j
  fin_cases j
  · simpa using ha
  · simpa using hb
  · simpa using hc

/-- Measurability of `t ↦ volume (slI ℓ h t)`. -/
lemma measurable_volume_slI (ℓ h : ℝ) :
    Measurable (fun t : ℝ => volume (Work.BoseFixB1S.slI ℓ h t)) := by
  have hcont : Continuous fun t : ℝ =>
      min (ℓ / 2) (h * t + h / 2) - max (-ℓ / 2) (h * t - h / 2) :=
    (continuous_const.min ((continuous_const.mul continuous_id).add continuous_const)).sub
      (continuous_const.max ((continuous_const.mul continuous_id).sub continuous_const))
  have heq : (fun t : ℝ => volume (Work.BoseFixB1S.slI ℓ h t))
      = fun t : ℝ =>
          ENNReal.ofReal (min (ℓ / 2) (h * t + h / 2) - max (-ℓ / 2) (h * t - h / 2)) := by
    funext t
    rw [Work.BoseFixB1S.slI, Real.volume_Icc]
  rw [heq]
  exact ENNReal.measurable_ofReal.comp hcont.measurable

/-- Joint measurability of the normalised sliding average in the parameter and the centre. -/
lemma measurable_avg1_joint {β : Type*} [MeasurableSpace β]
    {f : ℝ → β → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) (ℓ h : ℝ) :
    Measurable (fun p : β × ℝ => avg1 ℓ h (fun x => f x p.1) p.2) := by
  have h1 : Measurable (fun p : β × ℝ => ∫⁻ x in Work.BoseFixB1S.slI ℓ h p.2, f x p.1) :=
    measurable_slI_setIntegral hf ℓ h
  have h2 : Measurable (fun p : β × ℝ => volume (Work.BoseFixB1S.slI ℓ h p.2)) :=
    (measurable_volume_slI ℓ h).comp measurable_snd
  have h3 : Measurable (fun p : β × ℝ =>
      (∫⁻ x in Work.BoseFixB1S.slI ℓ h p.2, f x p.1)
        * (volume (Work.BoseFixB1S.slI ℓ h p.2))⁻¹) := h1.mul h2.inv
  simpa only [avg1, div_eq_mul_inv] using h3

/-- Joint measurability of `(y₀, y₁, c) ↦ slL ℓ h F y₀ y₁ c`. -/
lemma measurable_slL3 (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => slL ℓ h F p.1 p.2.1 p.2.2) := by
  have hvec : Measurable fun p : ℝ × (ℝ × ℝ) => (![p.2.1, p.2.2, p.1] : Fin 3 → ℝ) :=
    measurable_vec3 (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
      measurable_fst
  have hf : Measurable (fun p : ℝ × (ℝ × ℝ) => F ![p.2.1, p.2.2, p.1]) := hF.comp hvec
  have h := measurable_avg1_joint (f := fun (x : ℝ) (q : ℝ × ℝ) => F ![q.1, q.2, x]) hf ℓ h
  have hmap : Measurable fun p : ℝ × (ℝ × ℝ) => ((p.1, p.2.1), p.2.2) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  exact h.comp hmap

/-- Joint measurability of `(y₀, b, c) ↦ slM ℓ h F y₀ b c`. -/
lemma measurable_slM3 (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => slM ℓ h F p.1 p.2.1 p.2.2) := by
  have hmap : Measurable fun p : ℝ × (ℝ × ℝ) => (p.2.1, (p.1, p.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hf : Measurable (fun p : ℝ × (ℝ × ℝ) => slL ℓ h F p.2.1 p.1 p.2.2) :=
    (measurable_slL3 ℓ h hF).comp hmap
  have h := measurable_avg1_joint (f := fun (x : ℝ) (q : ℝ × ℝ) => slL ℓ h F q.1 x q.2) hf ℓ h
  have hmap2 : Measurable fun p : ℝ × (ℝ × ℝ) => ((p.1, p.2.2), p.2.1) :=
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)
  exact h.comp hmap2

/-- Joint measurability of `(a, b, c) ↦ slN ℓ h F a b c`. -/
lemma measurable_slN3 (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => slN ℓ h F p.1 p.2.1 p.2.2) := by
  have hf : Measurable (fun p : ℝ × (ℝ × ℝ) => slM ℓ h F p.1 p.2.1 p.2.2) :=
    measurable_slM3 ℓ h hF
  have h := measurable_avg1_joint (f := fun (x : ℝ) (q : ℝ × ℝ) => slM ℓ h F x q.1 q.2) hf ℓ h
  have hmap2 : Measurable fun p : ℝ × (ℝ × ℝ) => ((p.2.1, p.2.2), p.1) :=
    ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)).prodMk
      measurable_fst
  exact h.comp hmap2

/-! ## The peeling identity and the two measurability inputs -/

/-- Fixed-set slicing: measurability of `p ↦ ∫_{y ∈ s} g (p, y)`. -/
lemma measurable_setIntegral_fixed_apply {β : Type*} [MeasurableSpace β] {s : Set ℝ}
    (hs : MeasurableSet s) {g : β × ℝ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun p : β => ∫⁻ y in s, g (p, y)) := by
  let G : β → ℝ → ℝ≥0∞ := fun p y => s.indicator (fun z => g (p, z)) y
  have h1 : Measurable fun q : β × ℝ => s.indicator (fun z => g (q.1, z)) q.2 :=
    (show Measurable fun q : β × ℝ => g (q.1, q.2) from hg).indicator
      (hs.preimage measurable_snd)
  have hg' : Measurable (Function.uncurry G) := h1
  have h2 := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hg'
  have h3 : (fun p : β => ∫⁻ y, G p y ∂(volume : Measure ℝ))
      = fun p : β => ∫⁻ y in s, g (p, y) := by
    funext p
    exact lintegral_indicator hs (fun z => g (p, z))
  rw [h3] at h2
  exact h2

/-- The nested normalised average over `slI ℓ h a × slI ℓ h b × slI ℓ h c` equals the normalised
average over the sliding box. -/
theorem avg1_iter_eq (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (a b c : ℝ) :
    avg1 ℓ h (fun y₀ => avg1 ℓ h (fun y₁ => avg1 ℓ h (fun y₂ => F ![y₀, y₁, y₂]) c) b) a
      = (∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
          / volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c]) := by
  have hgA : Measurable (fun q : (ℝ × ℝ) × ℝ => F ![q.1.1, q.1.2, q.2]) :=
    hF.comp (measurable_vec3 (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) measurable_snd)
  have hA : Measurable (fun p : ℝ × ℝ =>
      ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![p.1, p.2, y₂]) :=
    measurable_setIntegral_fixed_apply (Work.BoseFixB1S.measurableSet_slI ℓ h c) hgA
  have hAfix : ∀ y₀ : ℝ, Measurable (fun y₁ : ℝ =>
      ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) := fun y₀ =>
    hA.comp ((measurable_const : Measurable fun _ : ℝ => y₀).prodMk measurable_id')
  have hB : Measurable (fun y₀ : ℝ => ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
      ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂]) :=
    measurable_setIntegral_fixed_apply (Work.BoseFixB1S.measurableSet_slI ℓ h b) hA
  have hI : ∀ y₀ : ℝ, (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
        (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
          / volume (Work.BoseFixB1S.slI ℓ h c))
      = (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c,
          F ![y₀, y₁, y₂]) * (volume (Work.BoseFixB1S.slI ℓ h c))⁻¹ := by
    intro y₀
    rw [show (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
          (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
            / volume (Work.BoseFixB1S.slI ℓ h c))
        = ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
              * (volume (Work.BoseFixB1S.slI ℓ h c))⁻¹ from by
      refine lintegral_congr fun y₁ => ?_
      rw [div_eq_mul_inv]]
    exact setLintegral_mul_const (Work.BoseFixB1S.measurableSet_slI ℓ h b)
      (volume (Work.BoseFixB1S.slI ℓ h c))⁻¹ (hAfix y₀)
  have hO : (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a,
        (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
              / volume (Work.BoseFixB1S.slI ℓ h c))
          / volume (Work.BoseFixB1S.slI ℓ h b))
      = (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a,
          ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b, ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c,
            F ![y₀, y₁, y₂])
        * ((volume (Work.BoseFixB1S.slI ℓ h c))⁻¹
            * (volume (Work.BoseFixB1S.slI ℓ h b))⁻¹) := by
    rw [show (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a,
          (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
              (∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
                / volume (Work.BoseFixB1S.slI ℓ h c))
            / volume (Work.BoseFixB1S.slI ℓ h b))
        = ∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a,
            (∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
              ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
              * ((volume (Work.BoseFixB1S.slI ℓ h c))⁻¹
                  * (volume (Work.BoseFixB1S.slI ℓ h b))⁻¹) from by
      refine lintegral_congr fun y₀ => ?_
      rw [hI y₀, div_eq_mul_inv, mul_assoc]]
    exact setLintegral_mul_const (Work.BoseFixB1S.measurableSet_slI ℓ h a)
      ((volume (Work.BoseFixB1S.slI ℓ h c))⁻¹ * (volume (Work.BoseFixB1S.slI ℓ h b))⁻¹) hB
  have e0 : (![a, b, c] : Fin 3 → ℝ) 0 = a := by simp
  have e1 : (![a, b, c] : Fin 3 → ℝ) 1 = b := by simp
  have e2 : (![a, b, c] : Fin 3 → ℝ) 2 = c := by simp
  have hAne : volume (Work.BoseFixB1S.slI ℓ h a) ≠ ⊤ := Work.BoseFixB1S.volume_slI_ne_top ℓ h a
  have hBne : volume (Work.BoseFixB1S.slI ℓ h b) ≠ ⊤ := Work.BoseFixB1S.volume_slI_ne_top ℓ h b
  have hCne : volume (Work.BoseFixB1S.slI ℓ h c) ≠ ⊤ := Work.BoseFixB1S.volume_slI_ne_top ℓ h c
  have hABne : volume (Work.BoseFixB1S.slI ℓ h a) * volume (Work.BoseFixB1S.slI ℓ h b) ≠ ⊤ :=
    ENNReal.mul_ne_top hAne hBne
  have hY : (∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
      = ∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a,
          ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂] := by
    rw [Work.BoseFixB1S.lintegral_slBox (u := ![a, b, c]) hF, e0, e1, e2]
  have hv : volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c])
      = volume (Work.BoseFixB1S.slI ℓ h a) * volume (Work.BoseFixB1S.slI ℓ h b)
        * volume (Work.BoseFixB1S.slI ℓ h c) := by
    rw [Work.BoseFixB1S.volume_slBox, Fin.prod_univ_three, e0, e1, e2]
  have hinv : (volume (Work.BoseFixB1S.slI ℓ h a) * volume (Work.BoseFixB1S.slI ℓ h b)
        * volume (Work.BoseFixB1S.slI ℓ h c))⁻¹
      = (volume (Work.BoseFixB1S.slI ℓ h a))⁻¹ * (volume (Work.BoseFixB1S.slI ℓ h b))⁻¹
        * (volume (Work.BoseFixB1S.slI ℓ h c))⁻¹ := by
    rw [ENNReal.mul_inv (a := volume (Work.BoseFixB1S.slI ℓ h a)
          * volume (Work.BoseFixB1S.slI ℓ h b))
        (b := volume (Work.BoseFixB1S.slI ℓ h c)) (Or.inr hCne) (Or.inl hABne),
      ENNReal.mul_inv (a := volume (Work.BoseFixB1S.slI ℓ h a))
        (b := volume (Work.BoseFixB1S.slI ℓ h b)) (Or.inr hBne) (Or.inl hAne)]
  have hR : (∫⁻ y in Work.BoseFixB1S.slBox ℓ h ![a, b, c], F y)
        / volume (Work.BoseFixB1S.slBox ℓ h ![a, b, c])
      = (∫⁻ y₀ in Work.BoseFixB1S.slI ℓ h a,
          ∫⁻ y₁ in Work.BoseFixB1S.slI ℓ h b,
            ∫⁻ y₂ in Work.BoseFixB1S.slI ℓ h c, F ![y₀, y₁, y₂])
        * ((volume (Work.BoseFixB1S.slI ℓ h a))⁻¹
            * (volume (Work.BoseFixB1S.slI ℓ h b))⁻¹
            * (volume (Work.BoseFixB1S.slI ℓ h c))⁻¹) := by
    rw [hY, hv, ENNReal.div_eq_inv_mul, hinv]
    ring
  simp only [avg1]
  rw [hO, hR]
  rw [ENNReal.div_eq_inv_mul]
  ring

/-- Measurability of the sliding-box integral as a function of the centre `u`. -/
theorem measurable_slBox_setIntegral (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun u : Fin 3 → ℝ => ∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y) := by
  have hset : MeasurableSet {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1} := by
    have heq : {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | p.2 ∈ Work.BoseFixB1S.slBox ℓ h p.1}
        = ⋂ j : Fin 3, {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
            max (-ℓ / 2) (h * (p.1 j) - h / 2) ≤ p.2 j
              ∧ p.2 j ≤ min (ℓ / 2) (h * (p.1 j) + h / 2)} := by
      ext p
      simp only [Work.BoseFixB1S.mem_slBox, Work.BoseFixB1S.slI, Set.mem_Icc, Set.mem_iInter,
        Set.mem_ofPred_eq]
    rw [heq]
    refine MeasurableSet.iInter fun j => ?_
    have hc1 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        max (-ℓ / 2) (h * (p.1 j) - h / 2) :=
      continuous_const.max ((continuous_const.mul
        ((continuous_apply j).comp continuous_fst)).sub continuous_const)
    have hc2 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        min (ℓ / 2) (h * (p.1 j) + h / 2) :=
      continuous_const.min ((continuous_const.mul
        ((continuous_apply j).comp continuous_fst)).add continuous_const)
    have hc3 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2 j :=
      (continuous_apply j).comp continuous_snd
    exact ((isClosed_le hc1 hc3).inter (isClosed_le hc3 hc2)).measurableSet
  have hΦ : Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (Work.BoseFixB1S.slBox ℓ h p.1).indicator F p.2) :=
    (hF.comp measurable_snd).indicator hset
  let Gf : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ≥0∞ :=
    fun u y => (Work.BoseFixB1S.slBox ℓ h u).indicator F y
  have hΦ' : Measurable (Function.uncurry Gf) := hΦ
  have h2 := Measurable.lintegral_prod_right (ν := (volume : Measure (Fin 3 → ℝ))) hΦ'
  have h3 : (fun u : Fin 3 → ℝ => ∫⁻ y, Gf u y ∂(volume : Measure (Fin 3 → ℝ)))
      = fun u : Fin 3 → ℝ => ∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y := by
    funext u
    exact lintegral_indicator (Work.BoseFixB1S.measurableSet_slBox ℓ h u) F
  rw [h3] at h2
  exact h2

/-- Measurability of the volume of the sliding box as a function of the centre `u`. -/
theorem measurable_volume_slBox (ℓ h : ℝ) :
    Measurable (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slBox ℓ h u)) := by
  have hfun : (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slBox ℓ h u))
      = fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slI ℓ h (u 0))
          * volume (Work.BoseFixB1S.slI ℓ h (u 1))
          * volume (Work.BoseFixB1S.slI ℓ h (u 2)) := by
    funext u
    rw [Work.BoseFixB1S.volume_slBox, Fin.prod_univ_three]
  rw [hfun]
  have h0 : Measurable (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slI ℓ h (u 0))) :=
    (measurable_volume_slI ℓ h).comp (measurable_pi_apply (0 : Fin 3))
  have h1 : Measurable (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slI ℓ h (u 1))) :=
    (measurable_volume_slI ℓ h).comp (measurable_pi_apply (1 : Fin 3))
  have h2 : Measurable (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slI ℓ h (u 2))) :=
    (measurable_volume_slI ℓ h).comp (measurable_pi_apply (2 : Fin 3))
  exact (h0.mul h1).mul h2

/-- **The three-dimensional sliding-box mean-square bound** (the `slBox` form).  For `0 < h ≤ ℓ`
and `F : (Fin 3 → ℝ) → ℝ≥0∞` measurable, *given* the one-dimensional bound `h1d` at the same
`(ℓ,h)`:

  `∫_u ( (∫_{y ∈ slBox ℓ h u} F y) / |slBox ℓ h u| )² du  ≤  (9/h)³ ∫_{y ∈ slBig ℓ} F y² dy`.

Here `slBox ℓ h u = {y | ∀ j, y j ∈ slI ℓ h (u j)}` is the product of the one-dimensional sliding
intervals `slI ℓ h t = [max(-ℓ/2, ht-h/2), min(ℓ/2, ht+h/2)]` and `slBig ℓ = {y | ∀ j, y j ∈
[-ℓ/2,ℓ/2]}` (`Submission.Work.BoseFixB1S.MeanSq.Box3`).  This is a verbatim copy of the statement
of `Work.BoseFixB1S.meanSq3d` (`Submission/Work/BoseFixB1S/meanSq3d.lean`), with its missing input —
the 1D bound — passed as the explicit hypothesis `h1d`, so that this file is provable independently
of that skeleton.

PROOF ROUTE.  Let `N(u) := (∫_{y ∈ slBox ℓ h u}F y)/|slBox ℓ h u|` be the nested normalised
average.  Peel the `y`-integral with `Work.BoseFixB1S.lintegral_slBox` (Box3), the `u`-integral
with `Work.BoseFixB1S.lintegralPi3_peel` (`...MeanSq.Peel`) and finally the `y`-integral back with
`Work.BoseFixB1S.lintegral_slBig` (Box3); `volume_slBox` rewrites the box volume as the product of
the coordinate lengths.  Then apply `h1d` three times, outermost coordinate first, with Tonelli
swaps in between (all integrands are nonnegative, so there are no integrability side conditions):
* for fixed `(u₁,u₂)`, `N(u₀,u₁,u₂) = (1/|I(u₀)|)∫_{y₀∈I(u₀)} M(u₁,u₂,y₀)dy₀` where `M` does not
  depend on `u₀` (it is the average over `y₁,y₂`); `h1d` gives
  `∫_{u₀}N² du₀ ≤ (9/h)∫_{[-ℓ/2,ℓ/2]}M(u₁,u₂,y₀)²dy₀`;
* integrate over `u₁,u₂` (Tonelli), and for fixed `(u₂,y₀)` apply `h1d` to the function
  `y₁ ↦ K(u₂,y₀,y₁)` (the average over `y₂`): `∫_{u₁}M²du₁ ≤ (9/h)∫_{[-ℓ/2,ℓ/2]}K²dy₁`;
* again `∫_{u₂}K(u₂,y₀,y₁)²du₂ ≤ (9/h)∫_{[-ℓ/2,ℓ/2]}F![y₀,y₁,y₂]²dy₂`.
Total `(9/h)³`.  The intermediate `slS`/`slR`/`slN` (`...MeanSq.Sliced3`) may be used to organise
the nesting, but the crucial point is that each `h1d`-application needs the average's *inner*
function to be independent of the free `u`-coordinate. -/
theorem meanSq3dH {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ)
    (h1d : ∀ {F : ℝ → ℝ≥0∞}, AEMeasurable F (volume : Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2)
    {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u : Fin 3 → ℝ,
        ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
          / (volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
      ≤ ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := by
  classical
  have hofR : 0 ≤ 9 / h := by positivity
  have hCt : ENNReal.ofReal (9 / h) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the one-dimensional input, written with `avg1`
  have h1d' : ∀ {g : ℝ → ℝ≥0∞}, AEMeasurable g (volume : Measure ℝ) →
      ∫⁻ u : ℝ, (avg1 ℓ h g u) ^ 2
        ≤ ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (g x) ^ 2 :=
    fun {g} hg => h1d hg
  -- ## measurability of the box average square
  have hbAvg_meas : Measurable (fun u : Fin 3 → ℝ => (bAvg ℓ h F u) ^ 2) := by
    have h1 : Measurable (fun u : Fin 3 → ℝ => ∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y) :=
      measurable_slBox_setIntegral ℓ h hF
    have h2 : Measurable (fun u : Fin 3 → ℝ => volume (Work.BoseFixB1S.slBox ℓ h u)) :=
      measurable_volume_slBox ℓ h
    have h3 : Measurable (fun u : Fin 3 → ℝ => (∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        * (volume (Work.BoseFixB1S.slBox ℓ h u))⁻¹) := h1.mul h2.inv
    simpa only [bAvg, div_eq_mul_inv] using h3.pow_const 2
  -- ## the inner functions are a.e. measurable
  have aemeas_slM : ∀ b c : ℝ, AEMeasurable (fun y₀ : ℝ => slM ℓ h F y₀ b c)
      (volume : Measure ℝ) := by
    intro b c
    have h1 : Measurable fun y₀ : ℝ => (y₀, (b, c)) :=
      measurable_id'.prodMk ((measurable_const : Measurable fun _ : ℝ => b).prodMk
        (measurable_const : Measurable fun _ : ℝ => c))
    exact ((measurable_slM3 ℓ h hF).comp h1).aemeasurable
  have aemeas_slL : ∀ y₀ c : ℝ, AEMeasurable (fun y₁ : ℝ => slL ℓ h F y₀ y₁ c)
      (volume : Measure ℝ) := by
    intro y₀ c
    have h1 : Measurable fun y₁ : ℝ => (y₀, (y₁, c)) :=
      (measurable_const : Measurable fun _ : ℝ => y₀).prodMk
        (measurable_id'.prodMk (measurable_const : Measurable fun _ : ℝ => c))
    exact ((measurable_slL3 ℓ h hF).comp h1).aemeasurable
  have aemeas_F : ∀ y₀ y₁ : ℝ, AEMeasurable (fun y₂ : ℝ => F ![y₀, y₁, y₂])
      (volume : Measure ℝ) := by
    intro y₀ y₁
    exact (hF.comp (measurable_vec3 (measurable_const : Measurable fun _ : ℝ => y₀)
      (measurable_const : Measurable fun _ : ℝ => y₁) measurable_id')).aemeasurable
  -- ## the peeling identity, specialised
  have slN_eq_bAvg : ∀ a b c : ℝ, slN ℓ h F a b c = bAvg ℓ h F ![a, b, c] :=
    fun a b c => avg1_iter_eq ℓ h hF a b c
  -- ## Step 1: peel the `u`-integral
  have h_peel : (∫⁻ u : Fin 3 → ℝ, (bAvg ℓ h F u) ^ 2)
      = ∫⁻ a : ℝ, ∫⁻ b : ℝ, ∫⁻ c : ℝ, (slN ℓ h F a b c) ^ 2 := by
    rw [Work.BoseFixB1S.lintegralPi3_peel (fun u : Fin 3 → ℝ => (bAvg ℓ h F u) ^ 2)
      hbAvg_meas]
    refine lintegral_congr fun a => lintegral_congr fun b => lintegral_congr fun c => ?_
    rw [← slN_eq_bAvg a b c]
  -- measurability of the auxiliary parametrised functions
  have hN_a : ∀ a : ℝ, Measurable (fun w : Fin 2 → ℝ => (slN ℓ h F a (w 0) (w 1)) ^ 2) := by
    intro a
    have h1 : Measurable fun w : Fin 2 → ℝ => (a, (w 0, w 1)) :=
      (measurable_const : Measurable fun _ : Fin 2 → ℝ => a).prodMk
        ((measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2)))
    exact ((measurable_slN3 ℓ h hF).comp h1).pow_const 2
  have hN_aw : Measurable
      (fun p : ℝ × (Fin 2 → ℝ) => (slN ℓ h F p.1 (p.2 0) (p.2 1)) ^ 2) := by
    have h1 : Measurable fun p : ℝ × (Fin 2 → ℝ) => (p.1, (p.2 0, p.2 1)) :=
      (measurable_fst : Measurable fun p : ℝ × (Fin 2 → ℝ) => p.1).prodMk
        (((measurable_pi_apply (0 : Fin 2)).comp measurable_snd).prodMk
          ((measurable_pi_apply (1 : Fin 2)).comp measurable_snd))
    exact ((measurable_slN3 ℓ h hF).comp h1).pow_const 2
  have hM_w : Measurable
      (fun p : (Fin 2 → ℝ) × ℝ => (slM ℓ h F p.2 (p.1 0) (p.1 1)) ^ 2) := by
    have h1 : Measurable fun p : (Fin 2 → ℝ) × ℝ => (p.2, (p.1 0, p.1 1)) :=
      (measurable_snd : Measurable fun p : (Fin 2 → ℝ) × ℝ => p.2).prodMk
        (((measurable_pi_apply (0 : Fin 2)).comp measurable_fst).prodMk
          ((measurable_pi_apply (1 : Fin 2)).comp measurable_fst))
    exact ((measurable_slM3 ℓ h hF).comp h1).pow_const 2
  have hM_a : ∀ y₀ : ℝ, Measurable (fun w : Fin 2 → ℝ => (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) := by
    intro y₀
    have h1 : Measurable fun w : Fin 2 → ℝ => (y₀, (w 0, w 1)) :=
      (measurable_const : Measurable fun _ : Fin 2 → ℝ => y₀).prodMk
        ((measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2)))
    exact ((measurable_slM3 ℓ h hF).comp h1).pow_const 2
  have hM_bc : ∀ y₀ : ℝ, Measurable
      (Function.uncurry (fun (b c : ℝ) => (slM ℓ h F y₀ b c) ^ 2)) := by
    intro y₀
    have h1 : Measurable fun p : ℝ × ℝ => (y₀, (p.1, p.2)) :=
      (measurable_const : Measurable fun _ : ℝ × ℝ => y₀).prodMk
        ((measurable_fst : Measurable fun p : ℝ × ℝ => p.1).prodMk
          (measurable_snd : Measurable fun p : ℝ × ℝ => p.2))
    exact ((measurable_slM3 ℓ h hF).comp h1).pow_const 2
  have hL_cy : ∀ y₀ : ℝ, Measurable
      (Function.uncurry (fun (c y₁ : ℝ) => (slL ℓ h F y₀ y₁ c) ^ 2)) := by
    intro y₀
    have h1 : Measurable fun p : ℝ × ℝ => (y₀, (p.2, p.1)) :=
      (measurable_const : Measurable fun _ : ℝ × ℝ => y₀).prodMk
        ((measurable_snd : Measurable fun p : ℝ × ℝ => p.2).prodMk
          (measurable_fst : Measurable fun p : ℝ × ℝ => p.1))
    exact ((measurable_slL3 ℓ h hF).comp h1).pow_const 2
  -- ## Step 2: swap `a` with `(b,c)`
  have h_swapA : (∫⁻ a : ℝ, ∫⁻ b : ℝ, ∫⁻ c : ℝ, (slN ℓ h F a b c) ^ 2)
      = ∫⁻ w : Fin 2 → ℝ, ∫⁻ a : ℝ, (slN ℓ h F a (w 0) (w 1)) ^ 2 := by
    have hb1 : (∫⁻ a : ℝ, ∫⁻ b : ℝ, ∫⁻ c : ℝ, (slN ℓ h F a b c) ^ 2)
        = ∫⁻ a : ℝ, ∫⁻ w : Fin 2 → ℝ, (slN ℓ h F a (w 0) (w 1)) ^ 2 := by
      refine lintegral_congr fun a => ?_
      exact (Work.BoseFixB1S.lintegralPi2_peel
        (fun w : Fin 2 → ℝ => (slN ℓ h F a (w 0) (w 1)) ^ 2) (hN_a a)).symm
    have hb2 : (∫⁻ a : ℝ, ∫⁻ w : Fin 2 → ℝ, (slN ℓ h F a (w 0) (w 1)) ^ 2)
        = ∫⁻ w : Fin 2 → ℝ, ∫⁻ a : ℝ, (slN ℓ h F a (w 0) (w 1)) ^ 2 := by
      rw [lintegral_lintegral_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Fin 2 → ℝ)))
        (f := fun (a : ℝ) (w : Fin 2 → ℝ) => (slN ℓ h F a (w 0) (w 1)) ^ 2)
        hN_aw.aemeasurable]
    exact hb1.trans hb2
  -- ## Step 3: apply `h1d` in the first coordinate
  have h1a : (∫⁻ w : Fin 2 → ℝ, ∫⁻ a : ℝ, (slN ℓ h F a (w 0) (w 1)) ^ 2)
      ≤ ENNReal.ofReal (9 / h) * (∫⁻ w : Fin 2 → ℝ,
          ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2), (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (9 / h))
      (fun w : Fin 2 → ℝ =>
        ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2), (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) hCt]
    exact lintegral_mono fun w => h1d' (aemeas_slM (w 0) (w 1))
  -- ## Step 4: swap `w` with `y₀`
  have h1b : (∫⁻ w : Fin 2 → ℝ, ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
        (slM ℓ h F y₀ (w 0) (w 1)) ^ 2)
      = ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ w : Fin 2 → ℝ, (slM ℓ h F y₀ (w 0) (w 1)) ^ 2 :=
    setLintegral_lintegral_swap (α := Fin 2 → ℝ) (μ := (volume : Measure (Fin 2 → ℝ)))
      (Ψ := fun (w : Fin 2 → ℝ) (y₀ : ℝ) => (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) hM_w
      (Set.Icc (-ℓ / 2) (ℓ / 2))
  -- ## Step 5: peel `w` into `(b,c)` and swap `b`, `c`
  have h1c : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ w : Fin 2 → ℝ, (slM ℓ h F y₀ (w 0) (w 1)) ^ 2)
      = ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ c : ℝ, ∫⁻ b : ℝ, (slM ℓ h F y₀ b c) ^ 2 := by
    have hc1 : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ w : Fin 2 → ℝ, (slM ℓ h F y₀ (w 0) (w 1)) ^ 2)
        = ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ b : ℝ, ∫⁻ c : ℝ, (slM ℓ h F y₀ b c) ^ 2 := by
      refine lintegral_congr fun y₀ => ?_
      exact Work.BoseFixB1S.lintegralPi2_peel
        (fun w : Fin 2 → ℝ => (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) (hM_a y₀)
    have hc2 : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ b : ℝ, ∫⁻ c : ℝ, (slM ℓ h F y₀ b c) ^ 2)
        = ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ c : ℝ, ∫⁻ b : ℝ, (slM ℓ h F y₀ b c) ^ 2 := by
      refine lintegral_congr fun y₀ => ?_
      rw [lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (f := fun (b c : ℝ) => (slM ℓ h F y₀ b c) ^ 2) (hM_bc y₀).aemeasurable]
    exact hc1.trans hc2
  -- ## Step 6: apply `h1d` in the second coordinate
  have h2 : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ c : ℝ, ∫⁻ b : ℝ, (slM ℓ h F y₀ b c) ^ 2)
      ≤ ENNReal.ofReal (9 / h) * (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ c : ℝ, ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), (slL ℓ h F y₀ y₁ c) ^ 2) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (9 / h))
      (fun y₀ : ℝ => ∫⁻ c : ℝ,
        ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), (slL ℓ h F y₀ y₁ c) ^ 2) hCt]
    refine lintegral_mono fun y₀ => ?_
    rw [← lintegral_const_mul' (ENNReal.ofReal (9 / h))
      (fun c : ℝ => ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), (slL ℓ h F y₀ y₁ c) ^ 2) hCt]
    exact lintegral_mono fun c => h1d' (aemeas_slL y₀ c)
  -- ## Step 7: swap `c` with `y₁`
  have h2b : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ c : ℝ, ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), (slL ℓ h F y₀ y₁ c) ^ 2)
      = ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ c : ℝ, (slL ℓ h F y₀ y₁ c) ^ 2 := by
    refine lintegral_congr fun y₀ => ?_
    exact setLintegral_lintegral_swap (α := ℝ) (μ := (volume : Measure ℝ))
      (Ψ := fun (c y₁ : ℝ) => (slL ℓ h F y₀ y₁ c) ^ 2) (hL_cy y₀)
      (Set.Icc (-ℓ / 2) (ℓ / 2))
  -- ## Step 8: apply `h1d` in the third coordinate
  have h3 : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), ∫⁻ c : ℝ, (slL ℓ h F y₀ y₁ c) ^ 2)
      ≤ ENNReal.ofReal (9 / h) * (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ y₂ in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![y₀, y₁, y₂]) ^ 2) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (9 / h))
      (fun y₀ : ℝ => ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2),
        ∫⁻ y₂ in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![y₀, y₁, y₂]) ^ 2) hCt]
    refine lintegral_mono fun y₀ => ?_
    rw [← lintegral_const_mul' (ENNReal.ofReal (9 / h))
      (fun y₁ : ℝ => ∫⁻ y₂ in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![y₀, y₁, y₂]) ^ 2) hCt]
    exact lintegral_mono fun y₁ => h1d' (aemeas_F y₀ y₁)
  -- ## Step 9: fold the cube integral back
  have h4 : (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ y₂ in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![y₀, y₁, y₂]) ^ 2)
      = ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 :=
    (Work.BoseFixB1S.lintegral_slBig (ℓ := ℓ) (F := fun y => (F y) ^ 2) (hF.pow_const 2)).symm
  -- ## the final constant algebra
  have hfinal : ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) *
        (ENNReal.ofReal (9 / h) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2))
      = ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := by
    rw [ENNReal.ofReal_pow hofR 3]
    ring
  change (∫⁻ u : Fin 3 → ℝ, (bAvg ℓ h F u) ^ 2)
      ≤ ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2
  calc (∫⁻ u : Fin 3 → ℝ, (bAvg ℓ h F u) ^ 2)
      = ∫⁻ a : ℝ, ∫⁻ b : ℝ, ∫⁻ c : ℝ, (slN ℓ h F a b c) ^ 2 := h_peel
    _ = ∫⁻ w : Fin 2 → ℝ, ∫⁻ a : ℝ, (slN ℓ h F a (w 0) (w 1)) ^ 2 := h_swapA
    _ ≤ ENNReal.ofReal (9 / h) * (∫⁻ w : Fin 2 → ℝ,
          ∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2), (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) := h1a
    _ = ENNReal.ofReal (9 / h) * (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ w : Fin 2 → ℝ, (slM ℓ h F y₀ (w 0) (w 1)) ^ 2) := by rw [h1b]
    _ = ENNReal.ofReal (9 / h) * (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
          ∫⁻ c : ℝ, ∫⁻ b : ℝ, (slM ℓ h F y₀ b c) ^ 2) := by rw [h1c]
    _ ≤ ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) *
          (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ c : ℝ, ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2), (slL ℓ h F y₀ y₁ c) ^ 2)) :=
        mul_le_mul_right h2 _
    _ = ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) *
          (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2),
              ∫⁻ c : ℝ, (slL ℓ h F y₀ y₁ c) ^ 2)) := by rw [h2b]
    _ ≤ ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) *
          (∫⁻ y₀ in Set.Icc (-ℓ / 2) (ℓ / 2),
            ∫⁻ y₁ in Set.Icc (-ℓ / 2) (ℓ / 2),
              ∫⁻ y₂ in Set.Icc (-ℓ / 2) (ℓ / 2), (F ![y₀, y₁, y₂]) ^ 2))) :=
        mul_le_mul_right (mul_le_mul_right h3 _) _
    _ = ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) * (ENNReal.ofReal (9 / h) *
          (∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2))) := by rw [h4]
    _ = ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := hfinal

end

end Work.BoseFixB1.Smear
