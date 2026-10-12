import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1.Core.meanSq3d
import Submission.Work.BoseFixB1B.MeanSqPiece.meanSq1d_holds
import Submission.Work.BoseFixB1S.MeanSq.Sliced3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000

/-!
# The three-dimensional sliding-box mean-square bound (sharp constant `(9/h)³`)

For `0 < h ≤ ℓ` and a measurable `F : (Fin 3 → ℝ) → ℝ≥0∞`,

  `∫⁻ u, ((∫⁻_{y ∈ slBox ℓ h u} F y) / |slBox ℓ h u|)² ≤ (9/h)³ ∫⁻_{y ∈ slBig ℓ} (F y)²`,

where `slBox ℓ h u = ∏_j slI ℓ h (u j)` is the sliding box and `slBig ℓ` the cube of
`Submission.Work.BoseFixB1S.MeanSq.Box3`.

PROOF ROUTE.  The box mean is the threefold iterated one-dimensional window mean
(`boxMean_eq_slN`, transported from the corpus identity `Work.BoseFixB1.Core.wMean_eq_wM0`), so
`(∫_{y ∈ slBox ℓ h u} F y) / |slBox ℓ h u| = slN ℓ h F (u 0) (u 1) (u 2)`.  The `u`-integral is
peeled in the coordinates (`lintegralPi3_peel`), the one-dimensional bound
`Work.BoseFixB1B.MeanSqPiece.meanSq1d_slI` (constant `9/h`) is applied once per coordinate — each
time with the remaining variables frozen, which is where `measurable_slR_gen`/`measurable_slS_gen`
supply the `AEMeasurable` side conditions — and the two reorderings of the iterated integrals are
`lintegral_rotate3` and `lintegral_swap23`, both derived here from
`MeasureTheory.lintegral_lintegral_swap`.  The cube integral is peeled back with
`lintegral_slBig`, and `(9/h)³` is `ENNReal.ofReal ((9/h)³)` since `9/h ≥ 0`.
-/

namespace Work.BoseFixB1B.MeanSqPiece

open MeasureTheory
open scoped ENNReal
open Work.BoseFixB1S

/-! ## Measurability of a parameter-dependent sliding-window integral -/

theorem measSlIParam {X : Type*} [MeasurableSpace X] {ℓ h : ℝ} {k : X → ℝ}
    (hk : Measurable k) {V : X → ℝ≥0∞} (hV : Measurable V) {g : X → ℝ → ℝ≥0∞}
    (hg : Measurable (fun q : X × ℝ => g q.1 q.2)) :
    Measurable (fun p : X => V p * (∫⁻ y in slI ℓ h (k p), g p y)) := by
  have hset : MeasurableSet {q : X × ℝ | q.2 ∈ slI ℓ h (k q.1)} := by
    have hEq : {q : X × ℝ | q.2 ∈ slI ℓ h (k q.1)}
        = {q : X × ℝ | max (-ℓ/2) (h * k q.1 - h/2) ≤ q.2}
          ∩ {q : X × ℝ | q.2 ≤ min (ℓ/2) (h * k q.1 + h/2)} := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, slI, Set.mem_Icc]
    rw [hEq]
    exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  have hjoint : Measurable (fun q : X × ℝ =>
      {q' : X × ℝ | q'.2 ∈ slI ℓ h (k q'.1)}.indicator (fun q' => g q'.1 q'.2) q) :=
    hg.indicator hset
  have hfun : (fun p : X => ∫⁻ y in slI ℓ h (k p), g p y)
      = fun p : X => ∫⁻ y, ({q' : X × ℝ | q'.2 ∈ slI ℓ h (k q'.1)}.indicator
          (fun q' => g q'.1 q'.2) (p, y)) := by
    funext p
    rw [← indicator_mul_setLintegral (measurableSet_slI ℓ h (k p)) (g p)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ slI ℓ h (k p) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  have hInt : Measurable (fun p : X => ∫⁻ y in slI ℓ h (k p), g p y) := by
    rw [hfun]
    exact Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hjoint
  exact hV.mul hInt

/-! ## The box mean is the nested iterated window mean -/

/-- The box mean equals the nested iterated one-dimensional window mean.  This is the identity
proved in the corpus as `Work.BoseFixB1.Core.wMean_eq_wM0` in terms of the iterated means
`wM0/wM1/wM2`; here it is transported to the copy `slN/slR/slS` of those means. -/
theorem boxMean_eq_slN {ℓ h : ℝ} (u : Fin 3 → ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y in slBox ℓ h u, F y) / (volume (slBox ℓ h u)) = slN ℓ h F (u 0) (u 1) (u 2) := by
  have hcoord : u = ![u 0, u 1, u 2] := by
    funext j
    fin_cases j <;> rfl
  rw [hcoord]
  show Work.BoseFixB1.Core.wMean F ℓ h (u 0) (u 1) (u 2) = slN ℓ h F (u 0) (u 1) (u 2)
  rw [Work.BoseFixB1.Core.wMean_eq_wM0 (ℓ := ℓ) (h := h) hF (u 0) (u 1) (u 2)]
  simp only [Work.BoseFixB1.Core.wM0, Work.BoseFixB1.Core.wM1, Work.BoseFixB1.Core.wM2,
    Work.BoseFixB1.Core.wv, slN, slR, slS, ENNReal.div_eq_inv_mul]

/-! ## Fubini: permuting the three nested integrals -/

/-- Swap of the two inner iterated integrals. -/
theorem lintegral_swap23 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ξ]
    {f : α → β → γ → ℝ≥0∞} (hf : Measurable (fun p : α × (β × γ) => f p.1 p.2.1 p.2.2)) :
    (∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c ∂ξ ∂ν ∂μ) = (∫⁻ a, ∫⁻ c, ∫⁻ b, f a b c ∂ν ∂ξ ∂μ) := by
  refine lintegral_congr fun a => ?_
  have hmap : Measurable (fun p : β × γ => (a, p)) := by fun_prop
  have hsec : AEMeasurable (Function.uncurry fun b c => f a b c) (ν.prod ξ) :=
    (hf.comp hmap).aemeasurable
  exact lintegral_lintegral_swap hsec

/-- Swap of the two outer iterated integrals. -/
theorem lintegral_swap12 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ξ]
    {f : α → β → γ → ℝ≥0∞} (hf : Measurable (fun p : α × (β × γ) => f p.1 p.2.1 p.2.2)) :
    (∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c ∂ξ ∂ν ∂μ) = (∫⁻ b, ∫⁻ a, ∫⁻ c, f a b c ∂ξ ∂μ ∂ν) := by
  have hg : Measurable (fun q : (α × β) × γ => f q.1.1 q.1.2 q.2) := by
    have hmap : Measurable (fun q : (α × β) × γ => (q.1.1, (q.1.2, q.2))) := by fun_prop
    exact hf.comp hmap
  have hmeas : Measurable (fun p : α × β => ∫⁻ c, f p.1 p.2 c ∂ξ) :=
    Measurable.lintegral_prod_right (f := fun (p : α × β) (c : γ) => f p.1 p.2 c) hg
  exact lintegral_lintegral_swap hmeas.aemeasurable

/-- Cyclic rotation of the three nested integrals. -/
theorem lintegral_rotate3 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ξ]
    {f : α → β → γ → ℝ≥0∞} (hf : Measurable (fun p : α × (β × γ) => f p.1 p.2.1 p.2.2)) :
    (∫⁻ a, ∫⁻ b, ∫⁻ c, f a b c ∂ξ ∂ν ∂μ) = (∫⁻ b, ∫⁻ c, ∫⁻ a, f a b c ∂μ ∂ξ ∂ν) := by
  have hmap : Measurable (fun p : β × (α × γ) => (p.2.1, (p.1, p.2.2))) := by fun_prop
  have hf' : Measurable (fun p : β × (α × γ) => f p.2.1 p.1 p.2.2) := hf.comp hmap
  rw [lintegral_swap12 μ ν ξ hf]
  exact lintegral_swap23 ν μ ξ hf'

/-! ## Measurability of the sliced averages -/

/-- The window volume is measurable as a function of the centre. -/
lemma measurable_slI_volume (ℓ h : ℝ) : Measurable (fun t : ℝ => volume (slI ℓ h t)) := by
  have hEq : (fun t : ℝ => volume (slI ℓ h t))
      = fun t : ℝ => ENNReal.ofReal (min (ℓ / 2) (h * t + h / 2)
          - max (-ℓ / 2) (h * t - h / 2)) := by
    funext t
    simp only [slI, Real.volume_Icc]
  rw [hEq]
  fun_prop

/-- The coordinate tuple map `a ↦ ![f a, g a, k a]` is measurable. -/
lemma measurable_tuple3 {α : Type*} [MeasurableSpace α] {f g k : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    Measurable (fun a : α => (![f a, g a, k a] : Fin 3 → ℝ)) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · simpa using hf
  · simpa using hg
  · simpa using hk

/-- `slS` is measurable for arbitrary measurable argument maps. -/
lemma measurable_slS_gen {X : Type*} [MeasurableSpace X] (ℓ h : ℝ)
    {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) {a b c : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun p : X => slS ℓ h F (a p) (b p) (c p)) := by
  have hg : Measurable (fun q : X × ℝ => F ![b q.1, c q.1, q.2]) :=
    hF.comp (measurable_tuple3 (hb.comp measurable_fst) (hc.comp measurable_fst)
      measurable_snd)
  have hvol : Measurable (fun p : X => volume (slI ℓ h (a p))) :=
    (measurable_slI_volume ℓ h).comp ha
  have hmain := measSlIParam (ℓ := ℓ) (h := h) (X := X) (k := a) ha
    (V := fun p : X => (volume (slI ℓ h (a p)))⁻¹) hvol.inv
    (g := fun (p : X) (y : ℝ) => F ![b p, c p, y]) hg
  simpa only [slS] using hmain

/-- `slR` is measurable for arbitrary measurable argument maps. -/
lemma measurable_slR_gen {X : Type*} [MeasurableSpace X] (ℓ h : ℝ)
    {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) {a b c : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun p : X => slR ℓ h F (a p) (b p) (c p)) := by
  have hg : Measurable (fun q : X × ℝ => slS ℓ h F (b q.1) (c q.1) q.2) :=
    measurable_slS_gen ℓ h hF (hb.comp measurable_fst) (hc.comp measurable_fst)
      measurable_snd
  have hvol : Measurable (fun p : X => volume (slI ℓ h (a p))) :=
    (measurable_slI_volume ℓ h).comp ha
  have hmain := measSlIParam (ℓ := ℓ) (h := h) (X := X) (k := a) ha
    (V := fun p : X => (volume (slI ℓ h (a p)))⁻¹) hvol.inv
    (g := fun (p : X) (y : ℝ) => slS ℓ h F (b p) (c p) y) hg
  simpa only [slR] using hmain

/-- `slN` is measurable for arbitrary measurable argument maps. -/
lemma measurable_slN_gen {X : Type*} [MeasurableSpace X] (ℓ h : ℝ)
    {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) {a b c : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun p : X => slN ℓ h F (a p) (b p) (c p)) := by
  have hg : Measurable (fun q : X × ℝ => slR ℓ h F (b q.1) (c q.1) q.2) :=
    measurable_slR_gen ℓ h hF (hb.comp measurable_fst) (hc.comp measurable_fst)
      measurable_snd
  have hvol : Measurable (fun p : X => volume (slI ℓ h (a p))) :=
    (measurable_slI_volume ℓ h).comp ha
  have hmain := measSlIParam (ℓ := ℓ) (h := h) (X := X) (k := a) ha
    (V := fun p : X => (volume (slI ℓ h (a p)))⁻¹) hvol.inv
    (g := fun (p : X) (y : ℝ) => slR ℓ h F (b p) (c p) y) hg
  simpa only [slN] using hmain

/-- Section measurability of `slR` in its own (last) argument. -/
lemma aemeasurable_slR_last (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (b c : ℝ) : AEMeasurable (fun y₀ : ℝ => slR ℓ h F b c y₀) volume :=
  (measurable_slR_gen ℓ h hF (a := fun _ : ℝ => b) (b := fun _ : ℝ => c)
    (c := fun y : ℝ => y) measurable_const measurable_const measurable_id).aemeasurable

/-- Section measurability of `slS` in the `c`-coordinate. -/
lemma aemeasurable_slS_section (ℓ h : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (c y₀ : ℝ) : AEMeasurable (fun y₁ : ℝ => slS ℓ h F c y₀ y₁) volume :=
  (measurable_slS_gen ℓ h hF (a := fun _ : ℝ => c) (b := fun _ : ℝ => y₀)
    (c := fun y : ℝ => y) measurable_const measurable_const measurable_id).aemeasurable

/-- Section measurability of the frozen slice `y ↦ F ![y₀,y₁,y]`. -/
lemma aemeasurable_slice3 {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) (y₀ y₁ : ℝ) :
    AEMeasurable (fun y₂ : ℝ => F ![y₀, y₁, y₂]) volume :=
  (hF.comp (measurable_tuple3 (f := fun _ : ℝ => y₀) (g := fun _ => y₁)
    (k := fun y : ℝ => y) measurable_const measurable_const measurable_id)).aemeasurable

/-! ## The main theorem -/

theorem meanSq3d_holds {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ)
    {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y) / (volume (Work.BoseFixB1S.slBox ℓ h u)))^2
      ≤ ENNReal.ofReal ((9/h)^3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y)^2 := by
  classical
  have hccne : ENNReal.ofReal (9/h) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- ## Step 1: peel the `u`-integral and rewrite the integrand as the nested average
  have hmeasN : Measurable (fun u : Fin 3 → ℝ => (slN ℓ h F (u 0) (u 1) (u 2))^2) :=
    (measurable_slN_gen ℓ h hF (a := fun u : Fin 3 → ℝ => u 0) (b := fun u => u 1)
      (c := fun u => u 2) (by fun_prop) (by fun_prop) (by fun_prop)).pow_const 2
  have hpeel : (∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in slBox ℓ h u, F y) / (volume (slBox ℓ h u)))^2)
      = (∫⁻ a, ∫⁻ b, ∫⁻ c, (slN ℓ h F a b c)^2) := by
    rw [show (∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in slBox ℓ h u, F y) / (volume (slBox ℓ h u)))^2)
        = ∫⁻ u : Fin 3 → ℝ, (slN ℓ h F (u 0) (u 1) (u 2))^2 from
      lintegral_congr fun u => by rw [boxMean_eq_slN u hF]]
    have hpeel' := lintegralPi3_peel
      (fun u : Fin 3 → ℝ => (slN ℓ h F (u 0) (u 1) (u 2))^2) hmeasN
    have e0 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 0 = a := fun a b c => by simp
    have e1 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 1 = b := fun a b c => by simp
    have e2 : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 2 = c := fun a b c => by simp
    simpa only [e0, e1, e2] using hpeel'
  -- ## Step 2: the outer application of the one-dimensional bound
  have hstep1 : ∀ b c : ℝ, (∫⁻ a : ℝ, (slN ℓ h F a b c)^2)
      ≤ ENNReal.ofReal (9/h) * ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2 := by
    intro b c
    have h1d := meanSq1d_slI (ℓ := ℓ) (h := h) hh hhℓ
      (F := fun y₀ : ℝ => slR ℓ h F b c y₀) (aemeasurable_slR_last ℓ h hF b c)
    simpa only [slN, slI, ENNReal.div_eq_inv_mul] using h1d
  have hmono1 : (∫⁻ b, ∫⁻ c, ∫⁻ a, (slN ℓ h F a b c)^2)
      ≤ (∫⁻ b, ∫⁻ c, ENNReal.ofReal (9/h)
          * ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2) :=
    lintegral_mono fun b => lintegral_mono fun c => hstep1 b c
  have hpull1 : (∫⁻ b, ∫⁻ c, ENNReal.ofReal (9/h)
        * ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2)
      = ENNReal.ofReal (9/h)
        * (∫⁻ b, ∫⁻ c, ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2) := by
    rw [show (∫⁻ b, ∫⁻ c, ENNReal.ofReal (9/h)
          * ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2)
        = ∫⁻ b, ENNReal.ofReal (9/h)
          * (∫⁻ c, ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2) from
      lintegral_congr fun b => lintegral_const_mul' _ _ hccne]
    rw [lintegral_const_mul' _ _ hccne]
  -- ## Step 3: bring the `y₀`-integral outside and swap the inner two
  have hrot2 : (∫⁻ b, ∫⁻ c, ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2)
      = (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ b, ∫⁻ c, (slR ℓ h F b c y₀)^2) := by
    have hcomp : Measurable (fun p : ℝ × (ℝ × ℝ) => (slR ℓ h F p.2.1 p.2.2 p.1)^2) :=
      (measurable_slR_gen ℓ h hF (a := fun p : ℝ × (ℝ × ℝ) => p.2.1)
        (b := fun p => p.2.2) (c := fun p => p.1)
        (by fun_prop) (by fun_prop) (by fun_prop)).pow_const 2
    exact (lintegral_rotate3 (volume.restrict (Set.Icc (-ℓ/2) (ℓ/2))) volume volume
      (f := fun y₀ b c => (slR ℓ h F b c y₀)^2) hcomp).symm
  have hswap1 : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ b, ∫⁻ c, (slR ℓ h F b c y₀)^2)
      = (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ∫⁻ b, (slR ℓ h F b c y₀)^2) := by
    have hcomp : Measurable (fun p : ℝ × (ℝ × ℝ) => (slR ℓ h F p.2.1 p.2.2 p.1)^2) :=
      (measurable_slR_gen ℓ h hF (a := fun p : ℝ × (ℝ × ℝ) => p.2.1)
        (b := fun p => p.2.2) (c := fun p => p.1)
        (by fun_prop) (by fun_prop) (by fun_prop)).pow_const 2
    exact lintegral_swap23 (volume.restrict (Set.Icc (-ℓ/2) (ℓ/2))) volume volume
      (f := fun y₀ b c => (slR ℓ h F b c y₀)^2) hcomp
  -- ## Step 4: the middle application of the one-dimensional bound
  have hstep2 : ∀ y₀ c : ℝ, (∫⁻ b : ℝ, (slR ℓ h F b c y₀)^2)
      ≤ ENNReal.ofReal (9/h) * ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), (slS ℓ h F c y₀ y₁)^2 := by
    intro y₀ c
    have h1d := meanSq1d_slI (ℓ := ℓ) (h := h) hh hhℓ
      (F := fun y₁ : ℝ => slS ℓ h F c y₀ y₁) (aemeasurable_slS_section ℓ h hF c y₀)
    simpa only [slR, slI, ENNReal.div_eq_inv_mul] using h1d
  have hmono2 : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ∫⁻ b, (slR ℓ h F b c y₀)^2)
      ≤ (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ENNReal.ofReal (9/h)
          * ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), (slS ℓ h F c y₀ y₁)^2) :=
    lintegral_mono fun y₀ => lintegral_mono fun c => hstep2 y₀ c
  have hpull2 : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ENNReal.ofReal (9/h)
        * ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), (slS ℓ h F c y₀ y₁)^2)
      = ENNReal.ofReal (9/h)
        * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
            (slS ℓ h F c y₀ y₁)^2) := by
    rw [show (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ENNReal.ofReal (9/h)
          * ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), (slS ℓ h F c y₀ y₁)^2)
        = ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ENNReal.ofReal (9/h)
          * (∫⁻ c, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), (slS ℓ h F c y₀ y₁)^2) from
      lintegral_congr fun y₀ => lintegral_const_mul' _ _ hccne]
    rw [lintegral_const_mul' _ _ hccne]
  -- ## Step 5: swap `c` and `y₁`
  have hswap2 : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
        (slS ℓ h F c y₀ y₁)^2)
      = (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c,
          (slS ℓ h F c y₀ y₁)^2) := by
    have hcomp : Measurable (fun p : ℝ × (ℝ × ℝ) => (slS ℓ h F p.2.1 p.1 p.2.2)^2) :=
      (measurable_slS_gen ℓ h hF (a := fun p : ℝ × (ℝ × ℝ) => p.2.1)
        (b := fun p => p.1) (c := fun p => p.2.2)
        (by fun_prop) (by fun_prop) (by fun_prop)).pow_const 2
    exact lintegral_swap23 (volume.restrict (Set.Icc (-ℓ/2) (ℓ/2))) volume
      (volume.restrict (Set.Icc (-ℓ/2) (ℓ/2)))
      (f := fun y₀ c y₁ => (slS ℓ h F c y₀ y₁)^2) hcomp
  -- ## Step 6: the inner application of the one-dimensional bound
  have hstep3 : ∀ y₀ y₁ : ℝ, (∫⁻ c : ℝ, (slS ℓ h F c y₀ y₁)^2)
      ≤ ENNReal.ofReal (9/h) * ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2 := by
    intro y₀ y₁
    have h1d := meanSq1d_slI (ℓ := ℓ) (h := h) hh hhℓ
      (F := fun y₂ : ℝ => F ![y₀, y₁, y₂]) (aemeasurable_slice3 hF y₀ y₁)
    simpa only [slS, slI, ENNReal.div_eq_inv_mul] using h1d
  have hmono3 : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c,
        (slS ℓ h F c y₀ y₁)^2)
      ≤ (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
          ENNReal.ofReal (9/h) * ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2) :=
    lintegral_mono fun y₀ => lintegral_mono fun y₁ => hstep3 y₀ y₁
  have hpull3 : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
        ENNReal.ofReal (9/h) * ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2)
      = ENNReal.ofReal (9/h)
        * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂
            in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2) := by
    rw [show (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
          ENNReal.ofReal (9/h) * ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2)
        = ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ENNReal.ofReal (9/h)
          * (∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2),
              (F ![y₀, y₁, y₂])^2) from
      lintegral_congr fun y₀ => lintegral_const_mul' _ _ hccne]
    rw [lintegral_const_mul' _ _ hccne]
  -- ## Step 7: peel the cube integral back
  have hbig : (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂
        in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2)
      = ∫⁻ y in slBig ℓ, (F y)^2 :=
    (lintegral_slBig (ℓ := ℓ) (F := fun y : Fin 3 → ℝ => (F y)^2) (hF.pow_const 2)).symm
  -- ## Assembly
  have hchain : (∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in slBox ℓ h u, F y) / (volume (slBox ℓ h u)))^2)
      ≤ ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
          * (∫⁻ y in slBig ℓ, (F y)^2))) := by
    rw [hpeel]
    calc (∫⁻ a, ∫⁻ b, ∫⁻ c, (slN ℓ h F a b c)^2)
        = (∫⁻ b, ∫⁻ c, ∫⁻ a, (slN ℓ h F a b c)^2) :=
          lintegral_rotate3 volume volume volume
            ((measurable_slN_gen ℓ h hF (a := fun p : ℝ × (ℝ × ℝ) => p.1)
              (b := fun p => p.2.1) (c := fun p => p.2.2)
              (by fun_prop) (by fun_prop) (by fun_prop)).pow_const 2)
      _ ≤ (∫⁻ b, ∫⁻ c, ENNReal.ofReal (9/h)
            * ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2) := hmono1
      _ = ENNReal.ofReal (9/h)
            * (∫⁻ b, ∫⁻ c, ∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), (slR ℓ h F b c y₀)^2) := hpull1
      _ = ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ b, ∫⁻ c, (slR ℓ h F b c y₀)^2) := by
          rw [hrot2]
      _ = ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ∫⁻ b, (slR ℓ h F b c y₀)^2) := by
          rw [hswap1]
      _ ≤ ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ENNReal.ofReal (9/h)
                * ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), (slS ℓ h F c y₀ y₁)^2) :=
          mul_le_mul_right hmono2 _
      _ = ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c, ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
                (slS ℓ h F c y₀ y₁)^2)) := by
          rw [hpull2]
      _ = ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ c,
                (slS ℓ h F c y₀ y₁)^2)) := by
          rw [hswap2]
      _ ≤ ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2),
                ENNReal.ofReal (9/h)
                  * ∫⁻ y₂ in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2)) :=
          mul_le_mul_right (mul_le_mul_right hmono3 _) _
      _ = ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
            * (∫⁻ y₀ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₁ in Set.Icc (-ℓ/2) (ℓ/2), ∫⁻ y₂
                in Set.Icc (-ℓ/2) (ℓ/2), (F ![y₀, y₁, y₂])^2))) := by
          rw [hpull3]
      _ = ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
            * (∫⁻ y in slBig ℓ, (F y)^2))) := by
          rw [hbig]
  refine le_trans hchain ?_
  have h9 : (0 : ℝ) ≤ 9/h := by positivity
  rw [show ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h) * (ENNReal.ofReal (9/h)
        * (∫⁻ y in slBig ℓ, (F y)^2)))
      = ENNReal.ofReal (9/h)^3 * (∫⁻ y in slBig ℓ, (F y)^2) from by ring,
    ← ENNReal.ofReal_pow h9 3]

end Work.BoseFixB1B.MeanSqPiece
