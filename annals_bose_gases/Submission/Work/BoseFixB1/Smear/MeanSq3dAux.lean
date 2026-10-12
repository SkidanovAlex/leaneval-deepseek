import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary definitions for the three-dimensional sliding-box mean-square bound

This file holds the small vocabulary used by `Work.BoseFixB1.Smear.meanSq3dH`, namely the
normalised sliding-window average `avg1` and the elementary `ℝ≥0∞` lemmas about set integrals
needed to peel the nested averages apart and to run Tonelli in the coordinates.
-/

namespace Work.BoseFixB1.Smear

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The normalised sliding-window average of `f` against the sliding interval `slI ℓ h u`:

  `avg1 ℓ h f u = (∫_{x ∈ slI ℓ h u} f x) / |slI ℓ h u|`. -/
def avg1 (ℓ h : ℝ) (f : ℝ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  (∫⁻ x in Work.BoseFixB1S.slI ℓ h u, f x) / (volume (Work.BoseFixB1S.slI ℓ h u))

lemma avg1_def (ℓ h : ℝ) (f : ℝ → ℝ≥0∞) (u : ℝ) :
    avg1 ℓ h f u
      = (∫⁻ x in Work.BoseFixB1S.slI ℓ h u, f x)
          / (volume (Work.BoseFixB1S.slI ℓ h u)) := rfl

/-- Pull a constant out of a set integral, `ℝ≥0∞`-valued version (no finiteness condition). -/
lemma setLintegral_mul_const {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (c : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in s, f x * c ∂μ = (∫⁻ x in s, f x ∂μ) * c := by
  have h1 : ∫⁻ x, s.indicator (fun x => f x * c) x ∂μ = ∫⁻ x, s.indicator f x * c ∂μ := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [show ∫⁻ x in s, f x * c ∂μ = ∫⁻ x, s.indicator (fun x => f x * c) x ∂μ from
        (lintegral_indicator hs _).symm,
      show ∫⁻ x in s, f x ∂μ = ∫⁻ x, s.indicator f x ∂μ from (lintegral_indicator hs f).symm,
      h1, lintegral_mul_const c (hf.indicator hs)]

/-- The volume of the sliding box is finite. -/
lemma volume_slBox_ne_top (ℓ h : ℝ) (u : Fin 3 → ℝ) :
    volume (Work.BoseFixB1S.slBox ℓ h u) ≠ ⊤ := by
  rw [Work.BoseFixB1S.volume_slBox]
  rw [Fin.prod_univ_three]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_
  · exact Work.BoseFixB1S.volume_slI_ne_top ℓ h (u 0)
  · exact Work.BoseFixB1S.volume_slI_ne_top ℓ h (u 1)
  · exact Work.BoseFixB1S.volume_slI_ne_top ℓ h (u 2)

/-- The set `{p : ℝ × ℝ | p.2 ∈ slI ℓ h p.1}` is measurable. -/
lemma measurableSet_slI_pair (ℓ h : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.2 ∈ Work.BoseFixB1S.slI ℓ h p.1} := by
  have hca : Continuous fun p : ℝ × ℝ => max (-ℓ/2) (h * p.1 - h/2) :=
    continuous_const.max ((continuous_const.mul continuous_fst).sub continuous_const)
  have hcb : Continuous fun p : ℝ × ℝ => min (ℓ/2) (h * p.1 + h/2) :=
    continuous_const.min ((continuous_const.mul continuous_fst).add continuous_const)
  have hh : {p : ℝ × ℝ | p.2 ∈ Work.BoseFixB1S.slI ℓ h p.1}
      = {p : ℝ × ℝ | max (-ℓ/2) (h * p.1 - h/2) ≤ p.2}
        ∩ {p : ℝ × ℝ | p.2 ≤ min (ℓ/2) (h * p.1 + h/2)} := by
    ext p
    simp only [Work.BoseFixB1S.slI, Set.mem_Icc, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hh]
  exact ((isClosed_le hca continuous_snd).inter (isClosed_le continuous_snd hcb)).measurableSet

/-- Slicing a set integral over a *fixed* measurable set keeps joint measurability. -/
lemma measurable_setIntegral_fixed {β : Type*} [MeasurableSpace β] {s : Set ℝ}
    (hs : MeasurableSet s) {f : β → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun p : β => ∫⁻ y in s, f p y) := by
  let G : β → ℝ → ℝ≥0∞ := fun p x => s.indicator (fun z => f p z) x
  have h1 : Measurable fun q : β × ℝ => f q.1 q.2 := hf
  have hg : Measurable (Function.uncurry G) := by
    show Measurable fun q : β × ℝ => s.indicator (fun z => f q.1 z) q.2
    exact h1.indicator (hs.preimage measurable_snd)
  have h2 := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hg
  have h3 : (fun p : β => ∫⁻ y, G p y ∂(volume : Measure ℝ)) = fun p : β => ∫⁻ y in s, f p y := by
    funext p
    exact lintegral_indicator hs (f p)
  rw [h3] at h2
  exact h2

/-- Joint measurability of the sliding-interval integral in both the parameter and the centre:
for `f` jointly measurable, `(p, u) ↦ ∫_{x ∈ slI ℓ h u} f x p` is measurable. -/
lemma measurable_slI_setIntegral {β : Type*} [MeasurableSpace β]
    {f : ℝ → β → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) (ℓ h : ℝ) :
    Measurable (fun p : β × ℝ => ∫⁻ x in Work.BoseFixB1S.slI ℓ h p.2, f x p.1) := by
  let G : (β × ℝ) → ℝ → ℝ≥0∞ :=
    fun p x => (Work.BoseFixB1S.slI ℓ h p.2).indicator (fun z => f z p.1) x
  have hpair : Measurable fun q : (β × ℝ) × ℝ => (q.2, q.1.1) :=
    measurable_snd.prodMk (measurable_fst.comp measurable_fst)
  have h1 : Measurable fun q : (β × ℝ) × ℝ => f q.2 q.1.1 := hf.comp hpair
  have hset : MeasurableSet {q : (β × ℝ) × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1.2} :=
    (measurableSet_slI_pair ℓ h).preimage
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable (Function.uncurry G) := by
    show Measurable fun q : (β × ℝ) × ℝ =>
      (Work.BoseFixB1S.slI ℓ h q.1.2).indicator (fun z => f z q.1.1) q.2
    exact h1.indicator hset
  have h2 := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) hg
  have h3 : (fun p : β × ℝ => ∫⁻ x, G p x ∂(volume : Measure ℝ))
      = fun p : β × ℝ => ∫⁻ x in Work.BoseFixB1S.slI ℓ h p.2, f x p.1 := by
    funext p
    exact lintegral_indicator (Work.BoseFixB1S.measurableSet_slI ℓ h p.2) (fun x => f x p.1)
  rw [h3] at h2
  exact h2

/-- Tonelli/Fubini for a set integral: the integral over `K` can be swapped with an integral over
any s-finite measure space. -/
lemma setLintegral_lintegral_swap {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {Ψ : α → ℝ → ℝ≥0∞} (hΨ : Measurable (Function.uncurry Ψ)) (K : Set ℝ) :
    ∫⁻ x : α, (∫⁻ y in K, Ψ x y) ∂μ = ∫⁻ y in K, (∫⁻ x : α, Ψ x y ∂μ) := by
  have h : AEMeasurable (Function.uncurry Ψ) (μ.prod (volume.restrict K)) := hΨ.aemeasurable
  simpa using lintegral_lintegral_swap (μ := μ) (ν := volume.restrict K) h

end

end Work.BoseFixB1.Smear
