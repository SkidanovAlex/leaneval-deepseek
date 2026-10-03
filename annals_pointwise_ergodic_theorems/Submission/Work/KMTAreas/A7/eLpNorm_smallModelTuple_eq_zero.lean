import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.LargeInterface

/-!
# The §7 model tuple vanishes for a vanishing input

`Work.KMTAreas.A7.smallModelTuple` is *bilinear* in the two functions `f, g`: `smallBtwist` is
linear in each of its two arguments and the IW multipliers `Tm` are linear as well.  Hence the
`V^r`-tuple of the small-scale model vanishes identically (in `x`) as soon as one of the two inputs
vanishes pointwise.

On `ℤ` with counting measure, `eLpNorm u p Measure.count = 0` with `p ≠ 0` already forces
`u = 0` pointwise: the measure has no non-empty null sets (`Measure.count_ne_zero_iff`), and every
function is a.e. strongly measurable because the measurable space of `ℤ` is discrete.  Combining
the two, the `ℒ^{(p₁⁻¹+p₂⁻¹)⁻¹}` norm of the variational norm of the small-scale model tuple is `0`
whenever one of the two input `ℒ^{pᵢ}` norms vanishes -- the degenerate cases `SmallModelVar`
needs to dispose of functions of vanishing norm.
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- On `ℤ` with counting measure a function of vanishing `ℒ^p` seminorm (`p ≠ 0`) is identically
zero: every set is measurable (the measurable space of `ℤ` is discrete) and the counting measure
has no non-empty null sets. -/
private lemma eq_zero_of_eLpNorm_count_eq_zero {p : ENNReal} (hp : p ≠ 0) {u : ℤ → ℂ}
    (h : eLpNorm u p (Measure.count : Measure ℤ) = 0) : u = 0 := by
  have hsm : AEStronglyMeasurable u (Measure.count : Measure ℤ) :=
    AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp h
  have hnull : Measure.count {m : ℤ | u m ≠ 0} = 0 := ae_iff.mp h0
  funext n
  by_contra hn
  have hne : Measure.count {m : ℤ | u m ≠ 0} ≠ 0 := by
    rw [Measure.count_ne_zero_iff]
    exact ⟨n, hn⟩
  exact hne hnull

/-- The `WithLp`-norm of the zero element is zero for *every* exponent (the norm structure
`PiLp.instNorm` on `WithLp p (ι → ℂ)` is defined for all `p`, not only for `p ≥ 1`). -/
private lemma norm_zero_withLp (r : ℝ≥0) (J : ℕ) :
    ‖(0 : WithLp (r : ENNReal) (Fin J → ℂ))‖ = 0 := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rw [PiLp.norm_eq_card]
    simp
  · have h0r : (r : ENNReal) ≠ 0 := by simpa [ENNReal.coe_eq_zero] using hr
    have htr : (r : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
    have ht : 0 < ((r : ENNReal)).toReal := ENNReal.toReal_pos h0r htr
    rw [PiLp.norm_eq_sum ht]
    have hz : ∀ i : Fin J, ‖(0 : ℂ)‖ ^ ((r : ENNReal)).toReal = 0 := by
      intro i
      rw [norm_zero, Real.zero_rpow (ne_of_gt ht)]
    rw [Finset.sum_eq_zero (fun i _ => by
      simpa [WithLp.ofLp_zero] using hz i)]
    exact Real.zero_rpow (by positivity)

/-- The variational norm of the zero sequence vanishes (for every `r`, including `r = 0`). -/
private lemma variationalNorm_zero (r : ℝ≥0) :
    PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
  refine le_antisymm ?_ bot_le
  rw [PointwiseErgodicTheorems.variationalNorm]
  refine le_trans (add_le_add ?_ ?_) (le_of_eq (zero_add (0 : ENNReal)))
  · refine iSup_le fun n => by simp
  · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    have h0 : (fun i : Fin J => (0 : ℕ → ℂ) (N (i + 1)) - (0 : ℕ → ℂ) (N i))
        = (0 : Fin J → ℂ) := by
      funext i
      simp
    rw [h0, WithLp.toLp_zero, norm_zero_withLp r J, ENNReal.ofReal_zero]

/-- The convolution with a vanishing function vanishes. -/
private lemma iwConv_zero_right (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IWMultiplier.iwConv A Φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [Work.Analysis.IWMultiplier.iwConv]

/-- The small-scale model tuple vanishes when its first argument does. -/
private lemma smallModelTuple_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallModelTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  simp only [smallModelTuple]
  split_ifs with h
  · simp only [smallModelOp, smallBtwist, Tm]
    simp [iwConv_zero_right]
  · rfl

/-- The small-scale model tuple vanishes when its second argument does. -/
private lemma smallModelTuple_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallModelTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  simp only [smallModelTuple]
  split_ifs with h
  · simp only [smallModelOp, smallBtwist, Tm]
    simp [iwConv_zero_right]
  · rfl

/-- The vanishing of the `V^r`-tuple of the small-scale model when one input vanishes
pointwise. -/
private lemma eLpNorm_smallModelTuple_eq_zero_of_eq_zero (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (q : ENNReal) {f g : ℤ → ℂ}
    (hf : f = 0) :
    eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      q Measure.count = 0 := by
  subst hf
  have hseq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => smallModelTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x)) = fun _ : ℤ => 0 := by
    funext x
    have hzero : (fun n : ℕ => smallModelTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n
      exact congrFun (congrFun (smallModelTuple_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂) n) x
    rw [hzero, variationalNorm_zero]
  rw [hseq]
  simp

/-- The same, for a vanishing second input. -/
private lemma eLpNorm_smallModelTuple_eq_zero_of_eq_zero_right (ρ : ℝ) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (q : ENNReal) {f g : ℤ → ℂ}
    (hg : g = 0) :
    eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      q Measure.count = 0 := by
  subst hg
  have hseq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => smallModelTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x)) = fun _ : ℤ => 0 := by
    funext x
    have hzero : (fun n : ℕ => smallModelTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n
      exact congrFun (congrFun (smallModelTuple_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂) n) x
    rw [hzero, variationalNorm_zero]
  rw [hseq]
  simp

theorem eLpNorm_smallModelTuple_eq_zero (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (p₁ p₂ : ENNReal) (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (f g : ℤ → ℂ)
    (h : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0 ∨
         MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count = 0 := by
  rcases h with hf | hg
  · exact eLpNorm_smallModelTuple_eq_zero_of_eq_zero ρ P C₀ a l₁ l₂ k₁ k₂ r _
      (eq_zero_of_eLpNorm_count_eq_zero hp₁ hf)
  · exact eLpNorm_smallModelTuple_eq_zero_of_eq_zero_right ρ P C₀ a l₁ l₂ k₁ k₂ r _
      (eq_zero_of_eLpNorm_count_eq_zero hp₂ hg)

end

end Work.KMTAreas.A7
