import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# Monotonicity of the conditional entropy `Hcond` in the conditioning σ-algebra

`Hcond μ P m = ∫ ∑ᵢ -𝔼[1_{Pᵢ}|m] log 𝔼[1_{Pᵢ}|m] dμ` is the conditional entropy of the finite
partition `P` given the σ-algebra `m`.  Conditioning on more information cannot increase it: for
`m₁ ≤ m₂` we have `Hcond μ P m₂ ≤ Hcond μ P m₁`.

The proof is the conditional Jensen inequality for the concave function `Real.negMulLog` on
`[0,∞)`, applied to `g = 𝔼[f|m₂]` with the tower property `𝔼[g|m₁] = 𝔼[f|m₁]`.

**Formalisation note.**  Lean's typeclass search treats a *local hypothesis* of class type
(`m : MeasurableSpace X`) as an instance candidate; a sub-σ-algebra variable `m` therefore
silently captures the ambient instance of `Measure X`, `condExp`, `Hcond`, ….  The lemmas below
are stated with the ambient instance introduced *after* all the other `MeasurableSpace` variables,
which makes the ambient the preferred candidate and keeps every elaboration below honest.
-/

namespace Work.EKLC6Core

open MeasureTheory Filter

/-- Conditional expectation of a `[0,1]`-valued function stays in `[0,1]` almost everywhere. -/
lemma condExp_mem_Icc {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (hm : m ≤ mX) {f : X → ℝ}
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hfi : Integrable f μ) : ∀ᵐ x ∂μ, condExp m μ f x ∈ Set.Icc 0 1 := by
  have hle : f ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hf1] with x hx
    simpa using hx
  have h2 : ∀ᵐ x ∂μ, condExp m μ f x ≤ 1 := by
    have hmono := condExp_mono (m := m) (μ := μ) hfi (integrable_const (1 : ℝ)) hle
    filter_upwards [hmono] with x hx
    simpa [condExp_const hm (1 : ℝ)] using hx
  filter_upwards [condExp_nonneg (m := m) (μ := μ) hf0, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/-- `condExp m μ f` is a.e. strongly measurable for the ambient instance. -/
lemma aestronglyMeasurable_condExp {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} : AEStronglyMeasurable (condExp m μ f) μ := by
  have h : Integrable (condExp m μ f) μ := integrable_condExp (μ := μ) (m := m) (f := f)
  exact h.aestronglyMeasurable

/-- `Real.negMulLog ∘ g` is integrable as soon as `g` is a.e. strongly measurable and a.e. in
`[0,1]` (on which `Real.negMulLog` is nonnegative and bounded by `1`). -/
lemma integrable_negMulLog_of_bdd {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {g : X → ℝ} (hg_meas : AEStronglyMeasurable g μ)
    (hg : ∀ᵐ x ∂μ, g x ∈ Set.Icc 0 1) :
    Integrable (fun x => Real.negMulLog (g x)) μ := by
  refine Integrable.of_bound (Real.continuous_negMulLog.comp_aestronglyMeasurable hg_meas) 1 ?_
  filter_upwards [hg] with x hx
  have h1 : 0 ≤ Real.negMulLog (g x) := Real.negMulLog_nonneg hx.1 hx.2
  have h2 : Real.negMulLog (g x) ≤ 1 :=
    le_trans (Real.negMulLog_le_one_sub_self hx.1) (by linarith [hx.1])
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

/-- `Real.negMulLog ∘ 𝔼[f|m]` is integrable when `f` takes values in `[0,1]` a.e. -/
lemma integrable_negMulLog_condExp {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1) (hfi : Integrable f μ) :
    Integrable (fun x => Real.negMulLog (condExp m μ f x)) μ := by
  by_cases hm : m ≤ mX
  · exact integrable_negMulLog_of_bdd (μ := μ) (g := condExp m μ f)
      (aestronglyMeasurable_condExp (μ := μ) (m := m) (f := f))
      (condExp_mem_Icc (μ := μ) (m := m) hm hf0 hf1 hfi)
  · have h0 : condExp m μ f = 0 := condExp_of_not_le hm
    rw [h0]
    simpa using (integrable_zero X ℝ μ)

/-- **Conditional Jensen for the entropy integrand.** For `m₁ ≤ m₂` and `f` a.e. in `[0,1]`,
`∫ -𝔼[f|m₂] log 𝔼[f|m₂] ≤ ∫ -𝔼[f|m₁] log 𝔼[f|m₁]`: conditioning on more information lowers the
entropy. -/
lemma integral_negMulLog_condExp_le {X : Type*} {m₁ m₂ : MeasurableSpace X}
    [mX : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (h : m₁ ≤ m₂)
    (hm₁ : m₁ ≤ mX) {f : X → ℝ} (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hfi : Integrable f μ) :
    ∫ x, Real.negMulLog (condExp m₂ μ f x) ∂μ
      ≤ ∫ x, Real.negMulLog (condExp m₁ μ f x) ∂μ := by
  by_cases hm₂ : m₂ ≤ mX
  · have hG0 : ∀ᵐ x ∂μ, 0 ≤ condExp m₂ μ f x := condExp_nonneg hf0
    have hGIcc : ∀ᵐ x ∂μ, condExp m₂ μ f x ∈ Set.Icc 0 1 :=
      condExp_mem_Icc (μ := μ) (m := m₂) hm₂ hf0 hf1 hfi
    have hGint : Integrable (condExp m₂ μ f) μ := integrable_condExp (μ := μ) (m := m₂) (f := f)
    have hφG : Integrable (fun x => Real.negMulLog (condExp m₂ μ f x)) μ :=
      integrable_negMulLog_of_bdd (μ := μ) (g := condExp m₂ μ f)
        (aestronglyMeasurable_condExp (μ := μ) (m := m₂) (f := f)) hGIcc
    have hJ : condExp m₁ μ (fun x => Real.negMulLog (condExp m₂ μ f x))
        ≤ᵐ[μ] (fun x => Real.negMulLog (condExp m₁ μ (condExp m₂ μ f) x)) :=
      ConcaveOn.condExp_map_le (μ := μ) (m := m₁) (mα := mX) (f := condExp m₂ μ f)
        (φ := Real.negMulLog) (s := Set.Ici 0) hm₁ Real.concaveOn_negMulLog
        Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn hG0 isClosed_Ici hGint hφG
    have hLint : Integrable (condExp m₁ μ (fun x => Real.negMulLog (condExp m₂ μ f x))) μ :=
      integrable_condExp (μ := μ) (m := m₁) (f := fun x => Real.negMulLog (condExp m₂ μ f x))
    have hRint : Integrable (fun x => Real.negMulLog (condExp m₁ μ (condExp m₂ μ f) x)) μ :=
      integrable_negMulLog_condExp (μ := μ) (m := m₁) (f := condExp m₂ μ f) hG0
        (hGIcc.mono fun x hx => hx.2) hGint
    have hmono : ∫ x, condExp m₁ μ (fun x => Real.negMulLog (condExp m₂ μ f x)) x ∂μ
        ≤ ∫ x, Real.negMulLog (condExp m₁ μ (condExp m₂ μ f) x) ∂μ :=
      integral_mono_ae hLint hRint hJ
    have hstep : ∫ x, condExp m₁ μ (fun x => Real.negMulLog (condExp m₂ μ f x)) x ∂μ
        = ∫ x, Real.negMulLog (condExp m₂ μ f x) ∂μ :=
      integral_condExp (μ := μ) (m := m₁) (f := fun x => Real.negMulLog (condExp m₂ μ f x)) hm₁
    have htower : condExp m₁ μ (condExp m₂ μ f) =ᵐ[μ] condExp m₁ μ f :=
      condExp_condExp_of_le (μ := μ) (m₁ := m₁) (m₂ := m₂) (m₀ := mX) h hm₂
    have hcongr : (fun x => Real.negMulLog (condExp m₁ μ (condExp m₂ μ f) x)) =ᵐ[μ]
        (fun x => Real.negMulLog (condExp m₁ μ f x)) :=
      htower.mono fun x hx => by simpa using congrArg Real.negMulLog hx
    calc ∫ x, Real.negMulLog (condExp m₂ μ f x) ∂μ
        = ∫ x, condExp m₁ μ (fun x => Real.negMulLog (condExp m₂ μ f x)) x ∂μ := hstep.symm
      _ ≤ ∫ x, Real.negMulLog (condExp m₁ μ (condExp m₂ μ f) x) ∂μ := hmono
      _ = ∫ x, Real.negMulLog (condExp m₁ μ f x) ∂μ := integral_congr_ae hcongr
  · have hzf : condExp m₂ μ f = 0 := condExp_of_not_le hm₂
    have hRint : Integrable (fun x => Real.negMulLog (condExp m₁ μ f x)) μ :=
      integrable_negMulLog_condExp (μ := μ) (m := m₁) (f := f) hf0 hf1 hfi
    have hnn : (0 : X → ℝ) ≤ᵐ[μ] (fun x => Real.negMulLog (condExp m₁ μ f x)) :=
      (condExp_mem_Icc (μ := μ) (m := m₁) hm₁ hf0 hf1 hfi).mono
        fun x hx => Real.negMulLog_nonneg hx.1 hx.2
    have hge : (0 : ℝ) ≤ ∫ x, Real.negMulLog (condExp m₁ μ f x) ∂μ := by
      calc (0 : ℝ) = ∫ x, (0 : X → ℝ) x ∂μ := by simp
        _ ≤ ∫ x, Real.negMulLog (condExp m₁ μ f x) ∂μ :=
            integral_mono_ae (integrable_zero X ℝ μ) hRint hnn
    have hLz : ∫ x, Real.negMulLog (condExp m₂ μ f x) ∂μ = 0 := by
      rw [hzf]
      simp
    rw [hLz]
    exact hge

/-- The indicator of a set, with values in `{0,1}`, is `[0,1]`-valued. -/
lemma indicator_mem_Icc {X : Type*} (s : Set X) (x : X) :
    (s.indicator (fun _ => (1 : ℝ))) x ∈ Set.Icc 0 1 := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]; norm_num
  · rw [Set.indicator_of_notMem hx]; norm_num

/-- `Hcond` as a sum of the integrals of the individual `negMulLog∘𝔼[·|m]` terms. -/
lemma Hcond_eq_sum_integral {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : @Work.EKLContract.FinPart X mX) :
    Work.EKLContract.Hcond μ P m =
      ∑ i : Fin P.n, ∫ x, Real.negMulLog
        (condExp m μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x) ∂μ := by
  have hint : ∀ i : Fin P.n, Integrable (fun x => Real.negMulLog
      (condExp m μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x)) μ := by
    intro i
    exact integrable_negMulLog_condExp (μ := μ) (m := m)
      (f := (P.parts i).indicator (fun _ => (1 : ℝ)))
      (Filter.Eventually.of_forall fun x => (indicator_mem_Icc (P.parts i) x).1)
      (Filter.Eventually.of_forall fun x => (indicator_mem_Icc (P.parts i) x).2)
      ((integrable_const (1 : ℝ)).indicator (P.measurable i))
  unfold Work.EKLContract.Hcond
  exact integral_finsetSum Finset.univ (fun i _ => hint i)

/-- If the σ-algebra `m` is not even a sub-σ-algebra of the ambient one, `Hcond` vanishes. -/
lemma Hcond_eq_zero_of_not_le {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : @Work.EKLContract.FinPart X mX)
    (hm : ¬ m ≤ mX) : Work.EKLContract.Hcond μ P m = 0 := by
  have hc : ∀ f : X → ℝ, condExp m μ f = 0 := fun f => condExp_of_not_le hm
  have hfun : (fun x => ∑ i : Fin P.n, Real.negMulLog
      (condExp m μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x)) = fun _ => (0 : ℝ) := by
    funext x
    simp only [hc, Pi.zero_apply, Real.negMulLog_zero, Finset.sum_const_zero]
  unfold Work.EKLContract.Hcond
  rw [hfun]
  simp

/-- Monotonicity of `Hcond` in the conditioning σ-algebra, with the ambient instance bound after
the two σ-algebras (see the formalisation note above). -/
lemma Hcond_mono_aux {X : Type*} {m₁ m₂ : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : @Work.EKLContract.FinPart X mX)
    (h : m₁ ≤ m₂) :
    Work.EKLContract.Hcond μ P m₂ ≤ Work.EKLContract.Hcond μ P m₁ := by
  by_cases hm₁ : m₁ ≤ mX
  · rw [Hcond_eq_sum_integral (μ := μ) (m := m₂) P,
      Hcond_eq_sum_integral (μ := μ) (m := m₁) P]
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine integral_negMulLog_condExp_le (μ := μ) (m₁ := m₁) (m₂ := m₂) h hm₁ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => (indicator_mem_Icc (P.parts i) x).1
    · exact Filter.Eventually.of_forall fun x => (indicator_mem_Icc (P.parts i) x).2
    · exact (integrable_const (1 : ℝ)).indicator (P.measurable i)
  · have hm₂ : ¬ m₂ ≤ mX := fun h2 => hm₁ (le_trans h h2)
    have h₂ := Hcond_eq_zero_of_not_le (μ := μ) (m := m₂) P hm₂
    have h₁ := Hcond_eq_zero_of_not_le (μ := μ) (m := m₁) P hm₁
    simp [h₂, h₁]

theorem Hcond_mono {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : @Work.EKLContract.FinPart X mX)
    (m₁ m₂ : MeasurableSpace X) (h : m₁ ≤ m₂) :
    @Work.EKLContract.Hcond X mX μ P m₂ ≤ @Work.EKLContract.Hcond X mX μ P m₁ :=
  Hcond_mono_aux (mX := mX) μ P h

end Work.EKLC6Core
