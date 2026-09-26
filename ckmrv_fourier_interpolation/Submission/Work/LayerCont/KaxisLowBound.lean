import Mathlib
import Submission.Work.LayerCont.GapSetCompact
import Submission.Work.LayerCont.GapBoundKaxis
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- The point `i · max t δ` of `ℍ` (`δ > 0`), a **globally defined and continuous** function of
`t` which agrees with `Work.Kernels.imagAxis t _` on `t ≥ δ`.  (Unlike `imagAxis`, which carries
a proof of `0 < t`, and unlike `Work.LayerCont.axisPt`/`iAxisFun`, which clamp at `1`, this is the
right parametrisation of the axis *below* `1`.) -/
def axisPtδ (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : UpperHalfPlane :=
  ⟨((max t δ : ℝ) : ℂ) * Complex.I, by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero]
    exact lt_of_lt_of_le hδ (le_max_right t δ)⟩

lemma axisPtδ_coe (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ((axisPtδ δ hδ t : UpperHalfPlane) : ℂ) = ((max t δ : ℝ) : ℂ) * Complex.I := rfl

lemma continuous_axisPtδ (δ : ℝ) (hδ : 0 < δ) : Continuous (axisPtδ δ hδ) := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous (fun t : ℝ => UpperHalfPlane.coe (axisPtδ δ hδ t))
  simp only [axisPtδ_coe]
  fun_prop

lemma axisPtδ_eq_imagAxis {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    axisPtδ δ hδ t = Work.Kernels.imagAxis t (lt_of_lt_of_le hδ ht) := by
  apply UpperHalfPlane.ext
  show ((max t δ : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I
  rw [max_eq_left ht]

/-- The plain product `K × [δ,T]` (no guard needed: cleanliness is assumed on the whole
interval). -/
def gapSetLow (K : Set UpperHalfPlane) (δ T : ℝ) : Set (UpperHalfPlane × ℝ) :=
  K ×ˢ Set.Icc δ T

theorem isCompact_gapSetLow {K : Set UpperHalfPlane} (hK : IsCompact K) (δ T : ℝ) :
    IsCompact (gapSetLow K δ T) := hK.prod isCompact_Icc

/-- **Two-variable continuity of the kernel on a compact axis piece *below* the usual range.**

This is the `t ≤ 1` companion of `Work.LayerCont.continuousOn_gapSet`: the parametrisation
`axisPt2 t = i t` (not `i · max t 1`) is the correct one there. -/
theorem continuousOn_gapSetLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} {δ T : ℝ} (hδ : 0 < δ)
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Icc δ T →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2) (gapSetLow K δ T) := by
  have hΨ : Continuous (fun p : UpperHalfPlane × ℝ => (p.1, axisPtδ δ hδ p.2)) :=
    continuous_fst.prodMk ((continuous_axisPtδ δ hδ).comp continuous_snd)
  have hA : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Asymptotics.AfunFun ℓ d p.1 (axisPtδ δ hδ p.2)) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => (p.1, axisPtδ δ hδ p.2))
      (g := fun q : UpperHalfPlane × UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d q.1 q.2)
      (Work.Asymptotics.continuous_AfunFun ℓ d) hΨ
  have hj1 : Continuous (fun p : UpperHalfPlane × ℝ => Work.Kernels.jInvariantFun p.1) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => p.1)
      (g := fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      Work.Asymptotics.continuous_jInvariantFun' continuous_fst
  have hj2 : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.jInvariantFun (axisPtδ δ hδ p.2)) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => axisPtδ δ hδ p.2)
      (g := fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      Work.Asymptotics.continuous_jInvariantFun'
      ((continuous_axisPtδ δ hδ).comp continuous_snd)
  have hj : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPtδ δ hδ p.2)) :=
    hj1.sub hj2
  have hne : ∀ p ∈ gapSetLow K δ T,
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPtδ δ hδ p.2) ≠ 0 := by
    intro p hp
    have ht : 0 < p.2 := lt_of_lt_of_le hδ hp.2.1
    refine sub_ne_zero.mpr ?_
    rw [axisPtδ_eq_imagAxis hδ hp.2.1]
    exact hclean p.1 hp.1 p.2 ht hp.2
  have hdiv : ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Asymptotics.AfunFun ℓ d p.1 (axisPtδ δ hδ p.2)
        / (Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPtδ δ hδ p.2)))
      (gapSetLow K δ T) :=
    hA.continuousOn.div hj.continuousOn hne
  have hKfun : ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.Kfun ℓ d p.1 (axisPtδ δ hδ p.2)) (gapSetLow K δ T) := by
    refine hdiv.congr (fun p hp => ?_)
    rw [eq_div_iff (hne p hp)]
    exact Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd p.1 (axisPtδ δ hδ p.2)
      (sub_ne_zero.mp (hne p hp))
  have hEqOn : Set.EqOn
      (fun p : UpperHalfPlane × ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2)
      (fun p : UpperHalfPlane × ℝ => Work.Kernels.Kfun ℓ d p.1 (axisPtδ δ hδ p.2))
      (gapSetLow K δ T) := by
    intro p hp
    have ht : 0 < p.2 := lt_of_lt_of_le hδ hp.2.1
    simp only [Work.Kernels.Kaxis, dif_pos ht]
    rw [axisPtδ_eq_imagAxis hδ hp.2.1]
  exact hKfun.congr hEqOn

/-- **The kernel is bounded on a compact axis piece `[δ,T]` with `δ > 0`**, given cleanliness
there.  (The `t ≤ 1` companion of `Work.LayerCont.GapBoundKaxis`.) -/
theorem GapBoundKaxisLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {δ T : ℝ} (hδ : 0 < δ)
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Icc δ T →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → t ∈ Set.Icc δ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_gapSetLow hK δ T).exists_bound_of_continuousOn
    (continuousOn_gapSetLow ℓ d hd hδ hclean)
  exact ⟨max C 0, le_max_right _ _, fun τ t hτ ht =>
    le_trans (hC (τ, t) ⟨hτ, ht⟩) (le_max_left C 0)⟩

/-- **The kernel is bounded on the whole interval `(0,1]` minus the coincidence neighbourhood
`I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)`, uniformly over a closed ball of `τ`.**

The small-`t` end is controlled by the cusp-`0` flatness
(`Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded` with `N = 0`), the rest by the compactness
bound `GapBoundKaxisLow`.  This is the dominator for the *coincidence-removed* low piece
`Work.LayerCont.layerLowCoinc`, and it is intentionally free of the `CleanBounded`/
`KaxisBoundedIcc` chain (which cannot be imported together with the cusp-expansion chain: both
declare `Work.Asymptotics.Pspace`). -/
theorem KaxisBoundedLowBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (x : UpperHalfPlane) (ρ t₀ A₂ : ℝ) (hA₂ : 0 < A₂) (hA₂inv : A₂ < t₀⁻¹)
    (hI₂low : t₀⁻¹ + A₂ < 1)
    (hclean : ∀ (w : UpperHalfPlane), w ∈ Metric.closedBall x ρ → ∀ (t : ℝ) (ht : 0 < t),
      t ∈ (Set.Ioc (0 : ℝ) 1 \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : UpperHalfPlane), w ∈ Metric.closedBall x ρ →
      ∀ t ∈ (Set.Ioc (0 : ℝ) 1 \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ C := by
  obtain ⟨δc, hδcpos, hcusp⟩ :=
    Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd
      (K := Metric.closedBall x ρ) Metric.isBounded_closedBall
  obtain ⟨c, hcpos, hcb⟩ := hcusp 0 le_rfl
  have ht₀inv : 0 < t₀⁻¹ := lt_trans hA₂ hA₂inv
  set δ : ℝ := min δc ((t₀⁻¹ - A₂) / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδcpos (by linarith)
  have hδδc : δ ≤ δc := min_le_left _ _
  have hδhalf : δ ≤ (t₀⁻¹ - A₂) / 2 := min_le_right _ _
  have hδle : δ ≤ t₀⁻¹ - A₂ := by linarith
  -- the middle piece `[δ, t₀⁻¹ - A₂]`
  obtain ⟨C₁, hC₁nn, hC₁b⟩ := GapBoundKaxisLow ℓ d hd (K := Metric.closedBall x ρ)
    (isCompact_closedBall x ρ) hδpos (T := t₀⁻¹ - A₂)
    (fun w hw t ht htI => hclean w hw t ht
      ⟨⟨lt_of_lt_of_le hδpos htI.1, by linarith [htI.2, hI₂low]⟩,
        fun hmem => absurd hmem.1 (not_lt.mpr htI.2)⟩)
  -- the upper piece `[t₀⁻¹ + A₂, 1]`
  obtain ⟨C₂, hC₂nn, hC₂b⟩ := GapBoundKaxisLow ℓ d hd (K := Metric.closedBall x ρ)
    (isCompact_closedBall x ρ) (lt_trans ht₀inv (by linarith))
    (T := 1)
    (fun w hw t ht htI => hclean w hw t ht
      ⟨⟨lt_of_lt_of_le (by linarith : (0:ℝ) < t₀⁻¹ + A₂) htI.1, htI.2⟩,
        fun hmem => absurd hmem.2 (not_lt.mpr htI.1)⟩)
  refine ⟨max (max c C₁) C₂, le_trans hcpos.le (le_trans (le_max_left c C₁)
    (le_max_left _ _)), fun w hw v hv => ?_⟩
  obtain ⟨hvpos, hv1⟩ := hv.1.1, hv.1.2
  have hvnotin : ¬(t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂) := hv.2
  push_neg at hvnotin
  rcases le_or_gt v δ with hvδ | hvδ
  · have hcv : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w v‖ ≤ c := by
      simpa using hcb w v hw hvpos (le_trans hvδ hδδc)
    exact le_trans hcv (le_trans (le_max_left c C₁) (le_max_left _ _))
  · have hδv : δ ≤ v := le_of_lt hvδ
    rcases le_or_gt v (t₀⁻¹ - A₂) with hvle | hvgt
    · exact le_trans (hC₁b w v hw ⟨hδv, hvle⟩) (le_trans (le_max_right c C₁)
        (le_max_left _ _))
    · have hhigh : t₀⁻¹ + A₂ ≤ v := hvnotin hvgt
      exact le_trans (hC₂b w v hw ⟨hhigh, hv1⟩) (le_max_right _ _)

end Work.LayerCont
