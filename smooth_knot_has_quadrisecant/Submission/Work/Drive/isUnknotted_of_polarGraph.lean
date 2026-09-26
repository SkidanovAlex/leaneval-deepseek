import Mathlib
import Submission.AnalyticUnknot

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- Translating a smooth knot by a constant vector gives a smooth knot: analyticity,
`period`-periodicity, injectivity on one period and regularity are all invariant under
the translation `z ↦ c + z`. -/
lemma isSmoothKnot_constAdd {r : ℝ → Space} (c : Space) (h : IsSmoothKnot r) :
    IsSmoothKnot (fun t => c + r t) where
  smooth := contDiff_const.add h.smooth
  periodic := by
    intro t
    change c + r (t + period) = c + r t
    rw [h.periodic t]
  injective_on_period := by
    intro t ht t' ht' heq
    exact h.injective_on_period ht ht' (add_left_cancel heq)
  regular := by
    intro t
    have hd : DifferentiableAt ℝ r t := (h.smooth.differentiable (by simp)).differentiableAt
    have hderiv : deriv (fun u : ℝ => c + r u) t = deriv r t :=
      (hd.hasDerivAt.const_add c).deriv
    rw [velocity, hderiv, ← velocity]
    exact h.regular t

/-- Translating an unknotted curve by a constant vector gives an unknotted curve:
the isotopy `R` is replaced by `(t, s) ↦ (1 - s) • c + R t s`, which at `s = 0` is the
translate of `r`, at `s = 1` is still the round circle (`(1-1) • c = 0`), and whose
slices are translates of the slices of `R`, hence smooth knots. -/
lemma isUnknotted_constAdd {r : ℝ → Space} (c : Space) (h : IsUnknotted r) :
    IsUnknotted (fun t => c + r t) := by
  obtain ⟨R, hR, h0, h1, hk⟩ := h
  refine ⟨fun t s => (1 - s) • c + R t s, ?_, ?_, ?_, ?_⟩
  · exact ((contDiff_const.sub contDiff_snd).smul contDiff_const).add hR
  · intro t
    simp [h0]
  · intro t
    simp [h1]
  · intro s hs
    exact isSmoothKnot_constAdd ((1 - s) • c) (hk s hs)

theorem isUnknotted_of_polarGraph {ρ : ℝ → ℝ} (c : LeanEval.KnotTheory.Quadrisecant.Space)
    (hρ : ContDiff ℝ ⊤ ρ)
    (hper : Function.Periodic ρ LeanEval.KnotTheory.Quadrisecant.period)
    (hpos : ∀ t : ℝ, 0 < ρ t) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted
      (fun t : ℝ => c + ρ t • (!₂[Real.cos t, Real.sin t, (0 : ℝ)])) := by
  have hcyl : IsUnknotted
      (fun t : ℝ => (!₂[ρ t * Real.cos t, ρ t * Real.sin t, (0 : ℝ)] : Space)) :=
    isUnknotted_of_cylindricalGraph (r := fun t : ℝ =>
        (!₂[ρ t * Real.cos t, ρ t * Real.sin t, (0 : ℝ)] : Space))
      (a := ρ) (b := fun _ : ℝ => (0 : ℝ)) hρ contDiff_const hpos hper
      (fun t => by simp) (fun t => rfl)
  have htr : IsUnknotted
      (fun t : ℝ => c + (!₂[ρ t * Real.cos t, ρ t * Real.sin t, (0 : ℝ)] : Space)) :=
    isUnknotted_constAdd c hcyl
  have hfun : (fun t : ℝ => c + ρ t • (!₂[Real.cos t, Real.sin t, (0 : ℝ)]))
      = (fun t : ℝ => c + (!₂[ρ t * Real.cos t, ρ t * Real.sin t, (0 : ℝ)] : Space)) := by
    funext t
    congr 1
    ext i
    fin_cases i <;> simp
  rw [hfun]
  exact htr

end Work.Drive
