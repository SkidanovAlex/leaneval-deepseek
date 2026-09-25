/-
# Instantiating `CauchyEstimates`

The structure `Work.Beltrami.CauchyEstimates` (`Solve.lean`) collects the analytic facts about the
Cauchy transform `cauchyT` and the Beurling transform `beurling` on which the Beltrami argument
rests.  This file instantiates it from the individually proved estimates:

* potential bound  : `norm_cauchyT_le_uniform`
* Schauder estimates: `beurling_schauder_uniform` (which builds on `beurling_bounded`,
  `beurling_holder_difference` and `beurling_holder_uniform`)
* linearity of `beurling` : `beurling_sub`
* Pompeiu formula  : `pompeiu` (`dbarW (cauchyT f) = f`)
* `∂ ∘ cauchyT = beurling` : `dW_cauchyT_eq_beurling_radial`
* smoothness of `cauchyT` : `contDiff_cauchyT`
* smoothness of the fixed point : `smooth_of_beurling_fixed`
-/
import Mathlib
import Submission.Work.Beltrami.Solve
import Submission.Work.Beltrami.norm_cauchyT_le_uniform
import Submission.Work.Beltrami.beurling_schauder
import Submission.Work.Beltrami.beurling_schauder_uniform
import Submission.Work.Beltrami.beurling_sub
import Submission.Work.Beltrami.dbarW_cauchyT
import Submission.Work.Beltrami.contDiff_cauchyT
import Submission.Work.Beltrami.smooth_of_beurling_fixed
import Submission.Work.Beltrami.dW_cauchyT_eq_beurling_radial
import Submission.Work.Beltrami.Theorem

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff

noncomputable section

/-- The uniform constant of the potential bound. -/
def cauchyPotConst : ℝ := norm_cauchyT_le_uniform.choose

theorem cauchyPotConst_pos : 0 < cauchyPotConst :=
  (norm_cauchyT_le_uniform.choose_spec).1

/-- The uniform Schauder constant. -/
def cauchySchConst (α : ℝ) : ℝ :=
  if h : 0 < α ∧ α < 1 then (beurling_schauder_uniform α h.1 h.2).choose else 1

theorem cauchySchConst_pos (α : ℝ) : 0 < cauchySchConst α := by
  unfold cauchySchConst
  split_ifs with h
  · exact (beurling_schauder_uniform α h.1 h.2).choose_spec.1
  · norm_num

/-- The smallness window for the smoothness of the fixed point. -/
def cauchySmoothDelta (R α K R' : ℝ) : ℝ :=
  if h : 0 < α ∧ α < 1 then (smooth_of_beurling_fixed R α K R' h.1 h.2).choose else 1

theorem cauchySmoothDelta_pos (R α K R' : ℝ) : 0 < cauchySmoothDelta R α K R' := by
  unfold cauchySmoothDelta
  split_ifs with h
  · exact (smooth_of_beurling_fixed R α K R' h.1 h.2).choose_spec.1
  · norm_num

/-- **The analytic estimates, instantiated.** -/
noncomputable def cauchyEstimates : CauchyEstimates where
  potConst := cauchyPotConst
  potConst_pos := cauchyPotConst_pos
  potential := fun f M R hf hR hM hsupp z =>
    (norm_cauchyT_le_uniform.choose_spec).2 f M R hf hR hM hsupp z
  schConst := cauchySchConst
  schConst_pos := cauchySchConst_pos
  schauder := by
    intro α hα hα1 f M K R hR hM hK hsupp
    have hδ : cauchySchConst α = (beurling_schauder_uniform α hα hα1).choose := by
      unfold cauchySchConst
      exact dif_pos (show 0 < α ∧ α < 1 from ⟨hα, hα1⟩)
    rw [hδ]
    exact (beurling_schauder_uniform α hα hα1).choose_spec.2 M K R f hR hM hK hsupp
  beurling_sub := fun α hα hα1 f g M K R hR hMf hMg hKf hKg hsf hsg =>
    Work.Beltrami.beurling_sub α hα hα1 f g M K R hR hMf hMg hKf hKg hsf hsg
  pompeiu := fun f hf hc z => dbarW_cauchyT f hf hc z
  beurlingDeriv := by
    intro f hf hc z
    exact dW_cauchyT_eq_beurling_radial f hf hc z
  contDiffT := fun f hf hc => contDiff_cauchyT f hf hc
  smoothDelta := cauchySmoothDelta
  smoothDelta_pos := cauchySmoothDelta_pos
  smoothFixed := by
    intro R α K R' hα hα1 μ f u hμs hμc hμb hfs hfc hfb hub huK husupp heq
    have hδ : cauchySmoothDelta R α K R'
        = (smooth_of_beurling_fixed R α K R' hα hα1).choose := by
      unfold cauchySmoothDelta
      exact dif_pos (show 0 < α ∧ α < 1 from ⟨hα, hα1⟩)
    have h := (smooth_of_beurling_fixed R α K R' hα hα1).choose_spec.2 μ f u
      hμs hμc (by rw [← hδ]; exact hμb) hfs hfc hfb hub huK husupp heq
    exact h

/-- **The `n = 1` Newlander--Nirenberg theorem.**  For an almost complex structure `J` on
`E 1 = ℝ²` (a smooth field of endomorphisms with `J y ∘ J y = -1`), every point `x` of an open
set `U` has a neighbourhood carrying a smooth chart `φ` into `ℂ = F 1` with smooth inverse and
complex-linear differential `dφ ∘ J = i · dφ`.

The Nijenhuis hypothesis is redundant in real dimension two and is not used. -/
theorem newlander_nirenberg_one
    {U : Set (E 1)} (hU : IsOpen U) (J : E 1 → E 1 →L[ℝ] E 1) (hJ : IsAlmostComplexOn J U)
    (hN : NijenhuisVanishesOn J U) {x : E 1} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E 1) (EuclideanSpace ℂ (Fin 1)),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : EuclideanSpace ℂ (Fin 1) → E 1) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E 1,
        fderiv ℝ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) y (J y v)
          = Complex.I • fderiv ℝ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) y v :=
  newlander_nirenberg_one_of_cauchy cauchyEstimates hU J hJ hN hx

/-- The same theorem **without** the Nijenhuis hypothesis: in real dimension two it is
automatic, and the proof above never uses it. -/
theorem newlander_nirenberg_one_noNijenhuis
    {U : Set (E 1)} (hU : IsOpen U) (J : E 1 → E 1 →L[ℝ] E 1) (hJ : IsAlmostComplexOn J U)
    {x : E 1} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E 1) (EuclideanSpace ℂ (Fin 1)),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : EuclideanSpace ℂ (Fin 1) → E 1) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E 1,
        fderiv ℝ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) y (J y v)
          = Complex.I • fderiv ℝ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) y v :=
  newlander_nirenberg_one_of_hol (localHolInput_of_cauchyEstimates cauchyEstimates) hU J hJ hx

end

end Work.Beltrami
