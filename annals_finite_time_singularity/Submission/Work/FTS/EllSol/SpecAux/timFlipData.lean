import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.SpecAux.FlipDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

-- The time reversal `(t,θ) ↦ u (-t) θ` is the composition of `u` with the (linear, hence
-- smooth) map `(t,θ) ↦ (-t,θ)`, which maps the strip `ℝ × (0,π/2)` to itself; hence it
-- preserves `C²`-regularity on the strip.
theorem timFlip_strip_contDiffOn (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (Function.uncurry (timFlip u))
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hflip : ContDiff ℝ 2 (fun p : ℝ × ℝ => (-p.1, p.2)) := by fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (-p.1, p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun p hp => ⟨trivial, hp.2⟩
  rw [uncurry_timFlip_eq_comp u]
  exact hu.comp hflip.contDiffOn hmaps

theorem timFlipData (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.EllSol.SpecAux.timFlip u))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ t : ℝ, Work.FTS.EllSol.SpecAux.timFlip u t 0 = 0) ∧
      (∀ t : ℝ, Work.FTS.EllSol.SpecAux.timFlip u t (Real.pi / 2) = 0) ∧
      (Work.FTS.EllSol.FlatFT.NiceFlat u →
        Work.FTS.EllSol.FlatFT.NiceFlat (Work.FTS.EllSol.SpecAux.timFlip u)) ∧
      (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Spaces.pz (Work.FTS.EllSol.SpecAux.timFlip u) t θ = -(Work.Spaces.pz u (-t) θ)) ∧
      (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Spaces.pth (Work.FTS.EllSol.SpecAux.timFlip u) t θ = Work.Spaces.pth u (-t) θ) := by
  have hcd := timFlip_strip_contDiffOn u hu
  refine ⟨hcd, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa using h0 (-t)
  · intro t
    simpa using h1 (-t)
  · intro hnf
    obtain ⟨hc, hz0, hz1, N, hN⟩ := hnf
    exact ⟨hcd, fun t => by simpa using h0 (-t), fun t => by simpa using h1 (-t),
      N, fun t θ ht => by
        have ht' : N < |-t| := by rwa [abs_neg]
        simpa [timFlip] using hN (-t) θ ht'⟩
  · intro t θ _
    show deriv (fun t' => u (-t') θ) t = -deriv (fun t' => u t' θ) (-t)
    exact deriv_comp_neg (f := fun s => u s θ) (x := t)
  · intro t θ _
    show deriv (fun θ' => u (-t) θ') θ = deriv (fun θ' => u (-t) θ') θ
    rfl

end Work.FTS.EllSol.SpecAux
