import Mathlib
import Submission.Work.Drive.Mono.tiltData_window_of_dir_export_param
import Submission.Work.Drive.Mono.Band.ae_height_good
import Submission.Work.Drive.Mono.Band.heightGood_open

namespace Work.Drive.Mono

/-- **The thin-slab tilt data in a prescribed window, staying off a prescribed null set of
parameters, with the wall direction exported as a *good* (Morse, distinct-value) height direction.**
This is `Work.Drive.Mono.tiltData_window_of_dir_export_param` with one extra conjunct: the wall
normal `dirOf τ a₀ b₀` produced by the construction is a `Work.Drive.Mono.Band.HeightGood` direction
for the surface.  The producer's proof already establishes this internally
(`hgoodf : HeightGood ψ nf` from the openness `Work.Drive.Mono.Band.heightGood_open` of the good set
around the prescribed `n = dirOf 1 a₀ b₀`), it is merely not exported. -/
theorem tiltData_window_of_dir_export_param_good
    (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u A B ρ : ℝ)
    (v n : LeanEval.KnotTheory.PardonDistortion.R3)
    (hA : 0 < A) (hAB : A < B) (hB : B ≤ Work.Drive.Mono.boxWidth s σ v - |u|) (hρ : 0 < ρ)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (haxis : ∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • v)
    (hgood : Work.Drive.Mono.Band.HeightGood ψ n)
    (a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hnb : n = (Real.sqrt 2)⁻¹ • (a₀ + b₀))
    (S : Set (ℝ × ℝ)) (hS : MeasureTheory.volume S = 0) :
    ∃ (h τ : ℝ) (exc : Finset ℝ), A < h ∧ h < B ∧ (h, τ) ∉ S ∧
      h + |u| < Work.Drive.Mono.boxWidth s σ v ∧
      ‖Work.Drive.Mono.Band.dirOf τ a₀ b₀ - n‖ < ρ ∧
      ‖Work.Drive.Mono.Band.dirOf τ a₀ b₀‖ = 1 ∧
      inner ℝ v (Work.Drive.Mono.Band.dirOf τ a₀ b₀) = 0 ∧
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) ∧
      (∀ i : Fin 3, (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
          (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) exc ∧
      (∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
        |inner ℝ v z - (inner ℝ v c + u)| = h →
        ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) := by
  -- The good set is open around the prescribed `n`: shrink the tolerance `ρ` to the openness radius
  -- so that the produced wall normal is automatically good.
  obtain ⟨ρg, hρg0, hρg⟩ := Work.Drive.Mono.Band.heightGood_open ψ hgood
  have hρmin : 0 < min ρ ρg := lt_min hρ hρg0
  obtain ⟨h, τ, exc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    tiltData_window_of_dir_export_param ψ s c σ u A B (min ρ ρg) v n
      hA hAB hB hρmin hv1 hn1 hvn haxis hgood a₀ b₀ ha hb hab hva hvb hnb S hS
  exact ⟨h, τ, exc, h1, h2, h3, h4,
    lt_of_lt_of_le h5 (min_le_left _ _), h6, h7,
    hρg _ (lt_of_lt_of_le h5 (min_le_right _ _)),
    h8, h9, h10⟩

end Work.Drive.Mono
