import Mathlib
import Submission.Work.Drive.Mono.FiberModel.planar_pieces

/-!
# The fibres of the closed box and the height functions

The fibre of the closed box over a point of the shadow is nonempty and compact.  (The attainedness
of the extremal values `fMin`/`fMax` on it, and their characterisation of the fibre, are the next
steps of `height_facts`; the difficulty there is purely notational, matching the definition of
`fibre` (`levPair v ℓ y = X`) with the definition of `fibreMax` (`p y = X.1 ∧ q y = X.2`).)
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

theorem isCompact_ClBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : IsCompact (ClBox s c σ) :=
  (isBounded_PBox s c σ).isCompact_closure

/-- The fibre of the closed box over a point of the shadow is nonempty. -/
theorem fibre_nonempty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    {X : ℝ × ℝ} (hX : X ∈ boxShadow s c σ v ℓ) : (fibre v ℓ s c σ X).Nonempty := by
  rw [boxShadow, shadow] at hX
  obtain ⟨y, hy, hyX⟩ := hX
  exact ⟨y, hy, hyX⟩

theorem isCompact_fibre {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    (X : ℝ × ℝ) : IsCompact (fibre v ℓ s c σ X) := by
  have hcl : IsClosed {y : R3 | levPair v ℓ y = X} :=
    isClosed_eq (map_continuous (levPairCLM v ℓ)) continuous_const
  exact (isCompact_ClBox s c σ).inter_right hcl

/-- **The identification of the fibre with the set used by `fibreMax`/`fibreMin`.**  This is the
notational bridge between `fibre` (`levPair v ℓ y = X`) and `fibreMax`/`fibreMin`
(`p y = X.1 ∧ q y = X.2`). -/
theorem fibre_eq_set {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (X : ℝ × ℝ) :
    fibre v ℓ s c σ X = {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2} := by
  ext y
  simp only [fibre, levPair, Set.mem_ofPred_eq, Set.mem_setOf_eq, Prod.ext_iff]

theorem isCompact_fibre_set {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (X : ℝ × ℝ) :
    IsCompact {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2} :=
  fibre_eq_set (v := v) (ℓ := ℓ) (s := s) (c := c) (σ := σ) X ▸ isCompact_fibre (v := v) (ℓ := ℓ) X

/-- The maximal value of `ζ` on the fibre is attained. -/
theorem fMax_mem {ζ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} {X : ℝ × ℝ} (hX : X ∈ boxShadow s c σ v ℓ) :
    fMax ζ v ℓ s c σ X ∈ ζ '' fibre v ℓ s c σ X := by
  rw [fMax, Work.Drive.Mono.fibreMax,
    fibre_eq_set (v := v) (ℓ := ℓ) (s := s) (c := c) (σ := σ) X]
  refine IsCompact.sSup_mem ((isCompact_fibre_set (s := s) (c := c) (σ := σ) X).image
    ζ.continuous) ?_
  simpa only [fibre_eq_set] using (fibre_nonempty (v := v) (ℓ := ℓ) hX).image ζ

/-- The minimal value of `ζ` on the fibre is attained. -/
theorem fMin_mem {ζ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} {X : ℝ × ℝ} (hX : X ∈ boxShadow s c σ v ℓ) :
    fMin ζ v ℓ s c σ X ∈ ζ '' fibre v ℓ s c σ X := by
  rw [fMin, Work.Drive.Mono.fibreMin,
    fibre_eq_set (v := v) (ℓ := ℓ) (s := s) (c := c) (σ := σ) X]
  refine IsCompact.sInf_mem ((isCompact_fibre_set (s := s) (c := c) (σ := σ) X).image
    ζ.continuous) ?_
  simpa only [fibre_eq_set] using (fibre_nonempty (v := v) (ℓ := ℓ) hX).image ζ

end

end Work.Drive.Mono.FiberModel
