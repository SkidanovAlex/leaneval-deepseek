import Mathlib
import Submission.Work.Mostow.stdFermiDefs

namespace Work.Mostow

open Submission.Mostow MeasureTheory

/-- Basic coordinate facts for the standard Fermi chart of `ℍ² = E 2`:
`coordMap` is the linear coordinate identification with the standard orthonormal frame
`(axis, axisPerp)`, so its two coordinates are the two entries of the pair; `axis`/`axisPerp`
do span `E 2`; `coordMap` is injective; it carries the coordinate rectangle onto `boxSq`;
`boxSq` is measurable; and `stdFermi` is `fermiSelf` read in the coordinates `coordMap`. -/
theorem stdFermiCoordFacts :
    (∀ p : ℝ × ℝ, (Work.Mostow.FermiTwo.coordMap p) 0 = p.1 ∧
      (Work.Mostow.FermiTwo.coordMap p) 1 = p.2) ∧
    (∀ x : Submission.Mostow.E 2,
      x = (x 0) • Work.Mostow.FermiTwo.axis + (x 1) • Work.Mostow.FermiTwo.axisPerp) ∧
    Function.Injective Work.Mostow.FermiTwo.coordMap ∧
    (∀ L ρ : ℝ, Work.Mostow.FermiTwo.coordMap '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ) =
      Work.Mostow.FermiTwo.boxSq L ρ) ∧
    (∀ L ρ : ℝ, MeasurableSet (Work.Mostow.FermiTwo.boxSq L ρ)) ∧
    (∀ p : ℝ × ℝ, Work.Mostow.FermiTwo.stdFermi p =
      Work.Mostow.FermiTwo.fermiSelf (Work.Mostow.FermiTwo.coordMap p)) := by
  -- coordinates of the linear identification `(s,r) ↦ s • axis + r • axisPerp`
  have hcoord : ∀ p : ℝ × ℝ,
      (FermiTwo.coordMap p) 0 = p.1 ∧ (FermiTwo.coordMap p) 1 = p.2 := by
    intro p
    constructor <;> simp [FermiTwo.coordMap, FermiTwo.axis, FermiTwo.axisPerp]
  -- the standard frame spans `E 2`
  have hrecon : ∀ x : Submission.Mostow.E 2,
      x = (x 0) • FermiTwo.axis + (x 1) • FermiTwo.axisPerp := by
    intro x
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [FermiTwo.axis, FermiTwo.axisPerp]
  refine ⟨hcoord, hrecon, ?_, ?_, ?_, ?_⟩
  · -- injectivity, from the coordinate formula
    intro p q hpq
    have h0 : p.1 = q.1 := by
      have := congrArg (fun x : Submission.Mostow.E 2 => x.ofLp 0) hpq
      simpa [FermiTwo.coordMap, FermiTwo.axis, FermiTwo.axisPerp] using this
    have h1 : p.2 = q.2 := by
      have := congrArg (fun x : Submission.Mostow.E 2 => x.ofLp 1) hpq
      simpa [FermiTwo.coordMap, FermiTwo.axis, FermiTwo.axisPerp] using this
    exact Prod.ext h0 h1
  · -- the image of the coordinate rectangle is the box
    intro L ρ
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Set.mem_prod] at hp
      exact ⟨by simpa [FermiTwo.coordMap, FermiTwo.axis, FermiTwo.axisPerp] using hp.1,
        by simpa [FermiTwo.coordMap, FermiTwo.axis, FermiTwo.axisPerp] using hp.2⟩
    · intro hx
      refine ⟨(x 0, x 1), ⟨hx.1, hx.2⟩, ?_⟩
      show FermiTwo.coordMap (x 0, x 1) = x
      rw [FermiTwo.coordMap]
      exact (hrecon x).symm
  · -- measurability: `boxSq` is the intersection of two coordinate slabs
    intro L ρ
    have c0 : Continuous (fun x : Submission.Mostow.E 2 => x 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
    have c1 : Continuous (fun x : Submission.Mostow.E 2 => x 1) :=
      PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
    rw [show FermiTwo.boxSq L ρ
        = ((fun x : Submission.Mostow.E 2 => x 0) ⁻¹' Set.Ico 0 L) ∩
          ((fun x : Submission.Mostow.E 2 => x 1) ⁻¹' Set.Ioo (-ρ) ρ) from rfl]
    exact (measurableSet_Ico.preimage c0.measurable).inter
      (measurableSet_Ioo.preimage c1.measurable)
  · -- `stdFermi` in the coordinates of `coordMap` is `fermiSelf`
    intro p
    obtain ⟨s, r⟩ := p
    simp [FermiTwo.stdFermi, FermiTwo.fermiSelf, FermiTwo.coordMap, FermiTwo.axis,
      FermiTwo.axisPerp]

end Work.Mostow
