import Mathlib
import Submission.Work.Mostow.fermiSetup

/-!
# `prodeMap` is volume preserving

`Work.Mostow.prodeMap k m` pads a pair `(v, w) ∈ E k × E m` to the vector `E (k+m)` whose first
`k` coordinates are those of `v` and whose last `m` coordinates are those of `w` (via `Fin.append`).
It is a "linear isomorphism with determinant 1", hence preserves Lebesgue measure.

The proof is a composition of three volume preserving maps:
* passing from `E k × E m` to `(Fin k → ℝ) × (Fin m → ℝ)` by `WithLp.ofLp` (`PiLp.volume_preserving_ofLp`);
* `Fin.append`, i.e. the decomposition `Measure.pi` on `Fin (k+m)` into the product of the
  `Measure.pi` on `Fin k` and `Fin m` (`volume_measurePreserving_sumPiEquivProdPi_symm`
  followed by `volume_measurePreserving_piCongrLeft` along `finSumFinEquiv`);
* passing back from `Fin (k+m) → ℝ` to `E (k+m)` by `WithLp.toLp` (`PiLp.volume_preserving_toLp`).
-/

namespace Work.Mostow

open MeasureTheory

noncomputable section

/-- `Fin.append` is volume preserving: the measure on `Fin (k+m) → ℝ` is the product of the
measures on `Fin k → ℝ` and `Fin m → ℝ` under the "append" identification. -/
theorem volume_preserving_finAppend (k m : ℕ) :
    MeasureTheory.MeasurePreserving (fun p : (Fin k → ℝ) × (Fin m → ℝ) => Fin.append p.1 p.2)
      (MeasureTheory.volume : MeasureTheory.Measure ((Fin k → ℝ) × (Fin m → ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (k + m) → ℝ)) := by
  have h₁ : MeasurePreserving
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) =>
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + m) => ℝ) finSumFinEquiv)
          ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin m => ℝ)).symm p))
      (volume : Measure ((Fin k → ℝ) × (Fin m → ℝ)))
      (volume : Measure (Fin (k + m) → ℝ)) :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (k + m) => ℝ) finSumFinEquiv).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin m => ℝ))
  convert h₁ using 1
  funext p
  ext i
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  rcases x with i | j
  · rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply]
    simp [finSumFinEquiv_apply_left, Fin.append_left]
  · rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply]
    simp [finSumFinEquiv_apply_right, Fin.append_right]

theorem measurePreserving_prodeMap (k m : ℕ) :
    MeasureTheory.MeasurePreserving (Work.Mostow.prodeMap k m)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E k × Submission.Mostow.E m))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E (k + m))) := by
  have hpair : MeasurePreserving (fun p : Submission.Mostow.E k × Submission.Mostow.E m =>
      (WithLp.ofLp p.1, WithLp.ofLp p.2))
      (volume : Measure (Submission.Mostow.E k × Submission.Mostow.E m))
      (volume : Measure ((Fin k → ℝ) × (Fin m → ℝ))) :=
    (PiLp.volume_preserving_ofLp (Fin k)).prod (PiLp.volume_preserving_ofLp (Fin m))
  have hto : MeasurePreserving (fun g : Fin (k + m) → ℝ => WithLp.toLp 2 g)
      (volume : Measure (Fin (k + m) → ℝ))
      (volume : Measure (Submission.Mostow.E (k + m))) :=
    PiLp.volume_preserving_toLp (Fin (k + m))
  exact hto.comp ((volume_preserving_finAppend k m).comp hpair)

end

end Work.Mostow
