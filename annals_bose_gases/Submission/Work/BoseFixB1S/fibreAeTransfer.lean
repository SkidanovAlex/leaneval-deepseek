import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxFlatAux
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `N`-particle centred box is the full cylinder over the one-particle centred cube. -/
theorem abox_eq_univ_pi (N : ℕ) (ℓ : ℝ) :
    Submission.BoseGases.abox N ℓ = Set.univ.pi (fun _ : Fin N => Submission.BoseGases.acube ℓ) := by
  ext x; simp [Submission.BoseGases.abox]

/-- The restricted box measure is the product of the restricted one-particle cube measures. -/
theorem restrict_abox_eq_pi (N : ℕ) (ℓ : ℝ) :
    (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)
      = Measure.pi (fun _ : Fin N => (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
  rw [abox_eq_univ_pi, volume_pi, Measure.restrict_pi_pi]

/-- The `i`-th coordinate is quasi-measure-preserving from the restricted box measure on
`X N` to the restricted cube measure on the one-particle space. -/
theorem quasiMeasurePreserving_coord_abox {N : ℕ} {ℓ : ℝ} (i : Fin N) :
    Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X N => x i)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ))
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
  rw [restrict_abox_eq_pi]
  exact Measure.quasiMeasurePreserving_eval _ i

theorem fibreAeTransfer {N : ℕ} {ℓ : ℝ} {f f' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : f =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)] f') (i : Fin N) :
    (fun x : Submission.BoseGases.X N => f (x i))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x : Submission.BoseGases.X N => f' (x i)) :=
  (quasiMeasurePreserving_coord_abox i).ae_eq h

end Work.BoseFixB1S
