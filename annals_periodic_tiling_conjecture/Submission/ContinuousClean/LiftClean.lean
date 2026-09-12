import Mathlib
import Submission.Commons.PeriodicTiling.IsAperiodicTilingEquation_map_addEquiv
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift
import Submission.Commons.PeriodicTiling.isContinuousTiling_rigid_of_lift
import Submission.Commons.PeriodicTiling.discrete_tiling_of_rigid_lift
import Submission.Commons.PeriodicTiling.bounded_measurable_pos_of_finite_lift
import Submission.Commons.PeriodicTiling.exists_rigid_tile
import Submission.ContinuousClean.PeriodicDiscreteClean
import Submission.ContinuousClean.CountableClean

open Filter Bornology MeasureTheory
open scoped Pointwise

namespace Submission.ContinuousClean

open Commons.PeriodicTiling

/-- A bounded measurable subset `σ` of `ℝᵈ` forms an aperiodic continuous tiling equation if
there exists a continuous tiling set for it, but every such tiling set is not periodic.
This is the Commons version (safe to import together with `ChallengeDeps`). -/
structure IsAperiodicContinuousTilingEquation {d : ℕ} (σ : Set (Fin d → ℝ)) : Prop where
  solvable : ∃ Λ, Commons.PeriodicTiling.IsContinuousTiling σ Λ
  aperiodic : ∀ Λ, Commons.PeriodicTiling.IsContinuousTiling σ Λ →
    ¬ PeriodicTilingConjecture.IsPeriodicContinuousTilingSet Λ

theorem lift_discrete_aperiodic_clean
    {d : ℕ} (hd : 0 < d)
    {F : Set (Fin d → ℤ)} (hFfin : F.Finite) (hFne : F.Nonempty)
    (hFap : Commons.PeriodicTiling.IsAperiodicTilingEquation F) :
    ∃ σ : Set (Fin d → ℝ), IsBounded σ ∧ MeasurableSet σ ∧
      0 < volume σ ∧ IsAperiodicContinuousTilingEquation σ := by
  classical
  obtain ⟨R, hRb, hRm, hRp, hRfund, hRrigid⟩ := Commons.PeriodicTiling.exists_rigid_tile hd
  let emb : (Fin d → ℤ) →+ (Fin d → ℝ) :=
    { toFun := fun z => fun i => (z i : ℝ)
      map_zero' := by ext i; simp
      map_add' := by intro a b; ext i; simp [Pi.add_apply, Int.cast_add] }
  let σ : Set (Fin d → ℝ) := emb '' F + R
  have hprops := Commons.PeriodicTiling.bounded_measurable_pos_of_finite_lift (d := d) (F := F) hFfin hFne
    (R := R) hRb hRm hRp
  have hprops' : IsBounded σ ∧ MeasurableSet σ ∧ 0 < volume σ := by
    simpa [σ, emb] using hprops
  refine ⟨σ, hprops'.1, hprops'.2.1, hprops'.2.2, ?_⟩
  constructor
  · rcases hFap.solvable with ⟨A, hA⟩
    let Λ : Set (Fin d → ℝ) := emb '' A
    refine ⟨Λ, ?_⟩
    have hlift := Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift (d := d) (R := R) hRfund (F := F) (A := A) hA
    have hlift' : Commons.PeriodicTiling.IsContinuousTiling σ Λ := by
      simpa [σ, Λ, emb] using hlift
    exact hlift'
  · intro Λ hcont hper
    have hΛcount : Λ.Countable := countable_clean hper
    have hRcont : Commons.PeriodicTiling.IsContinuousTiling R (Λ + emb '' F) := by
      exact Commons.PeriodicTiling.isContinuousTiling_rigid_of_lift (d := d) (R := R) hRfund (F := F) hFne
        (Λ := Λ) hΛcount hcont
    obtain ⟨t, ht⟩ := hRrigid (Λ + emb '' F) hRcont
    let A : Set (Fin d → ℤ) := {z | emb z ∈ Λ - ({t} : Set (Fin d → ℝ))}
    have hAtile : Commons.PeriodicTiling.IsTiling F A := by
      simpa [A, emb] using Commons.PeriodicTiling.discrete_tiling_of_rigid_lift (d := d) (R := R) (F := F) hFne
        (Λ := Λ) (t := t) hRp hcont ht
    have hAperCon : PeriodicTilingConjecture.IsPeriodicTilingSet A := by
      simpa [A, emb] using periodic_discrete_clean (d := d) (F := F) hFne
        (Λ := Λ) hper (t := t) ht
    have hAper : Commons.PeriodicTiling.IsPeriodicTilingSet A := by
      simpa [Commons.PeriodicTiling.IsPeriodicTilingSet,
        PeriodicTilingConjecture.IsPeriodicTilingSet] using hAperCon
    exact hFap.aperiodic A hAtile hAper

end Submission.ContinuousClean
