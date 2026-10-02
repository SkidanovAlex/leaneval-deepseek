import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The critical set of a `C¹` map is closed

`IsClosed {x | IsCriticalPoint f x}` for `f` with continuous derivative: a critical point is a point
where the derivative is not surjective, and surjectivity of a continuous linear map `ℝⁿ → ℝᵐ` is
characterised by `m ≤ rank`, an open condition
(Mathlib's `isOpen_setOfPred_nat_le_rank`).  This is what makes the image of the critical set on a
compact ball compact — hence measurable, as Fubini's argument for Sard's theorem requires.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (IsCriticalPoint)

/-- A continuous linear map `ℝⁿ → ℝᵐ` is surjective exactly when its rank is at least `m`. -/
theorem surjective_iff_rank_ge {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Function.Surjective L ↔
      (m : Cardinal) ≤ (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).rank := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  constructor
  · intro h
    have hrange : (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).range = ⊤ :=
      LinearMap.range_eq_top.mpr h
    rw [LinearMap.rank, hrange, rank_top ℝ (EuclideanSpace ℝ (Fin m)),
      ← Module.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin m)), hfin]
  · intro h
    have hle : (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).rank
        ≤ (m : Cardinal) := by
      refine le_trans (LinearMap.rank_le_range _) ?_
      rw [← Module.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin m)), hfin]
    have hrank : (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).rank
        = (m : Cardinal) := le_antisymm hle h
    have hfinrange : Module.finrank ℝ
        (LinearMap.range (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = m := by
      have h1 : ((Module.finrank ℝ (LinearMap.range
          (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) : ℕ) : Cardinal)
          = (m : Cardinal) := by
        rw [Module.finrank_eq_rank]
        rw [LinearMap.rank] at hrank
        exact hrank
      have h2 := congrArg Cardinal.toNat h1
      simpa only [Cardinal.toNat_natCast] using h2
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by rw [hfinrange, hfin]))

/-- **The set of critical points of a map with continuous derivative is closed.**  This is the
measurability input of the Fubini step of Sard's theorem. -/
theorem criticalSet_closed {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous fun x => fderiv ℝ f x) :
    IsClosed {x | IsCriticalPoint f x} := by
  have hset : {L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) |
        ¬ Function.Surjective L}
      = {L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) |
        (m : Cardinal) ≤ (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).rank}ᶜ := by
    ext L
    simp only [Set.mem_compl_iff]
    exact not_congr (surjective_iff_rank_ge L)
  have hclosed : IsClosed {L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) |
      ¬ Function.Surjective L} := by
    rw [hset]
    exact (isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
      (F := EuclideanSpace ℝ (Fin m)) m).isClosed_compl
  have : {x | IsCriticalPoint f x}
      = (fun x => fderiv ℝ f x) ⁻¹' {L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) |
          ¬ Function.Surjective L} := rfl
  rw [this]
  exact hclosed.preimage hf

end Work.ThomBordism.Transversality.Sard
