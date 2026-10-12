import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BF3cDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.meanProj_continuous`

`meanProj ℓ S Φ` averages a box state `Φ : X n → ℝ` in every slot `i ∈ S` over the centred
cube `acube ℓ` (`(ℓ³)⁻¹ ∫_{acube ℓ} Φ(…, xᵢ → y, …)`).  It is a parametric integral of a
continuous, compactly supported integrand, hence continuous as soon as `Φ` is.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

theorem meanProj_continuous (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ} (S : Finset (Fin n))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Continuous (Work.BoseBoxFock.meanProj ℓ S Φ) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _i : {i : Fin n // i ∈ S} => Submission.BoseGases.acube ℓ)) :=
    isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
  -- the assembly map `(x, z) ↦ (fun i => if i ∈ S then z ⟨i,_⟩ else x i)` is continuous
  have hasm : Continuous (fun p : Submission.BoseGases.X n ×
      ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) =>
      fun i : Fin n => if h : i ∈ S then p.2 ⟨i, h⟩ else p.1 i) := by
    apply continuous_pi
    intro i
    by_cases h : i ∈ S
    · rw [show (fun p : Submission.BoseGases.X n ×
          ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) =>
          (fun i : Fin n => if h : i ∈ S then p.2 ⟨i, h⟩ else p.1 i) i)
          = (fun p : Submission.BoseGases.X n ×
            ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) => p.2 ⟨i, h⟩) from by
            funext p; simp [h]]
      exact (continuous_apply (⟨i, h⟩ : {i : Fin n // i ∈ S})).comp continuous_snd
    · rw [show (fun p : Submission.BoseGases.X n ×
          ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) =>
          (fun i : Fin n => if h : i ∈ S then p.2 ⟨i, h⟩ else p.1 i) i)
          = (fun p : Submission.BoseGases.X n ×
            ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) => p.1 i) from by
            funext p; simp [h]]
      exact (continuous_apply i).comp continuous_fst
  have hg : Continuous (fun p : Submission.BoseGases.X n ×
      ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) =>
      (∏ _i : {i : Fin n // i ∈ S}, (ℓ ^ 3)⁻¹) *
        Φ (fun i : Fin n => if h : i ∈ S then p.2 ⟨i, h⟩ else p.1 i)) :=
    continuous_const.mul (hΦ.comp hasm)
  rw [show Work.BoseBoxFock.meanProj ℓ S Φ = (fun (x : Submission.BoseGases.X n) =>
      ∫ z in Set.pi Set.univ
        (fun _i : {i : Fin n // i ∈ S} => Submission.BoseGases.acube ℓ),
        (∏ _i : {i : Fin n // i ∈ S}, (ℓ ^ 3)⁻¹) *
          Φ (fun i : Fin n => if h : i ∈ S then z ⟨i, h⟩ else x i)) from rfl]
  refine continuous_parametric_integral_of_continuous
    (f := fun (x : Submission.BoseGases.X n)
      (z : {i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) =>
      (∏ _i : {i : Fin n // i ∈ S}, (ℓ ^ 3)⁻¹) *
        Φ (fun i : Fin n => if h : i ∈ S then z ⟨i, h⟩ else x i)) ?_ hK
  exact hg

end Work.BoseBoxFock
