import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLComp.atom_comap
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

open Work.EKLContract

/-- Membership in the atom of a pull-back `σ`-algebra. -/
private lemma mem_atom_comap {f : X3 → X3} {m : MeasurableSpace X3} {x z : X3} :
    z ∈ atom (MeasurableSpace.comap f m) x ↔ f z ∈ atom m (f x) := by
  rw [Work.EKLComp.atom_comap]
  exact Iff.rfl

/-- `conjBy (-t)` is the preimage under conjugation by `aDiag t`. -/
private lemma mem_conjBy_neg (t : Fin 3 → ℝ) (S : Set SL3) (u : SL3) :
    u ∈ conjBy (-t) S ↔ aDiag t * u * (aDiag t)⁻¹ ∈ S := by
  simp only [conjBy, Set.mem_image]
  constructor
  · rintro ⟨v, hv, hv'⟩
    have heq : aDiag t * u * (aDiag t)⁻¹ = v := by
      rw [← hv', aDiag_neg_eq_inv]
      group
    rwa [heq]
  · intro hu
    refine ⟨aDiag t * u * (aDiag t)⁻¹, hu, ?_⟩
    rw [aDiag_neg_eq_inv]
    group

/-- An `A`-normalised subgroup `U` is stable under `aDiag t`-conjugation, two-sidedly. -/
private lemma mem_U_iff_conj {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) (u : SL3) :
    u ∈ U ↔ aDiag t * u * (aDiag t)⁻¹ ∈ U := by
  constructor
  · intro hu
    exact hU.2.1 t u hu
  · intro hu
    have h := hU.2.1 (-t) (aDiag t * u * (aDiag t)⁻¹) hu
    have heq : aDiag (-t) * (aDiag t * u * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = u := by
      rw [aDiag_neg_eq_inv]
      group
    rwa [heq] at h

theorem shape_comap_conj {A : MeasurableSpace Work.EKLContract.X3} {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    (t : Fin 3 → ℝ) (x : Work.EKLContract.X3) :
    Work.EKLContract.shape (MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) A) U x =
      Work.EKLC6Core.conjBy (-t) (Work.EKLContract.shape A U (Work.EKLContract.aDiag t • x)) := by
  ext u
  show u ∈ U ∧ u • x ∈ atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) x ↔
    u ∈ conjBy (-t) {v : SL3 | v ∈ U ∧ v • (aDiag t • x) ∈ atom A (aDiag t • x)}
  rw [mem_atom_comap (f := fun y : X3 => aDiag t • y) (m := A) (x := x) (z := u • x)]
  have hsm : aDiag t • (u • x) = (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • x) := by
    conv_lhs => rw [← mul_smul]
    conv_rhs => rw [← mul_smul]
    congr 1
    group
  rw [hsm, mem_conjBy_neg, mem_U_iff_conj hU t]
  exact Iff.rfl

end Work.EKLC6Core
