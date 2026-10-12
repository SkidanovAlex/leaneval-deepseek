import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SlotProjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PV_algebra` — the projection-kernel algebra of `PV e`

`PV e x y = ∑ l, e l x * star (e l y)` (`SlotProjDefs.lean`) is the kernel of the orthogonal
projection onto `span{e l}` when the `e l` are orthonormal in `L²(ℝ³)`.  This file records the
three kernel identities consumed by the box ↔ model bridge (`BF3C_PLAN.md` §1):

* `star (PV e y x) = PV e x y` (self-adjointness — no hypothesis needed);
* `∫ z, PV e x z * PV e z y = PV e x y` (idempotence — uses orthonormality `horth`);
* the resolution form `∫ y, PV e x y * f y = ∑ l, e l x * ∫ y, star (e l y) * f y`
  (pure linearity of the integral over a finite sum).
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- `PV e` is self-adjoint: conjugating the two arguments of the kernel conjugates its value. -/
theorem star_PV_comm {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (x y : EuclideanSpace ℝ (Fin 3)) : star (PV e y x) = PV e x y := by
  simp only [PV, star_sum, star_mul, star_star]

/-- The pointwise expansion of the product of two `PV`-kernels as a double sum with the fibre
integrand `star (e l z) * e l' z` exposed. -/
theorem PV_mul_PV_eq_sum {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (x y z : EuclideanSpace ℝ (Fin 3)) :
    PV e x z * PV e z y =
      ∑ l : Fin m, ∑ l' : Fin m,
        (e l x * star (e l' y)) * (star (e l z) * e l' z) := by
  simp only [PV, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring

/-- Idempotence of the projection kernel: `PV` is a projection as soon as the modes are
orthonormal. -/
theorem integral_PV_mul_PV {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (horth : ∀ l l' : Fin m, ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l' : Fin m, MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (x y : EuclideanSpace ℝ (Fin 3)) : ∫ z, PV e x z * PV e z y = PV e x y := by
  have hpt : (fun z => PV e x z * PV e z y) =
      (fun z => ∑ l : Fin m, ∑ l' : Fin m,
        (e l x * star (e l' y)) * (star (e l z) * e l' z)) :=
    funext fun z => PV_mul_PV_eq_sum e x y z
  rw [hpt]
  rw [MeasureTheory.integral_finsetSum]
  swap
  · intro l _
    exact integrable_finsetSum _ fun l' _ => (hint l l').const_mul _
  rw [PV]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MeasureTheory.integral_finsetSum]
  swap
  · intro l' _
    exact (hint l l').const_mul _
  rw [Finset.sum_congr rfl (fun l' _ => integral_const_mul _ _)]
  simp only [horth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- The resolution of the identity form of `PV`: integrating against `PV e x ·` is the same as
summing the overlap integrals with the individual modes. -/
theorem integral_PV_mul_eq_sum {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : ∀ l : Fin m, MeasureTheory.Integrable (fun y => star (e l y) * f y))
    (x : EuclideanSpace ℝ (Fin 3)) :
    ∫ y, PV e x y * f y = ∑ l : Fin m, e l x * (∫ y, star (e l y) * f y) := by
  have hpt : (fun y => PV e x y * f y) =
      (fun y => ∑ l : Fin m, e l x * (star (e l y) * f y)) := by
    funext y
    simp only [PV, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hpt]
  rw [MeasureTheory.integral_finsetSum]
  swap
  · intro l _
    exact (hf l).const_mul _
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]

theorem PV_algebra {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (horth : ∀ l l' : Fin m, ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l' : Fin m, MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z)) :
    (∀ x y : EuclideanSpace ℝ (Fin 3), star (PV e y x) = PV e x y) ∧
    (∀ x y : EuclideanSpace ℝ (Fin 3), ∫ z, PV e x z * PV e z y = PV e x y) ∧
    (∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
      (∀ l : Fin m, MeasureTheory.Integrable (fun y => star (e l y) * f y)) →
      ∀ x : EuclideanSpace ℝ (Fin 3),
        ∫ y, PV e x y * f y = ∑ l : Fin m, e l x * (∫ y, star (e l y) * f y)) := by
  exact ⟨star_PV_comm e, integral_PV_mul_PV e horth hint, integral_PV_mul_eq_sum e⟩

end Work.BoseBoxFock
