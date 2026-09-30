import Mathlib
import Submission.Work.Thom.ModelThomDefs

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-!
# The total space of the trivial bundle as a product, and `ℝ¹ ≅ ℝ`

* `Work.Thom.trivProductHomeo` — the single chart of the trivial bundle `E = B × F → B` is the whole
  space, so its trivialisation is a homeomorphism `E ≃ₜ B × F`, carrying `E∖0` onto `B × (F∖0)`.
  Unlike the version in `Submission/Work/Thom/thomClass_trivial_contractible.lean`, no base point of
  `B` is needed.
* `Work.Thom.eucOneHomeo` — `EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ`.
-/

namespace Work.Thom

open CategoryTheory
open Work.TangentClasses

noncomputable section

/-- **The total space of the trivial bundle is the product.** -/
def trivProductHomeo (B : Type) [TopologicalSpace B] (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : Type) [Inhabited ι] :
    (RealBundle.trivial B F ι).TotalSpace ≃ₜ (B × F) :=
  (((RealBundle.trivial B F ι).localTriv (default : ι)).toOpenPartialHomeomorph
    |>.toHomeomorphOfSourceEqUnivTargetEqUniv
      (by rw [Bundle.Trivialization.source_eq,
        show ((RealBundle.trivial B F ι).localTriv (default : ι)).baseSet = Set.univ from rfl,
        Set.preimage_univ])
      (by rw [Bundle.Trivialization.target_eq,
        show ((RealBundle.trivial B F ι).localTriv (default : ι)).baseSet = Set.univ from rfl,
        Set.univ_prod_univ]))

theorem trivProductHomeo_apply (B : Type) [TopologicalSpace B] (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : Type) [Inhabited ι]
    (p : (RealBundle.trivial B F ι).TotalSpace) :
    trivProductHomeo B F ι p = (p.1, (show F from p.2)) := rfl

/-- `trivProductHomeo` identifies the complement of the zero section with `B × (F∖0)`. -/
theorem trivProductHomeo_zeroComplement (B : Type) [TopologicalSpace B] (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : Type) [Inhabited ι]
    (p : (RealBundle.trivial B F ι).TotalSpace) :
    p ∈ zeroComplement (RealBundle.trivial B F ι) ↔
      (trivProductHomeo B F ι p).2 ≠ 0 := by
  rw [mem_zeroComplement, trivProductHomeo_apply]

/-- **`ℝ¹` is `ℝ`**, as topological spaces. -/
def eucOneHomeo : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toHomeomorph

theorem eucOneHomeo_zero : eucOneHomeo (0 : EuclideanSpace ℝ (Fin 1)) = 0 := by
  simp [eucOneHomeo, PiLp.homeomorph, WithLp.equiv]

theorem eucOneHomeo_eq_zero {r : EuclideanSpace ℝ (Fin 1)} :
    eucOneHomeo r = 0 ↔ r = 0 := by
  constructor
  · intro h
    exact eucOneHomeo.injective (by rw [h, eucOneHomeo_zero])
  · intro h
    rw [h, eucOneHomeo_zero]

theorem eucOneHomeo_symm_eq_zero {r : ℝ} : eucOneHomeo.symm r = 0 ↔ r = 0 := by
  rw [Homeomorph.symm_apply_eq, eucOneHomeo_zero]

attribute [irreducible] trivProductHomeo

end

end Work.Thom
