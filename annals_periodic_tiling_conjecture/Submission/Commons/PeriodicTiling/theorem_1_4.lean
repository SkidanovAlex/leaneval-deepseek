import Mathlib
import Submission.Commons.PeriodicTiling.functional_system_to_tiling_system
import Submission.Commons.PeriodicTiling.concatenate_aperiodic_tiling_system
import Submission.Commons.PeriodicTiling.existence_aperiodic_functional_system_core
import Submission.Commons.PeriodicTiling.IsAperiodicTilingEquation_map_addEquiv

open scoped Pointwise

namespace Commons.PeriodicTiling

/-- Product reassociation `((ℤ × ℤ × G) × H) × K ≃+ ℤ × ℤ × ((G × H) × K)`. -/
def productAssocAddEquiv (G : Type*) [AddCommGroup G] (H : Type*) [AddCommGroup H]
    (K : Type*) [AddCommGroup K] :
    (((ℤ × ℤ × G) × H) × K) ≃+ ℤ × ℤ × ((G × H) × K) where
  toFun := fun p => (p.1.1.1, p.1.1.2.1, ((p.1.1.2.2, p.1.2), p.2))
  invFun := fun q => (((q.1, q.2.1, q.2.2.1.1), q.2.2.1.2), q.2.2.2)
  left_inv := by
    intro p
    ext <;> rfl
  right_inv := by
    intro q
    ext <;> rfl
  map_add' := by
    intro p q
    ext <;> rfl

theorem theorem_1_4 : ∃ (G₀ : Type) (_ : AddCommGroup G₀) (_ : Finite G₀),
    ∃ F : Set (ℤ × ℤ × G₀), F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F := by
  classical
  rcases existence_aperiodic_functional_system_core with
    ⟨G₁, hGadd, hGfin, H, hHadd, hHfin, M, J, h, E, hE, hsol, haper⟩
  letI : AddCommGroup G₁ := hGadd
  letI : Finite G₁ := hGfin
  letI : AddCommGroup H := hHadd
  letI : Finite H := hHfin
  obtain ⟨M', F, hFfin, hFsol, hFaper⟩ :=
    functional_system_to_tiling_system (G := ℤ × ℤ × G₁) (H := H) J h E hE hsol haper
  let hsys : IsAperiodicTilingSystem F := ⟨hFsol, hFaper⟩
  obtain ⟨N, hN, F₂, hF₂fin, hF₂ne, hF₂ap⟩ := concatenate_aperiodic_tiling_system F hFfin hsys
  haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
  let e : (((ℤ × ℤ × G₁) × H) × ZMod N) ≃+ ℤ × ℤ × ((G₁ × H) × ZMod N) :=
    productAssocAddEquiv G₁ H (ZMod N)
  refine ⟨(G₁ × H) × ZMod N, inferInstance, inferInstance, e '' F₂, ?_, ?_,
    IsAperiodicTilingEquation_map_addEquiv e hF₂ap⟩
  · exact hF₂fin.image e
  · exact hF₂ne.image e

end Commons.PeriodicTiling
