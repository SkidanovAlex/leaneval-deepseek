import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- **The Nielsen automorphism `η` of the free group on two generators.**
Writing `a = of 0`, `b = of 1` for the two generators of `F (ULift (Fin 2))`, there is an
automorphism `η` with `η a = a` and `η b = a * b⁻¹`.  It is the free-group homomorphism
`g : a ↦ a`, `b ↦ a * b⁻¹`, which is bijective with inverse `h : a ↦ a`, `b ↦ b⁻¹ * a`; the two
composites fix both generators, hence are the identity by `FreeGroup.ext_hom`. -/
theorem freeGroup_etaAut :
    ∃ φ : FreeGroup (ULift.{u,0} (Fin 2)) ≃* FreeGroup (ULift.{u,0} (Fin 2)),
      φ (FreeGroup.of (ULift.up (0 : Fin 2))) = FreeGroup.of (ULift.up (0 : Fin 2)) ∧
      φ (FreeGroup.of (ULift.up (1 : Fin 2))) =
        FreeGroup.of (ULift.up (0 : Fin 2)) * (FreeGroup.of (ULift.up (1 : Fin 2)))⁻¹ := by
  let g : ULift.{u,0} (Fin 2) → FreeGroup (ULift.{u,0} (Fin 2)) := fun x =>
    if x = ULift.up (0 : Fin 2) then FreeGroup.of (ULift.up (0 : Fin 2))
    else FreeGroup.of (ULift.up (0 : Fin 2)) * (FreeGroup.of (ULift.up (1 : Fin 2)))⁻¹
  let h : ULift.{u,0} (Fin 2) → FreeGroup (ULift.{u,0} (Fin 2)) := fun x =>
    if x = ULift.up (0 : Fin 2) then FreeGroup.of (ULift.up (0 : Fin 2))
    else (FreeGroup.of (ULift.up (1 : Fin 2)))⁻¹ * FreeGroup.of (ULift.up (0 : Fin 2))
  have hψφ : (FreeGroup.lift h).comp (FreeGroup.lift g) = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ ?_
    intro x
    rcases x with ⟨i⟩
    fin_cases i <;> simp [FreeGroup.lift_apply_of, g, h]
  have hφψ : (FreeGroup.lift g).comp (FreeGroup.lift h) = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ ?_
    intro x
    rcases x with ⟨i⟩
    fin_cases i <;> simp [FreeGroup.lift_apply_of, g, h]
  refine ⟨MulEquiv.ofBijective (FreeGroup.lift g) (Function.bijective_iff_has_inverse.mpr
    ⟨⇑(FreeGroup.lift h), fun y => ?_, fun x => ?_⟩), ?_, ?_⟩
  · simpa using DFunLike.congr_fun hψφ y
  · simpa using DFunLike.congr_fun hφψ x
  · rw [MulEquiv.ofBijective_apply, FreeGroup.lift_apply_of]; simp [g]
  · rw [MulEquiv.ofBijective_apply, FreeGroup.lift_apply_of]; simp [g]

/-- **The vertex `η`-automorphism of the one-relator group `⟨a, b | a ^ l⟩`.**

The Nielsen automorphism `a ↦ a`, `b ↦ a * b⁻¹` of the free group fixes the relator `a ^ l`, hence
its normal closure, so it descends to an automorphism `Ψ` of `PresentedGroup {a ^ l}` with
`Ψ (of 1) = of 0 * (of 1)⁻¹` and `Ψ (of 0) = of 0`. -/
theorem vertexEta (l : ℕ) :
    ∃ Ψ : PresentedGroup ({FreeGroup.of (ULift.up (0 : Fin 2)) ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))) ≃*
        PresentedGroup ({FreeGroup.of (ULift.up (0 : Fin 2)) ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))),
      Ψ (PresentedGroup.of (ULift.up (1 : Fin 2))) =
        PresentedGroup.of (ULift.up (0 : Fin 2)) * (PresentedGroup.of (ULift.up (1 : Fin 2)))⁻¹ ∧
      Ψ (PresentedGroup.of (ULift.up (0 : Fin 2))) = PresentedGroup.of (ULift.up (0 : Fin 2)) := by
  obtain ⟨φ, hφ0, hφ1⟩ : ∃ φ : FreeGroup (ULift.{u,0} (Fin 2)) ≃* FreeGroup (ULift.{u,0} (Fin 2)),
      φ (FreeGroup.of (ULift.up (0 : Fin 2))) = FreeGroup.of (ULift.up (0 : Fin 2)) ∧
      φ (FreeGroup.of (ULift.up (1 : Fin 2))) =
        FreeGroup.of (ULift.up (0 : Fin 2)) * (FreeGroup.of (ULift.up (1 : Fin 2)))⁻¹ :=
    freeGroup_etaAut
  -- `φ` fixes the generator `a`, hence the relator `a ^ l` and its normal closure.
  have hmono : (↑φ : FreeGroup (ULift.{u,0} (Fin 2)) →* FreeGroup (ULift.{u,0} (Fin 2)))
      (FreeGroup.of (ULift.up (0 : Fin 2))) = FreeGroup.of (ULift.up (0 : Fin 2)) := hφ0
  have hmap : Subgroup.map (↑φ) (Subgroup.normalClosure ({FreeGroup.of (ULift.up (0 : Fin 2)) ^ l} :
        Set (FreeGroup (ULift.{u,0} (Fin 2))))) =
      Subgroup.normalClosure ({FreeGroup.of (ULift.up (0 : Fin 2)) ^ l} :
        Set (FreeGroup (ULift.{u,0} (Fin 2)))) := by
    rw [Subgroup.map_normalClosure _ _ φ.surjective]
    simp only [Set.image_singleton]
    rw [map_pow, hmono]
  refine ⟨QuotientGroup.congr _ _ φ hmap, ?_, ?_⟩
  · change (QuotientGroup.congr _ _ φ hmap)
      (QuotientGroup.mk (FreeGroup.of (ULift.up (1 : Fin 2)))) = _
    rw [QuotientGroup.congr_mk, hφ1]
    change PresentedGroup.mk _
        (FreeGroup.of (ULift.up (0 : Fin 2)) * (FreeGroup.of (ULift.up (1 : Fin 2)))⁻¹) =
      PresentedGroup.of (ULift.up (0 : Fin 2)) * (PresentedGroup.of (ULift.up (1 : Fin 2)))⁻¹
    rw [map_mul, map_inv]
    rfl
  · change (QuotientGroup.congr _ _ φ hmap)
      (QuotientGroup.mk (FreeGroup.of (ULift.up (0 : Fin 2)))) = _
    rw [QuotientGroup.congr_mk, hφ0]
    rfl

end Work.OROneRel
