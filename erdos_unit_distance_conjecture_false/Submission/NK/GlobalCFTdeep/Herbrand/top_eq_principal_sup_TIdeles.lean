import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-- The idèles which are local units at every finite place are `T`-idèles for every set `T` of
places: at a finite place outside `T` they are local units by hypothesis, and at an archimedean
place the local units are everything. -/
theorem integralIdeles_le_TIdeles_aux {L : Type} [Field L] [NumberField L]
    (T : Set (Place L)) : Idele.integralIdeles L ≤ TIdeles T := by
  intro x hx w _
  rcases w with w | q
  · exact Place.mem_localUnits_ofInfinite
  · exact hx (Place.ofFinite q) (Place.isFinite_ofFinite q)

theorem top_eq_principal_sup_TIdeles {L : Type} [Field L] [NumberField L] (T : Set (NK.GlobalCFT.Place L))
    (hgen : ∀ c : ClassGroup (NumberField.RingOfIntegers L),
      ∃ u ∈ TIdeles T, NK.GlobalCFT.IdeleClassGroup.idealClassMap L u = c) :
    (⊤ : Subgroup (NK.GlobalCFT.Idele L)) = NK.GlobalCFT.Idele.principalSubgroup L ⊔ TIdeles T := by
  refine le_antisymm ?_ le_top
  intro x _
  obtain ⟨u, huT, hu⟩ := hgen (IdeleClassGroup.idealClassMap L x)
  have hker : IdeleClassGroup.idealClassMap L (x * u⁻¹) = 1 := by
    rw [map_mul, map_inv, hu, mul_inv_cancel]
  have hmem := (IdeleClassGroup.idealClassMap_eq_one_iff (x * u⁻¹)).mp hker
  rw [Subgroup.mem_sup] at hmem ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  refine ⟨b, hb, a * u, Subgroup.mul_mem _ (integralIdeles_le_TIdeles_aux T ha) huT, ?_⟩
  have hx : x = a * b * u := by rw [hab]; group
  rw [hx, ← mul_assoc, mul_comm b a]

end NK.GlobalCFTdeep.Herbrand
