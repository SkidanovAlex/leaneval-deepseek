import Submission.Work.GolodShafarevich.Setup

/-!
# Assembly lemmas for the Golod–Shafarevich inequality
-/

open scoped MonoidAlgebra

namespace Work.GolodShafarevich

/-- The range of `ψ` is the augmentation ideal (for a surjective `φ`). -/
theorem range_psi_eq_augIdeal {R : Type*} [CommRing R] {d : ℕ} {G : Type*} [Group G]
    (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ) :
    LinearMap.range (psi R φ) = augIdeal R G := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [psi_apply]
    exact Submodule.sum_mem (augIdeal R G) fun i _ =>
      Ideal.mul_mem_left (augIdeal R G) (x i) (mem_augIdeal_gGenSubOne R φ i)
  · intro x hx
    have hx' : x ∈ Submodule.span R (Set.range fun g : G => MonoidAlgebra.of R G g - 1) := by
      rw [← augIdeal_eq_span R G]
      exact hx
    have hle : Submodule.span R (Set.range fun g : G => MonoidAlgebra.of R G g - 1) ≤
        (LinearMap.range (psi R φ)).restrictScalars R := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨w, hw⟩ := hφ g
      exact ⟨Vfun R φ w, by rw [psi_Vfun, hw]⟩
    exact hle hx'

/-- The quotient of the group algebra by the augmentation ideal is one-dimensional. -/
theorem finrank_quotient_augIdeal {R : Type*} [CommRing R] {G : Type*} [Monoid G] :
    Module.finrank R (MonoidAlgebra R G ⧸ augIdeal R G) = 1 := by
  have hsingle : ∀ r : R, augAlgHom R G (MonoidAlgebra.single (1 : G) r) = r := by
    intro r
    rw [augAlgHom_apply]
    simp
  have hsurj : Function.Surjective (augAlgHom R G) := fun r =>
    ⟨algebraMap R (MonoidAlgebra R G) r, hsingle r⟩
  have e := Ideal.quotientKerAlgEquivOfSurjective (f := augAlgHom R G) hsurj
  have h := LinearEquiv.finrank_eq e.toLinearEquiv
  rw [show augIdeal R G = RingHom.ker (augAlgHom R G) from rfl, h, CommSemiring.finrank_self]

end Work.GolodShafarevich
