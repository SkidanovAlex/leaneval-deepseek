import Mathlib
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular
import Submission.Work.Rep.starProjection_mul_comm_of_invt

namespace Work.Rep

/-- The orthogonal projection onto the kernel of an element `A` of the group von Neumann
algebra `N(G)` again lies in `N(G)`.

Since `N(G)` is the commutant of the right regular representation `ρ`, it suffices to show
that `A.ker.starProjection` commutes with every `ρ g`.  Both `ρ g` and its adjoint
`star (ρ g) = ρ g⁻¹` preserve `A.ker`: if `A x = 0` then
`A (ρ g x) = ρ g (A x) = 0` because `A` commutes with `ρ g`.  An operator that preserves
a closed subspace together with its adjoint commutes with the orthogonal projection onto
it (`Work.Rep.starProjection_mul_comm_of_invt`). -/
theorem starProjection_ker_orthogonal_mem_groupVonNeumann {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (A : Work.ORVonNeumann.boundedEnd G) (hA : A ∈ Work.ORVonNeumann.groupVonNeumann G) : (A.ker).starProjection ∈ Work.ORVonNeumann.groupVonNeumann G := by
  rw [Work.ORVonNeumann.mem_groupVonNeumann_iff]
  intro g
  -- `ρ g` preserves `A.ker`
  have h1 : ∀ x ∈ A.ker, Work.ORVonNeumann.Rep.rightRegHom (G := G) g x ∈ A.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change A (Work.ORVonNeumann.Rep.rightRegHom (G := G) g x) = 0
    change A x = 0 at hx
    have h := DFunLike.congr_fun ((Work.ORVonNeumann.mem_groupVonNeumann_iff A).1 hA g) x
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at h
    rw [h, hx, map_zero]
  -- the adjoint `star (ρ g) = ρ g⁻¹` preserves `A.ker`
  have h2 : ∀ x ∈ A.ker, star (Work.ORVonNeumann.Rep.rightRegHom (G := G) g) x ∈ A.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show star (Work.ORVonNeumann.Rep.rightRegHom (G := G) g)
          = Work.ORVonNeumann.Rep.rightRegHom (G := G) g⁻¹ from
        Work.ORVonNeumann.Rep.rightRegOp_star g]
    change A (Work.ORVonNeumann.Rep.rightRegHom (G := G) g⁻¹ x) = 0
    change A x = 0 at hx
    have h := DFunLike.congr_fun ((Work.ORVonNeumann.mem_groupVonNeumann_iff A).1 hA g⁻¹) x
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at h
    rw [h, hx, map_zero]
  exact (starProjection_mul_comm_of_invt h1 h2).symm

end Work.Rep
