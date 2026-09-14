import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs

open scoped BigOperators

namespace Commons.LinearAlgebra.FreeModule

lemma ideal_smul_top_pi {R : Type*} [CommRing R] (ι : Type*) [Fintype ι] (I : Ideal R) :
    (I • (⊤ : Submodule R (ι → R))) = Submodule.pi Set.univ (fun _ : ι => (I : Submodule R R)) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [Submodule.mem_pi]
    intro j hj
    exact I.mul_mem_right (x j) hr
  · intro x hx
    have hsum : x = ∑ i : ι, (Pi.basisFun R ι).equivFun x i • (Pi.basisFun R ι) i := by
      exact ((Pi.basisFun R ι).sum_equivFun x).symm
    rw [hsum]
    refine Submodule.sum_mem _ ?_
    intro i hi
    apply Submodule.smul_mem_smul
    · simpa using (Submodule.mem_pi.mp hx i trivial)
    · exact Submodule.mem_top

theorem nonempty_quotient_ideal_free_equiv {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R] (ι → R ⧸ I)) := by
  classical
  let Q : Submodule R (ι → R) := I • ⊤
  have hmap : (I • (⊤ : Submodule R M)).map (b.equivFun : M →ₗ[R] ι → R) = Q := by
    dsimp [Q]
    rw [Submodule.map_smul'']
    simp
  exact ⟨(Submodule.Quotient.equiv (I • ⊤ : Submodule R M) Q b.equivFun hmap).trans
    ((Submodule.quotEquivOfEq Q (Submodule.pi Set.univ (fun _ : ι => (I : Submodule R R)))
      (ideal_smul_top_pi ι I)).trans
      (Submodule.quotientPi (fun _ : ι => (I : Submodule R R))))⟩

end Commons.LinearAlgebra.FreeModule