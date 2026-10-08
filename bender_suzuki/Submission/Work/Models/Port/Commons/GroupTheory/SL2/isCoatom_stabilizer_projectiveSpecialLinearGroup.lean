import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

/-!
# The stabilizer of a point of the projective line is a maximal subgroup of `PSL(2, K)`

The group `PSL(2, K) = Matrix.ProjectiveSpecialLinearGroup (Fin 2) K` acts on the
projective line `ℙ K (Fin 2 → K)`.  This action is primitive (it is even 2-transitive,
a Mathlib instance), hence by the standard theorem of Wielandt a point stabilizer is a
maximal proper subgroup, i.e. a coatom of the subgroup lattice.

The only ingredient missing from Mathlib is the nontriviality of the projective line over
a field, supplied here as `nontrivial_projectivization_fin_two`.
-/

namespace Commons.GroupTheory.SL2

open scoped LinearAlgebra.Projectivization

/-- The projective line `ℙ K (Fin 2 → K)` over a field has at least two points:
the images of the two coordinate vectors `e₀ = Pi.single 0 1` and `e₁ = Pi.single 1 1`. -/
theorem nontrivial_projectivization_fin_two (K : Type*) [Field K] :
    Nontrivial (Projectivization K (Fin 2 → K)) := by
  refine ⟨Projectivization.mk K (Pi.single 0 1) (Pi.single_ne_zero_iff.2 one_ne_zero),
    Projectivization.mk K (Pi.single 1 1) (Pi.single_ne_zero_iff.2 one_ne_zero), ?_⟩
  intro h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have h1 : c = 0 := by
    have h1' := congr_fun hc 1
    simpa using h1'
  have h0 : (1 : K) = 0 := by
    have h0' := congr_fun hc 0
    simpa [h1] using h0'
  exact one_ne_zero h0

theorem isCoatom_stabilizer_projectiveSpecialLinearGroup {K : Type*} [Field K]
    (a : Projectivization K (Fin 2 → K)) :
    IsCoatom (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a) := by
  haveI : Nontrivial (Projectivization K (Fin 2 → K)) := nontrivial_projectivization_fin_two K
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (X := Projectivization K (Fin 2 → K)) a

end Commons.GroupTheory.SL2