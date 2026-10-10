import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.CohomologicallyTrivial.SubQuotDefs
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The quotient `K ⧸ pK` of a `ℤ`-representation `K`

For a representation `K` of a group `G` over `Coeff = ULift ℤ` and a natural number `p`, this file
packages the submodule `pK ≤ K.V` (the image of multiplication by `p`), its stability under the
action of `G`, and the quotient representation `pMulQuot p K = K ⧸ pK` with its projection
`pMulQuotProj p K : K ⟶ pMulQuot p K`.

The point of using the concrete quotient `Work.CohomologicallyTrivial.quotRep` (rather than the
abstract cokernel `Limits.cokernel (p • 𝟙 K)`) is that its carrier is *literally*
`K.V ⧸ pMulSub p K`, so that finiteness and `p`-torsion of `K ⧸ pK` can be read off from
`Module.Finite.quotient` and from `Submodule.Quotient.mk_eq_zero`.
-/

-- The module structure on `K.V` carried by the representation `K` (rather than the generic
-- `ULift.module` instance) is the one used throughout this file.
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

namespace Work.SSGRoute.ExtChain

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {G : Type} [Group G]

/-- The submodule `pK ≤ K.V`: the image of the underlying linear map of `p • 𝟙 K`.  Its carrier is
the set of `p • x`, `x : K.V`. -/
def pMulSub (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Submodule SSGRoute.PTExt.Coeff K.V :=
  LinearMap.range ((p • 𝟙 K).hom.toLinearMap)

/-- The underlying map of `p • 𝟙 K` is multiplication by `p`. -/
theorem pMulSub_hom_apply (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) (x : K.V) :
    ((p • 𝟙 K).hom) x = p • x := by
  rw [Rep.nsmul_hom, Rep.hom_id]
  rfl

/-- Membership in `pK` is: being `p` times something. -/
theorem pMulSub_mem_iff (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) (y : K.V) :
    y ∈ pMulSub p K ↔ ∃ z : K.V, p • z = y := by
  rw [pMulSub, LinearMap.mem_range]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, (pMulSub_hom_apply p K z).trans hz⟩,
    fun ⟨z, hz⟩ => ⟨z, (pMulSub_hom_apply p K z).trans hz⟩⟩

/-- `pK` is stable under the action of `G`. -/
theorem pMulSub_stable (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∀ g : G, pMulSub p K ≤ Submodule.comap (K.ρ g) (pMulSub p K) := by
  intro g y hy
  rw [Submodule.mem_comap]
  rw [pMulSub_mem_iff] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  exact ⟨K.ρ g z, by
    simpa only [pMulSub_hom_apply] using Rep.hom_comm_apply (p • 𝟙 K) g z⟩

/-- The quotient representation `K ⧸ pK`. -/
abbrev pMulQuot (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) : Rep.{0} SSGRoute.PTExt.Coeff G :=
  Work.CohomologicallyTrivial.quotRep K (pMulSub p K) (pMulSub_stable p K)

/-- The projection `K ⟶ K ⧸ pK`. -/
abbrev pMulQuotProj (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) :
    K ⟶ pMulQuot p K :=
  Work.CohomologicallyTrivial.quotRepProj K (pMulSub p K) (pMulSub_stable p K)

/-- The projection to `K ⧸ pK` is the quotient map of `K.V` by `pK`. -/
theorem pMulQuotProj_apply (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) (y : K.V) :
    (pMulQuotProj p K).hom y = Submodule.Quotient.mk y := rfl

/-- The composite `K --p--> K --> K ⧸ pK` is zero. -/
theorem pMul_comp_pMulQuotProj (p : ℕ) (K : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (p • 𝟙 K) ≫ pMulQuotProj p K = 0 := by
  letI : Module SSGRoute.PTExt.Coeff K.V := K.hV2
  letI : Module SSGRoute.PTExt.Coeff (pMulQuot p K).V := (pMulQuot p K).hV2
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [pMulQuotProj, Work.CohomologicallyTrivial.quotRepProj, Rep.hom_comp, Rep.hom_ofHom,
    Rep.zero_hom, Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.comp_apply, LinearMap.zero_apply,
    Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

end

end Work.SSGRoute.ExtChain
